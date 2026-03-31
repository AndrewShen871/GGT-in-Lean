import Mathlib
import Cay.Automorphism.Basic

set_option linter.style.longLine false

/-- A lightweight notion of automorphism of the Cayley graph preserving adjacency. -/
structure CayleyGraphAut (G : Type*) [Group G] (S : Set G) where
  toEquiv : Equiv (CayleyGraph G S) (CayleyGraph G S)
  map_adj' : ∀ {u v : CayleyGraph G S}, Nonempty (u ⟶ v) ↔ Nonempty (toEquiv u ⟶ toEquiv v)

namespace Cay.Automorphism

variable {G : Type*} [Group G] {S : Set G}

/-- Left multiplication gives a Cayley-graph automorphism. -/
def leftMul_cayleyGraphAut (g : G) : CayleyGraphAut G S := by
  refine
    { toEquiv :=
        { toFun := fun v => ⟨g * v.elt⟩
          invFun := fun v => ⟨g⁻¹ * v.elt⟩
          left_inv := ?_
          right_inv := ?_ }
      map_adj' := ?_ }
  · intro v
    cases v
    simp
  · intro v
    cases v
    simp
  · intro u v
    constructor
    · rintro ⟨e⟩
      refine ⟨⟨e.val, ?_⟩⟩
      constructor
      · exact e.property.1
      · simpa [mul_assoc] using congrArg (fun x => g * x) e.property.2
    · rintro ⟨e⟩
      refine ⟨⟨e.val, ?_⟩⟩
      constructor
      · exact e.property.1
      · have hEdge := e.property.2
        have : g * (u.elt * e.val) = g * v.elt := by
          simpa [mul_assoc] using hEdge
        exact mul_left_cancel this

/-- The left-regular action gives a homomorphism into permutations of the Cayley graph. -/
theorem leftRegular_to_cayleyPerm :
    ∃ φ : G →* Equiv.Perm (CayleyGraph G S), Function.Injective φ := by
  let φ : G →* Equiv.Perm (CayleyGraph G S) :=
    { toFun := fun g =>
        { toFun := fun v => ⟨g * v.elt⟩
          invFun := fun v => ⟨g⁻¹ * v.elt⟩
          left_inv := by intro v; cases v; simp
          right_inv := by intro v; cases v; simp }
      map_one' := by
        ext v
        cases v
        simp
      map_mul' := by
        intro g h
        ext v
        cases v
        simp [mul_assoc] }
  refine ⟨φ, ?_⟩
  intro g h hEq
  have hAt : φ g ⟨1⟩ = φ h ⟨1⟩ := congrArg (fun e => e ⟨1⟩) hEq
  have hElt : g * 1 = h * 1 := by
    simpa [φ] using congrArg CayleyGraph.elt hAt
  simpa using hElt

/-- Cayley's theorem: every group embeds into a permutation group. -/
theorem cayley_theorem :
    ∃ φ : G →* Equiv.Perm G, Function.Injective φ := by
  let φ : G →* Equiv.Perm G :=
    { toFun := fun g =>
        { toFun := fun x => g * x
          invFun := fun x => g⁻¹ * x
          left_inv := by intro x; simp
          right_inv := by intro x; simp }
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro g h
        ext x
        simp [mul_assoc] }
  refine ⟨φ, ?_⟩
  intro g h hEq
  have hAt : φ g 1 = φ h 1 := congrArg (fun e => e 1) hEq
  have hMul : g * 1 = h * 1 := by
    simpa [φ] using hAt
  simpa using hMul

/-- A label-preserving automorphism is determined by the image of the identity. -/
theorem labeledAut_determined_by_identity (hSymm : IsSymmetric S) (hGen : IsGenerating S)
  (f g : LabeledAut G S)
  (h : f.toFun 1 = g.toFun 1) :
    f = g := by
  have hPathEq : ∀ {u v : CayleyGraph G S}, (p : Quiver.Path u v) →
      f.toFun u.elt = g.toFun u.elt → f.toFun v.elt = g.toFun v.elt := by
    intro u v p
    induction p with
    | nil =>
        intro hu
        simpa using hu
    | cons tail e ih =>
        intro hu
        obtain ⟨s, hs, heq⟩ := e
        have hMid : f.toFun _ = g.toFun _ := ih hu
        have hfEdge : f.toFun _ * s = f.toFun _ := (f.map_rel ⟨s, hs⟩).mp heq
        have hgEdge : g.toFun _ * s = g.toFun _ := (g.map_rel ⟨s, hs⟩).mp heq
        calc
          f.toFun _ = f.toFun _ * s := by simpa using hfEdge.symm
          _ = g.toFun _ * s := by rw [hMid]
          _ = g.toFun _ := by simpa using hgEdge
  have hAll : ∀ x : G, f.toFun x = g.toFun x := by
    intro x
    obtain ⟨p⟩ := CayleyGraph.Isconnected (G := G) (S := S) hSymm hGen ⟨1⟩ ⟨x⟩
    exact hPathEq p h
  have hEquiv : f.toEquiv = g.toEquiv := by
    ext x
    exact hAll x
  cases f
  cases g
  cases hEquiv
  simp

end Cay.Automorphism
