import Mathlib
import Cay.Automorphism.Basic

set_option linter.style.longLine false

/-- A lightweight notion of automorphism of the Cayley graph preserving adjacency. -/
structure CayleyGraphAut (G : Type*) [Group G] (S : Set G) where
  toEquiv : Equiv (CayleyGraph G S) (CayleyGraph G S)
  map_adj' : ∀ {u v : CayleyGraph G S}, Nonempty (u ⟶ v) ↔ Nonempty (toEquiv u ⟶ toEquiv v)

namespace CayleyGraphAut

variable {G : Type*} [Group G] {S : Set G}

@[ext]
theorem ext {f g : CayleyGraphAut G S} (h : f.toEquiv = g.toEquiv) : f = g := by
  cases f; cases g; simp_all

/-- Composition of two Cayley graph automorphisms. -/
instance : Mul (CayleyGraphAut G S) where
  mul f g :=
    { toEquiv := g.toEquiv.trans f.toEquiv
      map_adj' := by
        intro u v
        rw [g.map_adj', f.map_adj']
        simp [Equiv.trans] }

/-- The identity Cayley graph automorphism. -/
instance : One (CayleyGraphAut G S) where
  one :=
    { toEquiv := Equiv.refl _
      map_adj' := by simp }

/-- Inverse of a Cayley graph automorphism. -/
instance : Inv (CayleyGraphAut G S) where
  inv f :=
    { toEquiv := f.toEquiv.symm
      map_adj' := by
        intro u v
        rw [f.map_adj' (u := f.toEquiv.symm u) (v := f.toEquiv.symm v)]
        simp }

instance : Group (CayleyGraphAut G S) where
  mul_assoc f g h := by ext; simp [HMul.hMul, Mul.mul, Equiv.trans, Function.comp]
  one_mul f := by ext; simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one, Equiv.trans]
  mul_one f := by ext; simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one, Equiv.trans]
  inv_mul_cancel f := by
    ext x
    simp [HMul.hMul, Mul.mul, Inv.inv, OfNat.ofNat, One.one, Equiv.trans]

end CayleyGraphAut

namespace LabeledAut

variable {G : Type*} [Group G] {S : Set G}

@[ext]
theorem ext {f g : LabeledAut G S} (h : f.toEquiv = g.toEquiv) : f = g := by
  cases f
  cases g
  simp_all

instance : Mul (LabeledAut G S) where
  mul f g :=
    { toEquiv := g.toEquiv.trans f.toEquiv
      map_rel := by
        intro u v s
        rw [g.map_rel s, f.map_rel s]
        simp [Equiv.trans] }

instance : One (LabeledAut G S) where
  one :=
    { toEquiv := Equiv.refl _
      map_rel := by
        intro u v s
        simp }

instance : Inv (LabeledAut G S) where
  inv f :=
    { toEquiv := f.toEquiv.symm
      map_rel := by
        intro u v s
        have h := f.map_rel (u := f.toEquiv.symm u) (v := f.toEquiv.symm v) s
        simpa using h.symm }

instance : Group (LabeledAut G S) where
  mul_assoc f g h := by
    ext x
    rfl
  one_mul f := by
    ext x
    rfl
  mul_one f := by
    ext x
    rfl
  inv_mul_cancel f := by
    ext x
    change f.toEquiv.symm (f.toEquiv x) = x
    simp

end LabeledAut

namespace Cay.Automorphism

variable {G : Type*} [Group G] {S : Set G}

/-- Left multiplication gives a label-preserving automorphism. -/
def leftMul_labeledAut (g : G) : LabeledAut G S where
  toFun x := g * x
  invFun x := g⁻¹ * x
  left_inv x := by simp
  right_inv x := by simp
  map_rel := by
    intro u v s
    constructor <;> intro h
    · simpa [mul_assoc] using congrArg (fun x => g * x) h
    · have h' : g⁻¹ * (g * (u * s.val)) = g⁻¹ * (g * v) := by
        simpa [mul_assoc] using congrArg (fun x => g⁻¹ * x) h
      simpa [mul_assoc] using h'

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

/-- The left-regular action gives a homomorphism into label-preserving automorphisms. -/
def leftMul_labeledAut_hom : G →* LabeledAut G S where
  toFun := leftMul_labeledAut
  map_one' := by
    apply LabeledAut.ext
    ext x
    change (1 : G) * x = x
    simp
  map_mul' := by
    intro g h
    apply LabeledAut.ext
    ext x
    change (g * h) * x = g * (h * x)
    simp [mul_assoc]

/-- The left-regular representation into label-preserving automorphisms is injective. -/
theorem leftMul_labeledAut_hom_injective : Function.Injective (leftMul_labeledAut_hom (S := S)) := by
  intro g h hEq
  have hAt : (leftMul_labeledAut_hom (S := S) g).toFun 1 =
      (leftMul_labeledAut_hom (S := S) h).toFun 1 := by
    exact congrArg (fun f => f.toFun 1) hEq
  simpa [leftMul_labeledAut_hom, leftMul_labeledAut] using hAt

/-- A label-preserving automorphism is left multiplication by its value at the identity. -/
theorem labeledAut_eq_leftMul (hSymm : IsSymmetric S) (hGen : IsGenerating S)
  (f : LabeledAut G S) :
    leftMul_labeledAut (S := S) (f.toFun 1) = f := by
  apply labeledAut_determined_by_identity (S := S) hSymm hGen
  simp [leftMul_labeledAut]

/-- Cayley's theorem variant: for a symmetric generating set, G is isomorphic to
the group of label-preserving automorphisms of its Cayley graph. -/
def cayley_theorem_variant (hSymm : IsSymmetric S) (hGen : IsGenerating S) : G ≃* LabeledAut G S where
  toFun := leftMul_labeledAut_hom (S := S)
  invFun := fun f => f.toFun 1
  left_inv g := by
    simp [leftMul_labeledAut_hom, leftMul_labeledAut]
  right_inv f := by
    simpa [leftMul_labeledAut_hom] using (labeledAut_eq_leftMul (S := S) hSymm hGen f)
  map_mul' := by
    intro g h
    apply LabeledAut.ext
    ext x
    change (g * h) * x = g * (h * x)
    simp [mul_assoc]

/-- The map sending g to left-multiplication by g is a group homomorphism G →* Aut(Cay(G,S)). -/
def leftMul_hom : G →* CayleyGraphAut G S where
  toFun := leftMul_cayleyGraphAut
  map_one' := by
    apply CayleyGraphAut.ext
    ext v
    cases v with
    | mk x =>
        change ({ elt := 1 * x } : CayleyGraph G S) = { elt := x }
        simp
  map_mul' := by
    intro g h
    apply CayleyGraphAut.ext
    ext v
    cases v with
    | mk x =>
        change ({ elt := (g * h) * x } : CayleyGraph G S) = { elt := g * (h * x) }
        simp [mul_assoc]

/-- The left-regular representation into Aut(Cay(G,S)) is injective (Cayley embedding). -/
theorem leftMul_hom_injective : Function.Injective (leftMul_hom (S := S)) := by
  intro g h hEq
  have hAt : (leftMul_hom (S := S) g).toEquiv ⟨1⟩ =
      (leftMul_hom (S := S) h).toEquiv ⟨1⟩ := by
    exact congrArg (fun f => f.toEquiv ⟨1⟩) hEq
  simpa [leftMul_hom, leftMul_cayleyGraphAut] using hAt

end Cay.Automorphism
