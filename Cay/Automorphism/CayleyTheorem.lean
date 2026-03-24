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
  sorry

/-- The left-regular action gives a homomorphism into permutations of the Cayley graph. -/
theorem leftRegular_to_cayleyPerm :
    ∃ φ : G →* Equiv.Perm (CayleyGraph G S), Function.Injective φ := by
  sorry

/-- Cayley's theorem: every group embeds into a permutation group. -/
theorem cayley_theorem :
    ∃ φ : G →* Equiv.Perm G, Function.Injective φ := by
  sorry

/-- A label-preserving automorphism is determined by the image of the identity. -/
theorem labeledAut_determined_by_identity (f g : LabeledAut G S)
  (h : f.toFun 1 = g.toFun 1) :
    f = g := by
  sorry

end Cay.Automorphism
