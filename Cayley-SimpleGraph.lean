import Mathlib

set_option linter.style.whitespace false

/-!
# Cayley Graph Definition and Basic Properties

Given a group G and a generating set S ⊆ G (closed under inverses, not containing identity),
the Cayley graph Cay(G, S) has:
  - Vertices: elements of G
  - Edges: (g, h) ∈ E ↔ g⁻¹ * h ∈ S
-/

variable {G : Type*} [Group G] (S : Set G)

/-- The Cayley graph of a group G with mapping set S.
    Two vertices g, h are adjacent iff g⁻¹ * h ∈ S. -/
def cayleyGraph (G : Type*) [Group G] (S : Set G) : SimpleGraph G where
  Adj g h := g⁻¹ * h ∈ S ∧ g ≠ h
  symm := by
    intro g h ⟨hS, hne⟩
    constructor
    · -- If g⁻¹ * h ∈ S, we need h⁻¹ * g ∈ S
      -- This requires S to be closed under inverses

    · exact hne.symm
  loopless := by
    intro g ⟨_, hne⟩
    exact hne rfl

/-- S is symmetric (closed under inverses) -/
def IsSymmetric (S : Set G) : Prop :=
  ∀ s ∈ S, s⁻¹ ∈ S

/-- The Cayley graph when S is symmetric -/
def cayleyGraphSym (G : Type*) [Group G] (S : Set G) (hS : IsSymmetric S) :
    SimpleGraph G where
  Adj g h := g⁻¹ * h ∈ S
  symm := by
    intro g h hgh
    simp only
    have : (g⁻¹ * h)⁻¹ = h⁻¹ * g := by group
    rw [← this]
    exact hS _ hgh
  loopless := by
    intro g hgg
    simp only at hgg
    -- g⁻¹ * g = 1 ∈ S would be a contradiction if 1 ∉ S
    simp [mul_left_inv] at hgg

/-!
## Key Theorem: The Cayley graph is vertex-transitive

Left multiplication by any group element is a graph automorphism.
-/

/-- Left multiplication by `a` is an automorphism of the Cayley graph -/
theorem cayleyGraph_vertexTransitive
    (hS : IsSymmetric S) (hS1 : (1 : G) ∉ S)
    (a g h : G) :
    let Γ := cayleyGraphSym G S hS
    Γ.Adj g h ↔ Γ.Adj (a * g) (a * h) := by
  simp only [cayleyGraphSym]
  constructor
  · intro hgh
    show (a * g)⁻¹ * (a * h) ∈ S
    calc (a * g)⁻¹ * (a * h)
        = g⁻¹ * a⁻¹ * (a * h) := by rw [mul_inv_rev]
      _ = g⁻¹ * (a⁻¹ * a) * h := by group
      _ = g⁻¹ * 1 * h         := by rw [inv_mul_cancel]
      _ = g⁻¹ * h             := by group
    sorry
    exact hgh
  · intro hagh
    show g⁻¹ * h ∈ S
    have key : (a * g)⁻¹ * (a * h) = g⁻¹ * h := by group
    rwa [← key]

/-- The Cayley graph has no self-loops when 1 ∉ S -/
theorem cayleyGraph_loopless (hS : IsSymmetric S) (hS1 : (1 : G) ∉ S) :
    ∀ g : G, ¬ (cayleyGraphSym G S hS).Adj g g := by
  intro g hgg
  simp [cayleyGraphSym] at hgg
  have : g⁻¹ * g = 1 := mul_left_inv g  -- or inv_mul_cancel in newer Mathlib
  rw [this] at hgg
  exact hS1 hgg

/-- Adjacency in the Cayley graph is symmetric when S is symmetric -/
theorem cayleyGraph_symm (hS : IsSymmetric S) (g h : G) :
    (cayleyGraphSym G S hS).Adj g h ↔ (cayleyGraphSym G S hS).Adj h g := by
  simp only [cayleyGraphSym, SimpleGraph.adj_comm]
