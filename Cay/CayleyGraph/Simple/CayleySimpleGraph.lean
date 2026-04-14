import Cay.CayleyGraph.Quiver.CayleyGraph
set_option linter.style.longLine false
set_option linter.style.whitespace false


/-!
# Cayley Graph — SimpleGraph formulation

Vertices are elements of G; two vertices g, h are adjacent iff g⁻¹ * h ∈ S.
-/

variable {G : Type*} [Group G] (S : Set G)

-- ── Core definition ────────────────────────────────────────────────────────

/-- The Cayley graph of G with connection set S as a SimpleGraph.
    Two vertices g h are adjacent iff g⁻¹ * h ∈ S (and hence h⁻¹ * g ∈ S
    when S is symmetric). -/
def cayleySimpleGraph (G : Type*) [Group G] (S : Set G)
    (hS : IsSymmetric S) (hS1 : IsLoopless S) : SimpleGraph G where
  Adj g h := g⁻¹ * h ∈ S
  symm := by
    intro g h hgh
    show h⁻¹ * g ∈ S
    have : (g⁻¹ * h)⁻¹ = h⁻¹ * g := by group
    rw [← this]
    exact hS _ hgh
  loopless := by
    intro g hgg
    simp only [inv_mul_cancel] at hgg
    exact hS1 hgg

-- ── Basic edge example ─────────────────────────────────────────────────────

/-- Any s ∈ S gives an edge 1 ~ s in the Cayley graph. -/
example (hS : IsSymmetric S) (hS1 : IsLoopless S) (s : G) (hs : s ∈ S) :
    (cayleySimpleGraph G S hS hS1).Adj 1 s := by
  simp [cayleySimpleGraph, hs]

-- ── Vertex-transitivity ────────────────────────────────────────────────────
/-- Left multiplication by a is a graph automorphism:
    g ~ h ↔ (a*g) ~ (a*h). -/
theorem cayleySimpleGraph_vertexTransitive
    (hS : IsSymmetric S) (hS1 : IsLoopless S) (a g h : G) :
    (cayleySimpleGraph G S hS hS1).Adj g h ↔
    (cayleySimpleGraph G S hS hS1).Adj (a * g) (a * h) := by
  simp only [cayleySimpleGraph]
  constructor
  · intro hadj
    have : (a * g)⁻¹ * (a * h) = g⁻¹ * h := by group
    rw [this]; exact hadj
  · intro hadj
    have : (a * g)⁻¹ * (a * h) = g⁻¹ * h := by group
    rwa [← this]

-- ── Graph automorphism ─────────────────────────────────────────────────────

/-- The graph automorphism of left-multiplication by a. -/
def leftMultIso (hS : IsSymmetric S) (hS1 : IsLoopless S) (a : G) :
    (cayleySimpleGraph G S hS hS1) ≃g (cayleySimpleGraph G S hS hS1) where
  toFun    := (a * ·)
  invFun   := (a⁻¹ * ·)
  left_inv := by intro x; group
  right_inv := by intro x; group
  map_rel_iff' := by
    intro g h
    simp only [cayleySimpleGraph, Equiv.coe_fn_mk]
    constructor
    · intro hadj
      have key : (a * g)⁻¹ * (a * h) = g⁻¹ * h := by group
      rwa [key] at hadj
    · intro hadj
      have key : (a * g)⁻¹ * (a * h) = g⁻¹ * h := by group
      rw [key]; exact hadj


/-- Shift a walk by left multiplication -/
def cayleyWalk {G : Type*} [Group G] {S : Set G}
    (hS : IsSymmetric S) (hS1 : IsLoopless S)
    (a : G) {u v : G}
    (w : (cayleySimpleGraph G S hS hS1).Walk u v) :
    (cayleySimpleGraph G S hS hS1).Walk (a * u) (a * v) :=
  w.map (leftMultIso S hS hS1 a).toHom

-- ── Connectivity ────────────────────────────────────────────────────────────

namespace CayleySimpleGraph

/-- The Cayley graph is connected when S is a symmetric generating set
    and 1 ∉ S. -/
theorem isConnected (hS : IsSymmetric S) (hS1 : IsLoopless S) (hgen : IsGenerating S) :
    (cayleySimpleGraph G S hS hS1).Connected := by
  constructor
  · intro u v
    have h_union : S ∪ S⁻¹ = S := by
      ext s; constructor
      · rintro (h | h)
        · exact h
        · simp only [Set.mem_inv] at h
          have := hS s⁻¹ h; rwa [inv_inv] at this
      · intro h; exact Or.inl h
    have h_eq : (Subgroup.closure S).toSubmonoid = Submonoid.closure S := by
      have := Subgroup.closure_toSubmonoid S
      rw [h_union] at this; exact this
    have h_walk_from_one : ∀ {x : G}, x ∈ Submonoid.closure S →
        (cayleySimpleGraph G S hS hS1).Reachable 1 x := by
      intro x hx
      induction hx using Submonoid.closure_induction with
      | one => exact SimpleGraph.Reachable.refl _
      | mem s hs =>
        apply SimpleGraph.Reachable.trans (SimpleGraph.Reachable.refl _)
        rw [SimpleGraph.reachable_iff_reflTransGen]
        apply Relation.ReflTransGen.single
        simp [cayleySimpleGraph, hs]
      | mul a b _ _ iha ihb =>
        apply iha.trans
        obtain ⟨wb⟩ := ihb
        have : (cayleySimpleGraph G S hS hS1).Walk a (a * b) := by
          have hw := cayleyWalk hS hS1 a wb
          rwa [mul_one] at hw
        exact ⟨this⟩
    have hmem : u⁻¹ * v ∈ Subgroup.closure S := by
      rw [hgen]; trivial
    have hmono : u⁻¹ * v ∈ Submonoid.closure S := by
      rw [← h_eq]; exact hmem
    obtain ⟨w⟩ := h_walk_from_one hmono
    have hstart : u * 1 = u := mul_one u
    have hend   : u * (u⁻¹ * v) = v := by group
    rw [← hstart, ← hend]
    exact ⟨cayleyWalk hS hS1 u w⟩

-- ── Converse: connectivity implies generating ──────────────────────────────

theorem generating_of_connected (hS : IsSymmetric S) (hS1 : IsLoopless S) :
    (cayleySimpleGraph G S hS hS1).Connected → IsGenerating S := by
  intro hconn
  ext g
  simp only [Subgroup.mem_top, iff_true]
  obtain ⟨w⟩ := hconn.preconnected (1 : G) g
  suffices h : ∀ {u v : G}, (cayleySimpleGraph G S hS hS1).Walk u v →
      u ∈ Subgroup.closure S → v ∈ Subgroup.closure S by
    exact h w (Subgroup.one_mem _)
  intro u v walk hu
  induction walk with
  | nil => exact hu
  | @cons u mid v hadj tail ih =>
    apply ih
    simp only [cayleySimpleGraph] at hadj
    have hmid : mid = u * (u⁻¹ * mid) := by group
    rw [hmid]
    exact Subgroup.mul_mem _ hu (Subgroup.subset_closure hadj)

-- ── Biconditional ─────────────────────────────────────────────────────────

theorem connected_iff_generating (hS : IsSymmetric S) (hS1 : IsLoopless S) :
    (cayleySimpleGraph G S hS hS1).Connected ↔ IsGenerating S :=
  ⟨generating_of_connected S hS hS1, isConnected S hS hS1⟩

end CayleySimpleGraph
