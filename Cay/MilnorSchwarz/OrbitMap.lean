import Mathlib
import Cay.MilnorSchwarz.Actions
import Cay.Wordmetric.Wordmetric

set_option linter.style.longLine false

namespace Cay.MilnorSchwarz

variable {G X : Type*} [Group G] [MetricSpace X]

/-- The orbit map associated to a point `x0`. -/
def orbitMap (ρ : IsometricAction G X) (x0 : X) : G → X :=
  fun g => ρ.smul g x0

/-- Skeleton: the orbit map is coarsely Lipschitz with respect to the word metric. -/
theorem orbitMap_coarselyLipschitz
    {S : Set G} (hGen : IsGenerating S)
    (ρ : IsometricAction G X) (x0 : X) :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ g h : G,
      dist (orbitMap ρ x0 g) (orbitMap ρ x0 h)
        ≤ A * wordMetricDist S g h + B := by
  sorry

/-- Skeleton: the orbit map is coarsely expansive under a geometric action. -/
theorem orbitMap_coarselyExpansive
    {S : Set G} (hGen : IsGenerating S)
    (ρ : IsometricAction G X) (hGeom : GeometricAction ρ) (x0 : X) :
    ∃ A B : ℝ, 1 ≤ A ∧ 0 ≤ B ∧ ∀ g h : G,
      (1 / A) * wordMetricDist S g h - B
        ≤ dist (orbitMap ρ x0 g) (orbitMap ρ x0 h) := by
  sorry

/-- Skeleton: a cobounded action makes the orbit map coarsely surjective. -/
theorem orbitMap_coarselySurjective
    (ρ : IsometricAction G X) (hGeom : GeometricAction ρ) (x0 : X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : X, ∃ g : G, dist (orbitMap ρ x0 g) y ≤ C := by
  sorry

end Cay.MilnorSchwarz
