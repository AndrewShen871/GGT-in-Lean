import Mathlib
import Cay.MilnorSchwarz.OrbitMap
import Cay.QuasiIsometry.Equivalence

set_option linter.style.longLine false

namespace Cay.MilnorSchwarz

open Cay.QuasiIsometry

variable {G X : Type*} [Group G] [MetricSpace X]

/-- The word-metric model of the acting group used in the Milnor-Schwarz statement. -/
abbrev MilnorSchwarzGroupType (G : Type*) (S : Set G) := WordMetricType G S

/-- Skeleton of the Milnor-Schwarz lemma: a geometric action yields a quasi-isometry from the group to the space. -/
theorem milnor_schwarz_lemma
    {S : Set G} (hGen : IsGenerating S)
    (ρ : IsometricAction G X) (hGeom : GeometricAction ρ) (x0 : X) :
    ∃ A B C : ℝ,
      @IsQuasiIsometry
        (MilnorSchwarzGroupType G S)
        X
        (wordMetricTypeMetricSpace (G := G) (S := S) hGen)
        inferInstance
        (fun g => orbitMap ρ x0 (g : G))
        A B C := by
  sorry

/-- Skeleton corollary: the group with any word metric is quasi-isometric to the ambient space. -/
theorem group_quasiIsometric_space_of_geometric_action
    {S : Set G} (hGen : IsGenerating S)
    (ρ : IsometricAction G X) (hGeom : GeometricAction ρ) :
    @QuasiIsometric
      (MilnorSchwarzGroupType G S)
      X
      (wordMetricTypeMetricSpace (G := G) (S := S) hGen)
      inferInstance := by
  sorry

/-- Skeleton corollary: two spaces admitting geometric actions of the same group are quasi-isometric. -/
theorem spaces_quasiIsometric_of_common_geometric_action
    {Y : Type*} [MetricSpace Y]
    {S : Set G} (hGen : IsGenerating S)
    (ρX : IsometricAction G X) (hGeomX : GeometricAction ρX)
    (ρY : IsometricAction G Y) (hGeomY : GeometricAction ρY) :
    QuasiIsometric X Y := by
  sorry

end Cay.MilnorSchwarz
