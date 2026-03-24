import Mathlib
import Cay.QuasiIsometry.Equivalence

set_option linter.style.longLine false

namespace Cay.QuasiIsometry

variable {G : Type*} [Group G] {S T : Set G}

/-- Wrapper name for the metric-space model attached to a generating set, viewed as the Cayley-graph metric space. -/
abbrev CayleyGraphMetricType (G : Type*) (S : Set G) := WordMetricType G S

/-- Cayley graphs of a finitely generated group with respect to two finite generating sets are quasi-isometric. -/
theorem cayleyGraphs_quasiIsometric_of_finite_generating_sets
    (hSgen : IsGenerating S) (hTgen : IsGenerating T)
    (hSfin : S.Finite) (hTfin : T.Finite) :
    @QuasiIsometric
      (CayleyGraphMetricType G S)
      (CayleyGraphMetricType G T)
      (wordMetricTypeMetricSpace (G := G) (S := S) hSgen)
      (wordMetricTypeMetricSpace (G := G) (S := T) hTgen) := by
  sorry

/-- The identity on the underlying group gives the quasi-isometry between the two Cayley-graph metric models. -/
theorem id_quasiIsometry_between_cayleyGraphs
    (hSgen : IsGenerating S) (hTgen : IsGenerating T)
    (hSfin : S.Finite) (hTfin : T.Finite) :
    @IsQuasiIsometry
      (CayleyGraphMetricType G S)
      (CayleyGraphMetricType G T)
      (wordMetricTypeMetricSpace (G := G) (S := S) hSgen)
      (wordMetricTypeMetricSpace (G := G) (S := T) hTgen)
      (fun x => ⟨(x : G)⟩)
      (max 1 (max
        (generatorBound (S := S) (T := T) hSgen hTfin)
        (generatorBound (S := T) (T := S) hTgen hSfin)) : ℝ)
      0 0 := by
  sorry

/-- Changing finite generating sets does not change the quasi-isometry class of the Cayley graph. -/
theorem cayleyGraph_quasiIsometryClass_independent_of_finite_generating_set
    (hSgen : IsGenerating S) (hTgen : IsGenerating T)
    (hSfin : S.Finite) (hTfin : T.Finite) :
    @QuasiIsometric
      (CayleyGraphMetricType G S)
      (CayleyGraphMetricType G T)
      (wordMetricTypeMetricSpace (G := G) (S := S) hSgen)
      (wordMetricTypeMetricSpace (G := G) (S := T) hTgen) := by
  sorry

end Cay.QuasiIsometry
