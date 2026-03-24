import Mathlib
import Cay.QuasiIsometry.Basic

set_option linter.style.longLine false

namespace Cay.QuasiIsometry

/-- Two metric spaces are quasi-isometric if there exists a quasi-isometry between them. -/
def QuasiIsometric (X Y : Type*) [MetricSpace X] [MetricSpace Y] : Prop :=
  ∃ (f : X → Y) (A B C : ℝ), IsQuasiIsometry f A B C

theorem quasiIsometric_refl (X : Type*) [MetricSpace X] : QuasiIsometric X X := by
  sorry

theorem quasiIsometric_symm (X Y : Type*) [MetricSpace X] [MetricSpace Y] :
    QuasiIsometric X Y → QuasiIsometric Y X := by
  sorry

theorem quasiIsometric_trans (X Y Z : Type*)
    [MetricSpace X] [MetricSpace Y] [MetricSpace Z] :
    QuasiIsometric X Y → QuasiIsometric Y Z → QuasiIsometric X Z := by
  sorry

end Cay.QuasiIsometry
