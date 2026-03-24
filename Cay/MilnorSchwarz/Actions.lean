import Mathlib
import Cay.QuasiIsometry.Basic

set_option linter.style.longLine false

namespace Cay.MilnorSchwarz

/-- A placeholder structure for an isometric action of `G` on `X`. -/
structure IsometricAction (G X : Type*) [Group G] [MetricSpace X] where
  smul : G → X → X
  one_smul : ∀ x : X, smul 1 x = x
  mul_smul : ∀ g h : G, ∀ x : X, smul (g * h) x = smul g (smul h x)
  isometry_smul : ∀ g : G, ∀ x y : X, dist (smul g x) (smul g y) = dist x y

/-- Placeholder for proper discontinuity / metric properness of the action. -/
def ProperAction {G X : Type*} [Group G] [MetricSpace X]
    (_ρ : IsometricAction G X) : Prop :=
  True

/-- Placeholder for cocompactness / coboundedness of the action. -/
def CoboundedAction {G X : Type*} [Group G] [MetricSpace X]
    (_ρ : IsometricAction G X) : Prop :=
  True

/-- A geometric action is isometric, proper, and cobounded. -/
def GeometricAction {G X : Type*} [Group G] [MetricSpace X]
    (ρ : IsometricAction G X) : Prop :=
  ProperAction ρ ∧ CoboundedAction ρ

end Cay.MilnorSchwarz
