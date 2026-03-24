import Mathlib
import Cay.Wordmetric.Wordmetric
import Cay.CayleyGraph
set_option linter.style.longLine false

structure IsQuasiIsometry {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  (f : X → Y) (A B C : ℝ) : Prop where
  bound : ∀ x₁ x₂ : X,
    (1 / A) * dist x₁ x₂ - B ≤ dist (f x₁) (f x₂) ∧
    dist (f x₁) (f x₂) ≤ A * dist x₁ x₂ + B

  is_dense : ∀ y : Y, ∃ x : X, dist (f x) y ≤ C

  hA : 1 ≤ A
  hB : 0 ≤ B
  hC : 0 ≤ C

/-- Wrapper type used to host distinct metric-space instances for different generating sets. -/
structure WordMetricType (G : Type*) (S : Set G) where
  val : G

variable {G : Type*} [Group G]

instance : CoeOut (WordMetricType G S) G where
  coe x := x.val

noncomputable instance wordMetricTypeMetricSpace (S : Set G) (hGen : IsGenerating S) :
    MetricSpace (WordMetricType G S) where
  dist x y := wordMetricDist S x.val y.val
  dist_self := by
    intro x
    simp [wordMetricDist, wordDist_self (S := S) x.val]
  dist_comm := by
    intro x y
    have hcomm : (wordDist S x.val y.val : ℝ) = (wordDist S y.val x.val : ℝ) := by
      exact_mod_cast (wordDist_symm (S := S) hGen x.val y.val)
    simpa [wordMetricDist] using hcomm
  dist_triangle := by
    intro x y z
    have htri :
        (wordDist S x.val z.val : ℝ)
          ≤ (wordDist S x.val y.val : ℝ) + (wordDist S y.val z.val : ℝ) := by
      exact_mod_cast (wordDist_triangle (S := S) hGen x.val y.val z.val)
    simpa [wordMetricDist] using htri
  eq_of_dist_eq_zero := by
    intro x y hdist
    have hreal : (wordDist S x.val y.val : ℝ) = 0 := by
      simpa [wordMetricDist] using hdist
    have hnat : wordDist S x.val y.val = 0 := by
      exact_mod_cast hreal
    have hxy : x.val = y.val := (wordDist_eq_zero_iff (S := S) hGen x.val y.val).1 hnat
    cases x
    cases y
    cases hxy
    rfl

namespace Cay.QuasiIsometry

variable {G : Type*} [Group G] {S T : Set G}

/-- Identity map between word-metric spaces is quasi-isometry when both generating sets are finite. -/
theorem id_isQuasiIsometry_of_finite_generating_sets
    (hSgen : IsGenerating S) (hTgen : IsGenerating T)
    (hSfin : S.Finite) (hTfin : T.Finite) :
    @IsQuasiIsometry
      (X := WordMetricType G S)
      (Y := WordMetricType G T)
      (wordMetricTypeMetricSpace (G := G) (S := S) hSgen)
      (wordMetricTypeMetricSpace (G := G) (S := T) hTgen)
      (fun x => ⟨(x : G)⟩)
      (max 1 (max
        (generatorBound (S := S) (T := T) hSgen hTfin)
        (generatorBound (S := T) (T := S) hTgen hSfin)) : ℝ)
      0 0 := by
  let cST : ℕ := generatorBound (S := S) (T := T) hSgen hTfin
  let cTS : ℕ := generatorBound (S := T) (T := S) hTgen hSfin
  let Aₙ : ℕ := max 1 (max cST cTS)
  have hAₙ : 1 ≤ Aₙ := by
    simp [Aₙ]
  have hcST : cST ≤ Aₙ := by
    simp [Aₙ, cST]
  have hcTS : cTS ≤ Aₙ := by
    simp [Aₙ, cTS]
  have hApos : (0 : ℝ) < (Aₙ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hAₙ)
  refine @IsQuasiIsometry.mk
    (WordMetricType G S)
    (WordMetricType G T)
    (wordMetricTypeMetricSpace (G := G) (S := S) hSgen)
    (wordMetricTypeMetricSpace (G := G) (S := T) hTgen)
    (fun x => ⟨(x : G)⟩)
    (max 1 (max cST cTS) : ℝ)
    0
    0
    ?bound ?dense ?hA ?hB ?hC
  · intro x₁ x₂
    have hSTnat : wordDist S (x₁ : G) (x₂ : G) ≤ cST * wordDist T (x₁ : G) (x₂ : G) := by
      simpa [cST] using
        (wordDist_compare_one_side (S := S) (T := T) hSgen hTgen hTfin (x₁ : G) (x₂ : G))
    have hTSnat : wordDist T (x₁ : G) (x₂ : G) ≤ cTS * wordDist S (x₁ : G) (x₂ : G) := by
      simpa [cTS] using
        (wordDist_compare_one_side (S := T) (T := S) hTgen hSgen hSfin (x₁ : G) (x₂ : G))
    have hST : (wordDist S (x₁ : G) (x₂ : G) : ℝ) ≤ (cST : ℝ) * (wordDist T (x₁ : G) (x₂ : G) : ℝ) := by
      exact_mod_cast hSTnat
    have hTS : (wordDist T (x₁ : G) (x₂ : G) : ℝ) ≤ (cTS : ℝ) * (wordDist S (x₁ : G) (x₂ : G) : ℝ) := by
      exact_mod_cast hTSnat
    have hTnonneg : 0 ≤ (wordDist T (x₁ : G) (x₂ : G) : ℝ) := by
      exact_mod_cast (Nat.zero_le (wordDist T (x₁ : G) (x₂ : G)))
    have hSnonneg : 0 ≤ (wordDist S (x₁ : G) (x₂ : G) : ℝ) := by
      exact_mod_cast (Nat.zero_le (wordDist S (x₁ : G) (x₂ : G)))
    have hleftMul : (cST : ℝ) * (wordDist T (x₁ : G) (x₂ : G) : ℝ)
        ≤ (Aₙ : ℝ) * (wordDist T (x₁ : G) (x₂ : G) : ℝ) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcST) hTnonneg
    have hright : (wordDist T (x₁ : G) (x₂ : G) : ℝ)
        ≤ (Aₙ : ℝ) * (wordDist S (x₁ : G) (x₂ : G) : ℝ) := by
      have hTSMul : (cTS : ℝ) * (wordDist S (x₁ : G) (x₂ : G) : ℝ)
          ≤ (Aₙ : ℝ) * (wordDist S (x₁ : G) (x₂ : G) : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcTS) hSnonneg
      exact le_trans hTS hTSMul
    have hleftScaled : (1 / (Aₙ : ℝ)) * (wordDist S (x₁ : G) (x₂ : G) : ℝ)
        ≤ (wordDist T (x₁ : G) (x₂ : G) : ℝ) := by
      have hSle : (wordDist S (x₁ : G) (x₂ : G) : ℝ)
          ≤ (Aₙ : ℝ) * (wordDist T (x₁ : G) (x₂ : G) : ℝ) := le_trans hST hleftMul
      have hdiv : (wordDist S (x₁ : G) (x₂ : G) : ℝ) / (Aₙ : ℝ) ≤ (wordDist T (x₁ : G) (x₂ : G) : ℝ) := by
        exact (div_le_iff₀ hApos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hSle)
      simpa [one_div, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
    constructor
    · simpa [wordMetricDist, Aₙ] using hleftScaled
    · simpa [wordMetricDist, Aₙ] using hright
  · intro y
    exact ⟨⟨(y : G)⟩, by simp⟩
  · exact_mod_cast hAₙ
  · norm_num
  · norm_num

end Cay.QuasiIsometry
