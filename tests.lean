import Mathlib

open MeasureTheory Real Set

/-!
### 1. Define the function sequence
We define the sequence `f_n(x) = sin(nx)` on the real line.
-/
noncomputable def sin_seq (n : ℕ) (x : ℝ) : ℝ := sin ((n : ℝ) * x)

/-!
### 2. Define a simplified $L^2$ inner product
We define the `L^2` inner product of two functions on the interval `[-π, π]`.
-/
noncomputable def l2_inner (f g : ℝ → ℝ) : ℝ :=
  ∫ x in -π..π, f x * g x

lemma integral_cos_nat_mul (k : ℕ) (hk : k ≠ 0) :
    ∫ x in -π..π, cos ((k : ℝ) * x) = 0 := by
  calc
    ∫ x in -π..π, cos ((k : ℝ) * x)
      = ((k : ℝ)⁻¹) * ∫ u in (k : ℝ) * (-π)..(k : ℝ) * π, cos u := by
          simpa [smul_eq_mul] using
            (intervalIntegral.integral_comp_mul_left (f := fun u : ℝ => cos u)
              (a := -π) (b := π) (c := (k : ℝ)) (by exact_mod_cast hk))
    _ = ((k : ℝ)⁻¹) * (sin ((k : ℝ) * π) - sin ((k : ℝ) * (-π))) := by
          rw [integral_cos]
    _ = 0 := by
          simp [Real.sin_nat_mul_pi, sin_neg]

lemma integral_cos_int_mul (k : ℤ) (hk : k ≠ 0) :
    ∫ x in -π..π, cos ((k : ℝ) * x) = 0 := by
  calc
    ∫ x in -π..π, cos ((k : ℝ) * x)
      = ((k : ℝ)⁻¹) * ∫ u in (k : ℝ) * (-π)..(k : ℝ) * π, cos u := by
          simpa [smul_eq_mul] using
            (intervalIntegral.integral_comp_mul_left (f := fun u : ℝ => cos u)
              (a := -π) (b := π) (c := (k : ℝ)) (by exact_mod_cast hk))
    _ = ((k : ℝ)⁻¹) * (sin ((k : ℝ) * π) - sin ((k : ℝ) * (-π))) := by
          rw [integral_cos]
    _ = 0 := by
          simp [Real.sin_int_mul_pi, sin_neg]

lemma integral_cos_sub_nat_mul (m n : ℕ) (h : m ≠ n) :
    ∫ x in -π..π, cos (((m : ℝ) * x) - ((n : ℝ) * x)) = 0 := by
  have hmn : ((m : ℤ) - n : ℤ) ≠ 0 := by
    omega
  rw [show (∫ x in -π..π, cos (((m : ℝ) * x) - ((n : ℝ) * x))) =
      ∫ x in -π..π, cos ((((m : ℤ) - n : ℤ) : ℝ) * x) by
        refine intervalIntegral.integral_congr_ae ?_
        exact MeasureTheory.ae_of_all _ fun x _ => by
          congr 1
          rw [Int.cast_sub]
          rw [sub_mul]
          simp [mul_comm]]
  exact integral_cos_int_mul ((m : ℤ) - n) hmn

lemma integral_cos_add_nat_mul (m n : ℕ) (h : m ≠ n) :
    ∫ x in -π..π, cos (((m : ℝ) * x) + ((n : ℝ) * x)) = 0 := by
  have hmn : m + n ≠ 0 := by
    omega
  rw [show (∫ x in -π..π, cos (((m : ℝ) * x) + ((n : ℝ) * x))) =
      ∫ x in -π..π, cos (((m + n : ℕ) : ℝ) * x) by
        refine intervalIntegral.integral_congr_ae ?_
        exact MeasureTheory.ae_of_all _ fun x _ => by
          congr 1
          rw [Nat.cast_add]
          ring]
  exact integral_cos_nat_mul (m + n) hmn

/-!
### 3. Main theorem: orthogonality statement
This is the mathematical orthogonality statement.
The proof uses the product-to-sum identity together with Mathlib interval-integral lemmas.
-/
theorem sin_orthogonality (m n : ℕ) (h : m ≠ n) :
    l2_inner (sin_seq m) (sin_seq n) = 0 := by
  have hsub_int : IntervalIntegrable
      (fun x : ℝ => cos (((m : ℝ) * x) - ((n : ℝ) * x))) volume (-π) π := by
    apply Continuous.intervalIntegrable
    continuity
  have hadd_int : IntervalIntegrable
      (fun x : ℝ => cos (((m : ℝ) * x) + ((n : ℝ) * x))) volume (-π) π := by
    apply Continuous.intervalIntegrable
    continuity
  calc
    l2_inner (sin_seq m) (sin_seq n)
      = ∫ x in -π..π, (cos (((m : ℝ) * x) - ((n : ℝ) * x)) -
          cos (((m : ℝ) * x) + ((n : ℝ) * x))) / 2 := by
            unfold l2_inner sin_seq
            refine intervalIntegral.integral_congr_ae ?_
            exact MeasureTheory.ae_of_all _ fun x _ => by
              have hmul := Real.two_mul_sin_mul_sin ((m : ℝ) * x) ((n : ℝ) * x)
              nlinarith
    _ = ∫ x in -π..π, (1 / 2 : ℝ) *
          (cos (((m : ℝ) * x) - ((n : ℝ) * x)) -
            cos (((m : ℝ) * x) + ((n : ℝ) * x))) := by
            refine intervalIntegral.integral_congr_ae ?_
            exact MeasureTheory.ae_of_all _ fun x _ => by ring
    _ = (1 / 2 : ℝ) *
        ∫ x in -π..π, (cos (((m : ℝ) * x) - ((n : ℝ) * x)) -
          cos (((m : ℝ) * x) + ((n : ℝ) * x))) := by
            rw [intervalIntegral.integral_const_mul]
    _ = (1 / 2 : ℝ) *
        ((∫ x in -π..π, cos (((m : ℝ) * x) - ((n : ℝ) * x))) -
          ∫ x in -π..π, cos (((m : ℝ) * x) + ((n : ℝ) * x))) := by
            rw [intervalIntegral.integral_sub hsub_int hadd_int]
    _ = 0 := by
          rw [integral_cos_sub_nat_mul m n h, integral_cos_add_nat_mul m n h]
          ring

/-!
### 4. Check a basic property: oddness
Lean can verify symmetry properties directly.
This is often useful for simplifying integrals.
-/
example (n : ℕ) : ∀ x, sin_seq n (-x) = -sin_seq n x := by
  intro x
  unfold sin_seq
  simp [sin_neg]
