import Mathlib
import Cay
import Cay.Wordlength
set_option linter.style.longLine false
variable {G : Type*} [Group G] {S : Set G}

/-- Real-valued word metric obtained from `wordDist`. -/
noncomputable def wordMetricDist (S : Set G) (g h : G) : ℝ :=
  (wordDist S g h : ℝ)

/-- Normalization: distance from a point to itself is zero. -/
lemma wordMetricDist_self (_ : IsGenerating S) (g : G) :
    wordMetricDist S g g = 0 := by
  simp [wordMetricDist, wordDist_self (S := S) g]

/-- Distance from identity matches word length. -/
lemma wordMetricDist_one_right (g : G) :
    wordMetricDist S g 1 = wordLength S g⁻¹ := by
  simp [wordMetricDist, wordDist]









section CompareGeneratingSets

variable {S T : Set G}

/-- Step 1: max `S`-word-length of elements of a finite generating set `T`. -/
noncomputable def generatorBound
  (_hSgen : IsGenerating S) (hTfin : T.Finite) : ℕ :=
  (hTfin.toFinset.sup fun t => wordLength S t)

lemma wordLength_le_generatorBound
    (hSgen : IsGenerating S) (hTfin : T.Finite)
    {t : G} (ht : t ∈ T) :
    wordLength S t ≤ generatorBound (S := S) (T := T) hSgen hTfin := by
  unfold generatorBound
  have ht' : t ∈ hTfin.toFinset := (Set.Finite.mem_toFinset hTfin).2 ht
  exact Finset.le_sup (s := hTfin.toFinset) (f := fun x => wordLength S x)
    ht'

lemma wordLength_le_generatorBound_of_mem_or_inv
    (hSgen : IsGenerating S) (hTfin : T.Finite)
    {t : G} (ht : t ∈ T ∨ t⁻¹ ∈ T) :
    wordLength S t ≤ generatorBound (S := S) (T := T) hSgen hTfin := by
  rcases ht with ht | ht
  · exact wordLength_le_generatorBound (S := S) (T := T) hSgen hTfin ht
  · have hInv : wordLength S t = wordLength S t⁻¹ := by
      simpa [inv_inv] using (wordLength_inv_eq (S := S) hSgen (g := t⁻¹))
    calc
      wordLength S t = wordLength S t⁻¹ := hInv
      _ ≤ generatorBound (S := S) (T := T) hSgen hTfin :=
        wordLength_le_generatorBound (S := S) (T := T) hSgen hTfin ht

lemma wordLength_prod_le_sum_wordLength
    (hSgen : IsGenerating S) :
    ∀ w : List G, wordLength S w.prod ≤ (w.map (wordLength S)).sum
  | [] => by
      simp [wordLength_one]
  | x :: xs => by
      have hmul := wordLength_mul_le (S := S) hSgen x xs.prod
      have htail := wordLength_prod_le_sum_wordLength hSgen xs
      calc
        wordLength S (List.prod (x :: xs))
            = wordLength S (x * xs.prod) := by simp
        _ ≤ wordLength S x + wordLength S xs.prod := hmul
        _ ≤ wordLength S x + (xs.map (wordLength S)).sum :=
          Nat.add_le_add_left htail _
        _ = ((x :: xs).map (wordLength S)).sum := by simp

lemma sum_wordLength_le_mul_length
    (A : ℕ) :
    ∀ w : List G,
      (∀ x ∈ w, wordLength S x ≤ A) →
      (w.map (wordLength S)).sum ≤ A * w.length
  | [], _ => by simp
  | x :: xs, h => by
      have hx : wordLength S x ≤ A := h x (by simp)
      have hxs : ∀ y ∈ xs, wordLength S y ≤ A := by
        intro y hy
        exact h y (by simp [hy])
      have ih := sum_wordLength_le_mul_length A xs hxs
      calc
        ((x :: xs).map (wordLength S)).sum
            = wordLength S x + (xs.map (wordLength S)).sum := by simp
        _ ≤ A + A * xs.length := Nat.add_le_add hx ih
        _ = A * (List.length (x :: xs)) := by
          simp [Nat.mul_succ, Nat.add_comm]

/-- Step 2: one-sided comparison `|g|_S ≤ C * |g|_T`. -/
lemma wordLength_compare_one_side
    (hSgen : IsGenerating S) (hTgen : IsGenerating T) (hTfin : T.Finite) (g : G) :
    wordLength S g
      ≤ generatorBound (S := S) (T := T) hSgen hTfin * wordLength T g := by
  obtain ⟨w, hwT, hwprod, hwlen⟩ := exists_min_word (S := T) hTgen g
  have hprod_le_sum : wordLength S w.prod ≤ (w.map (wordLength S)).sum :=
    wordLength_prod_le_sum_wordLength (S := S) hSgen w
  have hfac : ∀ x ∈ w,
      wordLength S x ≤ generatorBound (S := S) (T := T) hSgen hTfin := by
    intro x hx
    exact wordLength_le_generatorBound_of_mem_or_inv
      (S := S) (T := T) hSgen hTfin (hwT x hx)
  have hsum_le : (w.map (wordLength S)).sum
      ≤ generatorBound (S := S) (T := T) hSgen hTfin * w.length :=
    sum_wordLength_le_mul_length (S := S)
      (generatorBound (S := S) (T := T) hSgen hTfin) w hfac
  calc
    wordLength S g = wordLength S w.prod := by simp [hwprod]
    _ ≤ (w.map (wordLength S)).sum := hprod_le_sum
    _ ≤ generatorBound (S := S) (T := T) hSgen hTfin * w.length := hsum_le
    _ = generatorBound (S := S) (T := T) hSgen hTfin * wordLength T g := by
      rw [hwlen]

lemma wordLength_compare_one_side'
    (hSgen : IsGenerating S) (hTgen : IsGenerating T) (hSfin : S.Finite) (g : G) :
    wordLength T g
      ≤ generatorBound (S := T) (T := S) hTgen hSfin * wordLength S g := by
  simpa using
    (wordLength_compare_one_side (S := T) (T := S) hTgen hSgen hSfin g)

lemma wordDist_compare_one_side
    (hSgen : IsGenerating S) (hTgen : IsGenerating T) (hTfin : T.Finite) (g h : G) :
    wordDist S g h
      ≤ generatorBound (S := S) (T := T) hSgen hTfin * wordDist T g h := by
  unfold wordDist
  exact wordLength_compare_one_side (S := S) (T := T) hSgen hTgen hTfin (g⁻¹ * h)

lemma wordDist_biLipschitz
    (hSgen : IsGenerating S) (hTgen : IsGenerating T)
    (hSfin : S.Finite) (hTfin : T.Finite) (g h : G) :
    wordDist S g h
      ≤ generatorBound (S := S) (T := T) hSgen hTfin * wordDist T g h ∧
    wordDist T g h
      ≤ generatorBound (S := T) (T := S) hTgen hSfin * wordDist S g h := by
  constructor
  · exact wordDist_compare_one_side (S := S) (T := T) hSgen hTgen hTfin g h
  · exact wordDist_compare_one_side (S := T) (T := S) hTgen hSgen hSfin g h



end CompareGeneratingSets

/-- The metric space structure induced by `wordDist` for a generating set `S`. -/
noncomputable def wordMetricSpace (S : Set G) (hGen : IsGenerating S) : MetricSpace G where
  dist := wordMetricDist S
  dist_self := by
    intro g
    simpa [wordMetricDist] using (wordDist_self (S := S) g)
  dist_comm := by
    intro g h
    have hcomm : (wordDist S g h : ℝ) = (wordDist S h g : ℝ) := by
      exact_mod_cast (wordDist_symm (S := S) hGen g h)
    simpa [wordMetricDist] using hcomm
  dist_triangle := by
    intro g h k
    have htri :
        (wordDist S g k : ℝ) ≤ (wordDist S g h : ℝ) + (wordDist S h k : ℝ) := by
      exact_mod_cast (wordDist_triangle (S := S) hGen g h k)
    simpa [wordMetricDist] using htri
  eq_of_dist_eq_zero := by
    intro g h hdist
    have hreal : (wordDist S g h : ℝ) = 0 := by
      simpa [wordMetricDist] using hdist
    have hnat : wordDist S g h = 0 := by
      exact_mod_cast hreal
    exact (wordDist_eq_zero_iff (S := S) hGen g h).1 hnat


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

section QuasiIso

variable {S T : Set G}

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

end QuasiIso
