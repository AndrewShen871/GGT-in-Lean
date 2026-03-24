import Mathlib
import Cay
set_option linter.style.longLine false


/-- Define word length via shortest admissible word over generators and their inverses. -/
noncomputable def wordLength {G : Type*} [Group G] (S : Set G) (g : G) : ℕ :=
  sInf {n : ℕ |
    ∃ w : List G,
      (∀ x ∈ w, x ∈ S ∨ x⁻¹ ∈ S) ∧
      w.prod = g ∧
      w.length = n}

/-- Define word distance via left-translation invariance. -/
noncomputable def wordDist {G : Type*} [Group G] (S : Set G) (g h : G) : ℕ :=
  wordLength S (g⁻¹ * h)


variable {G : Type*} [Group G] {S : Set G}

lemma wordLength_le_of_word {g : G} {w : List G}
    (hwS : ∀ x ∈ w, x ∈ S ∨ x⁻¹ ∈ S) (hwprod : w.prod = g) :
    wordLength S g ≤ w.length := by
  unfold wordLength
  refine Nat.sInf_le ?_
  exact ⟨w, hwS, hwprod, rfl⟩

lemma wordLength_one : wordLength S (1 : G) = 0 := by
  apply le_antisymm
  · exact wordLength_le_of_word (S := S) (g := (1 : G)) (w := [])
      (by intro x hx; cases hx)
      (by simp)
  · exact Nat.zero_le _

lemma wordDist_self (g : G) : wordDist S g g = 0 := by
  unfold wordDist
  simpa using (wordLength_one (G := G) (S := S))

lemma exists_word_of_generating (hGen : IsGenerating S) (g : G) :
    ∃ w : List G, (∀ x ∈ w, x ∈ S ∨ x⁻¹ ∈ S) ∧ w.prod = g := by
  have hg : g ∈ Subgroup.closure S := by
    rw [hGen]
    trivial
  refine Subgroup.closure_induction (k := S)
    (p := fun x _ => ∃ w : List G, (∀ y ∈ w, y ∈ S ∨ y⁻¹ ∈ S) ∧ w.prod = x)
    ?mem ?one ?mul ?inv hg
  · intro x hx
    refine ⟨[x], ?_, by simp⟩
    intro y hy
    have hy' : y = x := by simpa using hy
    rcases hy' with rfl
    exact Or.inl hx
  · refine ⟨[], ?_⟩
    constructor
    · intro y hy
      cases hy
    · simp
  · intro x y hx hy hxw hyw
    rcases hxw with ⟨wx, hwxS, hwxprod⟩
    rcases hyw with ⟨wy, hwyS, hwyprod⟩
    refine ⟨wx ++ wy, ?_, by simp [hwxprod, hwyprod, List.prod_append]⟩
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hwxS z hz
    · exact hwyS z hz
  · intro x hx hxw
    rcases hxw with ⟨w, hwS, hwprod⟩
    refine ⟨(w.map fun t => t⁻¹).reverse, ?_, ?_⟩
    · intro y hy
      have hy' : y ∈ w.map (fun t => t⁻¹) := by simpa [List.mem_reverse] using hy
      rcases List.mem_map.mp hy' with ⟨z, hz, rfl⟩
      rcases hwS z hz with hzS | hzSinv
      · exact Or.inr (by simpa using hzS)
      · exact Or.inl hzSinv
    · have hprodInv : (w.map fun t => t⁻¹).reverse.prod = w.prod⁻¹ := by
        simpa using (List.prod_inv_reverse w).symm
      simpa [hwprod] using hprodInv

lemma exists_min_word (hGen : IsGenerating S) (g : G) :
    ∃ w : List G,
      (∀ x ∈ w, x ∈ S ∨ x⁻¹ ∈ S) ∧ w.prod = g ∧ w.length = wordLength S g := by
  let W : Set ℕ := {n : ℕ |
    ∃ w : List G,
      (∀ x ∈ w, x ∈ S ∨ x⁻¹ ∈ S) ∧
      w.prod = g ∧
      w.length = n}
  obtain ⟨w0, hw0S, hw0prod⟩ := exists_word_of_generating (S := S) hGen g
  have hWnonempty : W.Nonempty := by
    refine ⟨w0.length, ⟨w0, hw0S, hw0prod, rfl⟩⟩
  have hsInfMem : sInf W ∈ W := Nat.sInf_mem hWnonempty
  rcases hsInfMem with ⟨w, hwS, hwprod, hwlen⟩
  refine ⟨w, hwS, hwprod, ?_⟩
  simpa [wordLength, W] using hwlen

lemma wordLength_mul_le (hGen : IsGenerating S) (g h : G) :
  wordLength S (g * h) ≤ wordLength S g + wordLength S h := by
  obtain ⟨wg, hwgS, hwgprod, hwglen⟩ := exists_min_word (S := S) hGen g
  obtain ⟨wh, hwhS, hwhprod, hwhlen⟩ := exists_min_word (S := S) hGen h
  have hconcatS : ∀ x ∈ wg ++ wh, x ∈ S ∨ x⁻¹ ∈ S := by
    intro x hx
    rcases List.mem_append.mp hx with hxg | hxh
    · exact hwgS x hxg
    · exact hwhS x hxh
  have hconcatProd : (wg ++ wh).prod = g * h := by
    simp [hwgprod, hwhprod, List.prod_append]
  calc
    wordLength S (g * h) ≤ (wg ++ wh).length := wordLength_le_of_word (S := S) hconcatS hconcatProd
    _ = wg.length + wh.length := by simp
    _ = wordLength S g + wordLength S h := by rw [hwglen, hwhlen]

lemma wordDist_triangle (hGen : IsGenerating S) (g h k : G) :
  wordDist S g k ≤ wordDist S g h + wordDist S h k := by
  unfold wordDist
  have h_mul : g⁻¹ * k = (g⁻¹ * h) * (h⁻¹ * k) := by
    group
  simpa [h_mul] using
    wordLength_mul_le (S := S) hGen (g := g⁻¹ * h) (h := h⁻¹ * k)

lemma wordLength_inv_eq (hGen : IsGenerating S) (g : G) :
  wordLength S g⁻¹ = wordLength S g := by
  have hle' : ∀ x : G, wordLength S x⁻¹ ≤ wordLength S x := by
    intro x
    obtain ⟨w, hwS, hwprod, hwlen⟩ := exists_min_word (S := S) hGen x
    let winv : List G := (w.map fun t => t⁻¹).reverse
    have hwinvS : ∀ y ∈ winv, y ∈ S ∨ y⁻¹ ∈ S := by
      intro y hy
      have hy' : y ∈ w.map (fun t => t⁻¹) := by
        simpa [winv, List.mem_reverse] using hy
      rcases List.mem_map.mp hy' with ⟨z, hz, rfl⟩
      rcases hwS z hz with hzS | hzSinv
      · exact Or.inr (by simpa using hzS)
      · exact Or.inl hzSinv
    have hwinvProd : winv.prod = x⁻¹ := by
      have hprodInv : (w.map fun t => t⁻¹).reverse.prod = w.prod⁻¹ := by
        simpa using (List.prod_inv_reverse w).symm
      simpa [winv, hwprod] using hprodInv
    have hwinvLen : winv.length = wordLength S x := by
      simp [winv, hwlen]
    calc
      wordLength S x⁻¹ ≤ winv.length := wordLength_le_of_word (S := S) hwinvS hwinvProd
      _ = wordLength S x := hwinvLen
  have hle : wordLength S g⁻¹ ≤ wordLength S g := hle' g
  have hge : wordLength S g ≤ wordLength S g⁻¹ := by
    simpa [inv_inv] using (hle' g⁻¹)
  exact le_antisymm hle hge

lemma wordDist_symm (hGen : IsGenerating S) (g h : G) :
  wordDist S g h = wordDist S h g := by
  unfold wordDist
  have hinv : h⁻¹ * g = (g⁻¹ * h)⁻¹ := by
    group
  calc
    wordLength S (g⁻¹ * h) = wordLength S ((g⁻¹ * h)⁻¹) :=
      (wordLength_inv_eq (S := S) hGen (g := g⁻¹ * h)).symm
    _ = wordLength S (h⁻¹ * g) := by rw [← hinv]

lemma wordDist_eq_zero_iff (hGen : IsGenerating S) (g h : G) :
  wordDist S g h = 0 ↔ g = h := by
  constructor
  · intro h0
    obtain ⟨w, hwS, hwprod, hwlen⟩ := exists_min_word (S := S) hGen (g⁻¹ * h)
    have hlen0 : w.length = 0 := by
      simpa [wordDist, wordLength] using hwlen.trans h0
    have hwNil : w = [] := by simpa using hlen0
    have hmul : g⁻¹ * h = 1 := by
      simpa [hwNil] using hwprod.symm
    have hmulg : g * (g⁻¹ * h) = g * 1 := congrArg (fun x => g * x) hmul
    have hEq : h = g := by simpa [mul_assoc] using hmulg
    exact hEq.symm
  · intro hEq
    subst hEq
    exact wordDist_self (S := S) g
