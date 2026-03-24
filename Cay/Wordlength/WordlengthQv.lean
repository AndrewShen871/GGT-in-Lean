import Mathlib
import Cay.Wordlength.Wordlength
set_option linter.style.longLine false

/-- Alternative word length definition in terms of Cayley-graph path length functions. -/
noncomputable def wordLengthQv {G : Type*} [Group G] (S : Set G) (g : G) : ℕ :=
  Cay.Wordlength.wordLength S g

/-- Alternative word distance def in terms of the path-based word metric. -/
noncomputable def wordDistQv {G : Type*} [Group G] (S : Set G) (g h : G) : ℕ :=
  Cay.Wordlength.wordDist S g h


-- TODO: add properties that connect these with CayleyGraph path lengths.


variable {G : Type*} [Group G] {S : Set G}




lemma shiftPath_length (g : G) {u v : G}
  (p : Quiver.Path (V := CayleyGraph G S) ⟨u⟩ ⟨v⟩) :
  (CayleyGraph.shiftPath g p).length = p.length := by
  have hlen : ∀ {b : CayleyGraph G S} (q : Quiver.Path (V := CayleyGraph G S) ⟨u⟩ b),
      (CayleyGraph.shiftPath (S := S) (g := g) (u := u) (v := b.elt) (by simpa using q)).length =
        q.length := by
    intro b q
    induction q with
    | nil =>
        simp [CayleyGraph.shiftPath]
    | cons tail e ih =>
      simpa [CayleyGraph.shiftPath] using congrArg Nat.succ ih
  simpa using hlen p




lemma wordLength_mul_le_qv (hSymm : IsSymmetric S) (hGen : IsGenerating S) (g h : G) :
  wordLength S (g * h) ≤ wordLength S g + wordLength S h := by
  let L : G → Set ℕ := fun x =>
    {n : ℕ | ∃ p : Quiver.Path (V := CayleyGraph G S) ⟨1⟩ ⟨x⟩, p.length = n}
  have hL_nonempty : ∀ x : G, (L x).Nonempty := by
    intro x
    obtain ⟨p⟩ := CayleyGraph.Isconnected (S := S) hSymm hGen ⟨1⟩ ⟨x⟩
    exact ⟨p.length, ⟨p, rfl⟩⟩
  obtain ⟨p1, hp1⟩ :
      ∃ p1 : Quiver.Path (V := CayleyGraph G S) ⟨1⟩ ⟨g * 1⟩, p1.length = sInf (L (g * 1)) := by
    rcases Nat.sInf_mem (hL_nonempty (g * 1)) with ⟨p1, hp1⟩
    exact ⟨p1, hp1⟩
  obtain ⟨p2, hp2⟩ :
      ∃ p2 : Quiver.Path (V := CayleyGraph G S) ⟨1⟩ ⟨h⟩, p2.length = sInf (L h) := by
    rcases Nat.sInf_mem (hL_nonempty h) with ⟨p2, hp2⟩
    exact ⟨p2, hp2⟩
  let p2raw : Quiver.Path (V := CayleyGraph G S) ⟨g * 1⟩ ⟨g * h⟩ :=
    CayleyGraph.shiftPath (S := S) g p2
  have hp2raw_len : p2raw.length = sInf (L h) := by
    simp [p2raw, shiftPath_length, hp2]
  let p : Quiver.Path (V := CayleyGraph G S) ⟨1⟩ ⟨g * h⟩ := p1.comp p2raw
  have hmain : sInf (L (g * h)) ≤ p.length := by
    refine Nat.sInf_le ?_
    exact ⟨p, rfl⟩
  have hlen : p.length = sInf (L g) + sInf (L h) := by
    calc
      p.length = p1.length + p2raw.length := by
        simp [p, Quiver.Path.length_comp]
      _ = sInf (L (g * 1)) + sInf (L h) := by rw [hp1, hp2raw_len]
      _ = sInf (L g) + sInf (L h) := by simp [mul_one]
  calc
    wordLength S (g * h) = sInf (L (g * h)) := by
      simp [wordLength, L]
    _ ≤ p.length := hmain
    _ = sInf (L g) + sInf (L h) := hlen
    _ = wordLength S g + wordLength S h := by
      simp [wordLength, L]





lemma wordDist_triangle (hSymm : IsSymmetric S) (hGen : IsGenerating S) (g h k : G) :
  wordDist S g k ≤ wordDist S g h + wordDist S h k := by
  classical
  unfold wordDist
  have h_mul :
    g⁻¹ * k = (g⁻¹ * h) * (h⁻¹ * k) := by
    group
  simpa [h_mul] using
    wordLength_mul_le (S := S) hSymm hGen (g := g⁻¹ * h) (h := h⁻¹ * k)

lemma wordLength_one : wordLength S (1 : G) = 0 := by
  unfold wordLength
  have hle :
      sInf ({n : ℕ | ∃ p : Quiver.Path (V := CayleyGraph G S) ⟨1⟩ ⟨(1 : G)⟩, p.length = n}) ≤ 0 := by
    refine Nat.sInf_le ?_
    exact ⟨Quiver.Path.nil, rfl⟩
  exact le_antisymm hle (Nat.zero_le _)

lemma wordDist_self (_hSymm : IsSymmetric S) (_hGen : IsGenerating S) (g : G) :
  wordDist S g g = 0 := by
  unfold wordDist
  simpa using (wordLength_one (G := G) (S := S))

lemma wordLength_inv_eq (hSymm : IsSymmetric S) (hGen : IsGenerating S) (g : G) :
  wordLength S g⁻¹ = wordLength S g := by
  classical
  let L : G → Set ℕ := fun x =>
    {n : ℕ | ∃ p : Quiver.Path (V := CayleyGraph G S) ⟨1⟩ ⟨x⟩, p.length = n}
  have hL_nonempty : ∀ x : G, (L x).Nonempty := by
    intro x
    obtain ⟨p⟩ := CayleyGraph.Isconnected (S := S) hSymm hGen ⟨1⟩ ⟨x⟩
    exact ⟨p.length, ⟨p, rfl⟩⟩
  letI : Quiver.HasReverse (CayleyGraph G S) :=
    { reverse' := fun {a b} e => reverseEdge (G := G) (S := S) hSymm e }
  have reverse_length {a b : CayleyGraph G S} (p : Quiver.Path (V := CayleyGraph G S) a b) :
      p.reverse.length = p.length := by
    induction p with
    | nil => simp
    | cons tail e ih =>
      simp [Quiver.Path.reverse, Quiver.Path.length_comp, ih, Nat.add_comm]
  have hle' : ∀ x : G, sInf (L x⁻¹) ≤ sInf (L x) := by
    intro x
    obtain ⟨p, hp⟩ :
        ∃ p : Quiver.Path (V := CayleyGraph G S) ⟨1⟩ ⟨x⟩, p.length = sInf (L x) := by
      rcases Nat.sInf_mem (hL_nonempty x) with ⟨p, hp⟩
      exact ⟨p, hp⟩
    let q0 : Quiver.Path (V := CayleyGraph G S) ⟨x⁻¹ * x⟩ ⟨x⁻¹ * 1⟩ :=
      CayleyGraph.shiftPath (S := S) x⁻¹ p.reverse
    have hq0_len : q0.length = sInf (L x) := by
      calc
        q0.length = p.reverse.length := by
          simpa [q0] using (shiftPath_length (S := S) (g := x⁻¹) (u := x) (v := 1) p.reverse)
        _ = p.length := reverse_length p
        _ = sInf (L x) := hp
    have hmem : q0.length ∈ L x⁻¹ := by
      dsimp [L]
      exact ⟨q0, rfl⟩
    exact le_trans (Nat.sInf_le hmem) (le_of_eq hq0_len)
  have hle : sInf (L g⁻¹) ≤ sInf (L g) := hle' g
  have hge : sInf (L g) ≤ sInf (L g⁻¹) := by
    simpa [inv_inv] using (hle' g⁻¹)
  have hsInf : sInf (L g⁻¹) = sInf (L g) := le_antisymm hle hge
  unfold wordLength
  simpa [L] using hsInf

lemma wordDist_symm (hSymm : IsSymmetric S) (hGen : IsGenerating S) (g h : G) :
  wordDist S g h = wordDist S h g := by
  unfold wordDist
  have hinv : h⁻¹ * g = (g⁻¹ * h)⁻¹ := by
    group
  calc
    wordLength S (g⁻¹ * h) = wordLength S ((g⁻¹ * h)⁻¹) := (wordLength_inv_eq (S := S) hSymm hGen (g := g⁻¹ * h)).symm
    _ = wordLength S (h⁻¹ * g) := by rw [← hinv]

lemma wordDist_eq_zero_iff (hSymm : IsSymmetric S) (hGen : IsGenerating S) (g h : G) :
  wordDist S g h = 0 ↔ g = h := by
  constructor
  · intro h0
    let L : Set ℕ := {n : ℕ | ∃ p : Quiver.Path (V := CayleyGraph G S) ⟨1⟩ ⟨g⁻¹ * h⟩, p.length = n}
    have hL_nonempty : L.Nonempty := by
      obtain ⟨p⟩ := CayleyGraph.Isconnected (S := S) hSymm hGen ⟨1⟩ ⟨g⁻¹ * h⟩
      exact ⟨p.length, ⟨p, rfl⟩⟩
    obtain ⟨p, hp⟩ : ∃ p : Quiver.Path (V := CayleyGraph G S) ⟨1⟩ ⟨g⁻¹ * h⟩, p.length = sInf L := by
      rcases Nat.sInf_mem hL_nonempty with ⟨p, hp⟩
      exact ⟨p, hp⟩
    have hp0 : p.length = 0 := by
      simpa [wordDist, wordLength, L] using hp.trans h0
    have hmul : (1 : G) = g⁻¹ * h := by
      simpa using (Quiver.Path.eq_of_length_zero p hp0)
    have : g = h := by
      have hmulg : g * (1 : G) = g * (g⁻¹ * h) := congrArg (fun x => g * x) hmul
      simpa [mul_assoc] using hmulg
    exact this
  · intro hEq
    subst hEq
    exact wordDist_self (S := S) hSymm hGen g
