import Mathlib
import Cay.CayleyGraph

set_option linter.style.longLine false

/-- Word length defined as the infimum of Cayley-graph path lengths from the identity. -/
noncomputable def wordLength_qv {G : Type*} [Group G] (S : Set G) (g : G) : ℕ :=
  sInf {n : ℕ | ∃ p : Quiver.Path (V := CayleyGraph G S) ⟨1⟩ ⟨g⟩, p.length = n}

/-- Word distance induced by the Cayley-graph path-length word length. -/
noncomputable def wordDist_qv {G : Type*} [Group G] (S : Set G) (g h : G) : ℕ :=
  wordLength_qv S (g⁻¹ * h)

variable {G : Type*} [Group G] {S : Set G}

lemma shiftPath_length_qv (g : G) {u v : G}
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
  wordLength_qv S (g * h) ≤ wordLength_qv S g + wordLength_qv S h := by
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
  have hp2raw : p2raw.length = sInf (L h) := by
    calc
      p2raw.length = p2.length := by
        simpa [p2raw] using (shiftPath_length_qv (S := S) (g := g) (u := 1) (v := h) p2)
      _ = sInf (L h) := hp2
  let p : Quiver.Path (V := CayleyGraph G S) ⟨1⟩ ⟨g * h⟩ := p1.comp p2raw
  have hmain : sInf (L (g * h)) ≤ p.length := by
    refine Nat.sInf_le ?_
    exact ⟨p, rfl⟩
  have hlen : p.length = sInf (L g) + sInf (L h) := by
    calc
      p.length = p1.length + p2raw.length := by
        simp [p, Quiver.Path.length_comp]
      _ = sInf (L (g * 1)) + sInf (L h) := by
        rw [hp1, hp2raw]
      _ = sInf (L g) + sInf (L h) := by simp [mul_one]
  calc
    wordLength_qv S (g * h) = sInf (L (g * h)) := by
      simp [wordLength_qv, L]
    _ ≤ p.length := hmain
    _ = sInf (L g) + sInf (L h) := hlen
    _ = wordLength_qv S g + wordLength_qv S h := by
      simp [wordLength_qv, L]

lemma wordDist_triangle_qv (hSymm : IsSymmetric S) (hGen : IsGenerating S) (g h k : G) :
  wordDist_qv S g k ≤ wordDist_qv S g h + wordDist_qv S h k := by
  unfold wordDist_qv
  have h_mul : g⁻¹ * k = (g⁻¹ * h) * (h⁻¹ * k) := by
    group
  simpa [h_mul] using
    wordLength_mul_le_qv (S := S) hSymm hGen (g := g⁻¹ * h) (h := h⁻¹ * k)

lemma wordLength_one_qv : wordLength_qv S (1 : G) = 0 := by
  unfold wordLength_qv
  apply le_antisymm
  · refine Nat.sInf_le ?_
    exact ⟨Quiver.Path.nil, rfl⟩
  · exact Nat.zero_le _

lemma wordDist_self_qv (g : G) :
  wordDist_qv S g g = 0 := by
  unfold wordDist_qv
  simpa using (wordLength_one_qv (G := G) (S := S))

lemma wordLength_inv_eq_qv (hSymm : IsSymmetric S) (hGen : IsGenerating S) (g : G) :
  wordLength_qv S g⁻¹ = wordLength_qv S g := by
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
  have cast_length {a b a' b' : CayleyGraph G S}
      (ha : a = a') (hb : b = b') (p : Quiver.Path (V := CayleyGraph G S) a b) :
      (p.cast ha hb).length = p.length := by
    subst ha hb
    rfl
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
          simpa [q0] using (shiftPath_length_qv (S := S) (g := x⁻¹) (u := x) (v := 1) p.reverse)
        _ = p.length := reverse_length p
        _ = sInf (L x) := hp
    have hmem : q0.length ∈ L x⁻¹ := by
      dsimp [L]
      have hstart : (⟨x⁻¹ * x⟩ : CayleyGraph G S) = ⟨1⟩ := by
        exact congrArg (fun y => (⟨y⟩ : CayleyGraph G S)) (by simp)
      have hend : (⟨x⁻¹ * 1⟩ : CayleyGraph G S) = ⟨x⁻¹⟩ := by
        exact congrArg (fun y => (⟨y⟩ : CayleyGraph G S)) (by simp)
      let q1 : Quiver.Path (V := CayleyGraph G S) ⟨1⟩ ⟨x⁻¹⟩ := q0.cast hstart hend
      have hq1 : q1.length = q0.length := by
        simpa [q1] using cast_length hstart hend q0
      exact ⟨q1, hq1⟩
    exact le_trans (Nat.sInf_le hmem) (le_of_eq hq0_len)
  have hle : sInf (L g⁻¹) ≤ sInf (L g) := hle' g
  have hge : sInf (L g) ≤ sInf (L g⁻¹) := by
    simpa [inv_inv] using (hle' g⁻¹)
  have hsInf : sInf (L g⁻¹) = sInf (L g) := le_antisymm hle hge
  simpa [wordLength_qv, L] using hsInf

lemma wordDist_symm_qv (hSymm : IsSymmetric S) (hGen : IsGenerating S) (g h : G) :
  wordDist_qv S g h = wordDist_qv S h g := by
  unfold wordDist_qv
  have hinv : h⁻¹ * g = (g⁻¹ * h)⁻¹ := by
    group
  calc
    wordLength_qv S (g⁻¹ * h) = wordLength_qv S ((g⁻¹ * h)⁻¹) :=
      (wordLength_inv_eq_qv (S := S) hSymm hGen (g := g⁻¹ * h)).symm
    _ = wordLength_qv S (h⁻¹ * g) := by rw [← hinv]

lemma wordDist_eq_zero_iff_qv (hSymm : IsSymmetric S) (hGen : IsGenerating S) (g h : G) :
  wordDist_qv S g h = 0 ↔ g = h := by
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
      simpa [wordDist_qv, wordLength_qv, L] using hp.trans h0
    have hmul : (1 : G) = g⁻¹ * h := by
      simpa using (Quiver.Path.eq_of_length_zero p hp0)
    have hmulg : g * (1 : G) = g * (g⁻¹ * h) := congrArg (fun x => g * x) hmul
    simpa [mul_assoc] using hmulg
  · intro hEq
    subst hEq
    exact wordDist_self_qv (S := S) g
