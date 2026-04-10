import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Int
import Mathlib
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.emptyLine false
universe u v w
structure QuasiIsometricEmbedding
  (α : Type u)
  (β : Type v)
  [MetricSpace α]
  [MetricSpace β] where
  f : α → β
  K : ℝ
  C : ℝ
  req_1 : K ≥ 1
  req_2 : C ≥ 0
  main_req : ∀ x y : α, (1 / K) * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ K * dist x y + C


structure QuasiIsometry
  (α : Type u)
  (β : Type v)
  [MetricSpace α]
  [MetricSpace β]
  extends QuasiIsometricEmbedding α β where
  D : ℝ
  req_3 : D > 0
  main_req_2 : ∀ y : β, ∃ x : α, dist (f x) y ≤ D


structure GeodesicMetricSpace

/-
noncomputable def seven_five_one : QuasiIsometry ℝ ℤ where
f := Int.floor
K := 1
C := 1
D := 1
req_1 := by norm_num
req_2 := by norm_num
req_3 := by norm_num
main_req := by
  intro x y
  sorry
-/
noncomputable def quasiInv
    (α : Type u) (β : Type v)
    [MetricSpace α] [MetricSpace β]
    (q : QuasiIsometry α β) : β → α :=
  fun y => Classical.choose (q.main_req_2 y)

lemma quasiInv_spec
    (α : Type u) (β : Type v)
    [MetricSpace α] [MetricSpace β]
    (q : QuasiIsometry α β) (y : β) :
    dist (q.f (quasiInv α β q y)) y ≤ q.D := by
  exact Classical.choose_spec (q.main_req_2 y)

def QuasiIsometryExists (α : Type u) (β : Type v) [MetricSpace α] [MetricSpace β] : Prop := Nonempty (QuasiIsometry α β)

theorem reflexive (α : Type u) (β : Type v) [MetricSpace α] [MetricSpace β] : QuasiIsometryExists α α := by
refine ⟨{
  f := id, K:= 1, C:= 0, D:=1, req_1 := by norm_num, req_2 := by norm_num, req_3 := by norm_num, main_req := ?_, main_req_2 := ?_
}⟩
· intro x y
  simp

· intro y
  exact ⟨y, by simp⟩


lemma c_div_le_k_mul_c {c k : ℝ} (hc : 0 ≤ c) (hk : 1 ≤ k) : c / k ≤ k * c := by
  have hk0 : 0 < k := by linarith
  have h1 : 1 / k ≤ k := by
    by_contra h
    have h' : k < 1 / k := by linarith
    have hk_sq : 1 ≤ k * k := by nlinarith [hk]
    have hlt1 : k * k < 1 := by
      have hmul : k * k < k * (1 / k) := by
        exact mul_lt_mul_of_pos_left h' hk0
      have : k * k < (1 / k) * k := by
        simpa [mul_comm] using hmul
      have hkne : k ≠ 0 := by linarith
      simpa [hkne, div_eq_mul_inv, mul_assoc] using this
    linarith
  have h2 : c * (1 / k) ≤ c * k := by
    exact mul_le_mul_of_nonneg_left h1 hc
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h2

theorem transitive
    (α : Type u) (β : Type v) (γ : Type w)
    [MetricSpace α] [MetricSpace β] [MetricSpace γ] :
    QuasiIsometryExists α β → (QuasiIsometryExists β γ → QuasiIsometryExists α γ) := by
  intro h₁ h₂
  rcases h₁ with ⟨q₁⟩
  rcases h₂ with ⟨q₂⟩
  refine ⟨{
    f := q₂.f ∘ q₁.f
    K := q₂.K * q₁.K
    C := q₂.K * q₁.C + q₂.C
    D := q₂.K * q₁.D + q₂.C + q₂.D
    req_1 := by
      have h1 : 1 ≤ q₁.K := q₁.req_1
      have h2 : 1 ≤ q₂.K := q₂.req_1
      nlinarith
    req_2 := by
      have hK : 0 ≤ q₂.K := by linarith [q₂.req_1]
      have hC1 : 0 ≤ q₁.C := q₁.req_2
      have hC2 : 0 ≤ q₂.C := q₂.req_2
      nlinarith
    req_3 := by
      have hK : 0 ≤ q₂.K := by linarith [q₂.req_1]
      have hD1 : 0 < q₁.D := q₁.req_3
      have hC2 : 0 ≤ q₂.C := q₂.req_2
      have hD2 : 0 < q₂.D := q₂.req_3
      nlinarith
    main_req := ?_
    main_req_2 := ?_
  }⟩
  · intro x y
    rcases q₁.main_req x y with ⟨h₁low, h₁up⟩
    rcases q₂.main_req (q₁.f x) (q₁.f y) with ⟨h₂low, h₂up⟩
    constructor
    · have hK1pos : 0 < q₁.K := by linarith [q₁.req_1]
      have hK2pos : 0 < q₂.K := by linarith [q₂.req_1]

      have hmul :
          (1 / q₂.K) * ((1 / q₁.K) * dist x y - q₁.C)
            ≤ (1 / q₂.K) * dist (q₁.f x) (q₁.f y) := by
        have hnonneg : 0 ≤ 1 / q₂.K := by positivity
        exact mul_le_mul_of_nonneg_left h₁low hnonneg

      have hmul' :
          (1 / q₂.K) * ((1 / q₁.K) * dist x y - q₁.C) - q₂.C
            ≤ (1 / q₂.K) * dist (q₁.f x) (q₁.f y) - q₂.C := by
        exact sub_le_sub_right hmul q₂.C

      have hqc : q₁.C / q₂.K ≤ q₂.K * q₁.C := by
        exact c_div_le_k_mul_c q₁.req_2 q₂.req_1

      have haux :
          (1 / (q₂.K * q₁.K)) * dist x y - (q₂.K * q₁.C + q₂.C)
            ≤ (1 / q₂.K) * dist (q₁.f x) (q₁.f y) - q₂.C := by
        calc
          (1 / (q₂.K * q₁.K)) * dist x y - (q₂.K * q₁.C + q₂.C)
            ≤ (1 / (q₂.K * q₁.K)) * dist x y - (q₁.C / q₂.K + q₂.C) := by
              linarith
          _ = (1 / q₂.K) * ((1 / q₁.K) * dist x y - q₁.C) - q₂.C := by
              field_simp [hK1pos.ne', hK2pos.ne']
              ring
          _ ≤ (1 / q₂.K) * dist (q₁.f x) (q₁.f y) - q₂.C := hmul'

      exact le_trans haux (by simpa [Function.comp] using h₂low)

    · have hK : 0 ≤ q₂.K := by linarith [q₂.req_1]
      have hq :
          q₂.K * dist (q₁.f x) (q₁.f y) ≤ q₂.K * (q₁.K * dist x y + q₁.C) := by
        exact mul_le_mul_of_nonneg_left h₁up hK
      calc
        dist ((q₂.f ∘ q₁.f) x) ((q₂.f ∘ q₁.f) y)
            = dist (q₂.f (q₁.f x)) (q₂.f (q₁.f y)) := by rfl
        _ ≤ q₂.K * dist (q₁.f x) (q₁.f y) + q₂.C := h₂up
        _ ≤ q₂.K * (q₁.K * dist x y + q₁.C) + q₂.C := by linarith
        _ = q₂.K * q₁.K * dist x y + (q₂.K * q₁.C + q₂.C) := by ring

  · intro z
    rcases q₂.main_req_2 z with ⟨y, hy⟩
    rcases q₁.main_req_2 y with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hcomp := (q₂.main_req (q₁.f x) y).2
    have htri :
        dist ((q₂.f ∘ q₁.f) x) z ≤
          dist ((q₂.f ∘ q₁.f) x) (q₂.f y) + dist (q₂.f y) z := by
      simpa [Function.comp] using dist_triangle (q₂.f (q₁.f x)) (q₂.f y) z
    have hK : 0 ≤ q₂.K := by linarith [q₂.req_1]
    have hcomp' :
        dist ((q₂.f ∘ q₁.f) x) (q₂.f y) ≤ q₂.K * dist (q₁.f x) y + q₂.C := by
      simpa [Function.comp] using hcomp
    have hmul : q₂.K * dist (q₁.f x) y ≤ q₂.K * q₁.D := by
      exact mul_le_mul_of_nonneg_left hx hK
    calc
      dist ((q₂.f ∘ q₁.f) x) z
          ≤ dist ((q₂.f ∘ q₁.f) x) (q₂.f y) + dist (q₂.f y) z := htri
      _ ≤ (q₂.K * dist (q₁.f x) y + q₂.C) + q₂.D := by linarith [hcomp', hy]
      _ ≤ (q₂.K * q₁.D + q₂.C) + q₂.D := by linarith
      _ = q₂.K * q₁.D + q₂.C + q₂.D := by ring





theorem symmetric
    (α : Type u) (β : Type v)
    [MetricSpace α] [MetricSpace β] :
    QuasiIsometryExists α β → QuasiIsometryExists β α := by
  intro h
  rcases h with ⟨q⟩
  classical
  let g : β → α := quasiInv α β q
  refine ⟨{
    f := g
    K := q.K
    C := q.K * (2 * q.D + q.C)
    D := q.K * (q.D + q.C)
    req_1 := q.req_1
    req_2 := by
      have hK : 0 ≤ q.K := by linarith [q.req_1]
      have hD : 0 ≤ q.D := by linarith [q.req_3]
      have hC : 0 ≤ q.C := q.req_2
      nlinarith
    req_3 := by
      have hK : 0 < q.K := by linarith [q.req_1]
      have hD : 0 < q.D := q.req_3
      have hC : 0 ≤ q.C := q.req_2
      nlinarith
    main_req := ?_
    main_req_2 := ?_
  }⟩
  · intro y₁ y₂
    have hgy₁ : dist (q.f (g y₁)) y₁ ≤ q.D := by
      simpa [g] using quasiInv_spec α β q y₁
    have hgy₂ : dist (q.f (g y₂)) y₂ ≤ q.D := by
      simpa [g] using quasiInv_spec α β q y₂

    have hA :
        dist (q.f (g y₁)) (q.f (g y₂)) ≤ dist y₁ y₂ + 2 * q.D := by
      calc
        dist (q.f (g y₁)) (q.f (g y₂))
            ≤ dist (q.f (g y₁)) y₁ + dist y₁ (q.f (g y₂)) := by
              exact dist_triangle _ _ _
        _ ≤ dist (q.f (g y₁)) y₁ + (dist y₁ y₂ + dist y₂ (q.f (g y₂))) := by
              gcongr
              exact dist_triangle _ _ _
        _ ≤ q.D + (dist y₁ y₂ + q.D) := by
              have h2 : dist y₂ (q.f (g y₂)) ≤ q.D := by
                simpa [dist_comm] using hgy₂
              linarith
        _ ≤ dist y₁ y₂ + 2 * q.D := by
              ring_nf
              exact le_rfl

    have hB :
        dist y₁ y₂ ≤ dist (q.f (g y₁)) (q.f (g y₂)) + 2 * q.D := by
      calc
        dist y₁ y₂
            ≤ dist y₁ (q.f (g y₁)) + dist (q.f (g y₁)) y₂ := by
              exact dist_triangle _ _ _
        _ ≤ dist y₁ (q.f (g y₁)) +
              (dist (q.f (g y₁)) (q.f (g y₂)) + dist (q.f (g y₂)) y₂) := by
              gcongr
              exact dist_triangle _ _ _
        _ ≤ q.D + (dist (q.f (g y₁)) (q.f (g y₂)) + q.D) := by
              gcongr
              · simpa [dist_comm] using hgy₁
        _ = dist (q.f (g y₁)) (q.f (g y₂)) + 2 * q.D := by ring

    rcases q.main_req (g y₁) (g y₂) with ⟨hlow, hup⟩
    constructor
    · have hnonneg : 0 ≤ 1 / q.K := by
        have : 0 < q.K := by linarith [q.req_1]
        positivity

      have hBscaled :
          (1 / q.K) * dist y₁ y₂ ≤
            (1 / q.K) * (dist (q.f (g y₁)) (q.f (g y₂)) + 2 * q.D) := by
        exact mul_le_mul_of_nonneg_left hB hnonneg

      have hB' :
          (1 / q.K) * dist y₁ y₂ ≤
            (1 / q.K) * dist (q.f (g y₁)) (q.f (g y₂)) + (2 * q.D) / q.K := by
        simpa [left_distrib, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
          add_assoc, add_comm, add_left_comm] using hBscaled

      have hupscaled :
          (1 / q.K) * dist (q.f (g y₁)) (q.f (g y₂))
            ≤ (1 / q.K) * (q.K * dist (g y₁) (g y₂) + q.C) := by
        exact mul_le_mul_of_nonneg_left hup hnonneg

      have hkne : q.K ≠ 0 := by linarith [q.req_1]

      have hup' :
          (1 / q.K) * dist (q.f (g y₁)) (q.f (g y₂))
            ≤ dist (g y₁) (g y₂) + q.C / q.K := by
        calc
          (1 / q.K) * dist (q.f (g y₁)) (q.f (g y₂))
              ≤ (1 / q.K) * (q.K * dist (g y₁) (g y₂) + q.C) := hupscaled
          _ = dist (g y₁) (g y₂) + q.C / q.K := by
                field_simp [hkne]

      have htmp :
          (1 / q.K) * dist y₁ y₂ - ((2 * q.D) / q.K + q.C / q.K)
            ≤ dist (g y₁) (g y₂) := by
        linarith

      have hconst :
          (2 * q.D) / q.K + q.C / q.K ≤ q.K * (2 * q.D + q.C) := by
        have hD : (2 * q.D) / q.K ≤ q.K * (2 * q.D) := by
          exact c_div_le_k_mul_c (by nlinarith [q.req_3]) q.req_1
        have hC : q.C / q.K ≤ q.K * q.C := by
          exact c_div_le_k_mul_c q.req_2 q.req_1
        nlinarith

      have hconst' :
          (1 / q.K) * dist y₁ y₂ - q.K * (2 * q.D + q.C)
            ≤ (1 / q.K) * dist y₁ y₂ - ((2 * q.D) / q.K + q.C / q.K) := by
        linarith

      exact le_trans hconst' htmp

    · have hKnonneg : 0 ≤ q.K := by linarith [q.req_1]
      have hkne : q.K ≠ 0 := by linarith [q.req_1]

      have htmp :
          (1 / q.K) * dist (g y₁) (g y₂)
            ≤ dist (q.f (g y₁)) (q.f (g y₂)) + q.C := by
        linarith [hlow]

      have hmul :
          q.K * ((1 / q.K) * dist (g y₁) (g y₂))
            ≤ q.K * (dist (q.f (g y₁)) (q.f (g y₂)) + q.C) := by
        exact mul_le_mul_of_nonneg_left htmp hKnonneg

      have hlow' :
          dist (g y₁) (g y₂)
            ≤ q.K * dist (q.f (g y₁)) (q.f (g y₂)) + q.K * q.C := by
        calc
          dist (g y₁) (g y₂)
              = q.K * ((1 / q.K) * dist (g y₁) (g y₂)) := by
                  field_simp [hkne]
          _ ≤ q.K * (dist (q.f (g y₁)) (q.f (g y₂)) + q.C) := hmul
          _ = q.K * dist (q.f (g y₁)) (q.f (g y₂)) + q.K * q.C := by ring

      have hA' :
          q.K * dist (q.f (g y₁)) (q.f (g y₂)) + q.K * q.C
            ≤ q.K * (dist y₁ y₂ + 2 * q.D) + q.K * q.C := by
        have htmp2 :
            q.K * dist (q.f (g y₁)) (q.f (g y₂))
              ≤ q.K * (dist y₁ y₂ + 2 * q.D) := by
          exact mul_le_mul_of_nonneg_left hA hKnonneg
        linarith

      calc
        dist (g y₁) (g y₂)
            ≤ q.K * dist (q.f (g y₁)) (q.f (g y₂)) + q.K * q.C := hlow'
        _ ≤ q.K * (dist y₁ y₂ + 2 * q.D) + q.K * q.C := hA'
        _ = q.K * dist y₁ y₂ + q.K * (2 * q.D + q.C) := by ring
  · intro x
    refine ⟨q.f x, ?_⟩
    have hchoice : dist (q.f (g (q.f x))) (q.f x) ≤ q.D := by
      simpa [g] using quasiInv_spec α β q (q.f x)
    have hchoice' : dist (q.f x) (q.f (g (q.f x))) ≤ q.D := by
      simpa [dist_comm] using hchoice
    have hlow := (q.main_req x (g (q.f x))).1
    have htmp : (1 / q.K) * dist x (g (q.f x)) ≤ q.D + q.C := by
      linarith [hlow, hchoice']
    have hKnonneg : 0 ≤ q.K := by linarith [q.req_1]
    have hkne : q.K ≠ 0 := by linarith [q.req_1]
    have hmul :
        q.K * ((1 / q.K) * dist x (g (q.f x))) ≤ q.K * (q.D + q.C) := by
      exact mul_le_mul_of_nonneg_left htmp hKnonneg
    calc
      dist (g (q.f x)) x = dist x (g (q.f x)) := by simp [dist_comm]
      _ = q.K * ((1 / q.K) * dist x (g (q.f x))) := by
            field_simp [hkne]
      _ ≤ q.K * (q.D + q.C) := hmul
