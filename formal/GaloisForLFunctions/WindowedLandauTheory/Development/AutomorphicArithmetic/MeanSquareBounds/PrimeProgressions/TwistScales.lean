import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrimeSetCount

/-! The exceptional-zero term and progression errors decay on the admissible prime scales. -/

open Finset Classical

noncomputable section

namespace QH.PrimeProgressions

theorem liX_upper {Y : ℝ} (hY : 2 ≤ Y) : 0 ≤ liX Y ∧ liX Y ≤ 2 * Y := by
  have hpos : ∀ t ∈ Set.Icc (2 : ℝ) Y, 0 < Real.log t := fun t ht => Real.log_pos (by linarith [ht.1])
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  constructor
  · unfold liX
    exact intervalIntegral.integral_nonneg hY (fun t ht => (one_div_pos.2 (hpos t ht)).le)
  · unfold liX
    calc ∫ t in (2 : ℝ)..Y, 1 / Real.log t ≤ ∫ t in (2 : ℝ)..Y, (2 : ℝ) := by
          apply intervalIntegral.integral_mono_on hY (intervalIntegrable_inv_log (by rfl) hY) intervalIntegrable_const
          intro t ht
          have h1 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1
          rw [div_le_iff₀ (hpos t ht)]
          linarith
      _ = (Y - 2) * 2 := by simp
      _ ≤ 2 * Y := by linarith

theorem liX_pow_le {X β δ : ℝ} (hX : 4 ≤ X) (hβ1 : 1 / 2 ≤ β) (hβ2 : β ≤ 1 - δ) :
    |liX (X ^ β)| ≤ 4 * Real.log X * Real.exp (-(δ * Real.log X)) * liX X := by
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log X := ⟨_, rfl⟩
  rw [← hL]
  have hXpos : 0 < X := by linarith
  have hL0 : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hXL : X = Real.exp L := by rw [hL, Real.exp_log hXpos]
  have hXb2 : 2 ≤ X ^ β := by
    have h4 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (2 : ℝ) = 4 ^ ((1 : ℝ) / 2) := h4.symm
      _ ≤ X ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
      _ ≤ X ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) hβ1
  obtain ⟨h0, hup⟩ := liX_upper hXb2
  have hlow : X / (2 * L) ≤ liX X := by rw [hL]; exact liX_lower hX
  calc |liX (X ^ β)| = liX (X ^ β) := abs_of_nonneg h0
    _ ≤ 2 * X ^ β := hup
    _ = 2 * Real.exp (β * L) := by rw [Real.rpow_def_of_pos hXpos, ← hL, mul_comm L β]
    _ ≤ 2 * Real.exp ((1 - δ) * L) := by
        have : β * L ≤ (1 - δ) * L := mul_le_mul_of_nonneg_right hβ2 hL0.le
        have := Real.exp_le_exp.2 this
        linarith
    _ = 4 * L * Real.exp (-(δ * L)) * (X / (2 * L)) := by
        rw [hXL, show (1 - δ) * L = -(δ * L) + L by ring, Real.exp_add]
        field_simp
        ring
    _ ≤ 4 * L * Real.exp (-(δ * L)) * liX X :=
        mul_le_mul_of_nonneg_left hlow (by positivity)

theorem eventually_log_cube (K a : ℝ) (hK : 0 < K) (ha : 0 < a) :
    ∃ x₂ : ℝ, ∀ x : ℝ, x₂ ≤ x → K * Real.log x ^ 3 ≤ x ^ a := by
  have h := (isLittleO_log_rpow_rpow_atTop 3 ha).bound (by positivity : (0 : ℝ) < 1 / K)
  obtain ⟨x₂, hx₂⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_gt_atTop 0))
  refine ⟨x₂, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx₂ x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos h2 a)] at h1
  have h3 : Real.log x ^ 3 = Real.log x ^ (3 : ℝ) := by
    rw [← Real.rpow_natCast]
    norm_num
  rw [h3]
  calc K * Real.log x ^ (3 : ℝ) ≤ K * |Real.log x ^ (3 : ℝ)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hK.le
    _ ≤ K * (1 / K * x ^ a) := mul_le_mul_of_nonneg_left h1 hK.le
    _ = x ^ a := by field_simp

private theorem progression_range {A ε C₀ L u lm ℓm ℓ : ℝ} (hA0 : 0 < A) (hε : 0 < ε)
    (hL1 : 2 ≤ L) (hL5 : 8 * |C₀| * (Real.log (6 + A) + ε / 5 + 1) ≤ L)
    (hℓm : ℓm ≤ 4 * Real.exp (ε / 5 * L))
    (hlm0 : 2 ≤ lm) (hlm : lm ≤ ℓ) (hℓ : ℓ ≤ ℓm + A * L) (hP0 : L ^ 2 * ℓ / 8 ≤ u) :
    C₀ * lm * Real.log (lm + 2) ≤ u := by
  have hL0 : 0 < L := by linarith only [hL1]
  have hA : lm + 2 ≤ (6 + A) * Real.exp ((ε / 5 + 1) * L) := by
    have ee : (ε / 5 + 1) * L = ε / 5 * L + L := by ring
    have hεL : 0 ≤ ε / 5 * L := by positivity
    have e1 : Real.exp (ε / 5 * L) ≤ Real.exp ((ε / 5 + 1) * L) := Real.exp_le_exp.mpr (by linarith)
    have e2 : L ≤ Real.exp ((ε / 5 + 1) * L) := by
      have := Real.add_one_le_exp L
      have : Real.exp L ≤ Real.exp ((ε / 5 + 1) * L) := Real.exp_le_exp.mpr (by linarith)
      linarith
    have e3 : 1 ≤ Real.exp ((ε / 5 + 1) * L) := Real.one_le_exp (by positivity)
    have e4 := mul_le_mul_of_nonneg_left e2 hA0.le
    linarith
  have hB : Real.log (lm + 2) ≤ Real.log (6 + A) + (ε / 5 + 1) * L := by
    calc Real.log (lm + 2) ≤ Real.log ((6 + A) * Real.exp ((ε / 5 + 1) * L)) := Real.log_le_log (by linarith) hA
      _ = _ := by rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  have hl806 : 0 ≤ Real.log (6 + A) := Real.log_nonneg (by linarith)
  have hlog0 : 0 ≤ Real.log (lm + 2) := Real.log_nonneg (by linarith)
  have hC : |C₀| * Real.log (lm + 2) ≤ L ^ 2 / 8 := by
    have : |C₀| * Real.log (lm + 2) ≤ |C₀| * (Real.log (6 + A) + (ε / 5 + 1) * L) :=
      mul_le_mul_of_nonneg_left hB (abs_nonneg _)
    have : |C₀| * (Real.log (6 + A) + (ε / 5 + 1) * L) ≤ |C₀| * ((Real.log (6 + A) + ε / 5 + 1) * L) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have h := le_mul_of_one_le_right hl806 (show (1 : ℝ) ≤ L by linarith only [hL1])
      linarith only [h]
    have h5 := mul_le_mul_of_nonneg_right hL5 hL0.le
    have e5 : |C₀| * ((Real.log (6 + A) + ε / 5 + 1) * L) = (8 * |C₀| * (Real.log (6 + A) + ε / 5 + 1) * L) / 8 := by ring
    have e6 : L ^ 2 / 8 = L * L / 8 := by ring
    linarith
  calc C₀ * lm * Real.log (lm + 2) ≤ |C₀| * lm * Real.log (lm + 2) := by
        apply mul_le_mul_of_nonneg_right _ hlog0
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    _ = lm * (|C₀| * Real.log (lm + 2)) := by ring
    _ ≤ lm * (L ^ 2 / 8) := mul_le_mul_of_nonneg_left hC (by linarith)
    _ ≤ ℓ * (L ^ 2 / 8) := mul_le_mul_of_nonneg_right hlm (by positivity)
    _ ≤ u := by linarith

private theorem exceptional_error {B ε c₀ L u ℓ : ℝ}
    (hc₀ : 0 < c₀) (hL1 : 2 ≤ L) (hu0 : 0 < u)
    (hL2 : 8 * (ε / 5 + 2 + B + Real.log 128) / c₀ ≤ L)
    (hlogu : Real.log u ≤ (ε / 5 + 2) * L) (hP1 : L ^ 2 / 8 ≤ u / ℓ) :
    16 * u * Real.exp (-(c₀ / ℓ * u)) ≤ Real.exp (-(B * L)) / 8 := by
  have hL0 : 0 < L := by linarith only [hL1]
  have hc : c₀ * L ^ 2 / 8 ≤ c₀ / ℓ * u := by
    have := mul_le_mul_of_nonneg_left hP1 hc₀.le
    have e1 : c₀ / ℓ * u = c₀ * (u / ℓ) := by ring
    have e2 : c₀ * L ^ 2 / 8 = c₀ * (L ^ 2 / 8) := by ring
    rw [e1, e2]; exact this
  have hk : (ε / 5 + 2 + B) * L + Real.log 128 ≤ c₀ * L ^ 2 / 8 := by
    have h8 : 8 * (ε / 5 + 2 + B + Real.log 128) ≤ c₀ * L := by rwa [div_le_iff₀ hc₀, mul_comm L] at hL2
    have h9 := mul_le_mul_of_nonneg_right h8 hL0.le
    have := le_mul_of_one_le_right (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 128))
      (show (1 : ℝ) ≤ L by linarith only [hL1])
    have e : c₀ * L ^ 2 / 8 = c₀ * L * L / 8 := by ring
    linarith
  calc 16 * u * Real.exp (-(c₀ / ℓ * u)) ≤ 16 * Real.exp ((ε / 5 + 2) * L) * Real.exp (-(c₀ * L ^ 2 / 8)) := by
        have hu : u ≤ Real.exp ((ε / 5 + 2) * L) := by
          rw [← Real.exp_log hu0]
          exact Real.exp_le_exp.mpr hlogu
        exact mul_le_mul (mul_le_mul_of_nonneg_left hu (by norm_num))
          (Real.exp_le_exp.mpr (neg_le_neg hc)) (Real.exp_pos _).le (by positivity)
    _ = Real.exp ((ε / 5 + 2) * L - c₀ * L ^ 2 / 8 + Real.log 16) := by
        rw [Real.exp_add, Real.exp_log (by norm_num), sub_eq_add_neg, Real.exp_add]; ring
    _ ≤ Real.exp (-(B * L) - Real.log 8) := Real.exp_le_exp.mpr (by
        have : Real.log 128 = Real.log 16 + Real.log 8 := by
          rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
        linarith)
    _ = Real.exp (-(B * L)) / 8 := by rw [Real.exp_sub, Real.exp_log (by norm_num)]

private theorem relative_progression_error {A B c₃ A₀ L u lm : ℝ}
    (hA0 : 0 < A) (hB0 : 0 < B) (hc₃ : 0 < c₃) (hL1 : 2 ≤ L)
    (hL3 : 8 * (B + Real.log (32 * (|A₀| + 1))) / c₃ ≤ L)
    (hL4 : Real.log (32 * (|A₀| + 1)) ≤ L)
    (hu2 : (A / 4 + (B + 1) ^ 2 / c₃ + 5 * (B + 1)) * L ^ 3 ≤ u)
    (hP2 : L ^ 2 / 8 ≤ u / lm) :
    2 * |A₀| * (Real.exp (-(c₃ * u / lm)) + Real.exp (-Real.sqrt (c₃ * u))) ≤
      Real.exp (-(B * L)) / 8 := by
  have hL0 : 0 < L := by linarith only [hL1]
  have hQ : 0 ≤ Real.log (32 * (|A₀| + 1)) :=
    Real.log_nonneg (by linarith only [abs_nonneg A₀])
  have h17 : 0 ≤ (A / 4) * L ^ 3 := by positivity
  have h18 : 0 ≤ 5 * (B + 1) * L ^ 3 := by positivity
  set Q := 32 * (|A₀| + 1)
  have hQ0 : 0 < Q := by positivity
  have hA : 2 * |A₀| ≤ Q / 16 := by simp only [Q]; linarith [abs_nonneg A₀]
  have key : ∀ t : ℝ, B * L + Real.log Q ≤ t → 2 * |A₀| * Real.exp (-t) ≤ Real.exp (-(B * L)) / 16 := by
    intro t ht
    calc 2 * |A₀| * Real.exp (-t) ≤ Q / 16 * Real.exp (-t) := mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
      _ ≤ Q / 16 * Real.exp (-(B * L) - Real.log Q) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
      _ = Real.exp (-(B * L)) / 16 := by
          rw [Real.exp_sub, Real.exp_log hQ0]; field_simp
  have t1 : B * L + Real.log Q ≤ c₃ * u / lm := by
    have : 8 * (B + Real.log Q) ≤ c₃ * L := by rwa [div_le_iff₀ hc₃, mul_comm L] at hL3
    have h2 : c₃ * (L ^ 2 / 8) ≤ c₃ * u / lm := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hP2 hc₃.le
    have h9 := mul_le_mul_of_nonneg_right this hL0.le
    have := le_mul_of_one_le_right hQ
      (show (1 : ℝ) ≤ L by linarith only [hL1])
    have e : c₃ * (L ^ 2 / 8) = c₃ * L * L / 8 := by ring
    linarith
  have t2 : B * L + Real.log Q ≤ Real.sqrt (c₃ * u) := by
    have : (B + 1) * L ≤ Real.sqrt (c₃ * u) := by
      apply Real.le_sqrt_of_sq_le
      have : c₃ * ((B + 1) ^ 2 / c₃ * L ^ 3) = (B + 1) ^ 2 * L ^ 3 := by field_simp
      have h3 : (B + 1) ^ 2 / c₃ * L ^ 3 ≤ u := by
        linarith
      have := mul_le_mul_of_nonneg_left h3 hc₃.le
      have hL23 : L ^ 2 ≤ L ^ 3 := by
        rw [show L ^ 3 = L ^ 2 * L by ring]
        exact le_mul_of_one_le_right (sq_nonneg L) (by linarith only [hL1])
      have e : ((B + 1) * L) ^ 2 = (B + 1) ^ 2 * L ^ 2 := by ring
      have := mul_le_mul_of_nonneg_left hL23 (sq_nonneg (B + 1))
      rw [e]; linarith
    linarith
  rw [mul_add]
  exact (add_le_add (key _ t1) (key _ t2)).trans_eq (by ring)

private theorem small_prime_error {A B c₃ L u : ℝ}
    (hA0 : 0 < A) (hB0 : 0 < B) (hc₃ : 0 < c₃) (hL1 : 2 ≤ L)
    (hu2 : (A / 4 + (B + 1) ^ 2 / c₃ + 5 * (B + 1)) * L ^ 3 ≤ u) :
    Real.exp (-(2 / 5 * u)) ≤ Real.exp (-(B * L)) / 4 := by
  have hL0 : 0 < L := by linarith only [hL1]
  have h16 : 0 ≤ (B + 1) ^ 2 / c₃ * L ^ 3 := by positivity
  have h17 : 0 ≤ A / 4 * L ^ 3 := by positivity
  have hl4 : Real.log 4 ≤ 2 := by
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9; linarith
  have h4L : 4 * L ≤ L ^ 3 := by
    rw [pow_succ]
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL1 2
    norm_num at h
    exact mul_le_mul_of_nonneg_right h hL0.le
  have h5L := mul_le_mul_of_nonneg_left h4L (by linarith : 0 ≤ B + 1)
  have h6L : 0 ≤ B * L := by positivity
  calc Real.exp (-(2 / 5 * u)) ≤ Real.exp (-(B * L) - Real.log 4) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num)]

theorem twist_scale_errors (A B ε c₀ c₃ A₀ C₀ L u lm ℓm ℓ : ℝ) (hA0 : 0 < A) (hB0 : 0 < B) (hε : 0 < ε) (hc₀ : 0 < c₀) (hc₃ : 0 < c₃)
    (hL1 : 2 ≤ L) (hL2 : 8 * (ε / 5 + 2 + B + Real.log 128) / c₀ ≤ L)
    (hL3 : 8 * (B + Real.log (32 * (|A₀| + 1))) / c₃ ≤ L) (hL4 : Real.log (32 * (|A₀| + 1)) ≤ L)
    (hL5 : 8 * |C₀| * (Real.log (6 + A) + ε / 5 + 1) ≤ L)
    (hu1 : (1 / 4) * L ^ 2 * ℓm ≤ u) (hu2 : (A / 4 + (B + 1) ^ 2 / c₃ + 5 * (B + 1)) * L ^ 3 ≤ u)
    (hlogu : Real.log u ≤ (ε / 5 + 2) * L)
    (hℓm : ℓm ≤ 4 * Real.exp (ε / 5 * L))
    (hlm0 : 2 ≤ lm) (hlm : lm ≤ ℓ) (hℓ : ℓ ≤ ℓm + A * L) :
    C₀ * lm * Real.log (lm + 2) ≤ u ∧
    16 * u * Real.exp (-(c₀ / ℓ * u)) ≤ Real.exp (-(B * L)) / 8 ∧
    2 * |A₀| * (Real.exp (-(c₃ * u / lm)) + Real.exp (-Real.sqrt (c₃ * u))) ≤ Real.exp (-(B * L)) / 8 ∧
    Real.exp (-(2 / 5 * u)) ≤ Real.exp (-(B * L)) / 4 := by
  have hL0 : 0 < L := by linarith only [hL1]
  have hu0 : 0 < u := by
    have h : 0 < (A / 4 + (B + 1) ^ 2 / c₃ + 5 * (B + 1)) * L ^ 3 := by positivity
    exact h.trans_le hu2
  have hP0 : L ^ 2 * ℓ / 8 ≤ u := by
    have h := mul_le_mul_of_nonneg_left hℓ (sq_nonneg L)
    have h₁ : 0 ≤ (B + 1) ^ 2 / c₃ * L ^ 3 := by positivity
    have h₂ : 0 ≤ 5 * (B + 1) * L ^ 3 := by positivity
    simp only [add_mul] at hu2
    linarith only [h, hu1, hu2, h₁, h₂]
  have hℓ0 : 0 < ℓ := by linarith only [hlm0, hlm]
  have hlm0' : 0 < lm := by linarith only [hlm0]
  have hP1 : L ^ 2 / 8 ≤ u / ℓ := (le_div_iff₀ hℓ0).mpr (by linarith only [hP0])
  have hP2 : L ^ 2 / 8 ≤ u / lm := hP1.trans (div_le_div_of_nonneg_left hu0.le hlm0' hlm)
  exact ⟨progression_range hA0 hε hL1 hL5 hℓm hlm0 hlm hℓ hP0,
    exceptional_error hc₀ hL1 hu0 hL2 hlogu hP1,
    relative_progression_error hA0 hB0 hc₃ hL1 hL3 hL4 hu2 hP2,
    small_prime_error hA0 hB0 hc₃ hL1 hu2⟩

end QH.PrimeProgressions
