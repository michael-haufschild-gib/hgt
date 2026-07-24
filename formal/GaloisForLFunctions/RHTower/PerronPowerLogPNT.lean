import GaloisForLFunctions.RHTower.PerronPolyExpAbsorb

/-!
# The power-log prime number theorem for the smoothed Chebyshev sum

Optimizing the Perron master bound with `a = 1 + 1/log x` and
`T = exp((log x)^{1/10})` yields

`‖∑ Λ(n)(log(x/n))⁺ − x‖ ≤ C₀·x·exp(−c₀·(log x)^{1/10})`

for absolute constants `c₀ = A/4 > 0`, `C₀`, valid for all
sufficiently large `x` — the de la Vallée Poussin error term in the
tenth-root exponent dictated by the `log⁹` zero-free region.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set

set_option maxHeartbeats 3200000 in
/-- **The power-log PNT for the smoothed Chebyshev sum.** -/
theorem exists_smoothed_chebyshev_power_log :
    ∃ c₀ C₀ x₀ : ℝ, 0 < c₀ ∧ 0 ≤ C₀ ∧ 3 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ‖(∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
            * ((max (Real.log (x / n)) 0 : ℝ) : ℂ)) - (x : ℂ)‖
          ≤ C₀ * x * Real.exp (-(c₀ * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨δ₀, M₀, hδ0, hδ8, hM0, hmaster⟩ :=
    exists_smoothed_chebyshev_error_bound
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hA1 : zetaLowerA ≤ 1 := by
    rw [zetaLowerA]
    norm_num
  refine ⟨zetaLowerA / 4,
    (2 * 8 * Real.exp 1 * 2 * Real.pi / (4 * Real.pi ^ 2))
        * ((Nat.factorial 21 : ℝ) * 2 ^ 21)
      + (2 * Real.pi)⁻¹ * ((M₀ + 2 / zetaLowerA + 2240 / zetaLowerA)
          * (8 * Real.pi / 7)
          * ((Nat.factorial 9 : ℝ) * (4 / zetaLowerA) ^ 9))
      + (2 * Real.pi)⁻¹ * (2 * (2240 / zetaLowerA) * Real.exp 1 * 2
          * ((Nat.factorial 9 : ℝ) * 2 ^ 9)),
    Real.exp ((max 3 (max (2 / zetaLowerA)
      ((zetaLowerA / (2 * δ₀)) ^ ((1 : ℝ) / 9)))) ^ (10 : ℕ)),
    by positivity, by positivity, ?_, ?_⟩
  · -- `3 ≤ x₀`
    have h1 : (3 : ℝ) ≤ max 3 (max (2 / zetaLowerA)
        ((zetaLowerA / (2 * δ₀)) ^ ((1 : ℝ) / 9))) := le_max_left _ _
    have h2 : (3 : ℝ) ^ (10 : ℕ)
        ≤ (max 3 (max (2 / zetaLowerA)
          ((zetaLowerA / (2 * δ₀)) ^ ((1 : ℝ) / 9)))) ^ (10 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h1 10
    calc (3 : ℝ) ≤ 3 ^ (10 : ℕ) := by norm_num
      _ ≤ (max 3 (max (2 / zetaLowerA)
          ((zetaLowerA / (2 * δ₀)) ^ ((1 : ℝ) / 9)))) ^ (10 : ℕ) := h2
      _ ≤ Real.exp ((max 3 (max (2 / zetaLowerA)
          ((zetaLowerA / (2 * δ₀)) ^ ((1 : ℝ) / 9)))) ^ (10 : ℕ)) := by
          have := Real.add_one_le_exp ((max 3 (max (2 / zetaLowerA)
            ((zetaLowerA / (2 * δ₀)) ^ ((1 : ℝ) / 9)))) ^ (10 : ℕ))
          linarith
  · -- the main bound
    intro x hx
    set u₀ : ℝ := max 3 (max (2 / zetaLowerA)
      ((zetaLowerA / (2 * δ₀)) ^ ((1 : ℝ) / 9))) with hu₀def
    have hu₀3 : (3 : ℝ) ≤ u₀ := le_max_left _ _
    have hu₀0 : (0 : ℝ) < u₀ := by linarith
    have hx0 : (0 : ℝ) < x :=
      lt_of_lt_of_le (Real.exp_pos _) hx
    have hlogx₀ : u₀ ^ (10 : ℕ) ≤ Real.log x := by
      have h1 := Real.log_le_log (Real.exp_pos _) hx
      rwa [Real.log_exp] at h1
    have hlogx0 : (0 : ℝ) < Real.log x := by
      have : (0 : ℝ) < u₀ ^ (10 : ℕ) := by positivity
      linarith
    set u : ℝ := Real.log x ^ ((1 : ℝ) / 10) with hudef
    have hu0 : (0 : ℝ) < u := Real.rpow_pos_of_pos hlogx0 _
    have hu10 : u ^ (10 : ℕ) = Real.log x := by
      rw [hudef, ← Real.rpow_natCast (Real.log x ^ ((1 : ℝ) / 10)) 10,
        ← Real.rpow_mul hlogx0.le]
      norm_num
    have huu₀ : u₀ ≤ u := by
      have h1 : u₀ ^ (10 : ℕ) ≤ u ^ (10 : ℕ) := by
        rw [hu10]
        exact hlogx₀
      exact le_of_pow_le_pow_left₀ (by norm_num) hu0.le h1
    have hu3 : (3 : ℝ) ≤ u := le_trans hu₀3 huu₀
    have hu1 : (1 : ℝ) ≤ u := by linarith
    have hu2A : 2 / zetaLowerA ≤ u :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) huu₀
    have hu9δ : zetaLowerA / (2 * δ₀) ≤ u ^ (9 : ℕ) := by
      have h1 : (zetaLowerA / (2 * δ₀)) ^ ((1 : ℝ) / 9) ≤ u :=
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) huu₀
      have h2 : ((zetaLowerA / (2 * δ₀)) ^ ((1 : ℝ) / 9)) ^ (9 : ℕ)
          ≤ u ^ (9 : ℕ) :=
        pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) h1 9
      rwa [← Real.rpow_natCast ((zetaLowerA / (2 * δ₀))
          ^ ((1 : ℝ) / 9)) 9, ← Real.rpow_mul (by positivity),
        show (1 : ℝ) / 9 * (9 : ℕ) = 1 from by norm_num,
        Real.rpow_one] at h2
    have hu90 : (0 : ℝ) < u ^ (9 : ℕ) := by positivity
    have hu91 : (1 : ℝ) ≤ u ^ (9 : ℕ) := one_le_pow₀ hu1
    -- the parameter choices
    have h2A : (2 : ℝ) ≤ zetaLowerA * u := by
      rw [div_le_iff₀ hA0] at hu2A
      linarith [hu2A]
    have hminA : zetaLowerA / (2 * u ^ (9 : ℕ)) ≤ δ₀ := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hu9δ
      linarith [hu9δ]
    have h2πW : 2 * Real.pi * (Real.exp u / (2 * Real.pi))
        = Real.exp u := by
      field_simp
    have hlogT : Real.log (2 * Real.pi
        * (Real.exp u / (2 * Real.pi))) = u := by
      rw [h2πW, Real.log_exp]
    have hexp3 : (9 : ℝ) < Real.exp 3 := by
      have h1 : Real.exp 3 = Real.exp 1 ^ (3 : ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [h1]
      have h2 : (2.7182818283 : ℝ) ^ (3 : ℕ) < Real.exp 1 ^ (3 : ℕ) :=
        pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
      nlinarith [h2]
    have hT9 : (9 : ℝ) ≤ 2 * Real.pi
        * (Real.exp u / (2 * Real.pi)) := by
      rw [h2πW]
      calc (9 : ℝ) ≤ Real.exp 3 := hexp3.le
        _ ≤ Real.exp u := Real.exp_le_exp.2 hu3
    have ha1 : 1 < 1 + 1 / Real.log x := by
      have : (0 : ℝ) < 1 / Real.log x := by positivity
      linarith
    have hlogx1 : (1 : ℝ) ≤ Real.log x := by
      rw [← hu10]
      exact le_trans hu1 (le_self_pow₀ hu1 (by norm_num))
    have ha2 : 1 + 1 / Real.log x ≤ 2 := by
      have : 1 / Real.log x ≤ 1 := by
        rw [div_le_one hlogx0]
        exact hlogx1
      linarith
    have haA : 1 + 1 / Real.log x ≤ 1 + zetaLowerA
        / (2 * Real.log (2 * Real.pi
          * (Real.exp u / (2 * Real.pi))) ^ 9) := by
      rw [hlogT]
      have h1 : 1 / Real.log x ≤ zetaLowerA / (2 * u ^ 9) := by
        rw [← hu10, div_le_div_iff₀ (by positivity) (by positivity)]
        have h2 : u ^ (10 : ℕ) = u * u ^ (9 : ℕ) := by ring
        rw [h2]
        nlinarith [h2A, hu90]
      linarith
    have hσ₀def : 1 - zetaLowerA / (2 * u ^ (9 : ℕ))
        = 1 - min δ₀ (zetaLowerA
          / (2 * Real.log (2 * Real.pi
            * (Real.exp u / (2 * Real.pi))) ^ 9)) := by
      rw [hlogT, min_eq_right hminA]
    have hx1 : (1 : ℝ) ≤ x := by
      calc (1 : ℝ) ≤ Real.exp (u₀ ^ (10 : ℕ)) :=
            Real.one_le_exp (by positivity)
        _ ≤ x := hx
    -- apply the master bound
    have hmb := hmaster x (1 + 1 / Real.log x)
      (Real.exp u / (2 * Real.pi))
      (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))
      (max (M₀ + (1 - (1 - zetaLowerA / (2 * u ^ (9 : ℕ))))⁻¹)
        (2240 / zetaLowerA * Real.log (2 * Real.pi
          * (Real.exp u / (2 * Real.pi))) ^ 9))
      hx1 ha1 ha2 hT9 haA hσ₀def rfl
    rw [hlogT, h2πW] at hmb
    -- simplify the pieces
    have hlog2 : Real.log x ^ (2 : ℕ) = u ^ (20 : ℕ) := by
      rw [← hu10]
      ring
    have hquot : 8 / ((1 + 1 / Real.log x) - 1) ^ 2
        = 8 * u ^ (20 : ℕ) := by
      rw [show (1 + 1 / Real.log x) - 1 = 1 / Real.log x from by ring,
        ← hlog2]
      field_simp
    have hane : Real.log x ≠ 0 := ne_of_gt hlogx0
    have hxa : x ^ (1 + 1 / Real.log x) = Real.exp 1 * x := by
      rw [Real.rpow_add hx0, Real.rpow_one,
        Real.rpow_def_of_pos hx0, mul_one_div, div_self hane, mul_comm]
    have hexpσ : Real.log x * (zetaLowerA / (2 * u ^ (9 : ℕ)))
        = zetaLowerA * u / 2 := by
      rw [← hu10]
      field_simp
    have hxσ : x ^ (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))
        = x * Real.exp (-(zetaLowerA * u / 2)) := by
      rw [show (1 : ℝ) - zetaLowerA / (2 * u ^ (9 : ℕ))
          = 1 + -(zetaLowerA / (2 * u ^ (9 : ℕ))) from by ring,
        Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0,
        mul_neg, hexpσ]
    have hσ₀78 : (7 : ℝ) / 8 ≤ 1 - zetaLowerA / (2 * u ^ (9 : ℕ)) := by
      linarith [hminA, hδ8]
    have hσ₀pos2 : (0 : ℝ) < 1 - zetaLowerA / (2 * u ^ (9 : ℕ)) := by
      linarith
    have hπσ : Real.pi / (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))
        ≤ 8 * Real.pi / 7 := by
      calc Real.pi / (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))
          ≤ Real.pi / (7 / 8) :=
            div_le_div_of_nonneg_left hπ0.le (by norm_num) hσ₀78
        _ = 8 * Real.pi / 7 := by ring
    have hinv : (1 - (1 - zetaLowerA / (2 * u ^ (9 : ℕ))))⁻¹
        = 2 * u ^ (9 : ℕ) / zetaLowerA := by
      rw [show (1 : ℝ) - (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))
          = zetaLowerA / (2 * u ^ (9 : ℕ)) from by ring]
      rw [inv_div]
    have hMedge_le : max (M₀
          + (1 - (1 - zetaLowerA / (2 * u ^ (9 : ℕ))))⁻¹)
          (2240 / zetaLowerA * u ^ 9)
        ≤ (M₀ + 2 / zetaLowerA + 2240 / zetaLowerA)
          * u ^ (9 : ℕ) := by
      apply max_le
      · rw [hinv]
        have h1 : M₀ ≤ M₀ * u ^ (9 : ℕ) :=
          le_mul_of_one_le_right hM0 hu91
        have h2 : 2 * u ^ (9 : ℕ) / zetaLowerA
            = (2 / zetaLowerA) * u ^ (9 : ℕ) := by ring
        have h3 : (0 : ℝ) ≤ 2240 / zetaLowerA * u ^ (9 : ℕ) := by
          positivity
        have hdist : (M₀ + 2 / zetaLowerA + 2240 / zetaLowerA)
              * u ^ (9 : ℕ)
            = M₀ * u ^ (9 : ℕ) + (2 / zetaLowerA) * u ^ (9 : ℕ)
              + (2240 / zetaLowerA) * u ^ (9 : ℕ) := by ring
        linarith [h1, h3, hdist, h2]
      · have h1 : (0 : ℝ) ≤ (M₀ + 2 / zetaLowerA) * u ^ (9 : ℕ) := by
          positivity
        have hdist : (M₀ + 2 / zetaLowerA + 2240 / zetaLowerA)
              * u ^ (9 : ℕ)
            = (M₀ + 2 / zetaLowerA) * u ^ (9 : ℕ)
              + (2240 / zetaLowerA) * u ^ (9 : ℕ) := by ring
        linarith [h1, hdist]
    have habsd : |(1 + 1 / Real.log x)
        - (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))| ≤ 2 := by
      rw [show (1 + 1 / Real.log x)
          - (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))
          = 1 / Real.log x + zetaLowerA / (2 * u ^ (9 : ℕ)) from by
        ring]
      rw [abs_of_nonneg (by positivity)]
      have h1 : 1 / Real.log x ≤ 1 := by
        rw [div_le_one hlogx0]
        exact hlogx1
      have h2 : zetaLowerA / (2 * u ^ (9 : ℕ)) ≤ 1 := by
        linarith [hminA, hδ8]
      linarith
    -- the three absorptions
    have hexpmono : Real.exp (-(u / 2))
        ≤ Real.exp (-(zetaLowerA / 4 * u)) := by
      apply Real.exp_le_exp.2
      have hAu : zetaLowerA * u ≤ 1 * u :=
        mul_le_mul_of_nonneg_right hA1 hu0.le
      linarith [hAu]
    have habs1 : u ^ (20 : ℕ) * Real.exp (-u)
        ≤ (Nat.factorial 21 : ℝ) * 2 ^ 21
          * Real.exp (-(zetaLowerA / 4 * u)) := by
      have h1 : u ^ (20 : ℕ) ≤ u ^ (21 : ℕ) :=
        pow_le_pow_right₀ hu1 (by norm_num)
      have h2 := pow_mul_exp_neg_le one_pos hu0.le 21
      rw [show (1 : ℝ) * u = u from one_mul u] at h2
      have h3 : ((2 : ℝ) / 1) ^ (21 : ℕ) = 2 ^ 21 := by norm_num
      rw [h3] at h2
      calc u ^ (20 : ℕ) * Real.exp (-u)
          ≤ u ^ (21 : ℕ) * Real.exp (-u) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
        _ ≤ (Nat.factorial 21 : ℝ) * 2 ^ 21 * Real.exp (-(u / 2)) :=
            h2
        _ ≤ (Nat.factorial 21 : ℝ) * 2 ^ 21
            * Real.exp (-(zetaLowerA / 4 * u)) :=
            mul_le_mul_of_nonneg_left hexpmono (by positivity)
    have habs2 : u ^ (9 : ℕ) * Real.exp (-(zetaLowerA * u / 2))
        ≤ (Nat.factorial 9 : ℝ) * (4 / zetaLowerA) ^ 9
          * Real.exp (-(zetaLowerA / 4 * u)) := by
      have h2 := pow_mul_exp_neg_le
        (b := zetaLowerA / 2) (by positivity) hu0.le 9
      rw [show zetaLowerA / 2 * u = zetaLowerA * u / 2 from by ring,
        show (2 : ℝ) / (zetaLowerA / 2) = 4 / zetaLowerA from by
          field_simp; ring,
        show zetaLowerA * u / 2 / 2 = zetaLowerA / 4 * u from by
          ring] at h2
      exact h2
    have habs3 : u ^ (9 : ℕ) * Real.exp (-(2 * u))
        ≤ (Nat.factorial 9 : ℝ) * 2 ^ 9
          * Real.exp (-(zetaLowerA / 4 * u)) := by
      have h1 : Real.exp (-(2 * u)) ≤ Real.exp (-u) := by
        apply Real.exp_le_exp.2
        linarith
      have h2 := pow_mul_exp_neg_le one_pos hu0.le 9
      rw [show (1 : ℝ) * u = u from one_mul u] at h2
      have h3 : ((2 : ℝ) / 1) ^ (9 : ℕ) = 2 ^ 9 := by norm_num
      rw [h3] at h2
      calc u ^ (9 : ℕ) * Real.exp (-(2 * u))
          ≤ u ^ (9 : ℕ) * Real.exp (-u) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ (Nat.factorial 9 : ℝ) * 2 ^ 9 * Real.exp (-(u / 2)) := h2
        _ ≤ (Nat.factorial 9 : ℝ) * 2 ^ 9
            * Real.exp (-(zetaLowerA / 4 * u)) :=
            mul_le_mul_of_nonneg_left hexpmono (by positivity)
    -- bound the three master terms
    have hexpne : Real.exp u ≠ 0 := Real.exp_ne_zero u
    have hT1 : 2 * (8 / ((1 + 1 / Real.log x) - 1) ^ 2
          * x ^ (1 + 1 / Real.log x)
          / (4 * Real.pi ^ 2 * (Real.exp u / (2 * Real.pi))))
        ≤ 2 * 8 * Real.exp 1 * 2 * Real.pi / (4 * Real.pi ^ 2)
          * ((Nat.factorial 21 : ℝ) * 2 ^ 21) * x
          * Real.exp (-(zetaLowerA / 4 * u)) := by
      rw [hquot, hxa]
      have heq : 2 * (8 * u ^ (20 : ℕ) * (Real.exp 1 * x)
            / (4 * Real.pi ^ 2 * (Real.exp u / (2 * Real.pi))))
          = (2 * 8 * Real.exp 1 * 2 * Real.pi / (4 * Real.pi ^ 2))
            * x * (u ^ (20 : ℕ) * Real.exp (-u)) := by
        rw [Real.exp_neg]
        field_simp
      rw [heq]
      calc (2 * 8 * Real.exp 1 * 2 * Real.pi / (4 * Real.pi ^ 2))
            * x * (u ^ (20 : ℕ) * Real.exp (-u))
          ≤ (2 * 8 * Real.exp 1 * 2 * Real.pi / (4 * Real.pi ^ 2))
            * x * ((Nat.factorial 21 : ℝ) * 2 ^ 21
              * Real.exp (-(zetaLowerA / 4 * u))) :=
            mul_le_mul_of_nonneg_left habs1 (by positivity)
        _ = 2 * 8 * Real.exp 1 * 2 * Real.pi / (4 * Real.pi ^ 2)
            * ((Nat.factorial 21 : ℝ) * 2 ^ 21) * x
            * Real.exp (-(zetaLowerA / 4 * u)) := by ring
    have hT2 : (2 * Real.pi)⁻¹ * (max (M₀
          + (1 - (1 - zetaLowerA / (2 * u ^ (9 : ℕ))))⁻¹)
          (2240 / zetaLowerA * u ^ 9)
          * x ^ (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))
          * (Real.pi / (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))))
        ≤ (2 * Real.pi)⁻¹ * ((M₀ + 2 / zetaLowerA
            + 2240 / zetaLowerA) * (8 * Real.pi / 7)
          * ((Nat.factorial 9 : ℝ) * (4 / zetaLowerA) ^ 9)) * x
          * Real.exp (-(zetaLowerA / 4 * u)) := by
      rw [hxσ]
      have h1 : max (M₀
            + (1 - (1 - zetaLowerA / (2 * u ^ (9 : ℕ))))⁻¹)
            (2240 / zetaLowerA * u ^ 9)
            * (x * Real.exp (-(zetaLowerA * u / 2)))
            * (Real.pi / (1 - zetaLowerA / (2 * u ^ (9 : ℕ))))
          ≤ ((M₀ + 2 / zetaLowerA + 2240 / zetaLowerA)
              * u ^ (9 : ℕ))
            * (x * Real.exp (-(zetaLowerA * u / 2)))
            * (8 * Real.pi / 7) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right hMedge_le
            (by positivity)
        · exact hπσ
        · positivity
        · positivity
      have h2 : ((M₀ + 2 / zetaLowerA + 2240 / zetaLowerA)
            * u ^ (9 : ℕ))
          * (x * Real.exp (-(zetaLowerA * u / 2)))
          * (8 * Real.pi / 7)
          = (M₀ + 2 / zetaLowerA + 2240 / zetaLowerA)
            * (8 * Real.pi / 7) * x
            * (u ^ (9 : ℕ) * Real.exp (-(zetaLowerA * u / 2))) := by
        ring
      have h3 : (M₀ + 2 / zetaLowerA + 2240 / zetaLowerA)
            * (8 * Real.pi / 7) * x
            * (u ^ (9 : ℕ) * Real.exp (-(zetaLowerA * u / 2)))
          ≤ (M₀ + 2 / zetaLowerA + 2240 / zetaLowerA)
            * (8 * Real.pi / 7) * x
            * ((Nat.factorial 9 : ℝ) * (4 / zetaLowerA) ^ 9
              * Real.exp (-(zetaLowerA / 4 * u))) :=
        mul_le_mul_of_nonneg_left habs2 (by positivity)
      calc (2 * Real.pi)⁻¹ * (max (M₀
            + (1 - (1 - zetaLowerA / (2 * u ^ (9 : ℕ))))⁻¹)
            (2240 / zetaLowerA * u ^ 9)
            * (x * Real.exp (-(zetaLowerA * u / 2)))
            * (Real.pi / (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))))
          ≤ (2 * Real.pi)⁻¹ * ((M₀ + 2 / zetaLowerA
              + 2240 / zetaLowerA)
              * (8 * Real.pi / 7) * x
              * ((Nat.factorial 9 : ℝ) * (4 / zetaLowerA) ^ 9
                * Real.exp (-(zetaLowerA / 4 * u)))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc _ ≤ _ := h1
              _ = _ := h2
              _ ≤ _ := h3
        _ = (2 * Real.pi)⁻¹ * ((M₀ + 2 / zetaLowerA
              + 2240 / zetaLowerA) * (8 * Real.pi / 7)
            * ((Nat.factorial 9 : ℝ) * (4 / zetaLowerA) ^ 9)) * x
            * Real.exp (-(zetaLowerA / 4 * u)) := by ring
    have hT3 : (2 * Real.pi)⁻¹ * (2 * (2240 / zetaLowerA
            * u ^ 9 * x ^ (1 + 1 / Real.log x)
          / (Real.exp u) ^ 2
          * |(1 + 1 / Real.log x)
            - (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))|))
        ≤ (2 * Real.pi)⁻¹ * (2 * (2240 / zetaLowerA) * Real.exp 1
            * 2 * ((Nat.factorial 9 : ℝ) * 2 ^ 9)) * x
          * Real.exp (-(zetaLowerA / 4 * u)) := by
      rw [hxa]
      have heq : 2 * (2240 / zetaLowerA * u ^ 9 * (Real.exp 1 * x)
            / (Real.exp u) ^ 2
            * |(1 + 1 / Real.log x)
              - (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))|)
          = 2 * (2240 / zetaLowerA) * Real.exp 1 * x
            * (u ^ (9 : ℕ) * Real.exp (-(2 * u)))
            * |(1 + 1 / Real.log x)
              - (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))| := by
        rw [show Real.exp (-(2 * u)) = ((Real.exp u) ^ 2)⁻¹ from by
          rw [← Real.exp_nat_mul, Real.exp_neg]
          norm_num]
        field_simp
      rw [heq]
      have h1 : 2 * (2240 / zetaLowerA) * Real.exp 1 * x
            * (u ^ (9 : ℕ) * Real.exp (-(2 * u)))
            * |(1 + 1 / Real.log x)
              - (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))|
          ≤ 2 * (2240 / zetaLowerA) * Real.exp 1 * x
            * ((Nat.factorial 9 : ℝ) * 2 ^ 9
              * Real.exp (-(zetaLowerA / 4 * u))) * 2 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left habs3 (by positivity)
        · exact habsd
        · exact abs_nonneg _
        · positivity
      calc (2 * Real.pi)⁻¹ * (2 * (2240 / zetaLowerA) * Real.exp 1
              * x * (u ^ (9 : ℕ) * Real.exp (-(2 * u)))
            * |(1 + 1 / Real.log x)
              - (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))|)
          ≤ (2 * Real.pi)⁻¹ * (2 * (2240 / zetaLowerA) * Real.exp 1
              * x * ((Nat.factorial 9 : ℝ) * 2 ^ 9
                * Real.exp (-(zetaLowerA / 4 * u))) * 2) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (2 * Real.pi)⁻¹ * (2 * (2240 / zetaLowerA) * Real.exp 1
              * 2 * ((Nat.factorial 9 : ℝ) * 2 ^ 9)) * x
            * Real.exp (-(zetaLowerA / 4 * u)) := by ring
    -- combine
    calc ‖(∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
            * ((max (Real.log (x / n)) 0 : ℝ) : ℂ)) - (x : ℂ)‖
        ≤ 2 * (8 / ((1 + 1 / Real.log x) - 1) ^ 2
            * x ^ (1 + 1 / Real.log x)
            / (4 * Real.pi ^ 2 * (Real.exp u / (2 * Real.pi))))
          + (2 * Real.pi)⁻¹ * (max (M₀
              + (1 - (1 - zetaLowerA / (2 * u ^ (9 : ℕ))))⁻¹)
              (2240 / zetaLowerA * u ^ 9)
              * x ^ (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))
              * (Real.pi / (1 - zetaLowerA / (2 * u ^ (9 : ℕ))))
            + 2 * (2240 / zetaLowerA * u ^ 9
              * x ^ (1 + 1 / Real.log x) / (Real.exp u) ^ 2
              * |(1 + 1 / Real.log x)
                - (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))|)) := hmb
      _ ≤ (2 * 8 * Real.exp 1 * 2 * Real.pi / (4 * Real.pi ^ 2)
            * ((Nat.factorial 21 : ℝ) * 2 ^ 21)
          + (2 * Real.pi)⁻¹ * ((M₀ + 2 / zetaLowerA
              + 2240 / zetaLowerA) * (8 * Real.pi / 7)
            * ((Nat.factorial 9 : ℝ) * (4 / zetaLowerA) ^ 9))
          + (2 * Real.pi)⁻¹ * (2 * (2240 / zetaLowerA) * Real.exp 1
              * 2 * ((Nat.factorial 9 : ℝ) * 2 ^ 9))) * x
          * Real.exp (-(zetaLowerA / 4 * u)) := by
          have hdistr : (2 * Real.pi)⁻¹ * (max (M₀
              + (1 - (1 - zetaLowerA / (2 * u ^ (9 : ℕ))))⁻¹)
              (2240 / zetaLowerA * u ^ 9)
              * x ^ (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))
              * (Real.pi / (1 - zetaLowerA / (2 * u ^ (9 : ℕ))))
            + 2 * (2240 / zetaLowerA * u ^ 9
              * x ^ (1 + 1 / Real.log x) / (Real.exp u) ^ 2
              * |(1 + 1 / Real.log x)
                - (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))|))
            = (2 * Real.pi)⁻¹ * (max (M₀
              + (1 - (1 - zetaLowerA / (2 * u ^ (9 : ℕ))))⁻¹)
              (2240 / zetaLowerA * u ^ 9)
              * x ^ (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))
              * (Real.pi / (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))))
            + (2 * Real.pi)⁻¹ * (2 * (2240 / zetaLowerA * u ^ 9
              * x ^ (1 + 1 / Real.log x) / (Real.exp u) ^ 2
              * |(1 + 1 / Real.log x)
                - (1 - zetaLowerA / (2 * u ^ (9 : ℕ)))|)) := by
            ring
          rw [hdistr]
          linarith [hT1, hT2, hT3]
      _ = (2 * 8 * Real.exp 1 * 2 * Real.pi / (4 * Real.pi ^ 2)
            * ((Nat.factorial 21 : ℝ) * 2 ^ 21)
          + (2 * Real.pi)⁻¹ * ((M₀ + 2 / zetaLowerA
              + 2240 / zetaLowerA) * (8 * Real.pi / 7)
            * ((Nat.factorial 9 : ℝ) * (4 / zetaLowerA) ^ 9))
          + (2 * Real.pi)⁻¹ * (2 * (2240 / zetaLowerA) * Real.exp 1
              * 2 * ((Nat.factorial 9 : ℝ) * 2 ^ 9))) * x
          * Real.exp (-(zetaLowerA / 4
            * Real.log x ^ ((1 : ℝ) / 10))) := by
          rw [hudef]

end RHTower
