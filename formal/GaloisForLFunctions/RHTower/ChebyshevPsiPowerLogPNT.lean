import GaloisForLFunctions.RHTower.PerronUnsmoothingStep

/-!
# The power-log prime number theorem for Chebyshev's `ψ`

Unsmoothing the tent-sum estimate through the two-sided sandwich with
step `h = e^{-c₀u/4}`, `u = (log x)^{1/10}`:

`|ψ(⌊x⌋) - x| ≤ C·x·exp(-c·(log x)^{1/10})`

— the unconditional de la Vallée Poussin prime number theorem with
power-log error in tenth-root form.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction

/-- **The power-log PNT for Chebyshev's `ψ`.** -/
theorem exists_chebyshevPsi_power_log :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 ≤ C ∧ 3 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        |chebyshevPsi ⌊x⌋₊ - x|
          ≤ C * x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨c₀, C₀, x₀', hc₀, hC₀, hx₀'3, hbound⟩ :=
    exists_smoothed_chebyshev_power_log
  have htent : ∀ z : ℝ, x₀' ≤ z → |perronTentSum z - z|
      ≤ C₀ * z * Real.exp (-(c₀ * Real.log z ^ ((1 : ℝ) / 10))) := by
    intro z hz
    have h1 := hbound z hz
    rwa [norm_perron_sum_sub_eq] at h1
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  refine ⟨c₀ / 4, 1 + 2 * Real.exp 1 * C₀,
    max (Real.exp 1 * x₀') (Real.exp 2), by positivity,
    by positivity, ?_, ?_⟩
  · calc (3 : ℝ) = 2 + 1 := by norm_num
      _ ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
      _ ≤ max (Real.exp 1 * x₀') (Real.exp 2) := le_max_right _ _
  · intro x hx
    have hx₀'0 : (0 : ℝ) < x₀' := by linarith
    have hxe : Real.exp 1 * x₀' ≤ x := le_trans (le_max_left _ _) hx
    have hxexp2 : Real.exp 2 ≤ x := le_trans (le_max_right _ _) hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by positivity) hxe
    have hlogx2 : (2 : ℝ) ≤ Real.log x := by
      have h1 := Real.log_le_log (Real.exp_pos 2) hxexp2
      rwa [Real.log_exp] at h1
    have hlogx0 : (0 : ℝ) < Real.log x := by linarith
    set u : ℝ := Real.log x ^ ((1 : ℝ) / 10) with hu
    have hu0 : (0 : ℝ) < u := Real.rpow_pos_of_pos hlogx0 _
    set h : ℝ := Real.exp (-(c₀ / 4 * u)) with hh
    have hh0 : (0 : ℝ) < h := Real.exp_pos _
    have hh1 : h ≤ 1 := by
      rw [hh, show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
      apply Real.exp_le_exp.2
      nlinarith [hc₀, hu0]
    have hpow4 : h ^ (4 : ℕ) = Real.exp (-(c₀ * u)) := by
      rw [hh, ← Real.exp_nat_mul]
      congr 1
      ring
    have hpow2 : h ^ (2 : ℕ) = Real.exp (-(c₀ / 2 * u)) := by
      rw [hh, ← Real.exp_nat_mul]
      congr 1
      ring
    -- the two comparison points
    have hexph1 : Real.exp h ≤ Real.exp 1 := Real.exp_le_exp.2 hh1
    have hyx : x ≤ x * Real.exp h :=
      le_mul_of_one_le_right hx0.le (Real.one_le_exp hh0.le)
    have hexpnegh : Real.exp (-h) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
      apply Real.exp_le_exp.2
      linarith
    have hx'le : x * Real.exp (-h) ≤ x :=
      mul_le_of_le_one_right hx0.le hexpnegh
    have hx'pos : (0 : ℝ) < x * Real.exp (-h) := by positivity
    -- the sandwich at (x, x·e^h) and (x·e^{-h}, x)
    have hlogyx : Real.log (x * Real.exp h / x) = h := by
      rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hx0), mul_one,
        Real.log_exp]
    have hlow := log_mul_psi_le_perronTent_sub hx0 hyx
    rw [hlogyx] at hlow
    have hlogxx' : Real.log (x / (x * Real.exp (-h))) = h := by
      rw [show x / (x * Real.exp (-h)) = (Real.exp (-h))⁻¹ from by
        field_simp]
      rw [← Real.exp_neg, neg_neg, Real.log_exp]
    have hup := perronTent_sub_le_log_mul_psi hx'pos hx'le
    rw [hlogxx'] at hup
    -- tent bounds at the three points
    have hxx₀' : x₀' ≤ x := by
      have h1 : x₀' ≤ Real.exp 1 * x₀' :=
        le_mul_of_one_le_left hx₀'0.le he1
      linarith
    have hbx := htent x hxx₀'
    rw [← hu] at hbx
    have hby := htent (x * Real.exp h) (le_trans hxx₀' hyx)
    have hbx' := htent (x * Real.exp (-h)) (by
      have h1 : Real.exp (-(1 : ℝ)) ≤ Real.exp (-h) :=
        Real.exp_le_exp.2 (by linarith)
      have h2 : x₀' = Real.exp 1 * x₀' * Real.exp (-(1 : ℝ)) := by
        rw [mul_comm (Real.exp 1) x₀', mul_assoc, ← Real.exp_add]
        norm_num
      calc x₀' = Real.exp 1 * x₀' * Real.exp (-(1 : ℝ)) := h2
        _ ≤ x * Real.exp (-h) :=
          mul_le_mul hxe h1 (Real.exp_pos _).le hx0.le)
    -- rate transfers
    have hEy : Real.exp (-(c₀ * Real.log (x * Real.exp h)
        ^ ((1 : ℝ) / 10))) ≤ h ^ (4 : ℕ) := by
      rw [hpow4]
      apply Real.exp_le_exp.2
      have h1 : Real.log x ≤ Real.log (x * Real.exp h) := by
        rw [Real.log_mul (ne_of_gt hx0) (Real.exp_ne_zero h),
          Real.log_exp]
        linarith
      have h2 : u ≤ Real.log (x * Real.exp h) ^ ((1 : ℝ) / 10) := by
        rw [hu]
        exact Real.rpow_le_rpow hlogx0.le h1 (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_left h2 hc₀.le]
    have hEx' : Real.exp (-(c₀ * Real.log (x * Real.exp (-h))
        ^ ((1 : ℝ) / 10))) ≤ h ^ (2 : ℕ) := by
      rw [hpow2]
      apply Real.exp_le_exp.2
      have hlx' : Real.log (x * Real.exp (-h)) = Real.log x - h := by
        rw [Real.log_mul (ne_of_gt hx0) (Real.exp_ne_zero _),
          Real.log_exp]
        ring
      have h1 : Real.log x / 2 ≤ Real.log x - h := by linarith
      have h2 : (Real.log x / 2) ^ ((1 : ℝ) / 10)
          ≤ (Real.log x - h) ^ ((1 : ℝ) / 10) :=
        Real.rpow_le_rpow (by positivity) h1 (by norm_num)
      have h3 : u / 2 ≤ (Real.log x / 2) ^ ((1 : ℝ) / 10) := by
        rw [Real.div_rpow hlogx0.le (by norm_num), hu]
        have h4 : (2 : ℝ) ^ ((1 : ℝ) / 10) ≤ 2 := by
          calc (2 : ℝ) ^ ((1 : ℝ) / 10)
              ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num)
                  (by norm_num)
            _ = 2 := Real.rpow_one 2
        exact div_le_div_of_nonneg_left
          (Real.rpow_nonneg hlogx0.le _) (by positivity) h4
      have h5 := le_trans h3 h2
      rw [hlx']
      nlinarith [mul_le_mul_of_nonneg_left h5 hc₀.le]
    -- Taylor bounds for the step
    have htay := Real.abs_exp_sub_one_sub_id_le
      (x := h) (by rw [abs_of_pos hh0]; exact hh1)
    have htay' := Real.abs_exp_sub_one_sub_id_le
      (x := -h) (by rw [abs_neg, abs_of_pos hh0]; exact hh1)
    have htay1 : Real.exp h - 1 ≤ h + h ^ 2 := by
      have h1 := (abs_le.1 htay).2
      linarith [h1]
    have htay2 : h - h ^ 2 ≤ 1 - Real.exp (-h) := by
      have h1 := (abs_le.1 htay').2
      linarith [h1]
    -- assemble: numeric bounds on the three tent errors
    have hBy : |perronTentSum (x * Real.exp h) - x * Real.exp h|
        ≤ C₀ * Real.exp 1 * x * h ^ (4 : ℕ) := by
      calc |perronTentSum (x * Real.exp h) - x * Real.exp h|
          ≤ C₀ * (x * Real.exp h)
            * Real.exp (-(c₀ * Real.log (x * Real.exp h)
              ^ ((1 : ℝ) / 10))) := hby
        _ ≤ C₀ * (x * Real.exp 1) * h ^ (4 : ℕ) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hexph1 hx0.le) hC₀
            · exact hEy
            · positivity
            · positivity
        _ = C₀ * Real.exp 1 * x * h ^ (4 : ℕ) := by ring
    have hBx : |perronTentSum x - x| ≤ C₀ * x * h ^ (4 : ℕ) := by
      calc |perronTentSum x - x|
          ≤ C₀ * x * Real.exp (-(c₀ * u)) := hbx
        _ = C₀ * x * h ^ (4 : ℕ) := by rw [hpow4]
    have hBx' : |perronTentSum (x * Real.exp (-h))
        - x * Real.exp (-h)| ≤ C₀ * x * h ^ (2 : ℕ) := by
      calc |perronTentSum (x * Real.exp (-h)) - x * Real.exp (-h)|
          ≤ C₀ * (x * Real.exp (-h))
            * Real.exp (-(c₀ * Real.log (x * Real.exp (-h))
              ^ ((1 : ℝ) / 10))) := hbx'
        _ ≤ C₀ * x * h ^ (2 : ℕ) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hx'le hC₀
            · exact hEx'
            · positivity
            · positivity
    -- upper estimate
    have hyd : x * (Real.exp h - 1) ≤ x * (h + h ^ 2) :=
      mul_le_mul_of_nonneg_left htay1 hx0.le
    have hxd : x * (h - h ^ 2) ≤ x * (1 - Real.exp (-h)) :=
      mul_le_mul_of_nonneg_left htay2 hx0.le
    have hup1 : h * (chebyshevPsi ⌊x⌋₊ - x)
        ≤ x * h ^ 2 + C₀ * Real.exp 1 * x * h ^ (4 : ℕ)
          + C₀ * x * h ^ (4 : ℕ) := by
      have h1 := (abs_le.1 hBy).2
      have h2 := (abs_le.1 hBx).1
      have h3 : h * (chebyshevPsi ⌊x⌋₊ - x)
          = h * chebyshevPsi ⌊x⌋₊ - h * x := by ring
      have h4 : x * (Real.exp h - 1)
          = x * Real.exp h - x := by ring
      have h5 : x * (h + h ^ 2) = x * h + x * h ^ 2 := by ring
      linarith only [hlow, h1, h2, hyd, h3, h4, h5]
    -- lower estimate
    have hlow1 : h * (x - chebyshevPsi ⌊x⌋₊)
        ≤ x * h ^ 2 + C₀ * x * h ^ (2 : ℕ)
          + C₀ * x * h ^ (4 : ℕ) := by
      have h1 := (abs_le.1 hBx').2
      have h2 := (abs_le.1 hBx).1
      linarith only [hup, h1, h2, hxd]
    -- cancel one power of `h`
    have hh4le : h ^ (4 : ℕ) ≤ h ^ 2 := by
      calc h ^ (4 : ℕ) = h ^ 2 * h ^ 2 := by ring
        _ ≤ 1 * h ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            nlinarith only [hh1, hh0.le]
        _ = h ^ 2 := one_mul _
    have hk1 : C₀ * Real.exp 1 * x * h ^ (4 : ℕ)
        ≤ C₀ * Real.exp 1 * x * h ^ 2 :=
      mul_le_mul_of_nonneg_left hh4le (by positivity)
    have hk2 : C₀ * x * h ^ (4 : ℕ) ≤ C₀ * x * h ^ 2 :=
      mul_le_mul_of_nonneg_left hh4le (by positivity)
    have hk3 : C₀ * x * h ^ 2 ≤ C₀ * Real.exp 1 * x * h ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left he1
        (show (0 : ℝ) ≤ C₀ * x * h ^ 2 by positivity)
      nlinarith only [h1]
    have hfinal_up : chebyshevPsi ⌊x⌋₊ - x
        ≤ (1 + 2 * Real.exp 1 * C₀) * x * h := by
      have h1 : h * (chebyshevPsi ⌊x⌋₊ - x)
          ≤ h * ((1 + 2 * Real.exp 1 * C₀) * x * h) := by
        have hrhs : h * ((1 + 2 * Real.exp 1 * C₀) * x * h)
            = x * h ^ 2 + 2 * (C₀ * Real.exp 1 * x * h ^ 2) := by
          ring
        linarith only [hup1, hk1, hk2, hk3, hrhs]
      exact le_of_mul_le_mul_left h1 hh0
    have hfinal_low : x - chebyshevPsi ⌊x⌋₊
        ≤ (1 + 2 * Real.exp 1 * C₀) * x * h := by
      have h1 : h * (x - chebyshevPsi ⌊x⌋₊)
          ≤ h * ((1 + 2 * Real.exp 1 * C₀) * x * h) := by
        have hrhs : h * ((1 + 2 * Real.exp 1 * C₀) * x * h)
            = x * h ^ 2 + 2 * (C₀ * Real.exp 1 * x * h ^ 2) := by
          ring
        linarith only [hlow1, hk1, hk2, hk3, hrhs]
      exact le_of_mul_le_mul_left h1 hh0
    rw [abs_sub_le_iff]
    exact ⟨hfinal_up, hfinal_low⟩

end RHTower
