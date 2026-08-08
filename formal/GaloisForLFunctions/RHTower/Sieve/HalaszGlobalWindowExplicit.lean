import GaloisForLFunctions.RHTower.Sieve.HalaszGlobalIntegralBound

/-!
# The window width explicitly

`charSepLower z Δ` depends on the separation only through `log(5 + 1/Δ)`, and `5 + 1/Δ ≤ 6/Δ` for
`Δ ≤ 1`, so

`charSepLower z Δ ≥ logLog z − charGapConst + log Δ`.

The gap condition `4δ² < charSepLower z Δ` is therefore met by

`Δ = exp(4δ² + charGapConst + 1)/log z`,

admissible as soon as `4δ² + charGapConst + 1 ≤ logLog z`.  The window term of the Halász integral
bound becomes `(1 + 1/(σ−1))e^{7/2}·2exp(4δ² + charGapConst + 1)/log z`: at `σ − 1 = 1/log z` the
factor `log z` cancels and the term is of order `e^{4δ²}`, against a damped term of order
`(log z)e^{-δ²}T`.  Balancing the two exponents gives an integral of order `(T log z)^{4/5}`, below the
trivial bound `2T·(log z)`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- Every loss in `charSepLower` that does not involve the separation, together with the `log 6` from
`5 + 1/Δ ≤ 6/Δ`. -/
noncomputable def charGapConst : ℝ :=
  mertensSecondLowerConst + Real.pi ^ 2 / 6
    + 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
    + (1 + Real.log 4) + Real.log 6

/-- **The separation bound below `Δ ≤ 1`.**  The additive form of `charSepLower`. -/
theorem lt_charSepLower_of_lt {z : ℕ} {Δ x : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (h : x < logLog z - charGapConst + Real.log Δ) : x < charSepLower z Δ := by
  have h5 : 5 + 1 / Δ ≤ 6 / Δ := by
    rw [← sub_nonneg]
    have hid : 6 / Δ - (5 + 1 / Δ) = 5 * (1 - Δ) / Δ := by
      field_simp
      ring
    rw [hid]
    exact div_nonneg (by nlinarith) hΔ0.le
  have hlog : Real.log (5 + 1 / Δ) ≤ Real.log 6 - Real.log Δ := by
    have hdiv : Real.log (6 / Δ) = Real.log 6 - Real.log Δ :=
      Real.log_div (by norm_num) hΔ0.ne'
    calc Real.log (5 + 1 / Δ) ≤ Real.log (6 / Δ) := Real.log_le_log (by positivity) h5
      _ = Real.log 6 - Real.log Δ := hdiv
  rw [charSepLower, abs_of_pos hΔ0]
  rw [charGapConst] at h
  linarith

/-- **An admissible window width.**  The gap condition holds at `Δ = e^{4δ² + C + 1}/log z`. -/
theorem four_mul_sq_lt_charSepLower_exp {z : ℕ} {δ : ℝ} (hlz : 0 < Real.log (z : ℝ))
    (hz : 4 * δ ^ 2 + charGapConst + 1 ≤ logLog z) :
    4 * δ ^ 2
      < charSepLower z (Real.exp (4 * δ ^ 2 + charGapConst + 1) / Real.log (z : ℝ)) := by
  have hΔ0 : (0 : ℝ) < Real.exp (4 * δ ^ 2 + charGapConst + 1) / Real.log (z : ℝ) := by
    positivity
  have hlogΔ : Real.log (Real.exp (4 * δ ^ 2 + charGapConst + 1) / Real.log (z : ℝ))
      = 4 * δ ^ 2 + charGapConst + 1 - Real.log (Real.log (z : ℝ)) := by
    rw [Real.log_div (Real.exp_ne_zero _) hlz.ne', Real.log_exp]
  have hΔ1 : Real.exp (4 * δ ^ 2 + charGapConst + 1) / Real.log (z : ℝ) ≤ 1 := by
    rw [div_le_one hlz]
    calc Real.exp (4 * δ ^ 2 + charGapConst + 1)
        ≤ Real.exp (Real.log (Real.log (z : ℝ))) := Real.exp_le_exp.mpr (by rw [logLog] at hz; exact hz)
      _ = Real.log (z : ℝ) := Real.exp_log hlz
  refine lt_charSepLower_of_lt hΔ0 hΔ1 ?_
  rw [hlogΔ, logLog]
  linarith

/-- **The Halász integral bound with an explicit window.**  Unconditional, for every bounded
multiplicative `f`: the exceptional window has width `e^{4δ² + C + 1}/log z`. -/
theorem integral_norm_tsum_twistedSummand_le_explicit_window {f : ℕ → ℂ}
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 3 ≤ z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hgap : 4 * δ ^ 2 + charGapConst + 1 ≤ logLog z)
    {T : ℝ} (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    (∫ t in Set.Icc (-T) T,
        ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖)
      ≤ (1 + 1 / (σ - 1)) *
            Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) * (2 * T)
          + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
            (2 * (Real.exp (4 * δ ^ 2 + charGapConst + 1) / Real.log (z : ℝ))) := by
  have hz1 : (1 : ℝ) < ((z : ℕ) : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num : (1:ℕ) < 3) hz
  have hlz : 0 < Real.log ((z : ℕ) : ℝ) := Real.log_pos hz1
  exact integral_norm_tsum_twistedSummand_le_window hf1 hmul hbdd hσ hz hδ
    (by positivity) (four_mul_sq_lt_charSepLower_exp hlz hgap) hT hT1

section
open Real

/-- **Balancing the damped term against the window term.**  At `x = log(LT)/5` the two exponentials
`LTe^{-x}` and `e^{4x}` are equal, both `(LT)^{4/5}`. -/
theorem window_balance_le {L T x C : ℝ} (hL : 1 ≤ L) (hT0 : 0 < T)
    (hLT : 1 ≤ L * T) (hx : x = Real.log (L * T) / 5) :
    (1 + 1 / (1 / L)) * Real.exp (7 / 2 + 2 * (1 / L) * (L + Real.log 4) - x) * (2 * T)
        + (1 + 1 / (1 / L)) * Real.exp (7 / 2) * (2 * (Real.exp (4 * x + C + 1) / L))
      ≤ (64 * Real.exp (11 / 2) + 4 * Real.exp (9 / 2 + C)) * (L * T) ^ (4 / 5 : ℝ) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hLT0 : (0 : ℝ) < L * T := by linarith
  have hlogLT : (0 : ℝ) ≤ Real.log (L * T) := Real.log_nonneg hLT
  have hcoef : 1 + 1 / (1 / L) = 1 + L := by
    rw [one_div_one_div]
  have hpow : (L * T) ^ (4 / 5 : ℝ) = Real.exp (Real.log (L * T) * (4 / 5)) :=
    Real.rpow_def_of_pos hLT0 (4 / 5)
  -- the damped term
  have hexpo : 7 / 2 + 2 * (1 / L) * (L + Real.log 4) - x
      ≤ 11 / 2 + 2 * Real.log 4 - x := by
    have hL4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hinv : 1 / L ≤ 1 := by
      rw [div_le_one hL0]; exact hL
    have hstep : 2 * (1 / L) * (L + Real.log 4)
        = 2 * (1 / L) * L + 2 * (1 / L) * Real.log 4 := by ring
    have h3 : 2 * (1 / L) * Real.log 4 ≤ 2 * Real.log 4 := by
      nlinarith [hL4, hinv]
    have hcancel : 2 * (1 / L) * L = 2 := by
      field_simp
    linarith
  have hdamped : (1 + 1 / (1 / L))
        * Real.exp (7 / 2 + 2 * (1 / L) * (L + Real.log 4) - x) * (2 * T)
      ≤ 64 * Real.exp (11 / 2) * (L * T) ^ (4 / 5 : ℝ) := by
    have hb : Real.exp (7 / 2 + 2 * (1 / L) * (L + Real.log 4) - x)
        ≤ 16 * Real.exp (11 / 2) * Real.exp (-x) := by
      have h16 : Real.exp (2 * Real.log 4) = 16 := by
        rw [show (2 : ℝ) * Real.log 4 = Real.log (4 ^ (2 : ℕ)) by
          rw [Real.log_pow]; push_cast; ring]
        rw [Real.exp_log (by norm_num)]
        norm_num
      calc Real.exp (7 / 2 + 2 * (1 / L) * (L + Real.log 4) - x)
          ≤ Real.exp (11 / 2 + 2 * Real.log 4 - x) := Real.exp_le_exp.mpr hexpo
        _ = Real.exp (2 * Real.log 4) * Real.exp (11 / 2) * Real.exp (-x) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
        _ = 16 * Real.exp (11 / 2) * Real.exp (-x) := by rw [h16]
    have hkey : L * T * Real.exp (-x) = (L * T) ^ (4 / 5 : ℝ) := by
      calc L * T * Real.exp (-x)
          = Real.exp (Real.log (L * T)) * Real.exp (-x) := by rw [Real.exp_log hLT0]
        _ = Real.exp (Real.log (L * T) + -x) := by rw [← Real.exp_add]
        _ = Real.exp (Real.log (L * T) * (4 / 5)) := by rw [hx]; congr 1; ring
        _ = (L * T) ^ (4 / 5 : ℝ) := hpow.symm
    have hcoefle : 1 + L ≤ 2 * L := by linarith
    calc (1 + 1 / (1 / L))
          * Real.exp (7 / 2 + 2 * (1 / L) * (L + Real.log 4) - x) * (2 * T)
        = (1 + L) * Real.exp (7 / 2 + 2 * (1 / L) * (L + Real.log 4) - x) * (2 * T) := by
          rw [hcoef]
      _ ≤ (2 * L) * (16 * Real.exp (11 / 2) * Real.exp (-x)) * (2 * T) := by
          have h1 : (0 : ℝ) ≤ Real.exp (7 / 2 + 2 * (1 / L) * (L + Real.log 4) - x) :=
            (Real.exp_pos _).le
          have h2 : (0 : ℝ) < 2 * T := by linarith
          have hmul1 : (1 + L) * Real.exp (7 / 2 + 2 * (1 / L) * (L + Real.log 4) - x)
              ≤ (2 * L) * (16 * Real.exp (11 / 2) * Real.exp (-x)) := by
            have hA : (1 + L) * Real.exp (7 / 2 + 2 * (1 / L) * (L + Real.log 4) - x)
                ≤ (1 + L) * (16 * Real.exp (11 / 2) * Real.exp (-x)) :=
              mul_le_mul_of_nonneg_left hb (by linarith)
            have hB : (1 + L) * (16 * Real.exp (11 / 2) * Real.exp (-x))
                ≤ (2 * L) * (16 * Real.exp (11 / 2) * Real.exp (-x)) :=
              mul_le_mul_of_nonneg_right hcoefle (by positivity)
            linarith
          exact mul_le_mul_of_nonneg_right hmul1 h2.le
      _ = 64 * Real.exp (11 / 2) * (L * T * Real.exp (-x)) := by ring
      _ = 64 * Real.exp (11 / 2) * (L * T) ^ (4 / 5 : ℝ) := by rw [hkey]
  -- the window term
  have hwindow : (1 + 1 / (1 / L)) * Real.exp (7 / 2) * (2 * (Real.exp (4 * x + C + 1) / L))
      ≤ 4 * Real.exp (9 / 2 + C) * (L * T) ^ (4 / 5 : ℝ) := by
    have hkey : Real.exp (4 * x) = (L * T) ^ (4 / 5 : ℝ) := by
      rw [hpow, hx]
      congr 1
      ring
    have hsplit : Real.exp (4 * x + C + 1) = Real.exp (4 * x) * Real.exp (C + 1) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hcoefle : 1 + L ≤ 2 * L := by linarith
    have hstep : (1 + L) * Real.exp (7 / 2) * (2 * (Real.exp (4 * x) * Real.exp (C + 1) / L))
        ≤ (2 * L) * Real.exp (7 / 2) * (2 * (Real.exp (4 * x) * Real.exp (C + 1) / L)) := by
      have hnn : (0 : ℝ) ≤ Real.exp (7 / 2) * (2 * (Real.exp (4 * x) * Real.exp (C + 1) / L)) := by
        positivity
      have := mul_le_mul_of_nonneg_right hcoefle hnn
      calc (1 + L) * Real.exp (7 / 2) * (2 * (Real.exp (4 * x) * Real.exp (C + 1) / L))
          = (1 + L) * (Real.exp (7 / 2) * (2 * (Real.exp (4 * x) * Real.exp (C + 1) / L))) := by
            ring
        _ ≤ (2 * L) * (Real.exp (7 / 2) * (2 * (Real.exp (4 * x) * Real.exp (C + 1) / L))) := this
        _ = (2 * L) * Real.exp (7 / 2) * (2 * (Real.exp (4 * x) * Real.exp (C + 1) / L)) := by ring
    have hval : (2 * L) * Real.exp (7 / 2) * (2 * (Real.exp (4 * x) * Real.exp (C + 1) / L))
        = 4 * Real.exp (9 / 2 + C) * Real.exp (4 * x) := by
      have hexp : Real.exp (7 / 2) * Real.exp (C + 1) = Real.exp (9 / 2 + C) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc (2 * L) * Real.exp (7 / 2) * (2 * (Real.exp (4 * x) * Real.exp (C + 1) / L))
          = 4 * (Real.exp (7 / 2) * Real.exp (C + 1)) * Real.exp (4 * x) * (L / L) := by ring
        _ = 4 * (Real.exp (7 / 2) * Real.exp (C + 1)) * Real.exp (4 * x) * 1 := by
            rw [div_self hL0.ne']
        _ = 4 * Real.exp (9 / 2 + C) * Real.exp (4 * x) := by rw [hexp]; ring
    rw [hcoef, hsplit]
    calc (1 + L) * Real.exp (7 / 2) * (2 * (Real.exp (4 * x) * Real.exp (C + 1) / L))
        ≤ (2 * L) * Real.exp (7 / 2) * (2 * (Real.exp (4 * x) * Real.exp (C + 1) / L)) := hstep
      _ = 4 * Real.exp (9 / 2 + C) * Real.exp (4 * x) := hval
      _ = 4 * Real.exp (9 / 2 + C) * (L * T) ^ (4 / 5 : ℝ) := by rw [hkey]
  have hexpand : (64 * Real.exp (11 / 2) + 4 * Real.exp (9 / 2 + C)) * (L * T) ^ (4 / 5 : ℝ)
      = 64 * Real.exp (11 / 2) * (L * T) ^ (4 / 5 : ℝ)
        + 4 * Real.exp (9 / 2 + C) * (L * T) ^ (4 / 5 : ℝ) := by ring
  linarith [hdamped, hwindow, hexpand]

/-- **A power saving for the mean modulus of the series.**  For every bounded multiplicative `f` and
every range of length at most `1`, at `σ = 1 + 1/log z`,

`∫_{|t| ≤ T} ‖∑_n f(n)n^{-σ-it}‖ dt ≤ C·(T log z)^{4/5}`,

below the trivial bound `≍ T log z`.  The exponent `4/5` is the balance point of the damped term
`(log z)e^{-δ²}T` against the window term `e^{4δ²}`; the factor `4` in the window exponent is the
square of the triangle-inequality factor `2`. -/
theorem integral_norm_tsum_twistedSummand_le_power_saving {f : ℕ → ℂ}
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) {z : ℕ} (hz : 3 ≤ z)
    (hzL : 5 * (charGapConst + 1) ≤ logLog z)
    {T : ℝ} (hT0 : 0 < T) (hT1 : T ≤ 1) (hLT : 1 ≤ Real.log (z : ℝ) * T) :
    (∫ t in Set.Icc (-T) T,
        ‖∑' n : ℕ, twistedSummand f
          (((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖)
      ≤ (64 * Real.exp (11 / 2) + 4 * Real.exp (9 / 2 + charGapConst))
          * (Real.log (z : ℝ) * T) ^ (4 / 5 : ℝ) := by
  have hz1 : (1 : ℝ) < ((z : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (1 : ℕ) < 3) hz
  have hlz : 0 < Real.log ((z : ℕ) : ℝ) := Real.log_pos hz1
  set L := Real.log ((z : ℕ) : ℝ) with hLdef
  have hLTle : L * T ≤ L := by
    calc L * T ≤ L * 1 := mul_le_mul_of_nonneg_left hT1 hlz.le
      _ = L := mul_one L
  have hL1 : (1 : ℝ) ≤ L := le_trans hLT hLTle
  have hLT0 : (0 : ℝ) < L * T := by positivity
  set x := Real.log (L * T) / 5 with hxdef
  have hx0 : (0 : ℝ) ≤ x := by
    have h := Real.log_nonneg hLT
    rw [hxdef]
    positivity
  have hδsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have hgap : 4 * Real.sqrt x ^ 2 + charGapConst + 1 ≤ logLog z := by
    rw [hδsq, hxdef]
    have hle : Real.log (L * T) ≤ Real.log L := Real.log_le_log hLT0 hLTle
    have hlogL : Real.log L = logLog z := by rw [logLog, hLdef]
    rw [hlogL] at hle
    linarith
  have hσ : (1 : ℝ) < 1 + 1 / L := by
    have : (0 : ℝ) < 1 / L := by positivity
    linarith
  have hmain := integral_norm_tsum_twistedSummand_le_explicit_window hf1 hmul hbdd hσ hz
    (Real.sqrt_nonneg x) hgap hT0.le hT1
  have hsub : (1 + 1 / L) - 1 = 1 / L := by ring
  rw [hsub, hδsq] at hmain
  exact le_trans hmain (window_balance_le hL1 hT0 hLT hxdef)

end

end RHTower.Sieve
end
