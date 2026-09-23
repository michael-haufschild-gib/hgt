import GaloisForLFunctions.RHTower.ZetaVerticalLineBound

/-!
# The logarithmic bound just left of the one-line

`ζ` obeys `|ζ(σ+it)| ≤ 8 log|t| + 39` on the whole strip `1 − 1/log|t| ≤ σ ≤ 2`, `|t| ≥ 8`, not
merely on `σ ≥ 1`.  The Euler–Maclaurin truncation at `N = ⌈|t|⌉` costs one factor `N^{1−σ}`, and
that factor is bounded by `exp 2` throughout the strip because `log N ≤ 2 log|t|` there.

Widening the region leftwards is what makes a Cauchy estimate on a disc of radius `1/log|t|`
available, so this is the growth input a derivative bound near the one-line consumes.
-/

namespace RHTower

open Complex

noncomputable section

theorem exp_two_le_eight : Real.exp 2 ≤ 8 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [h1, h0, hsq]

theorem two_le_log_of_eight_le {t : ℝ} (ht : 8 ≤ t) : 2 ≤ Real.log t := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have hmono : Real.log 8 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  linarith

/-- **The truncation factor is bounded on the strip.**  For `n ≤ t + 1` and
`σ ≥ 1 − 1/log t`, the factor `n^{1−σ}` never exceeds `exp 2`. -/
theorem rpow_one_sub_le_eight {t : ℝ} (ht : 8 ≤ t) {σ : ℝ}
    (hσ : 1 - 1 / Real.log t ≤ σ) {n : ℕ} (hn : 1 ≤ n) (hnt : (n : ℝ) ≤ t + 1) :
    (n : ℝ) ^ (1 - σ) ≤ 8 := by
  have hlogt : 2 ≤ Real.log t := two_le_log_of_eight_le ht
  have hlogt0 : (0 : ℝ) < Real.log t := by linarith
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  rcases le_or_gt (1 - σ) 0 with hle | hpos
  · have := Real.rpow_le_one_of_one_le_of_nonpos hnR hle
    linarith
  · have hexp : 1 - σ ≤ 1 / Real.log t := by linarith
    have hlogn0 : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
    have hsq : (n : ℝ) ≤ t ^ (2 : ℕ) := by
      have : t + 1 ≤ t ^ (2 : ℕ) := by nlinarith [ht]
      linarith
    have hlogn : Real.log (n : ℝ) ≤ 2 * Real.log t := by
      have h2 : Real.log (n : ℝ) ≤ Real.log (t ^ (2 : ℕ)) :=
        Real.log_le_log hn0 hsq
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith
    have hprod : Real.log (n : ℝ) * (1 - σ) ≤ 2 := by
      calc Real.log (n : ℝ) * (1 - σ) ≤ (2 * Real.log t) * (1 / Real.log t) :=
            mul_le_mul hlogn hexp (by linarith) (by positivity)
        _ = 2 := by field_simp
    rw [Real.rpow_def_of_pos hn0]
    calc Real.exp (Real.log (n : ℝ) * (1 - σ)) ≤ Real.exp 2 := Real.exp_le_exp.2 hprod
      _ ≤ 8 := exp_two_le_eight

/-- The Dirichlet polynomial on the strip. -/
theorem norm_dirichletPoly_le_near_one {s : ℂ} (ht : 8 ≤ |s.im|)
    (hσ : 1 - 1 / Real.log |s.im| ≤ s.re) {N : ℕ} (hN : (N : ℝ) ≤ |s.im| + 1) :
    ‖dirichletPoly N s‖ ≤ 8 * (1 + Real.log N) := by
  have hterm : ∀ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-s)‖ ≤ 8 * ((n : ℝ))⁻¹ := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hnt : (n : ℝ) ≤ |s.im| + 1 := le_trans (by exact_mod_cast hnN) hN
    rw [norm_natCast_cpow_zetaVerticalLineBound hn1]
    simp only [Complex.neg_re]
    have hsplit : (n : ℝ) ^ (-s.re) = (n : ℝ) ^ (1 - s.re) * ((n : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one (n : ℝ), ← Real.rpow_add hn0]
      congr 1
      ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (rpow_one_sub_le_eight ht hσ hn1 hnt) (by positivity)
  calc ‖dirichletPoly N s‖ ≤ ∑ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-s)‖ := by
        rw [dirichletPoly]
        exact norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, 8 * ((n : ℝ))⁻¹ := Finset.sum_le_sum hterm
    _ = 8 * ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := by rw [Finset.mul_sum]
    _ = 8 * (harmonic N : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        ring
    _ ≤ 8 * (1 + Real.log N) := by
        have := harmonic_le_one_add_log N
        linarith

/-- The Euler–Maclaurin pole term on the strip. -/
theorem norm_emPole_le_near_one {s : ℂ} (ht : 8 ≤ |s.im|)
    (hσ : 1 - 1 / Real.log |s.im| ≤ s.re) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : (N : ℝ) ≤ |s.im| + 1) :
    ‖emPole N s‖ ≤ 1 := by
  have hnum : ‖(N : ℂ) ^ (1 - s)‖ ≤ 8 := by
    rw [norm_natCast_cpow_zetaVerticalLineBound hN1]
    have hre : (1 - s).re = 1 - s.re := by simp
    rw [hre]
    exact rpow_one_sub_le_eight ht hσ hN1 hN
  have hden : (8 : ℝ) ≤ ‖s - 1‖ := by
    have habs : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    have him : (s - 1).im = s.im := by simp
    rw [him] at habs
    linarith
  rw [emPole, norm_div]
  rw [div_le_one (by linarith)]
  linarith

/-- **The logarithmic bound just left of the one-line.**  `|ζ(σ+it)| ≤ 8 log|t| + 39` for
`1 − 1/log|t| ≤ σ ≤ 2` and `|t| ≥ 8`, uniformly in `σ`. -/
theorem norm_riemannZeta_le_log_near_one {s : ℂ}
    (hσ1 : 1 - 1 / Real.log |s.im| ≤ s.re) (hσ2 : s.re ≤ 2) (ht : 8 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 8 * Real.log |s.im| + 39 := by
  have htpos : (0 : ℝ) < |s.im| := by linarith
  have hlogt : 2 ≤ Real.log |s.im| := two_le_log_of_eight_le ht
  have hσ0 : (1 : ℝ) / 2 ≤ s.re := by
    have hinv : 1 / Real.log |s.im| ≤ 1 / 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlogt
    linarith
  have hσpos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at ht
    simp only [Complex.one_im, abs_zero] at ht
    linarith
  set N : ℕ := ⌈|s.im|⌉₊ with hNdef
  have hNge : |s.im| ≤ (N : ℝ) := Nat.le_ceil _
  have hNlt : ((N : ℕ) : ℝ) < |s.im| + 1 := Nat.ceil_lt_add_one htpos.le
  have hNR : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by linarith
  have hN1 : 1 ≤ N := by exact_mod_cast hNR
  have hNle : ((N : ℕ) : ℝ) ≤ |s.im| + 1 := hNlt.le
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by linarith
  have hEM := zeta_sub_emCarrier_norm_le hN1 hσpos hs1
  -- the remainder
  have hrem : ‖s‖ * ((N : ℕ) : ℝ) ^ (-s.re) / s.re ≤ 20 := by
    have hsplit : ((N : ℕ) : ℝ) ^ (-s.re) = ((N : ℕ) : ℝ) ^ (1 - s.re) * (((N : ℕ) : ℝ))⁻¹ := by
      rw [← Real.rpow_neg_one ((N : ℕ) : ℝ), ← Real.rpow_add hN0]
      congr 1
      ring
    have hfac : ((N : ℕ) : ℝ) ^ (1 - s.re) ≤ 8 := rpow_one_sub_le_eight ht hσ1 hN1 hNle
    have hinvN : (((N : ℕ) : ℝ))⁻¹ ≤ (|s.im|)⁻¹ := inv_anti₀ htpos hNge
    have hpow : ((N : ℕ) : ℝ) ^ (-s.re) ≤ 8 * (|s.im|)⁻¹ := by
      rw [hsplit]
      have h1 : ((N : ℕ) : ℝ) ^ (1 - s.re) * (((N : ℕ) : ℝ))⁻¹
          ≤ 8 * (((N : ℕ) : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hfac (by positivity)
      have h2 : (8 : ℝ) * (((N : ℕ) : ℝ))⁻¹ ≤ 8 * (|s.im|)⁻¹ :=
        mul_le_mul_of_nonneg_left hinvN (by norm_num)
      linarith
    have hnorm : ‖s‖ ≤ 2 + |s.im| := by
      have hb := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_nonneg hσpos.le] at hb
      linarith
    have hs0 : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
    have hpow0 : (0 : ℝ) ≤ ((N : ℕ) : ℝ) ^ (-s.re) := Real.rpow_nonneg hN0.le _
    have hmul : ‖s‖ * ((N : ℕ) : ℝ) ^ (-s.re) ≤ (2 + |s.im|) * (8 * (|s.im|)⁻¹) :=
      mul_le_mul hnorm hpow hpow0 (by linarith)
    have hval : (2 + |s.im|) * (8 * (|s.im|)⁻¹) ≤ 10 := by
      have hinv : (|s.im|)⁻¹ ≤ (8 : ℝ)⁻¹ := inv_anti₀ (by norm_num) ht
      have hprod : (2 + |s.im|) * (8 * (|s.im|)⁻¹)
          = 16 * (|s.im|)⁻¹ + 8 * (|s.im| * (|s.im|)⁻¹) := by ring
      have hcancel : |s.im| * (|s.im|)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt htpos)
      rw [hprod, hcancel]
      norm_num at hinv ⊢
      linarith
    have hdiv : ‖s‖ * ((N : ℕ) : ℝ) ^ (-s.re) / s.re
        ≤ ‖s‖ * ((N : ℕ) : ℝ) ^ (-s.re) / (1 / 2) :=
      div_le_div_of_nonneg_left (mul_nonneg hs0 hpow0) (by norm_num) hσ0
    have hfin : ‖s‖ * ((N : ℕ) : ℝ) ^ (-s.re) / (1 / 2) ≤ 20 := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1 / 2)]
      linarith
    linarith
  -- the truncation point
  have hlogN : Real.log ((N : ℕ) : ℝ) ≤ Real.log |s.im| + 1 := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hle : ((N : ℕ) : ℝ) ≤ Real.exp 1 * |s.im| := by nlinarith [hNlt, htpos, he]
    calc Real.log ((N : ℕ) : ℝ) ≤ Real.log (Real.exp 1 * |s.im|) :=
          Real.log_le_log hN0 hle
      _ = 1 + Real.log |s.im| := by
          rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt htpos), Real.log_exp]
      _ = Real.log |s.im| + 1 := by ring
  have hcar : ‖emCarrier N s‖ ≤ 8 * Real.log |s.im| + 19 := by
    have hpoly := norm_dirichletPoly_le_near_one (s := s) ht hσ1 (N := N) hNle
    have hpole := norm_emPole_le_near_one (s := s) ht hσ1 hN1 hNle
    calc ‖emCarrier N s‖ ≤ ‖dirichletPoly N s‖ + ‖emPole N s‖ := by
          rw [emCarrier]
          exact norm_add_le _ _
      _ ≤ 8 * (1 + Real.log ((N : ℕ) : ℝ)) + 1 := by linarith
      _ ≤ 8 * Real.log |s.im| + 19 := by linarith
  have hfinal : ‖riemannZeta s‖
      ≤ ‖riemannZeta s - emCarrier N s‖ + ‖emCarrier N s‖ := by
    have := norm_add_le (riemannZeta s - emCarrier N s) (emCarrier N s)
    simpa using this
  linarith

end

end RHTower
