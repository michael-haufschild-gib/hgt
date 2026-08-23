import Mathlib

/-!
# The iterated boundary derivative of the Gamma integral

The Mellin transform of `(log x)^t e^{-x}` is the `t`-th derivative of `Γ` on the half-plane
`0 < Re s`: differentiating a Mellin transform multiplies the integrand by `log`, and the family
`(log x)^t e^{-x}` is closed under that operation while retaining the decay hypotheses at both ends
of `(0, ∞)`.
-/

open Filter MeasureTheory Set Asymptotics

open scoped Topology

namespace RHTower

noncomputable section

/-- The real `t`-fold log-weighted Gamma integrand `(log x)^t e^{-x}`. -/
def gammaLogIntegrandReal (t : ℕ) (x : ℝ) : ℝ := (Real.log x) ^ t * Real.exp (-x)

/-- The `t`-fold log-weighted Gamma integrand, complex-valued. -/
def gammaLogIntegrand (t : ℕ) (x : ℝ) : ℂ := ((gammaLogIntegrandReal t x : ℝ) : ℂ)

theorem gammaLogIntegrand_zero (x : ℝ) :
    gammaLogIntegrand 0 x = ((Real.exp (-x) : ℝ) : ℂ) := by
  rw [gammaLogIntegrand, gammaLogIntegrandReal, pow_zero, one_mul]

theorem log_smul_gammaLogIntegrand (t : ℕ) (x : ℝ) :
    Real.log x • gammaLogIntegrand t x = gammaLogIntegrand (t + 1) x := by
  rw [gammaLogIntegrand, gammaLogIntegrand, gammaLogIntegrandReal, gammaLogIntegrandReal,
    Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  rw [pow_succ]
  ring

theorem continuousOn_gammaLogIntegrand (t : ℕ) :
    ContinuousOn (gammaLogIntegrand t) (Ioi (0 : ℝ)) := by
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  refine ContinuousOn.mul ?_ ?_
  · exact (Real.continuousOn_log.mono fun x hx =>
      Set.mem_compl_singleton_iff.mpr (ne_of_gt hx)).pow t
  · exact (Real.continuous_exp.comp continuous_neg).continuousOn

theorem locallyIntegrableOn_gammaLogIntegrand (t : ℕ) :
    LocallyIntegrableOn (gammaLogIntegrand t) (Ioi (0 : ℝ)) :=
  (continuousOn_gammaLogIntegrand t).locallyIntegrableOn measurableSet_Ioi

theorem isBigO_log_pow_atTop (t : ℕ) :
    (fun x : ℝ => (Real.log x) ^ t) =O[atTop] (fun x : ℝ => x ^ (1 : ℝ)) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [pow_zero, Real.rpow_one, norm_one, one_mul, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    exact hx
  · have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    have hlt : (0 : ℝ) < 1 / (t : ℝ) := by positivity
    have h := ((isLittleO_log_rpow_atTop hlt).isBigO).pow t
    refine h.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hcollapse : (x ^ (1 / (t : ℝ))) ^ t = x ^ (1 : ℝ) := by
      rw [← Real.rpow_natCast (x ^ (1 / (t : ℝ))) t, ← Real.rpow_mul hx.le]
      congr 1
      field_simp
    rw [hcollapse, one_mul]

theorem isBigO_gammaLogIntegrandReal_atTop (t : ℕ) (a : ℝ) :
    gammaLogIntegrandReal t =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  have hexp : (fun x : ℝ => Real.exp (-x)) =O[atTop] (fun x : ℝ => x ^ (-a - 1)) := by
    have h := isLittleO_exp_neg_mul_rpow_atTop (a := 1) one_pos (-a - 1)
    have hcongr : (fun x : ℝ => Real.exp (-1 * x)) = fun x : ℝ => Real.exp (-x) := by
      funext x
      congr 1
      ring
    rw [hcongr] at h
    exact h.isBigO
  have hmul := (isBigO_log_pow_atTop t).mul hexp
  refine hmul.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hcollapse : x ^ (1 : ℝ) * x ^ (-a - 1) = x ^ (-a) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  rw [hcollapse, one_mul]

theorem isBigO_gammaLogIntegrand_atTop (t : ℕ) (a : ℝ) :
    gammaLogIntegrand t =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  refine IsBigO.trans (IsBigO.of_bound 1 ?_) (isBigO_gammaLogIntegrandReal_atTop t a)
  filter_upwards with x
  rw [gammaLogIntegrand, Complex.norm_real, one_mul]

theorem isBigO_gammaLogIntegrand_nhdsGT_zero (t : ℕ) {b : ℝ} (hb : 0 < b) :
    gammaLogIntegrand t =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-b)) := by
  induction t generalizing b with
  | zero =>
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (one_pos (α := ℝ)))]
      with x hx hx1
    have hx0 : (0 : ℝ) < x := hx
    have hexp : Real.exp (-x) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have hrpow : (1 : ℝ) ≤ x ^ (-b) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx0 hx1.le (by linarith)
    rw [gammaLogIntegrand_zero, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _), abs_of_nonneg (by linarith), one_mul]
    linarith
  | succ n ih =>
    have hhalf : (0 : ℝ) < b / 2 := by positivity
    have h := isBigO_rpow_zero_log_smul (a := b / 2) (b := b) (by linarith) (ih hhalf)
    refine h.congr_left fun x => ?_
    exact log_smul_gammaLogIntegrand n x

/-- Differentiating the Mellin transform of the log-weighted Gamma integrand raises the
logarithmic weight by one. -/
theorem hasDerivAt_mellin_gammaLogIntegrand (t : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (mellin (gammaLogIntegrand t)) (mellin (gammaLogIntegrand (t + 1)) s) s := by
  have h := mellin_hasDerivAt_of_isBigO_rpow (a := s.re + 1) (b := s.re / 2)
    (locallyIntegrableOn_gammaLogIntegrand t)
    (isBigO_gammaLogIntegrand_atTop t (s.re + 1)) (by linarith)
    (isBigO_gammaLogIntegrand_nhdsGT_zero t (by linarith : (0 : ℝ) < s.re / 2)) (by linarith)
  refine h.2.congr_deriv ?_
  congr 1
  funext x
  exact log_smul_gammaLogIntegrand t x

/-- **The iterated boundary derivative of `Γ` is the log-weighted Gamma integral.** -/
theorem iteratedDeriv_Gamma_eq_mellin (t : ℕ) {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv t Complex.Gamma s = mellin (gammaLogIntegrand t) s := by
  induction t generalizing s with
  | zero =>
    rw [iteratedDeriv_zero, Complex.Gamma_eq_integral hs, Complex.GammaIntegral_eq_mellin]
    congr 1
    funext x
    exact (gammaLogIntegrand_zero x).symm
  | succ n ih =>
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : iteratedDeriv n Complex.Gamma =ᶠ[nhds s] mellin (gammaLogIntegrand n) := by
      filter_upwards [hopen.mem_nhds hs] with z hz
      exact ih hz
    rw [iteratedDeriv_succ, hev.deriv_eq, (hasDerivAt_mellin_gammaLogIntegrand n hs).deriv]

theorem iteratedDeriv_Gamma_eq_integral (t : ℕ) {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv t Complex.Gamma s
      = ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * gammaLogIntegrand t x := by
  rw [iteratedDeriv_Gamma_eq_mellin t hs, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [smul_eq_mul]

/-- The friable log-moment kernel `G_t(j) = ∫_0^∞ x^j (log x)^t e^{-x} dx`. -/
def gammaLogMoment (t j : ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), x ^ j * gammaLogIntegrandReal t x

/-- **The log-moment kernel is the iterated boundary derivative of `Γ` at a positive integer.** -/
theorem iteratedDeriv_Gamma_natSucc (t j : ℕ) :
    iteratedDeriv t Complex.Gamma ((j : ℂ) + 1) = ((gammaLogMoment t j : ℝ) : ℂ) := by
  have hre : (0 : ℝ) < ((j : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity
  rw [iteratedDeriv_Gamma_eq_integral t hre, gammaLogMoment, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  have hpow : (x : ℂ) ^ (((j : ℂ) + 1) - 1) = ((x ^ j : ℝ) : ℂ) := by
    rw [show (((j : ℂ) + 1) - 1) = (j : ℂ) by ring, ← Complex.ofReal_natCast,
      ← Complex.ofReal_cpow hx0.le, Real.rpow_natCast]
  rw [hpow, gammaLogIntegrand, ← Complex.ofReal_mul]

end

end RHTower
