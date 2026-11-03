import GaloisForLFunctions.SelbergClass.CompletedEulerQuotientGrowth
import GaloisForLFunctions.SelbergClass.CriticalEulerQuotient
import GaloisForLFunctions.SelbergClass.GammaLogSlope
import GaloisForLFunctions.SelbergClass.DirichletVerticalDecay
import GaloisForLFunctions.HTGeometry.AddPolynomialInvariance

/-!
# Euler rigidity independent of the Gamma presentation

An Euler discrepancy absolutely convergent on the critical line gives a completed
quotient which is a polynomial exponential. Differentiating its logarithmic
derivative past the polynomial degree leaves polygamma terms decaying on
vertical lines. Almost periodicity then kills the Dirichlet coefficients.
-/

noncomputable section
open Complex Filter Set Topology

namespace GaloisForLFunctions.SelbergClass

private theorem logDeriv_cexp {f : ℂ → ℂ} {s : ℂ}
    (hf : DifferentiableAt ℂ f s) : logDeriv (fun z => exp (f z)) s = deriv f s := by
  rw [logDeriv_apply, hf.hasDerivAt.cexp.deriv]
  exact mul_div_cancel_left₀ _ (exp_ne_zero _)

private theorem eulerDiscrepancy_deriv (F G : RHTower.SelbergClass) {σ : ℝ}
    (hσ : σ < 1)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ)
    (P : Polynomial ℂ)
    (hP : ∀ s, completedEulerQuotient F G s = exp (P.eval s))
    {s : ℂ} (hs : 1 < s.re) :
    deriv (LSeries (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n)) s =
      P.derivative.eval s - gammaLogSlope F.gammaData s + gammaLogSlope G.gammaData s := by
  have hL := (LSeries_hasDerivAt (s := s) (hb.abscissaOfAbsConv_le.trans_lt
    (by exact_mod_cast (show σ < s.re by linarith)))).differentiableAt
  have hF := gammaFactor_analytic_ne_zero F.gammaData (show 0 < s.re by linarith)
  have hG := gammaFactor_analytic_ne_zero G.gammaData (show 0 < s.re by linarith)
  have hevent : (fun z => exp (P.eval z) * G.gammaData.gammaFactor z) =ᶠ[𝓝 s]
      (fun z => F.gammaData.gammaFactor z * eulerQuotient F G z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    have he := hP z
    rw [completedEulerQuotient_eq_right F G (by linarith), rightCompletedEulerQuotient] at he
    have hGz := (gammaFactor_analytic_ne_zero G.gammaData (show 0 < z.re by linarith)).2
    rw [← he]
    field_simp
  have hlog : logDeriv (fun z => exp (P.eval z) * G.gammaData.gammaFactor z) s =
      logDeriv (fun z => F.gammaData.gammaFactor z * eulerQuotient F G z) s := by
    simp only [logDeriv_apply, hevent.deriv_eq, hevent.eq_of_nhds]
  rw [logDeriv_mul (f := fun z : ℂ => exp (P.eval z)) (g := G.gammaData.gammaFactor)
      s (exp_ne_zero _) hG.2 (by fun_prop) hG.1.differentiableAt,
    logDeriv_mul (f := F.gammaData.gammaFactor) (g := eulerQuotient F G)
      s hF.2 (exp_ne_zero _) hF.1.differentiableAt hL.cexp,
    logDeriv_gammaFactor _ (by linarith), logDeriv_gammaFactor _ (by linarith),
    logDeriv_cexp (P.hasDerivAt s).differentiableAt, (P.hasDerivAt s).deriv] at hlog
  change P.derivative.eval s + gammaLogSlope G.gammaData s =
    gammaLogSlope F.gammaData s + logDeriv (fun z => exp
      (LSeries (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) z)) s at hlog
  rw [logDeriv_cexp hL] at hlog
  linear_combination -hlog

/-- The Euler logarithms agree whenever their discrepancy converges absolutely
on the critical line, for arbitrary Gamma presentations. -/
theorem eulerLogCoeff_eq_of_critical_discrepancy (F G : RHTower.SelbergClass)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) (1 / 2 : ℝ)) :
    F.eulerLogCoeff = G.eulerLogCoeff := by
  obtain ⟨P, hP⟩ := completedEulerQuotient_eq_exp_polynomial_of_analytic F G
    (completedEulerQuotient_analyticOnNhd_of_critical_discrepancy F G hb)
  let b : ℕ → ℂ := fun n => F.eulerLogCoeff n - G.eulerLogCoeff n
  let m : ℕ := P.derivative.natDegree
  have hjet {s : ℂ} (hs : 1 < s.re) :
      iteratedDeriv (m + 2) (LSeries b) s =
        -iteratedDeriv (m + 1) (gammaLogSlope F.gammaData) s +
          iteratedDeriv (m + 1) (gammaLogSlope G.gammaData) s := by
    have hevent : deriv (LSeries b) =ᶠ[𝓝 s]
        (fun z => P.derivative.eval z - gammaLogSlope F.gammaData z + gammaLogSlope G.gammaData z) := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
      exact eulerDiscrepancy_deriv F G (by norm_num) hb P hP hz
    have hpoly : ContDiffAt ℂ (m + 1 : ℕ) (fun z => P.derivative.eval z) s :=
      ((analyticOnNhd_univ_iff_differentiable.mpr
        (fun z => (P.derivative.hasDerivAt z).differentiableAt)) s (mem_univ s)).contDiffAt
    have hF := gammaLogSlope_contDiffAt F.gammaData (show 0 < s.re by linarith) (m + 1)
    have hG := gammaLogSlope_contDiffAt G.gammaData (show 0 < s.re by linarith) (m + 1)
    have he := hevent.iteratedDeriv_eq (m + 1)
    rw [← iteratedDeriv_succ', iteratedDeriv_fun_add (hpoly.sub hF) hG,
      iteratedDeriv_fun_sub hpoly hF, HTGeometry.iteratedDeriv_polynomial_eval,
      Polynomial.iterate_derivative_eq_zero (show P.derivative.natDegree < m + 1 by omega),
      Polynomial.eval_zero, zero_sub] at he
    exact he
  have habs : LSeries.abscissaOfAbsConv b < (2 : ℝ) :=
    hb.abscissaOfAbsConv_le.trans_lt (by norm_num)
  have hlim : Tendsto (fun t : ℝ => iteratedDeriv (m + 2) (LSeries b)
      ((2 : ℂ) + (t : ℂ) * I)) atTop (𝓝 0) := by
    have heq : (fun t : ℝ => iteratedDeriv (m + 2) (LSeries b) ((2 : ℂ) + (t : ℂ) * I)) =
        fun t : ℝ => -iteratedDeriv (m + 1) (gammaLogSlope F.gammaData) ((2 : ℂ) + (t : ℂ) * I) +
          iteratedDeriv (m + 1) (gammaLogSlope G.gammaData) ((2 : ℂ) + (t : ℂ) * I) := by
      funext t
      exact hjet (by simp)
    rw [heq]
    simpa only [ofReal_ofNat, neg_zero, zero_add] using
      (iteratedDeriv_gammaLogSlope_vertical_tendsto_zero F.gammaData m (by norm_num : (0 : ℝ) < 2)).neg.add
        (iteratedDeriv_gammaLogSlope_vertical_tendsto_zero G.gammaData m (by norm_num : (0 : ℝ) < 2))
  have hweighted : LSeriesSummable (LSeries.logMul^[m + 2] b) (2 : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using habs)
  have hseries : Tendsto (fun t : ℝ => LSeries (LSeries.logMul^[m + 2] b)
      ((2 : ℂ) + (t : ℂ) * I)) atTop (𝓝 0) := by
    have heq : (fun t : ℝ => LSeries (LSeries.logMul^[m + 2] b) ((2 : ℂ) + (t : ℂ) * I)) =
        fun t : ℝ => ((-1 : ℂ) ^ (m + 2))⁻¹ *
          iteratedDeriv (m + 2) (LSeries b) ((2 : ℂ) + (t : ℂ) * I) := by
      funext t
      rw [LSeries_iteratedDeriv _ (by simpa using habs),
        inv_mul_cancel_left₀ (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0))]
    rw [heq]
    simpa only [mul_zero] using hlim.const_mul (((-1 : ℂ) ^ (m + 2))⁻¹)
  have hcoeff := coeff_eq_zero_of_lSeries_vertical_tendsto_zero (σ := 2) hweighted
    (by simpa only [ofReal_ofNat] using hseries)
  have hone (H : RHTower.SelbergClass) : H.eulerLogCoeff 1 = 0 := by
    by_contra hne
    obtain ⟨p, k, hp, hk, he⟩ := H.eulerLogCoeff_primePower hne
    have hlt := pow_right_strictMono₀ hp.one_lt hk
    simp only [pow_zero, ← he, lt_self_iff_false] at hlt
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [ArithmeticFunction.map_zero]
  by_cases hn1 : n = 1
  · subst n
    rw [hone F, hone G]
  have hn2 : 1 < n := by omega
  have hlog : Complex.log n ≠ 0 := by
    rw [← ofReal_natCast, ← ofReal_log (Nat.cast_nonneg n)]
    exact ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hn2)).ne'
  have hiter : ∀ k : ℕ, (LSeries.logMul^[k] b) n = (Complex.log n) ^ k * b n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ]
        ring
  have hz := hcoeff n hn
  rw [hiter] at hz
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hlog))

/-- Subcritical absolute convergence implies critical absolute convergence. -/
theorem eulerLogCoeff_eq_of_subcritical_discrepancy (F G : RHTower.SelbergClass) {σ : ℝ}
    (hσ : σ < 1 / 2)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ) :
    F.eulerLogCoeff = G.eulerLogCoeff :=
  eulerLogCoeff_eq_of_critical_discrepancy F G
    (hb.of_re_le_re (by simpa only [ofReal_re] using hσ.le))

/-- Strong multiplicity one at the critical Euler abscissa, without fixing
any part of the Gamma presentation. -/
theorem coeff_eq_of_critical_discrepancy (F G : RHTower.SelbergClass)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) (1 / 2 : ℝ)) :
    F.coeff = G.coeff := by
  have heuler := eulerLogCoeff_eq_of_critical_discrepancy F G hb
  have hF : LSeries.abscissaOfAbsConv F.coeff < ⊤ :=
    (F.lSeriesSummable 2 (by norm_num)).abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
  have hG : LSeries.abscissaOfAbsConv G.coeff < ⊤ :=
    (G.lSeriesSummable 2 (by norm_num)).abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
  have hev : (fun x : ℝ => LSeries F.coeff x) =ᶠ[atTop] (fun x => LSeries G.coeff x) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [F.lSeries_eq_value _ hx, G.lSeries_eq_value _ hx, ← F.eulerProduct _ hx,
      ← G.eulerProduct _ hx, heuler]
  ext n
  by_cases hn : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero]
  · exact LSeries.eq_of_LSeries_eventually_eq hF hG hev hn

/-- Strong multiplicity one below the critical Euler abscissa. -/
theorem coeff_eq_of_subcritical_discrepancy (F G : RHTower.SelbergClass) {σ : ℝ}
    (hσ : σ < 1 / 2)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ) :
    F.coeff = G.coeff :=
  coeff_eq_of_critical_discrepancy F G
    (hb.of_re_le_re (by simpa only [ofReal_re] using hσ.le))

end GaloisForLFunctions.SelbergClass
