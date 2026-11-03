import GaloisForLFunctions.RHTower.SelbergClass.GammaCriticalLine
import GaloisForLFunctions.RHTower.SelbergClass.Full
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Analysis.Complex.Liouville

/-!
# Rigidity below the critical Euler abscissa

An absolutely convergent Euler-log discrepancy gives a bounded holomorphic
quotient on a right half-plane. When that half-plane crosses the critical
line, the functional equations glue the quotient to its reflected function.
The resulting bounded entire function is constant.
-/

noncomputable section
open Complex Filter Set Topology

namespace GaloisForLFunctions.SelbergClass

open RHTower

/-- Exponentiated difference of the two canonical Euler logarithms. -/
def eulerQuotient (F G : RHTower.SelbergClass) (s : ℂ) : ℂ :=
  Complex.exp (LSeries (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) s)

private theorem analyticOnNhd_LSeries_right {b : ℕ → ℂ} {σ : ℝ}
    (hb : LSeriesSummable b σ) :
    AnalyticOnNhd ℂ (LSeries b) {s : ℂ | σ < s.re} := by
  have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const continuous_re
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro s hs
  apply (LSeries_hasDerivAt (f := b) ?_).differentiableAt.differentiableWithinAt
  exact hb.abscissaOfAbsConv_le.trans_lt (by exact_mod_cast hs)

theorem eulerQuotient_analyticOnNhd (F G : RHTower.SelbergClass) {σ : ℝ}
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ) :
    AnalyticOnNhd ℂ (eulerQuotient F G) {s : ℂ | σ < s.re} := by
  intro s hs
  exact ((analyticOnNhd_LSeries_right hb) s hs).cexp

/-- Absolute convergence supplies a uniform quotient bound, including the boundary line. -/
theorem norm_eulerQuotient_le (F G : RHTower.SelbergClass) {σ : ℝ}
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ)
    {s : ℂ} (hs : σ ≤ s.re) :
    ‖eulerQuotient F G s‖ ≤ Real.exp
      (∑' n, ‖LSeries.term (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ n‖) := by
  rw [eulerQuotient, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  apply (Complex.re_le_norm _).trans
  apply (norm_tsum_le_tsum_norm (hb.of_re_le_re hs).norm).trans
  exact Summable.tsum_le_tsum
    (LSeries.norm_term_le_of_re_le_re _ hs) (hb.of_re_le_re hs).norm hb.norm

/-- In the Euler half-plane the exponentiated discrepancy is the actual quotient. -/
theorem eulerQuotient_mul_value (F G : RHTower.SelbergClass) {s : ℂ}
    (hs : 1 < s.re) : eulerQuotient F G s * G s = F s := by
  change Complex.exp (LSeries ((F.eulerLogCoeff : ℕ → ℂ) -
    (G.eulerLogCoeff : ℕ → ℂ)) s) * G.continuation.value s = F.continuation.value s
  rw [LSeries_sub (F.eulerLogSummable s hs) (G.eulerLogSummable s hs),
    Complex.exp_sub, ← G.eulerProduct s hs, ← F.eulerProduct s hs,
    div_mul_cancel₀ _ (Complex.exp_ne_zero _)]

/-- The quotient identity continues through zeros of the denominator; its proof
uses the entire pole regularizations, rather than division by their values. -/
theorem eulerQuotient_mul_value_of_summable (F G : RHTower.SelbergClass) {σ : ℝ}
    (hσ : σ < 1)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ)
    {s : ℂ} (hs : σ < s.re) (hs1 : s ≠ 1) :
    eulerQuotient F G s * G s = F s := by
  let f (z : ℂ) := F.continuation.regularized z * (z - 1) ^ G.continuation.poleOrder
  let g (z : ℂ) := eulerQuotient F G z * G.continuation.regularized z *
    (z - 1) ^ F.continuation.poleOrder
  have hf : AnalyticOnNhd ℂ f {z : ℂ | σ < z.re} := fun z _ =>
    (F.continuation.regularized.analytic z (mem_univ z)).mul (by fun_prop)
  have hg : AnalyticOnNhd ℂ g {z : ℂ | σ < z.re} := fun z hz =>
    ((eulerQuotient_analyticOnNhd F G hb z hz).mul
      (G.continuation.regularized.analytic z (mem_univ z))).mul (by fun_prop)
  have hloc : f =ᶠ[𝓝 (2 : ℂ)] g := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    have hz1 : z - 1 ≠ 0 := by
      intro heq
      have : z = 1 := sub_eq_zero.mp heq
      subst z
      norm_num at hz
    have hv := (eulerQuotient_mul_value F G hz).symm
    change F.continuation.regularized z / (z - 1) ^ F.continuation.poleOrder =
      eulerQuotient F G z *
        (G.continuation.regularized z / (z - 1) ^ G.continuation.poleOrder) at hv
    rw [← mul_div_assoc] at hv
    exact (div_eq_div_iff (pow_ne_zero _ hz1) (pow_ne_zero _ hz1)).mp hv
  have hcross := hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_halfSpace_re_gt σ).isPreconnected
    (show (2 : ℂ) ∈ {z : ℂ | σ < z.re} by change σ < (2 : ℝ); linarith) hloc hs
  change eulerQuotient F G s *
    (G.continuation.regularized s / (s - 1) ^ G.continuation.poleOrder) =
      F.continuation.regularized s / (s - 1) ^ F.continuation.poleOrder
  rw [← mul_div_assoc]
  exact ((div_eq_div_iff (pow_ne_zero _ (sub_ne_zero.mpr hs1))
    (pow_ne_zero _ (sub_ne_zero.mpr hs1))).mpr hcross).symm

/-- Gamma factors are holomorphic and nonzero in the open right half-plane. -/
theorem gammaFactor_analytic_ne_zero (D : SelbergGammaData) {s : ℂ}
    (hs : 0 < s.re) : AnalyticAt ℂ D.gammaFactor s ∧ D.gammaFactor s ≠ 0 := by
  have harg (j : Fin D.rank) : 0 < ((D.lambda j : ℂ) * s + D.mu j).re := by
    simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact add_pos_of_pos_of_nonneg (mul_pos (D.lambda_pos j) hs) (D.mu_re_nonneg j)
  have hnot (j : Fin D.rank) (m : ℕ) : (D.lambda j : ℂ) * s + D.mu j ≠ -(m : ℂ) := by
    intro heq
    have hp := harg j
    rw [heq] at hp
    simp only [neg_re, natCast_re] at hp
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have han (j : Fin D.rank) :
      AnalyticAt ℂ (fun z : ℂ => Gamma ((D.lambda j : ℂ) * z + D.mu j)) s := by
    have hm : MeromorphicAt (fun z : ℂ => Gamma ((D.lambda j : ℂ) * z + D.mu j)) s := by
      simpa only [Function.comp_def] using
        (Meromorphic.Gamma ((D.lambda j : ℂ) * s + D.mu j)).comp_analyticAt
          (x := s) (g := fun z : ℂ => (D.lambda j : ℂ) * z + D.mu j) (by fun_prop)
    apply hm.analyticAt
    simpa only [Function.comp_def] using
      ContinuousAt.comp (g := Gamma) (f := fun z : ℂ => (D.lambda j : ℂ) * z + D.mu j)
        (x := s) (continuousAt_Gamma _ (hnot j)) (by fun_prop)
  have hQ : Differentiable ℂ (fun z : ℂ => (D.Q : ℂ) ^ z) :=
    differentiable_id.const_cpow (.inl (ofReal_ne_zero.mpr D.Q_pos.ne'))
  constructor
  · exact ((analyticOnNhd_univ_iff_differentiable.mpr hQ) s (mem_univ s)).mul
      (Finset.univ.analyticAt_prod fun j _ => han j)
  · simp only [SelbergGammaData.gammaFactor, Pi.mul_apply, Finset.prod_apply]
    apply mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (.inl (ofReal_ne_zero.mpr D.Q_pos.ne')))
    exact Finset.prod_ne_zero_iff.mpr fun j _ => Complex.Gamma_ne_zero_of_re_pos (harg j)

private theorem value_eventually_ne_zero (G : RHTower.SelbergClass) (s : ℂ) (hs : s ≠ 1) :
    ∀ᶠ z in 𝓝[≠] s, G z ≠ 0 := by
  have htwo : G.continuation.regularized (2 : ℂ) ≠ 0 := by
    intro hzero
    have he := G.eulerProduct 2 (by norm_num)
    rw [SelbergAnalyticContinuation.value, hzero, zero_div] at he
    exact Complex.exp_ne_zero _ he
  have hn : ¬ ∃ᶠ z in 𝓝[≠] s, G.continuation.regularized z = 0 := by
    intro hz
    exact htwo (G.continuation.regularized.analytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (mem_univ s) hz (mem_univ (2 : ℂ)))
  have hn' : ∀ᶠ z in 𝓝[≠] s, G.continuation.regularized z ≠ 0 := by
    simpa only [not_frequently] using hn
  have hone : ∀ᶠ z in 𝓝[≠] s, z ≠ 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hs)
  filter_upwards [hn', hone] with z hz hz1
  exact div_ne_zero hz (pow_ne_zero _ (sub_ne_zero.mpr hz1))

/-- A holomorphic quotient of completed values inherits their functional equations,
including at common zeros by analytic continuation. -/
theorem completedQuotient_reflection (F G : RHTower.SelbergClass) {σ : ℝ}
    {R : ℂ → ℂ}
    (hσ0 : 0 ≤ σ)
    (hR : AnalyticOnNhd ℂ R {s : ℂ | σ < s.re})
    (hquot : ∀ z : ℂ, σ < z.re → z ≠ 1 →
      R z * (G.gammaData.gammaFactor z * G z) = F.gammaData.gammaFactor z * F z)
    {s : ℂ} (hs : σ < s.re) (hs' : s.re < 1 - σ) :
    R s = F.gammaData.rootNumber / G.gammaData.rootNumber * star (R (1 - star s)) := by
  have hroot : G.gammaData.rootNumber ≠ 0 := by
    intro hzero
    have := G.gammaData.rootNumber_norm
    simp only [hzero, norm_zero] at this
    norm_num at this
  have hrefl (z : ℂ) : (1 - star z).re = 1 - z.re := by simp
  have hpoint (z : ℂ) (hz : σ < z.re) (hz' : z.re < 1 - σ) (hne : G z ≠ 0) :
      R z = F.gammaData.rootNumber / G.gammaData.rootNumber * star (R (1 - star z)) := by
    have hz0 : 0 < z.re := lt_of_le_of_lt hσ0 hz
    have hr0 : 0 < (1 - star z).re := by rw [hrefl]; linarith
    have hzr : σ < (1 - star z).re := by rw [hrefl]; linarith
    have hz1 : z ≠ 1 := by intro heq; rw [heq] at hz'; norm_num at hz'; linarith
    have hr1 : 1 - star z ≠ 1 := by
      intro heq
      have he := congrArg Complex.re heq
      rw [hrefl] at he
      simp only [one_re] at he
      linarith
    have hcomp (T : RHTower.SelbergClass) (w : ℂ) (hw : 0 < w.re) (hw1 : w ≠ 1) :
        AnalyticAt ℂ (selbergCompletedValue T.gammaData T.continuation) w :=
      (gammaFactor_analytic_ne_zero T.gammaData hw).1.mul
        (T.continuation.analyticAt_value_of_ne_one hw1)
    have eF := F.toExtendedSelbergClass.completedFE_eq_of_analytic_pair
      (hcomp F z hz0 hz1) (hcomp F (1 - star z) hr0 hr1)
    have eG := G.toExtendedSelbergClass.completedFE_eq_of_analytic_pair
      (hcomp G z hz0 hz1) (hcomp G (1 - star z) hr0 hr1)
    change F.gammaData.gammaFactor z * F z = F.gammaData.rootNumber *
      star (F.gammaData.gammaFactor (1 - star z) * F (1 - star z)) at eF
    change G.gammaData.gammaFactor z * G z = G.gammaData.rootNumber *
      star (G.gammaData.gammaFactor (1 - star z) * G (1 - star z)) at eG
    rw [← hquot z hz hz1, ← hquot (1 - star z) hzr hr1] at eF
    simp only [star_mul] at eF eG
    have hcancel : (R z * G.gammaData.rootNumber -
        F.gammaData.rootNumber * star (R (1 - star z))) *
        (G.gammaData.gammaFactor z * G z) = 0 := by
      linear_combination G.gammaData.rootNumber * eF -
        F.gammaData.rootNumber * star (R (1 - star z)) * eG
    have heq := sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_right
      (mul_ne_zero (gammaFactor_analytic_ne_zero G.gammaData hz0).2 hne))
    apply (mul_right_cancel₀ hroot)
    calc R z * G.gammaData.rootNumber = _ := heq
      _ = (F.gammaData.rootNumber / G.gammaData.rootNumber *
          star (R (1 - star z))) * G.gammaData.rootNumber := by
            field_simp
  have hs1 : s ≠ 1 := by intro heq; rw [heq] at hs'; norm_num at hs'; linarith
  have hU : IsOpen {z : ℂ | σ < z.re ∧ z.re < 1 - σ} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hevent : R =ᶠ[𝓝[≠] s]
      (fun z => F.gammaData.rootNumber / G.gammaData.rootNumber *
        star (R (1 - star z))) := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (hU.mem_nhds ⟨hs, hs'⟩),
      value_eventually_ne_zero G s hs1] with z hz hne
    exact hpoint z hz.1 hz.2 hne
  have hr : σ < (1 - star s).re := by rw [hrefl]; linarith
  exact ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hR s hs).continuousAt
    (analyticAt_const.mul (analyticAt_selbergConjugateReflection (hR _ hr))).continuousAt).mp
      hevent).eq_of_nhds

/-- The actual functional equations reflect the holomorphic Euler quotient on
the overlap strip, including the common zeros of the two functions. -/
theorem eulerQuotient_reflection (F G : RHTower.SelbergClass) {σ : ℝ}
    (hσ0 : 0 ≤ σ)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ)
    (hgamma : F.gammaData.gammaFactor = G.gammaData.gammaFactor)
    {s : ℂ} (hs : σ < s.re) (hs' : s.re < 1 - σ) :
    eulerQuotient F G s = F.gammaData.rootNumber / G.gammaData.rootNumber *
      star (eulerQuotient F G (1 - star s)) := by
  apply completedQuotient_reflection F G hσ0 (eulerQuotient_analyticOnNhd F G hb) _ hs hs'
  intro z hz hz1
  rw [hgamma, mul_left_comm, eulerQuotient_mul_value_of_summable F G (by linarith) hb hz hz1]

private theorem bounded_reflection_constant {R : ℂ → ℂ} {σ C : ℝ} {ε : ℂ}
    (hσ : σ < 1 / 2) (hε : ‖ε‖ = 1)
    (hR : AnalyticOnNhd ℂ R {s : ℂ | σ < s.re})
    (hbound : ∀ s : ℂ, 1 / 2 ≤ s.re → ‖R s‖ ≤ C)
    (hreflection : ∀ s : ℂ, σ < s.re → s.re < 1 - σ →
      R s = ε * star (R (1 - star s))) :
    ∃ c : ℂ, ∀ s : ℂ, σ < s.re → R s = c := by
  let E (s : ℂ) := if 1 / 2 ≤ s.re then R s else ε * star (R (1 - star s))
  have hright : ∀ s : ℂ, σ < s.re → E s = R s := by
    intro s hs
    dsimp only [E]
    split_ifs with h
    · rfl
    · exact (hreflection s hs (by linarith)).symm
  have hleft : ∀ s : ℂ, s.re < 1 - σ → E s = ε * star (R (1 - star s)) := by
    intro s hs
    dsimp only [E]
    split_ifs with h
    · exact hreflection s (by linarith) hs
    · rfl
  have hdiff : Differentiable ℂ E := by
    intro s
    by_cases hs : σ < s.re
    · have hopen : IsOpen {z : ℂ | σ < z.re} := isOpen_lt continuous_const continuous_re
      apply (hR s hs).differentiableAt.congr_of_eventuallyEq
      filter_upwards [hopen.mem_nhds hs] with z hz
      exact hright z hz
    · have hs' : s.re < 1 - σ := by linarith
      have href : σ < (1 - star s).re := by simpa using (by linarith : σ < 1 - s.re)
      have ha : AnalyticAt ℂ (fun z => ε * star (R (1 - star z))) s :=
        analyticAt_const.mul (analyticAt_selbergConjugateReflection (hR _ href))
      have hopen : IsOpen {z : ℂ | z.re < 1 - σ} := isOpen_lt continuous_re continuous_const
      apply ha.differentiableAt.congr_of_eventuallyEq
      filter_upwards [hopen.mem_nhds hs'] with z hz
      exact hleft z hz
  have hb : ∀ s : ℂ, ‖E s‖ ≤ C := by
    intro s
    dsimp only [E]
    split_ifs with hs
    · exact hbound s hs
    · rw [norm_mul, hε, norm_star, one_mul]
      exact hbound _ (by simpa using (by linarith : 1 / 2 ≤ 1 - s.re))
  obtain ⟨c, hc⟩ := hdiff.exists_const_forall_eq_of_bounded
    (isBounded_iff_forall_norm_le.mpr ⟨C, by rintro _ ⟨s, rfl⟩; exact hb s⟩)
  exact ⟨c, fun s hs => (hright s hs).symm.trans (hc s)⟩

/-- With the same gamma factor, a discrepancy converging strictly to the left
of the critical line cannot change any normalized Dirichlet coefficient. -/
theorem coeff_eq_of_subcritical_euler_discrepancy (F G : RHTower.SelbergClass)
    (hgamma : F.gammaData.gammaFactor = G.gammaData.gammaFactor) {σ : ℝ}
    (hσ : σ < 1 / 2)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ) :
    F.coeff = G.coeff := by
  let τ := max σ 0
  have hτ : τ < 1 / 2 := max_lt hσ (by norm_num)
  have hτ0 : 0 ≤ τ := le_max_right σ 0
  have hbτ : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) τ :=
    hb.of_re_le_re (by simpa only [ofReal_re] using le_max_left σ 0)
  have hphase : ‖F.gammaData.rootNumber / G.gammaData.rootNumber‖ = 1 := by
    rw [norm_div, F.gammaData.rootNumber_norm, G.gammaData.rootNumber_norm, div_one]
  obtain ⟨c, hc⟩ := bounded_reflection_constant hτ hphase
    (eulerQuotient_analyticOnNhd F G hbτ)
    (fun s hs => norm_eulerQuotient_le F G hbτ (hτ.le.trans hs))
    (fun s hs hs' => eulerQuotient_reflection F G hτ0 hbτ hgamma hs hs')
  have hF : LSeries.abscissaOfAbsConv F.coeff < ⊤ :=
    (F.lSeriesSummable 2 (by norm_num)).abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
  have hcG : LSeries.abscissaOfAbsConv (c • (G.coeff : ℕ → ℂ)) < ⊤ :=
    ((G.lSeriesSummable 2 (by norm_num)).smul c).abscissaOfAbsConv_le.trans_lt
      (EReal.coe_lt_top _)
  have hev : (fun x : ℝ => LSeries F.coeff x) =ᶠ[atTop]
      (fun x => LSeries (c • (G.coeff : ℕ → ℂ)) x) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [LSeries_smul, F.lSeries_eq_value _ hx, G.lSeries_eq_value _ hx]
    have hmul := eulerQuotient_mul_value F G (s := (x : ℂ)) hx
    rw [hc _ (by simpa only [ofReal_re] using (by linarith : τ < x))] at hmul
    exact hmul.symm
  have hcoeff (n : ℕ) (hn : n ≠ 0) : F.coeff n = c * G.coeff n :=
    LSeries.eq_of_LSeries_eventually_eq hF hcG hev hn
  have hc1 : c = 1 := by
    simpa only [F.coeff_one, G.coeff_one, mul_one] using (hcoeff 1 one_ne_zero).symm
  ext n
  by_cases hn : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero]
  · simpa only [hc1, one_mul] using hcoeff n hn

/-- The archimedean Gamma product, excluding the positive exponential parameter. -/
def archGammaFactor (D : SelbergGammaData) (s : ℂ) : ℂ :=
  ∏ j, Gamma ((D.lambda j : ℂ) * s + D.mu j)

theorem gammaFactor_eq_exp_mul_archGammaFactor (D : SelbergGammaData) (s : ℂ) :
    D.gammaFactor s = Complex.exp ((Real.log D.Q : ℂ) * s) * archGammaFactor D s := by
  simp only [SelbergGammaData.gammaFactor, Pi.mul_apply, Finset.prod_apply,
    archGammaFactor, Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr D.Q_pos.ne'),
    ← Complex.ofReal_log D.Q_pos.le]

private theorem gammaFactor_eq_conductor_mul (F G : RHTower.SelbergClass)
    (hgamma : archGammaFactor F.gammaData = archGammaFactor G.gammaData) (s : ℂ) :
    F.gammaData.gammaFactor s =
      Complex.exp (((Real.log F.gammaData.Q - Real.log G.gammaData.Q : ℝ) : ℂ) * s) *
        G.gammaData.gammaFactor s := by
  rw [gammaFactor_eq_exp_mul_archGammaFactor, gammaFactor_eq_exp_mul_archGammaFactor,
    hgamma, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Normalized Dirichlet coefficients fix the Euler quotient at real infinity. -/
theorem eulerQuotient_tendsto_atTop (F G : RHTower.SelbergClass) :
    Tendsto (fun x : ℝ => eulerQuotient F G x) atTop (𝓝 1) := by
  have hlim (H : RHTower.SelbergClass) :
      Tendsto (fun x : ℝ => LSeries H.coeff x) atTop (𝓝 1) := by
    simpa only [H.coeff_one] using LSeries.tendsto_atTop
      ((H.lSeriesSummable 2 (by norm_num)).abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _))
  have hlimdiv := (hlim F).div (hlim G) (one_ne_zero : (1 : ℂ) ≠ 0)
  simp only [div_one] at hlimdiv
  apply hlimdiv.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  change LSeries F.coeff (x : ℂ) / LSeries G.coeff (x : ℂ) = eulerQuotient F G x
  rw [F.lSeries_eq_value _ hx, G.lSeries_eq_value _ hx]
  have hne : G (x : ℂ) ≠ 0 := by
    change G.continuation.value (x : ℂ) ≠ 0
    rw [← G.eulerProduct (x : ℂ) hx]
    exact Complex.exp_ne_zero _
  exact (div_eq_iff hne).mpr (eulerQuotient_mul_value F G hx).symm

private theorem rigidity_of_ordered_conductors (F G : RHTower.SelbergClass)
    (hgamma : archGammaFactor F.gammaData = archGammaFactor G.gammaData)
    (hQ : F.gammaData.Q ≤ G.gammaData.Q) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ) :
    F.coeff = G.coeff ∧ F.gammaData.Q = G.gammaData.Q ∧
      F.gammaData.rootNumber = G.gammaData.rootNumber := by
  let d : ℝ := Real.log F.gammaData.Q - Real.log G.gammaData.Q
  let T (s : ℂ) := Complex.exp ((d : ℂ) * s) * eulerQuotient F G s
  have hd : d ≤ 0 := sub_nonpos.mpr (Real.log_le_log F.gammaData.Q_pos hQ)
  have hT : AnalyticOnNhd ℂ T {s : ℂ | σ < s.re} := by
    intro s hs
    exact (show AnalyticAt ℂ (fun z : ℂ => Complex.exp ((d : ℂ) * z)) s by fun_prop).mul
      (eulerQuotient_analyticOnNhd F G hb s hs)
  have href (s : ℂ) (hs : σ < s.re) (hs' : s.re < 1 - σ) :
      T s = F.gammaData.rootNumber / G.gammaData.rootNumber * star (T (1 - star s)) := by
    apply completedQuotient_reflection F G hσ0 hT _ hs hs'
    intro z hz hz1
    rw [gammaFactor_eq_conductor_mul F G hgamma]
    have hv := eulerQuotient_mul_value_of_summable F G (by linarith) hb hz hz1
    dsimp only [T, d]
    rw [← hv]
    ring
  have hphase : ‖F.gammaData.rootNumber / G.gammaData.rootNumber‖ = 1 := by
    rw [norm_div, F.gammaData.rootNumber_norm, G.gammaData.rootNumber_norm, div_one]
  obtain ⟨c, hc⟩ := bounded_reflection_constant hσ hphase hT
    (fun s hs => show ‖T s‖ ≤ _ from by
      have hexp : ‖Complex.exp ((d : ℂ) * s)‖ ≤ 1 := by
        rw [Complex.norm_exp]
        apply Real.exp_le_one_iff.mpr
        simpa only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] using
          mul_nonpos_of_nonpos_of_nonneg hd (by linarith : 0 ≤ s.re)
      exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right hexp (norm_nonneg _)).trans
        (by simpa only [one_mul] using norm_eulerQuotient_le F G hb (hσ.le.trans hs)))) href
  have hcne : c ≠ 0 := by
    rw [← hc 2 (by change σ < (2 : ℝ); linarith)]
    exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  have hd0 : d = 0 := by
    by_contra hdn
    have hdn' : d < 0 := lt_of_le_of_ne hd hdn
    have he : Tendsto (fun x : ℝ => Real.exp (d * x)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hdn')
    have hR : Tendsto (fun x : ℝ => ‖eulerQuotient F G x‖) atTop (𝓝 1) := by
      simpa only [norm_one] using (eulerQuotient_tendsto_atTop F G).norm
    have hzero : Tendsto (fun _ : ℝ => ‖c‖) atTop (𝓝 0) := by
      have hprod := he.mul hR
      simp only [zero_mul] at hprod
      apply hprod.congr'
      filter_upwards [eventually_gt_atTop σ] with x hx
      rw [← hc x (by simpa only [ofReal_re] using hx)]
      simp only [T, norm_mul, Complex.norm_exp, mul_re, ofReal_re, ofReal_im,
        mul_zero, sub_zero]
    exact hcne (norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hzero))
  have hQeq : F.gammaData.Q = G.gammaData.Q :=
    Real.log_injOn_pos F.gammaData.Q_pos G.gammaData.Q_pos (sub_eq_zero.mp hd0)
  have hfull : F.gammaData.gammaFactor = G.gammaData.gammaFactor := by
    funext s
    rw [gammaFactor_eq_conductor_mul F G hgamma]
    change Complex.exp ((d : ℂ) * s) * G.gammaData.gammaFactor s = _
    simp only [hd0, ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  have hcoeff := coeff_eq_of_subcritical_euler_discrepancy F G hfull hσ hb
  have hc1 : c = 1 := by
    have hlim : Tendsto (fun _ : ℝ => c) atTop (𝓝 1) := by
      apply (eulerQuotient_tendsto_atTop F G).congr'
      filter_upwards [eventually_gt_atTop σ] with x hx
      have heq := hc x (by simpa only [ofReal_re] using hx)
      simpa only [T, hd0, ofReal_zero, zero_mul, Complex.exp_zero, one_mul] using heq
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  have hroot : F.gammaData.rootNumber = G.gammaData.rootNumber := by
    have heq := href (1 / 2) (by norm_num; linarith) (by norm_num; linarith)
    rw [hc _ (by norm_num; linarith), hc _ (by norm_num; linarith), hc1] at heq
    simp only [star_one, mul_one] at heq
    apply (div_eq_one_iff_eq ?_).mp heq.symm
    intro hzero
    have hn := G.gammaData.rootNumber_norm
    simp only [hzero, norm_zero] at hn
    norm_num at hn
  exact ⟨hcoeff, hQeq, hroot⟩

/-- A subcritical Euler discrepancy cannot change coefficients, the positive
exponential parameter, or the root number when the bare Gamma products agree. -/
theorem rigidity_of_subcritical_euler_discrepancy (F G : RHTower.SelbergClass)
    (hgamma : archGammaFactor F.gammaData = archGammaFactor G.gammaData) {σ : ℝ}
    (hσ : σ < 1 / 2)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ) :
    F.coeff = G.coeff ∧ F.gammaData.Q = G.gammaData.Q ∧
      F.gammaData.rootNumber = G.gammaData.rootNumber := by
  let τ := max σ 0
  have hτ : τ < 1 / 2 := max_lt hσ (by norm_num)
  have hτ0 : 0 ≤ τ := le_max_right σ 0
  have hbτ : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) τ :=
    hb.of_re_le_re (by simpa only [ofReal_re] using le_max_left σ 0)
  rcases le_total F.gammaData.Q G.gammaData.Q with hQ | hQ
  · exact rigidity_of_ordered_conductors F G hgamma hQ hτ0 hτ hbτ
  · have hb' : LSeriesSummable (fun n => G.eulerLogCoeff n - F.eulerLogCoeff n) τ := by
      have heq : (fun n => G.eulerLogCoeff n - F.eulerLogCoeff n) =
          -(fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) := by
        funext n
        exact (neg_sub _ _).symm
      rw [heq]
      exact hbτ.neg
    obtain ⟨hcoeff, hQeq, hroot⟩ :=
      rigidity_of_ordered_conductors G F hgamma.symm hQ hτ0 hτ hb'
    exact ⟨hcoeff.symm, hQeq.symm, hroot.symm⟩

end GaloisForLFunctions.SelbergClass
