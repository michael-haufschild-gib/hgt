import GaloisForLFunctions.RHTower.CCMLogarithmicCuspBoundaryNoGo
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# CCM meromorphic-cusp boundary exclusion

Positive first-order thermal density determines the integral Laurent charge of
every meromorphic boundary germ in an arbitrary complex normed target. At rate
`q`, the exact law is `2 q n = 1`, where `n` is the meromorphic order. Thus
poles, nonzero constants, and locally-zero germs are excluded automatically.

For a periodic logarithmic cusp, the same law quantizes its period as
`h = 4π n`. Consequently no `2π`-periodic meromorphic cusp can carry a positive
finite thermal density, including the CCM four-unit density. No boundedness,
completeness, finite-dimensionality, or holomorphy-at-the-cusp premise occurs.
-/

open Complex Filter Asymptotics Function Set Topology WithTop
open scoped Real

noncomputable section

namespace RHTower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The positive real exponential arc approaches zero through the punctured
complex plane. -/
theorem tendsto_ofReal_exp_neg_mul_nhdsNE_zero
    {q : ℝ} (hq : 0 < q) :
    Tendsto (fun h : ℝ => (Real.exp (-q * h) : ℂ))
      atTop (𝓝[≠] 0) := by
  have hexpR : Tendsto (fun h : ℝ => Real.exp (-q * h)) atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_id.const_mul_atTop_of_neg (by linarith : -q < 0)
  rw [tendsto_nhdsWithin_iff]
  refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.comp hexpR,
    Eventually.of_forall fun h => ?_⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_eq_zero]
  exact (Real.exp_pos (-q * h)).ne'

/-- Exact exponential factorization along the physical arc for an arbitrary
integral Laurent charge. This extends analytic nonnegative-order
factorization to all meromorphic orders. -/
theorem normedAnalyticShiftMultiplier_eventually_factor_zpow
    {q : ℝ} (hq : 0 < q) {F G : ℂ → E} {n : ℤ}
    (hG : ContinuousAt G 0)
    (hfactor : F =ᶠ[𝓝[≠] 0] fun z => z ^ n • G z) :
    Tendsto (normedAnalyticShiftMultiplier q G) atTop (nhds ‖G 0‖) ∧
      normedAnalyticShiftMultiplier q F =ᶠ[atTop]
        fun h => Real.exp (-(q * (n : ℝ)) * h) *
          normedAnalyticShiftMultiplier q G h := by
  refine ⟨tendsto_normedAnalyticShiftMultiplier hq hG, ?_⟩
  filter_upwards [
    (tendsto_ofReal_exp_neg_mul_nhdsNE_zero hq).eventually hfactor] with h hh
  rw [normedAnalyticShiftMultiplier, normedAnalyticShiftMultiplier, hh,
    norm_smul, norm_zpow]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (-q * h))]
  rw [← Real.rpow_intCast, ← Real.exp_mul]
  congr 1
  ring_nf

/-- Positive finite thermal density excludes a locally-zero meromorphic germ.
Finiteness of Laurent order is a conclusion, not a premise. -/
theorem meromorphicOrderAt_ne_top_of_analyticRamifiedBoundaryDensity_pos
    {q : ℝ} (hq : 0 < q) {F : ℂ → E} {ell : ℝ} (hell : 0 < ell)
    (hdensity : Tendsto (analyticRamifiedBoundaryDensity q F) atTop (nhds ell)) :
    meromorphicOrderAt F 0 ≠ ⊤ := by
  intro htop
  have hzero : ∀ᶠ z : ℂ in 𝓝[≠] 0, F z = 0 :=
    meromorphicOrderAt_eq_top_iff.mp htop
  have hzeroMultiplier : normedAnalyticShiftMultiplier q F =ᶠ[atTop]
      fun _ => (0 : ℝ) := by
    filter_upwards [
      (tendsto_ofReal_exp_neg_mul_nhdsNE_zero hq).eventually hzero] with h hh
    rw [normedAnalyticShiftMultiplier, hh, norm_zero]
  have hzeroDensity : analyticRamifiedBoundaryDensity q F =ᶠ[atTop]
      fun _ => (0 : ℝ) := by
    filter_upwards [hzeroMultiplier] with h hh
    rw [analyticRamifiedBoundaryDensity, hh]
    simp
  have hzeroAtEll : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds ell) :=
    hdensity.congr' hzeroDensity
  have : (0 : ℝ) = ell := tendsto_nhds_unique tendsto_const_nhds hzeroAtEll
  linarith

/-- **Universal meromorphic charge-rate law.** In every complex normed target,
positive finite first-order thermal density forces a finite, strictly positive
integral Laurent order `n` and the exact relation `2 q n = 1`. -/
theorem meromorphic_boundaryDensity_chargeLaw
    {q : ℝ} (hq : 0 < q) {F : ℂ → E} (hF : MeromorphicAt F 0)
    {ell : ℝ} (hell : 0 < ell)
    (hdensity : Tendsto (analyticRamifiedBoundaryDensity q F) atTop (nhds ell)) :
    ∃ n : ℤ, meromorphicOrderAt F 0 = (n : WithTop ℤ) ∧
      0 < n ∧ 2 * q * (n : ℝ) = 1 := by
  have hfinite : meromorphicOrderAt F 0 ≠ ⊤ :=
    meromorphicOrderAt_ne_top_of_analyticRamifiedBoundaryDensity_pos
      hq hell hdensity
  lift meromorphicOrderAt F 0 to ℤ using hfinite with n hn
  have horder : meromorphicOrderAt F 0 = (n : WithTop ℤ) := hn.symm
  obtain ⟨G, hGan, hG0, hfactor⟩ :=
    (meromorphicOrderAt_eq_int_iff hF).mp horder
  have hfactor' : F =ᶠ[𝓝[≠] 0] fun z => z ^ n • G z := by
    filter_upwards [hfactor] with z hz
    simpa only [sub_zero] using hz
  obtain ⟨hGlim, hmult⟩ :=
    normedAnalyticShiftMultiplier_eventually_factor_zpow
      hq hGan.continuousAt hfactor'
  let U : ℝ → ℝ := fun h =>
    normedAnalyticShiftMultiplier q G h ^ 2 *
      (Real.exp (-h) / (1 - Real.exp (-Real.exp (-h))))
  have hU : Tendsto U atTop (nhds (‖G 0‖ ^ 2)) := by
    have hGsq : Tendsto
        (fun h => normedAnalyticShiftMultiplier q G h ^ 2)
        atTop (nhds (‖G 0‖ ^ 2)) := hGlim.pow 2
    simpa only [U, mul_one] using
      hGsq.mul tendsto_exp_neg_div_one_sub_exp_neg_exp_neg
  have hUpos : 0 < ‖G 0‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hG0)
  have hcongr : analyticRamifiedBoundaryDensity q F =ᶠ[atTop]
      fun h => Real.exp ((1 - 2 * q * (n : ℝ)) * h) * U h := by
    filter_upwards [hmult] with h hh
    rw [analyticRamifiedBoundaryDensity, hh]
    dsimp only [U]
    have hden : 1 - Real.exp (-Real.exp (-h)) ≠ 0 := by
      have hlt : Real.exp (-Real.exp (-h)) < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (neg_neg_of_pos (Real.exp_pos (-h)))
      linarith
    rw [mul_pow]
    field_simp [hden]
    have hexpeq :
        Real.exp (-(q * (n : ℝ)) * h) ^ 2 =
          Real.exp (-h) * Real.exp ((1 - 2 * q * (n : ℝ)) * h) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring_nf
    have hexpeq' :
        Real.exp (-(q * (n : ℝ) * h)) ^ 2 =
          Real.exp (-h) * Real.exp ((1 - 2 * q * (n : ℝ)) * h) := by
      convert hexpeq using 1
      all_goals ring_nf
    rw [hexpeq']
    ring_nf
  have hproduct : Tendsto
      (fun h => Real.exp ((1 - 2 * q * (n : ℝ)) * h) * U h)
      atTop (nhds ell) := hdensity.congr' hcongr
  have hk : 1 - 2 * q * (n : ℝ) = 0 :=
    exp_rate_eq_zero_of_tendsto_mul_pos hUpos hell hU hproduct
  have hcharge : 2 * q * (n : ℝ) = 1 := by linarith
  have hnpos : 0 < n := by
    have hnR : (0 : ℝ) < n := by nlinarith
    exact_mod_cast hnR
  exact ⟨n, rfl, hnpos, hcharge⟩

/-- **Meromorphic periodic-cusp law.** Positive finite density quantizes every
meromorphic logarithmic cusp period as `h = 4π n` for a positive integral
Laurent charge `n`. -/
theorem meromorphic_logarithmicCusp_period_chargeLaw
    {h : ℝ} (hh : 0 < h) {f : ℂ → E} (hf : Periodic f (h : ℂ))
    (hmero : MeromorphicAt
      (HTGeometry.normedPeriodicCuspFunction h f) 0)
    {ell : ℝ} (hell : 0 < ell)
    (hdensity : Tendsto (HTGeometry.logarithmicCuspBoundaryDensity f)
      atTop (nhds ell)) :
    ∃ n : ℤ,
      meromorphicOrderAt (HTGeometry.normedPeriodicCuspFunction h f) 0 =
        (n : WithTop ℤ) ∧
      0 < n ∧ h = 4 * Real.pi * (n : ℝ) := by
  have hq : 0 < 2 * Real.pi / h :=
    div_pos (mul_pos (by norm_num) Real.pi_pos) hh
  have hdensity' : Tendsto
      (analyticRamifiedBoundaryDensity (2 * Real.pi / h)
        (HTGeometry.normedPeriodicCuspFunction h f))
      atTop (nhds ell) := by
    simpa only [
      logarithmicCuspBoundaryDensity_eq_analyticRamifiedBoundaryDensity
        hh.ne' hf] using hdensity
  obtain ⟨n, horder, hnpos, hcharge⟩ :=
    meromorphic_boundaryDensity_chargeLaw hq hmero hell hdensity'
  have hperiod : h = 4 * Real.pi * (n : ℝ) := by
    field_simp [hh.ne'] at hcharge
    nlinarith [Real.pi_pos]
  exact ⟨n, horder, hnpos, hperiod⟩

/-- **One-loop meromorphic exclusion.** Period `2π` is incompatible with every
positive finite first-order thermal density, for arbitrary complex normed
targets and arbitrary finite Laurent singularities. -/
theorem not_tendsto_meromorphic_logarithmicCuspBoundaryDensity_pos_of_two_pi_periodic
    {f : ℂ → E} (hf : Periodic f ((2 * Real.pi : ℝ) : ℂ))
    (hmero : MeromorphicAt
      (HTGeometry.normedPeriodicCuspFunction (2 * Real.pi) f) 0)
    {ell : ℝ} (hell : 0 < ell) :
    ¬ Tendsto (HTGeometry.logarithmicCuspBoundaryDensity f)
      atTop (nhds ell) := by
  intro hdensity
  obtain ⟨n, _, _, hperiod⟩ :=
    meromorphic_logarithmicCusp_period_chargeLaw
      (by positivity : (0 : ℝ) < 2 * Real.pi) hf hmero hell hdensity
  have hreal : (1 : ℝ) = 2 * (n : ℝ) := by
    nlinarith [Real.pi_pos]
  have hint : (1 : ℤ) = 2 * n := by
    exact_mod_cast hreal
  omega

/-- Direct CCM connector: no one-loop meromorphic logarithmic cusp realizes
the four-unit boundary normalization. -/
theorem ccmFourUnit_not_two_pi_periodic_meromorphic_logarithmicCuspBoundary
    {f : ℂ → E} (hf : Periodic f ((2 * Real.pi : ℝ) : ℂ))
    (hmero : MeromorphicAt
      (HTGeometry.normedPeriodicCuspFunction (2 * Real.pi) f) 0) :
    ¬ Tendsto (HTGeometry.logarithmicCuspBoundaryDensity f)
      atTop (nhds 4) := by
  exact
    not_tendsto_meromorphic_logarithmicCuspBoundaryDensity_pos_of_two_pi_periodic
      hf hmero (by norm_num)

end RHTower
