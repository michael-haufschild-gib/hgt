import GaloisForLFunctions.RHTower.Sieve.MertensFirstExpRate
import GaloisForLFunctions.RHTower.MertensPrimeMeanReader
import GaloisForLFunctions.RHTower.MertensPrimeWindowWeakConvergence
import GaloisForLFunctions.RHTower.MarcinkiewiczPrimeTailBanach
import GaloisForLFunctions.RHTower.PrimeRpowAbelSummation
import GaloisForLFunctions.HTGeometry.HarmonicLogEquidistribution
import GaloisForLFunctions.HTGeometry.CircleEmbeddingBiLipschitz

open Complex Filter Topology MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

namespace RHTower

def logarithmicPhase (xi t : ℝ) : ℂ :=
  Complex.exp (((xi * Real.log t : ℝ) : ℂ) * Complex.I)

theorem logarithmicPhase_eq_exp (xi t : ℝ) :
    logarithmicPhase xi t =
      Complex.exp (((xi * Real.log t : ℝ) : ℂ) * Complex.I) := by
  rfl

theorem norm_logarithmicPhase (xi t : ℝ) : ‖logarithmicPhase xi t‖ = 1 := by
  rw [logarithmicPhase_eq_exp, Complex.norm_exp]
  simp

theorem hasDerivAt_logarithmicPhase {xi t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (logarithmicPhase xi)
      ((((xi / t : ℝ) : ℂ) * Complex.I) * logarithmicPhase xi t) t := by
  have hinner : HasDerivAt (fun y : ℝ => xi * Real.log y) (xi / t) t := by
    simpa [div_eq_mul_inv] using (Real.hasDerivAt_log ht).const_mul xi
  have harg : HasDerivAt
      (fun y : ℝ => (((xi * Real.log y : ℝ) : ℂ) * Complex.I))
      (((xi / t : ℝ) : ℂ) * Complex.I) t :=
    hinner.ofReal_comp.mul_const Complex.I
  have hexp := (Complex.hasDerivAt_exp
    (((xi * Real.log t : ℝ) : ℂ) * Complex.I)).scomp t harg
  change HasDerivAt
    (fun y : ℝ => Complex.exp (((xi * Real.log y : ℝ) : ℂ) * Complex.I))
    ((((xi / t : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((xi * Real.log t : ℝ) : ℂ) * Complex.I)) t
  simpa [logarithmicPhase, Function.comp_def, mul_comm] using! hexp

def logarithmicPhaseOverId (xi t : ℝ) : ℂ :=
  logarithmicPhase xi t / (t : ℂ)

theorem norm_logarithmicPhaseOverId {xi t : ℝ} (ht : 0 < t) :
    ‖logarithmicPhaseOverId xi t‖ = 1 / t := by
  rw [logarithmicPhaseOverId, norm_div, norm_logarithmicPhase,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]

theorem hasDerivAt_logarithmicPhaseOverId {xi t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (logarithmicPhaseOverId xi)
      (((((xi / t : ℝ) : ℂ) * Complex.I) * logarithmicPhase xi t * (t : ℂ) -
        logarithmicPhase xi t) / (t : ℂ) ^ 2) t := by
  have hphase := hasDerivAt_logarithmicPhase (xi := xi) ht
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 t :=
    (hasDerivAt_id (𝕜 := ℝ) (x := t)).ofReal_comp
  have hdiv := hphase.div hid (by exact_mod_cast ht)
  simpa only [logarithmicPhaseOverId, Pi.div_apply, mul_one] using! hdiv

theorem deriv_logarithmicPhaseOverId {xi t : ℝ} (ht : t ≠ 0) :
    deriv (logarithmicPhaseOverId xi) t =
      (((xi : ℂ) * Complex.I - 1) * logarithmicPhase xi t) / (t : ℂ) ^ 2 :=
  by
    rw [(hasDerivAt_logarithmicPhaseOverId (xi := xi) ht).deriv,
      Complex.ofReal_div]
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    field_simp [htC]

theorem norm_deriv_logarithmicPhaseOverId {xi t : ℝ} (ht : t ≠ 0) :
    ‖deriv (logarithmicPhaseOverId xi) t‖ =
      ‖(xi : ℂ) * Complex.I - 1‖ / |t| ^ 2 := by
  rw [deriv_logarithmicPhaseOverId ht, norm_div, norm_mul,
    norm_logarithmicPhase, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs]
  ring

theorem continuousOn_deriv_logarithmicPhaseOverId (xi : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (deriv (logarithmicPhaseOverId xi)) (Icc a b) := by
  refine ContinuousOn.congr ?_ (fun t ht => deriv_logarithmicPhaseOverId (ne_of_gt (ha.trans_le ht.1)))
  have hlog : ContinuousOn Real.log (Icc a b) :=
    Real.continuousOn_log.mono (fun t ht => ne_of_gt (ha.trans_le ht.1))
  have harg : ContinuousOn (fun t : ℝ => xi * Real.log t) (Icc a b) :=
    continuousOn_const.mul hlog
  have hphase : ContinuousOn (logarithmicPhase xi) (Icc a b) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn harg).mul continuousOn_const)
  have hnum : ContinuousOn
      (fun t : ℝ => ((xi : ℂ) * Complex.I - 1) * logarithmicPhase xi t) (Icc a b) :=
    continuousOn_const.mul hphase
  have hden : ContinuousOn (fun t : ℝ => (t : ℂ) ^ 2) (Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn continuousOn_id).pow 2
  exact hnum.div hden (fun t ht => pow_ne_zero 2 (by exact_mod_cast ne_of_gt (ha.trans_le ht.1)))

theorem integrableOn_deriv_logarithmicPhaseOverId (xi : ℝ) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (deriv (logarithmicPhaseOverId xi)) (Icc a b) :=
  (continuousOn_deriv_logarithmicPhaseOverId xi ha).integrableOn_Icc

def logarithmicPrimePhaseSumIoc (xi : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.Ioc 2 N,
    if k.Prime then ((Real.log k / k : ℝ) : ℂ) * logarithmicPhase xi k else 0

theorem sum_complexPrimeLogWeight_eq_theta (t : ℝ) :
    ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (primeLogWeight k : ℂ) =
      (Chebyshev.theta t : ℂ) := by
  rw [← Complex.ofReal_sum, sum_primeLogWeight_eq_theta]

theorem logarithmicPhaseOverId_mul_primeLogWeight {xi : ℝ} {k : ℕ} (hk : 2 < k) :
    logarithmicPhaseOverId xi k * (primeLogWeight k : ℂ) =
      if k.Prime then ((Real.log k / k : ℝ) : ℂ) * logarithmicPhase xi k else 0 := by
  rw [primeLogWeight]
  split_ifs with hp
  · have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hk)
    rw [logarithmicPhaseOverId]
    push_cast
    field_simp [hk0]
  · simp

theorem logarithmicPrimePhaseSumIoc_eq_thetaAbel {xi : ℝ} {N : ℕ} (hN : 2 ≤ N) :
    logarithmicPrimePhaseSumIoc xi N =
      logarithmicPhaseOverId xi N * (Chebyshev.theta N : ℂ) -
        logarithmicPhaseOverId xi 2 * (Chebyshev.theta 2 : ℂ) -
        ∫ t in Ioc (2 : ℝ) N,
          deriv (logarithmicPhaseOverId xi) t * (Chebyshev.theta t : ℂ) := by
  have hdiff : ∀ t ∈ Icc (2 : ℝ) (N : ℝ),
      DifferentiableAt ℝ (logarithmicPhaseOverId xi) t := by
    intro t ht
    exact (hasDerivAt_logarithmicPhaseOverId
      (xi := xi) (ne_of_gt (lt_of_lt_of_le two_pos ht.1))).differentiableAt
  have hab := sum_mul_eq_sub_sub_integral_mul
    (fun k : ℕ => (primeLogWeight k : ℂ))
    (f := logarithmicPhaseOverId xi) (a := (2 : ℝ)) (b := (N : ℝ))
    (by norm_num) (by exact_mod_cast hN) hdiff
    (integrableOn_deriv_logarithmicPhaseOverId xi (by norm_num))
  simp only [sum_complexPrimeLogWeight_eq_theta] at hab
  rw [Nat.floor_natCast, show ⌊(2 : ℝ)⌋₊ = 2 by norm_num] at hab
  rw [logarithmicPrimePhaseSumIoc, ← hab]
  exact Finset.sum_congr rfl fun k hk => by
    have hk2 : 2 < k := by
      simpa using (Finset.mem_Ioc.mp hk).1
    exact (logarithmicPhaseOverId_mul_primeLogWeight hk2).symm

def logarithmicPhaseContinuousMain (xi : ℝ) (N : ℕ) : ℂ :=
  logarithmicPhaseOverId xi N * (N : ℂ) -
    logarithmicPhaseOverId xi 2 * (2 : ℂ) -
    ∫ t in Ioc (2 : ℝ) N,
      deriv (logarithmicPhaseOverId xi) t * (t : ℂ)

theorem logarithmicPhaseContinuousMain_eq_integral {xi : ℝ} {N : ℕ} (hN : 2 ≤ N) :
    logarithmicPhaseContinuousMain xi N =
      ∫ t in Ioc (2 : ℝ) N, logarithmicPhaseOverId xi t := by
  have hu : ∀ t ∈ uIcc (2 : ℝ) (N : ℝ),
      HasDerivAt (logarithmicPhaseOverId xi)
        (deriv (logarithmicPhaseOverId xi) t) t := by
    intro t ht
    rw [uIcc_of_le (by exact_mod_cast hN)] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le two_pos ht.1)
    have h := hasDerivAt_logarithmicPhaseOverId (xi := xi) ht0
    rw [h.deriv]
    exact h
  have hv : ∀ t ∈ uIcc (2 : ℝ) (N : ℝ),
      HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
    intro t _
    exact (hasDerivAt_id (𝕜 := ℝ) (x := t)).ofReal_comp
  have huInt : IntervalIntegrable (deriv (logarithmicPhaseOverId xi)) volume 2 N := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le (by exact_mod_cast hN)]
    exact integrableOn_deriv_logarithmicPhaseOverId xi (by norm_num)
  have hvInt : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume 2 N :=
    intervalIntegrable_const
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv huInt hvInt
  have hle : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rw [intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_of_le hle] at hibp
  rw [logarithmicPhaseContinuousMain]
  simpa [mul_one] using hibp.symm

theorem hasDerivAt_logarithmicPhase_div_frequency {xi t : ℝ}
    (hxi : xi ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun y : ℝ => logarithmicPhase xi y / ((xi : ℂ) * Complex.I))
      (logarithmicPhaseOverId xi t) t := by
  have h := (hasDerivAt_logarithmicPhase (xi := xi) ht).div_const
    ((xi : ℂ) * Complex.I)
  have hxiC : (xi : ℂ) ≠ 0 := by exact_mod_cast hxi
  have hden : (xi : ℂ) * Complex.I ≠ 0 := mul_ne_zero hxiC Complex.I_ne_zero
  apply h.congr_deriv
  rw [logarithmicPhaseOverId, Complex.ofReal_div]
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  field_simp [hden, htC]

theorem integral_logarithmicPhaseOverId_eq {xi : ℝ} (hxi : xi ≠ 0)
    {N : ℕ} (hN : 2 ≤ N) :
    (∫ t in Ioc (2 : ℝ) N, logarithmicPhaseOverId xi t) =
      logarithmicPhase xi N / ((xi : ℂ) * Complex.I) -
        logarithmicPhase xi 2 / ((xi : ℂ) * Complex.I) := by
  have hle : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hderiv : ∀ t ∈ uIcc (2 : ℝ) (N : ℝ),
      HasDerivAt (fun y : ℝ => logarithmicPhase xi y / ((xi : ℂ) * Complex.I))
        (logarithmicPhaseOverId xi t) t := by
    intro t ht
    rw [uIcc_of_le hle] at ht
    exact hasDerivAt_logarithmicPhase_div_frequency hxi
      (ne_of_gt (lt_of_lt_of_le two_pos ht.1))
  have hcont : ContinuousOn (logarithmicPhaseOverId xi) (Icc (2 : ℝ) N) := by
    have hlog : ContinuousOn Real.log (Icc (2 : ℝ) N) :=
      Real.continuousOn_log.mono
        (fun t ht => ne_of_gt (lt_of_lt_of_le two_pos ht.1))
    have harg : ContinuousOn (fun t : ℝ => xi * Real.log t) (Icc (2 : ℝ) N) :=
      continuousOn_const.mul hlog
    have hphase : ContinuousOn (logarithmicPhase xi) (Icc (2 : ℝ) N) :=
      Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn harg).mul continuousOn_const)
    exact hphase.div
      (Complex.continuous_ofReal.comp_continuousOn continuousOn_id)
      (fun t ht => by exact_mod_cast ne_of_gt (lt_of_lt_of_le two_pos ht.1))
  have hint : IntervalIntegrable (logarithmicPhaseOverId xi) volume 2 N := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le hle]
    exact hcont.integrableOn_Icc
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_of_le hle] at hftc
  exact hftc

theorem norm_integral_logarithmicPhaseOverId_le {xi : ℝ} (hxi : xi ≠ 0)
    {N : ℕ} (hN : 2 ≤ N) :
    ‖∫ t in Ioc (2 : ℝ) N, logarithmicPhaseOverId xi t‖ ≤ 2 / |xi| := by
  rw [integral_logarithmicPhaseOverId_eq hxi hN]
  calc
    ‖logarithmicPhase xi N / ((xi : ℂ) * Complex.I) -
        logarithmicPhase xi 2 / ((xi : ℂ) * Complex.I)‖
        ≤ ‖logarithmicPhase xi N / ((xi : ℂ) * Complex.I)‖ +
          ‖logarithmicPhase xi 2 / ((xi : ℂ) * Complex.I)‖ := norm_sub_le _ _
    _ = 2 / |xi| := by
      rw [norm_div, norm_div, norm_logarithmicPhase, norm_logarithmicPhase,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]
      ring

theorem integrableOn_thetaErrorDensity_Ioi_two_unconditional :
    IntegrableOn Sieve.thetaErrorDensity (Ioi (2 : ℝ)) := by
  obtain ⟨c, hc0, hbigO⟩ := Sieve.chebyshevTheta_sub_id_isBigO
  rw [Asymptotics.isBigO_iff] at hbigO
  obtain ⟨K, hKev⟩ := hbigO
  rw [eventually_atTop] at hKev
  obtain ⟨T0, hT0⟩ := hKev
  set T : ℝ := max T0 2 with hTdef
  have hT2 : (2 : ℝ) ≤ T := le_max_right _ _
  have hbd : ∀ t : ℝ, T < t →
      |Chebyshev.theta t - t| ≤
        |K| * t * Real.exp (-c * Real.sqrt (Real.log t)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans (by linarith) ht
    have h := hT0 t (le_trans (le_max_left _ _) ht.le)
    have hshape : ‖t * Real.exp (-c * Real.sqrt (Real.log t))‖ =
        t * Real.exp (-c * Real.sqrt (Real.log t)) := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [Pi.sub_apply, id_eq, Real.norm_eq_abs, hshape] at h
    have hE : (0 : ℝ) < Real.exp (-c * Real.sqrt (Real.log t)) := Real.exp_pos _
    nlinarith [le_abs_self K, h, mul_pos ht0 hE]
  exact Sieve.integrableOn_thetaErrorDensity_Ioi hc0 hT2 hbd

def logarithmicPhaseThetaErrorIntegrand (xi t : ℝ) : ℂ :=
  deriv (logarithmicPhaseOverId xi) t *
    ((Chebyshev.theta t - t : ℝ) : ℂ)

theorem logarithmicPhaseThetaErrorIntegrand_eq {xi t : ℝ} (ht : 0 < t) :
    logarithmicPhaseThetaErrorIntegrand xi t =
      (((xi : ℂ) * Complex.I - 1) * logarithmicPhase xi t) *
        (Sieve.thetaErrorDensity t : ℂ) := by
  rw [logarithmicPhaseThetaErrorIntegrand,
    deriv_logarithmicPhaseOverId (ne_of_gt ht), Sieve.thetaErrorDensity]
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  push_cast
  field_simp [htC]

theorem integrableOn_logarithmicPhaseThetaErrorIntegrand (xi : ℝ) :
    IntegrableOn (logarithmicPhaseThetaErrorIntegrand xi) (Ioi (2 : ℝ)) := by
  let mu : Measure ℝ := volume.restrict (Ioi (2 : ℝ))
  have htheta : Integrable (fun t : ℝ => (Sieve.thetaErrorDensity t : ℂ)) mu :=
    integrableOn_thetaErrorDensity_Ioi_two_unconditional.ofReal
  let factor : ℝ → ℂ := fun t =>
    ((xi : ℂ) * Complex.I - 1) * logarithmicPhase xi t
  have hfactorContinuous : ContinuousOn factor (Ioi (2 : ℝ)) := by
    have hlog : ContinuousOn Real.log (Ioi (2 : ℝ)) :=
      Real.continuousOn_log.mono
        (fun t ht => ne_of_gt (lt_trans two_pos ht))
    have harg : ContinuousOn (fun t : ℝ => xi * Real.log t) (Ioi (2 : ℝ)) :=
      continuousOn_const.mul hlog
    have hphase : ContinuousOn (logarithmicPhase xi) (Ioi (2 : ℝ)) :=
      Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn harg).mul continuousOn_const)
    exact continuousOn_const.mul hphase
  have hfactorMeas : AEStronglyMeasurable factor mu :=
    hfactorContinuous.aestronglyMeasurable measurableSet_Ioi
  have hfactorBound : ∀ᵐ t : ℝ ∂mu,
      ‖factor t‖ ≤ ‖(xi : ℂ) * Complex.I - 1‖ := by
    filter_upwards with t
    rw [norm_mul, norm_logarithmicPhase, mul_one]
  have hprod : Integrable (fun t => factor t * (Sieve.thetaErrorDensity t : ℂ)) mu :=
    htheta.bdd_mul hfactorMeas hfactorBound
  refine hprod.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (logarithmicPhaseThetaErrorIntegrand_eq
    (lt_trans two_pos ht)).symm

def logarithmicPhaseThetaError (xi : ℝ) (N : ℕ) : ℂ :=
  logarithmicPhaseOverId xi N *
      ((Chebyshev.theta N - N : ℝ) : ℂ) -
    logarithmicPhaseOverId xi 2 *
      ((Chebyshev.theta 2 - 2 : ℝ) : ℂ) -
    ∫ t in Ioc (2 : ℝ) N, logarithmicPhaseThetaErrorIntegrand xi t

theorem logarithmicPrimePhaseSumIoc_eq_main_add_error {xi : ℝ} {N : ℕ}
    (hN : 2 ≤ N) :
    logarithmicPrimePhaseSumIoc xi N =
      logarithmicPhaseContinuousMain xi N + logarithmicPhaseThetaError xi N := by
  have hle : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hderivCont : ContinuousOn (deriv (logarithmicPhaseOverId xi))
      (Icc (2 : ℝ) N) :=
    continuousOn_deriv_logarithmicPhaseOverId xi (by norm_num)
  have hidCont : ContinuousOn (fun t : ℝ => (t : ℂ)) (Icc (2 : ℝ) N) :=
    Complex.continuous_ofReal.comp_continuousOn continuousOn_id
  have hmainInt : IntegrableOn
      (fun t : ℝ => deriv (logarithmicPhaseOverId xi) t * (t : ℂ))
      (Ioc (2 : ℝ) N) :=
    (hderivCont.mul hidCont).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have herrInt : IntegrableOn (logarithmicPhaseThetaErrorIntegrand xi)
      (Ioc (2 : ℝ) N) :=
    (integrableOn_logarithmicPhaseThetaErrorIntegrand xi).mono_set
      (fun _ ht => ht.1)
  have hsplit :
      (∫ t in Ioc (2 : ℝ) N,
        deriv (logarithmicPhaseOverId xi) t * (Chebyshev.theta t : ℂ)) =
      (∫ t in Ioc (2 : ℝ) N,
        deriv (logarithmicPhaseOverId xi) t * (t : ℂ)) +
      ∫ t in Ioc (2 : ℝ) N, logarithmicPhaseThetaErrorIntegrand xi t := by
    rw [← MeasureTheory.integral_add hmainInt herrInt]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [logarithmicPhaseThetaErrorIntegrand]
    push_cast
    ring
  rw [logarithmicPrimePhaseSumIoc_eq_thetaAbel hN,
    logarithmicPhaseContinuousMain, logarithmicPhaseThetaError, hsplit]
  push_cast
  ring

def logarithmicPhaseThetaErrorIntegralNorm (xi : ℝ) : ℝ :=
  ∫ t in Ioi (2 : ℝ), ‖logarithmicPhaseThetaErrorIntegrand xi t‖

theorem logarithmicPhaseThetaErrorIntegralNorm_nonneg (xi : ℝ) :
    0 ≤ logarithmicPhaseThetaErrorIntegralNorm xi := by
  exact integral_nonneg (fun _ => norm_nonneg _)

theorem norm_integral_logarithmicPhaseThetaErrorIntegrand_le (xi : ℝ) (N : ℕ) :
    ‖∫ t in Ioc (2 : ℝ) N, logarithmicPhaseThetaErrorIntegrand xi t‖ ≤
      logarithmicPhaseThetaErrorIntegralNorm xi := by
  have hfull := integrableOn_logarithmicPhaseThetaErrorIntegrand xi
  calc
    ‖∫ t in Ioc (2 : ℝ) N, logarithmicPhaseThetaErrorIntegrand xi t‖
        ≤ ∫ t in Ioc (2 : ℝ) N, ‖logarithmicPhaseThetaErrorIntegrand xi t‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (2 : ℝ), ‖logarithmicPhaseThetaErrorIntegrand xi t‖ := by
      apply setIntegral_mono_set hfull.norm
      · exact ae_of_all _ (fun _ => norm_nonneg _)
      · exact Eventually.of_forall (fun _ ht => ht.1)
    _ = logarithmicPhaseThetaErrorIntegralNorm xi := rfl

theorem exists_eventually_abs_chebyshevTheta_sub_div_nat_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      |Chebyshev.theta N - N| / N ≤ B := by
  obtain ⟨c, hc, hbigO⟩ := Sieve.chebyshevTheta_sub_id_isBigO
  rw [Asymptotics.isBigO_iff] at hbigO
  obtain ⟨K, hKev⟩ := hbigO
  have hNat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hKev
  refine ⟨|K|, abs_nonneg K, ?_⟩
  filter_upwards [hNat, eventually_ge_atTop (2 : ℕ)] with N hN hN2
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hexp : Real.exp (-c * Real.sqrt (Real.log (N : ℝ))) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hsqrt : 0 ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
    nlinarith
  have hshape :
      ‖(N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N : ℝ)))‖ =
        (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N : ℝ))) := by
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos hNr (Real.exp_pos _))]
  rw [Pi.sub_apply, id_eq, Real.norm_eq_abs, hshape] at hN
  rw [div_le_iff₀ hNr]
  calc
    |Chebyshev.theta (N : ℝ) - (N : ℝ)|
        ≤ K * ((N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N : ℝ)))) := hN
    _ ≤ |K| * ((N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N : ℝ)))) := by
      exact mul_le_mul_of_nonneg_right (le_abs_self K)
        (mul_nonneg hNr.le (Real.exp_pos _).le)
    _ ≤ |K| * (N : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right hNr.le hexp) (abs_nonneg K)
    _ = |K| * (N : ℝ) := rfl

theorem exists_eventually_norm_logarithmicPhaseThetaError_le (xi : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ‖logarithmicPhaseThetaError xi N‖ ≤ C := by
  obtain ⟨B, hB, hboundary⟩ :=
    exists_eventually_abs_chebyshevTheta_sub_div_nat_le
  let C : ℝ := B +
    ‖logarithmicPhaseOverId xi 2 *
      ((Chebyshev.theta 2 - 2 : ℝ) : ℂ)‖ +
    logarithmicPhaseThetaErrorIntegralNorm xi
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (add_nonneg hB (norm_nonneg _))
      (logarithmicPhaseThetaErrorIntegralNorm_nonneg xi)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hboundary, eventually_ge_atTop (2 : ℕ)] with N hN hN2
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN2)
  have hfirst :
      ‖logarithmicPhaseOverId xi N *
        ((Chebyshev.theta N - N : ℝ) : ℂ)‖ ≤ B := by
    rw [norm_mul, norm_logarithmicPhaseOverId hNr,
      Complex.norm_real, Real.norm_eq_abs, one_div, inv_mul_eq_div]
    exact hN
  have hint := norm_integral_logarithmicPhaseThetaErrorIntegrand_le xi N
  rw [logarithmicPhaseThetaError]
  calc
    ‖logarithmicPhaseOverId xi N * ((Chebyshev.theta N - N : ℝ) : ℂ) -
        logarithmicPhaseOverId xi 2 * ((Chebyshev.theta 2 - 2 : ℝ) : ℂ) -
        ∫ t in Ioc (2 : ℝ) N, logarithmicPhaseThetaErrorIntegrand xi t‖
        ≤ ‖logarithmicPhaseOverId xi N * ((Chebyshev.theta N - N : ℝ) : ℂ)‖ +
          ‖logarithmicPhaseOverId xi 2 * ((Chebyshev.theta 2 - 2 : ℝ) : ℂ)‖ +
          ‖∫ t in Ioc (2 : ℝ) N, logarithmicPhaseThetaErrorIntegrand xi t‖ := by
      calc
        ‖_ - _ - _‖ ≤ ‖_ - _‖ + ‖_‖ := norm_sub_le _ _
        _ ≤ (‖_‖ + ‖_‖) + ‖_‖ := add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ C := by
      dsimp [C]
      linarith

theorem exists_eventually_norm_logarithmicPrimePhaseSumIoc_le
    {xi : ℝ} (hxi : xi ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ‖logarithmicPrimePhaseSumIoc xi N‖ ≤ C := by
  obtain ⟨E, hE, hErr⟩ :=
    exists_eventually_norm_logarithmicPhaseThetaError_le xi
  let C : ℝ := 2 / |xi| + E
  have hxiAbs : 0 < |xi| := abs_pos.mpr hxi
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hErr, eventually_ge_atTop (2 : ℕ)] with N hErrN hN
  rw [logarithmicPrimePhaseSumIoc_eq_main_add_error hN]
  calc
    ‖logarithmicPhaseContinuousMain xi N + logarithmicPhaseThetaError xi N‖
        ≤ ‖logarithmicPhaseContinuousMain xi N‖ +
          ‖logarithmicPhaseThetaError xi N‖ := norm_add_le _ _
    _ ≤ 2 / |xi| + E := by
      gcongr
      rw [logarithmicPhaseContinuousMain_eq_integral hN]
      exact norm_integral_logarithmicPhaseOverId_le hxi hN
    _ = C := rfl

theorem tendsto_logarithmicPrimePhaseSumIoc_div_log
    {xi : ℝ} (hxi : xi ≠ 0) :
    Tendsto (fun N : ℕ =>
      logarithmicPrimePhaseSumIoc xi N / (Real.log N : ℂ))
      atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_eventually_norm_logarithmicPrimePhaseSumIoc_le hxi
  have hnorm : Tendsto (fun N : ℕ =>
      ‖logarithmicPrimePhaseSumIoc xi N / (Real.log N : ℂ)‖)
      atTop (nhds 0) := by
    refine squeeze_zero'
      (f := fun N : ℕ =>
        ‖logarithmicPrimePhaseSumIoc xi N / (Real.log N : ℂ)‖)
      (g := fun N : ℕ => C / Real.log N) ?_ ?_ (tendsto_const_div_log_nat C)
    · exact Eventually.of_forall (fun _ => norm_nonneg _)
    · filter_upwards [hbound, eventually_ge_atTop (2 : ℕ)] with N hN hN2
      have hlog : 0 < Real.log (N : ℝ) :=
        Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN2)
      calc
        ‖logarithmicPrimePhaseSumIoc xi N / (Real.log N : ℂ)‖ =
            ‖logarithmicPrimePhaseSumIoc xi N‖ / Real.log N := by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
        _ ≤ C / Real.log N := div_le_div_of_nonneg_right hN hlog.le
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

def mertensPrimeWeightSumIocTwo (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc 2 N, mertensPrimeWeight k

theorem mertensPrimeWeightSum_eq_two_add_Ioc {N : ℕ} (hN : 2 ≤ N) :
    mertensPrimeWeightSum N = Real.log 2 / 2 + mertensPrimeWeightSumIocTwo N := by
  rw [mertensPrimeWeightSum, mertensPrimeWeightSumIocTwo,
    show Finset.Icc 0 N = Finset.Icc 0 2 ∪ Finset.Ioc 2 N by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      omega,
    Finset.sum_union (by
      rw [Finset.disjoint_left]
      intro n hn hm
      simp only [Finset.mem_Icc] at hn
      simp only [Finset.mem_Ioc] at hm
      omega)]
  rw [show Finset.Icc 0 2 = ({0, 1, 2} : Finset ℕ) by decide]
  norm_num [mertensPrimeWeight]

theorem mertensPrimeMean_unit_eq_weightSum_div_log (N : ℕ) :
    mertensPrimeMean (fun _ => (1 : ℝ)) N =
      mertensPrimeWeightSum N / Real.log N := by
  rw [mertensPrimeMean, mertensPrimeWeightSum_eq]
  congr 1
  exact Finset.sum_congr rfl fun n hn => by simp

theorem tendsto_mertensPrimeWeightSum_div_log :
    Tendsto (fun N : ℕ => mertensPrimeWeightSum N / Real.log N)
      atTop (nhds 1) := by
  apply tendsto_mertensPrimeMean_unit.congr'
  filter_upwards with N
  exact mertensPrimeMean_unit_eq_weightSum_div_log N

theorem tendsto_mertensPrimeWeightSumIocTwo_div_log :
    Tendsto (fun N : ℕ => mertensPrimeWeightSumIocTwo N / Real.log N)
      atTop (nhds 1) := by
  have hconst := tendsto_const_div_log_nat (Real.log 2 / 2)
  have hsub := tendsto_mertensPrimeWeightSum_div_log.sub hconst
  simpa only [sub_zero] using hsub.congr' (by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    rw [mertensPrimeWeightSum_eq_two_add_Ioc hN]
    ring)

theorem logarithmicPrimePhaseSumIoc_zero (N : ℕ) :
    logarithmicPrimePhaseSumIoc 0 N =
      (mertensPrimeWeightSumIocTwo N : ℂ) := by
  rw [logarithmicPrimePhaseSumIoc, mertensPrimeWeightSumIocTwo,
    Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mertensPrimeWeight]
  split_ifs with hp
  · rw [logarithmicPhase]
    simp
  · simp

theorem tendsto_logarithmicPrimePhaseSumIoc_zero_div_log :
    Tendsto (fun N : ℕ =>
      logarithmicPrimePhaseSumIoc 0 N / (Real.log N : ℂ))
      atTop (nhds 1) := by
  have h := tendsto_mertensPrimeWeightSumIocTwo_div_log
  have hcast : Tendsto (fun N : ℕ =>
      ((mertensPrimeWeightSumIocTwo N / Real.log N : ℝ) : ℂ))
      atTop (nhds (1 : ℂ)) := h.ofReal
  apply hcast.congr'
  filter_upwards with N
  rw [logarithmicPrimePhaseSumIoc_zero]
  push_cast
  rfl

/-! ## Prime-log phase equidistribution on the unit additive circle -/

abbrev mertensPrimeCircleHaar : Measure (AddCircle (1 : ℝ)) :=
  GaloisForLFunctions.unitCircleHaar

/-- Logarithmically weighted prime sampling of a continuous circle function. -/
def mertensPrimeCircleAverage (delta : ℝ)
    (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) : ℂ :=
  (∑ k ∈ Finset.Ioc 2 N,
      (mertensPrimeWeight k : ℂ) *
        f (((delta * Real.log k) / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ))) /
    (Real.log N : ℂ)

lemma mertensPrimeCircleAverage_zero (delta : ℝ) (N : ℕ) :
    mertensPrimeCircleAverage delta 0 N = 0 := by
  simp [mertensPrimeCircleAverage]

lemma mertensPrimeCircleAverage_add (delta : ℝ)
    (f g : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    mertensPrimeCircleAverage delta (f + g) N =
      mertensPrimeCircleAverage delta f N +
        mertensPrimeCircleAverage delta g N := by
  rw [mertensPrimeCircleAverage, mertensPrimeCircleAverage,
    mertensPrimeCircleAverage]
  simp_rw [ContinuousMap.add_apply, mul_add]
  rw [Finset.sum_add_distrib, add_div]

lemma mertensPrimeCircleAverage_smul (delta : ℝ) (c : ℂ)
    (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    mertensPrimeCircleAverage delta (c • f) N =
      c * mertensPrimeCircleAverage delta f N := by
  rw [mertensPrimeCircleAverage, mertensPrimeCircleAverage]
  simp_rw [ContinuousMap.smul_apply, smul_eq_mul]
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma mertensPrimeCircleAverage_sub (delta : ℝ)
    (f g : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    mertensPrimeCircleAverage delta (f - g) N =
      mertensPrimeCircleAverage delta f N -
        mertensPrimeCircleAverage delta g N := by
  rw [mertensPrimeCircleAverage, mertensPrimeCircleAverage,
    mertensPrimeCircleAverage]
  simp_rw [ContinuousMap.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib, sub_div]

lemma fourier_primeLogCirclePoint (delta : ℝ) (j : ℤ) (k : ℕ) :
    fourier j
        (((delta * Real.log k) / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ)) =
      logarithmicPhase ((j : ℝ) * delta) k := by
  rw [fourier_coe_apply, logarithmicPhase]
  congr 1
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

lemma mertensPrimeCircleAverage_fourier_eq (delta : ℝ) (j : ℤ) (N : ℕ) :
    mertensPrimeCircleAverage delta (fourier j) N =
      logarithmicPrimePhaseSumIoc ((j : ℝ) * delta) N /
        (Real.log N : ℂ) := by
  rw [mertensPrimeCircleAverage, logarithmicPrimePhaseSumIoc]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [mertensPrimeWeight]
  split_ifs with hp
  · rw [fourier_primeLogCirclePoint]
  · simp

lemma integral_fourier_mertensPrimeCircleHaar (j : ℤ) :
    (∫ x : AddCircle (1 : ℝ), fourier j x ∂mertensPrimeCircleHaar) =
      if j = 0 then 1 else 0 := by
  exact GaloisForLFunctions.integral_fourier_unitCircleHaar j

theorem tendsto_mertensPrimeCircleAverage_fourier
    (delta : ℝ) (hdelta : delta ≠ 0) (j : ℤ) :
    Tendsto (fun N : ℕ => mertensPrimeCircleAverage delta (fourier j) N)
      atTop (nhds (if j = 0 then 1 else 0)) := by
  by_cases hj : j = 0
  · subst j
    simpa [mertensPrimeCircleAverage_fourier_eq] using
      tendsto_logarithmicPrimePhaseSumIoc_zero_div_log
  · have hfrequency : (j : ℝ) * delta ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hj) hdelta
    simpa only [if_neg hj, mertensPrimeCircleAverage_fourier_eq] using
      tendsto_logarithmicPrimePhaseSumIoc_div_log hfrequency

theorem tendsto_mertensPrimeCircleAverage_span_fourier
    (delta : ℝ) (hdelta : delta ≠ 0)
    {f : C(AddCircle (1 : ℝ), ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range (@fourier (1 : ℝ)))) :
    Tendsto (fun N : ℕ => mertensPrimeCircleAverage delta f N) atTop
      (nhds (∫ x, f x ∂mertensPrimeCircleHaar)) := by
  refine Submodule.span_induction
    (p := fun f _ =>
      Tendsto (fun N : ℕ => mertensPrimeCircleAverage delta f N) atTop
        (nhds (∫ x, f x ∂mertensPrimeCircleHaar))) ?_ ?_ ?_ ?_ hf
  · rintro g ⟨j, rfl⟩
    rw [integral_fourier_mertensPrimeCircleHaar]
    exact tendsto_mertensPrimeCircleAverage_fourier delta hdelta j
  · simp [mertensPrimeCircleAverage_zero]
  · intro f g hfs hgs hflim hglim
    have hadd := hflim.add hglim
    have hfi : Integrable f mertensPrimeCircleHaar := by
      rw [← integrableOn_univ]
      exact f.continuous.continuousOn.integrableOn_compact isCompact_univ
    have hgi : Integrable g mertensPrimeCircleHaar := by
      rw [← integrableOn_univ]
      exact g.continuous.continuousOn.integrableOn_compact isCompact_univ
    simpa only [mertensPrimeCircleAverage_add, ContinuousMap.add_apply,
      integral_add hfi hgi] using hadd
  · intro c f hfs hflim
    have hsmul := hflim.const_mul c
    have hint :
        (∫ x : AddCircle (1 : ℝ), (c • f) x ∂mertensPrimeCircleHaar) =
          c * ∫ x : AddCircle (1 : ℝ), f x ∂mertensPrimeCircleHaar := by
      simpa only [ContinuousMap.smul_apply, smul_eq_mul] using
        (integral_smul (μ := mertensPrimeCircleHaar) c
          (fun x : AddCircle (1 : ℝ) => f x))
    simpa only [mertensPrimeCircleAverage_smul, hint] using hsmul

/-- Uniform operator bound for the prime-circle sampling functional. -/
theorem norm_mertensPrimeCircleAverage_le (delta : ℝ)
    (f : C(AddCircle (1 : ℝ), ℂ)) {N : ℕ} (hN : 2 ≤ N) :
    ‖mertensPrimeCircleAverage delta f N‖ ≤
      (mertensPrimeWeightSumIocTwo N / Real.log N) * ‖f‖ := by
  have hlog : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN)
  rw [mertensPrimeCircleAverage, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hlog]
  refine (div_le_div_of_nonneg_right (norm_sum_le _ _) hlog.le).trans ?_
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hlog.le
  calc
    ∑ k ∈ Finset.Ioc 2 N,
        ‖(mertensPrimeWeight k : ℂ) *
          f (((delta * Real.log k) / (2 * Real.pi) : ℝ) :
            AddCircle (1 : ℝ))‖
      ≤ ∑ k ∈ Finset.Ioc 2 N, mertensPrimeWeight k * ‖f‖ := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mertensPrimeWeight_nonneg k)]
        exact mul_le_mul_of_nonneg_left
          (ContinuousMap.norm_coe_le_norm f _) (mertensPrimeWeight_nonneg k)
    _ = mertensPrimeWeightSumIocTwo N * ‖f‖ := by
      rw [mertensPrimeWeightSumIocTwo, Finset.sum_mul]

theorem tendsto_mertensPrimeCircleAverage_haar
    (delta : ℝ) (hdelta : delta ≠ 0)
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (fun N : ℕ => mertensPrimeCircleAverage delta f N) atTop
      (nhds (∫ x, f x ∂mertensPrimeCircleHaar)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hfclosure :
      f ∈ (Submodule.span ℂ
        (Set.range (@fourier (1 : ℝ)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  obtain ⟨q, hqspan, hfq⟩ :=
    Metric.mem_closure_iff.mp hfclosure (epsilon / 8) (by positivity)
  have hqconv :=
    tendsto_mertensPrimeCircleAverage_span_fourier delta hdelta hqspan
  obtain ⟨Nq, hNq⟩ :=
    (Metric.tendsto_atTop.mp hqconv) (epsilon / 4) (by positivity)
  have hmassEventually : ∀ᶠ N : ℕ in atTop,
      mertensPrimeWeightSumIocTwo N / Real.log N < 2 :=
    tendsto_mertensPrimeWeightSumIocTwo_div_log.eventually
      (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  obtain ⟨Nm, hNm⟩ := eventually_atTop.mp hmassEventually
  refine ⟨max 2 (max Nq Nm), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
  have hNNq : Nq ≤ N :=
    le_trans (le_max_left Nq Nm) (le_trans (le_max_right 2 _) hN)
  have hNNm : Nm ≤ N :=
    le_trans (le_max_right Nq Nm) (le_trans (le_max_right 2 _) hN)
  have havg :
      ‖mertensPrimeCircleAverage delta f N -
          mertensPrimeCircleAverage delta q N‖ < epsilon / 4 := by
    rw [← mertensPrimeCircleAverage_sub]
    refine (norm_mertensPrimeCircleAverage_le delta (f - q) hN2).trans_lt ?_
    have hmass := hNm N hNNm
    have hnorm : ‖f - q‖ < epsilon / 8 := by
      simpa [dist_eq_norm] using hfq
    have hmassNonneg :
        0 ≤ mertensPrimeWeightSumIocTwo N / Real.log N := by
      exact div_nonneg (Finset.sum_nonneg fun k _ => mertensPrimeWeight_nonneg k)
        (le_of_lt (Real.log_pos
          (by exact_mod_cast lt_of_lt_of_le one_lt_two hN2)))
    nlinarith [norm_nonneg (f - q)]
  have hint :
      ‖(∫ x, q x ∂mertensPrimeCircleHaar) -
          ∫ x, f x ∂mertensPrimeCircleHaar‖ < epsilon / 8 := by
    refine (GaloisForLFunctions.norm_integral_sub_unitCircleHaar_le_norm q f).trans_lt ?_
    simpa [dist_eq_norm, norm_sub_rev] using hfq
  rw [dist_eq_norm]
  calc
    ‖mertensPrimeCircleAverage delta f N -
        ∫ x, f x ∂mertensPrimeCircleHaar‖
      ≤ ‖mertensPrimeCircleAverage delta f N -
            mertensPrimeCircleAverage delta q N‖ +
          ‖mertensPrimeCircleAverage delta q N -
            ∫ x, q x ∂mertensPrimeCircleHaar‖ +
          ‖(∫ x, q x ∂mertensPrimeCircleHaar) -
            ∫ x, f x ∂mertensPrimeCircleHaar‖ := by
        calc
          _ = ‖(mertensPrimeCircleAverage delta f N -
                  mertensPrimeCircleAverage delta q N) +
                ((mertensPrimeCircleAverage delta q N -
                    ∫ x, q x ∂mertensPrimeCircleHaar) +
                  ((∫ x, q x ∂mertensPrimeCircleHaar) -
                    ∫ x, f x ∂mertensPrimeCircleHaar))‖ := by ring_nf
          _ ≤ _ := by
            calc
              _ ≤ ‖mertensPrimeCircleAverage delta f N -
                    mertensPrimeCircleAverage delta q N‖ +
                  ‖(mertensPrimeCircleAverage delta q N -
                      ∫ x, q x ∂mertensPrimeCircleHaar) +
                    ((∫ x, q x ∂mertensPrimeCircleHaar) -
                      ∫ x, f x ∂mertensPrimeCircleHaar)‖ := norm_add_le _ _
              _ ≤ _ := by
                have htail := norm_add_le
                  (mertensPrimeCircleAverage delta q N -
                    ∫ x, q x ∂mertensPrimeCircleHaar)
                  ((∫ x, q x ∂mertensPrimeCircleHaar) -
                    ∫ x, f x ∂mertensPrimeCircleHaar)
                linarith
    _ < epsilon / 4 + epsilon / 4 + epsilon / 8 := by
      gcongr
      simpa [dist_eq_norm] using hNq N hNNq
    _ < epsilon := by linarith

/-! ## Exact mean chord -/

/-- Chord length from the negative first character to the unit, as a complex-valued
continuous circle function. -/
def primePhaseChord : C(AddCircle (1 : ℝ), ℂ) :=
  ⟨fun x => ((‖fourier (-1) x - 1‖ : ℝ) : ℂ),
    Complex.continuous_ofReal.comp
      (((fourier (-1 : ℤ)).continuous.sub continuous_const).norm)⟩

@[simp] theorem primePhaseChord_apply (x : AddCircle (1 : ℝ)) :
    primePhaseChord x = ((‖fourier (-1) x - 1‖ : ℝ) : ℂ) := rfl

theorem primePhaseChord_coe_eq_two_abs_sin (x : ℝ) :
    primePhaseChord ((x : ℝ) : AddCircle (1 : ℝ)) =
      ((2 * |Real.sin (Real.pi * x)| : ℝ) : ℂ) := by
  rw [primePhaseChord_apply]
  have hfourier :
      fourier (-1 : ℤ) ((x : ℝ) : AddCircle (1 : ℝ)) =
        Complex.exp (2 * Real.pi * (-x) * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [hfourier]
  norm_cast
  rw [show (((2 * Real.pi * (-x) : ℝ) : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) * ((-x : ℝ) : ℂ) * Complex.I by
        push_cast
        ring,
    GaloisForLFunctions.HTGeometry.norm_exp_two_pi_sub_one (-x)]
  rw [mul_neg, Real.sin_neg, abs_neg]

theorem primePhaseChord_coe_eq_two_sin {x : ℝ}
    (hx : x ∈ Set.uIcc (0 : ℝ) 1) :
    primePhaseChord ((x : ℝ) : AddCircle (1 : ℝ)) =
      ((2 * Real.sin (Real.pi * x) : ℝ) : ℂ) := by
  rw [primePhaseChord_apply]
  have hfourier :
      fourier (-1 : ℤ) ((x : ℝ) : AddCircle (1 : ℝ)) =
        Complex.exp (2 * Real.pi * (-x) * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [hfourier]
  norm_cast
  have hx' : 0 ≤ x ∧ x ≤ 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  have hsin : 0 ≤ Real.sin (Real.pi * x) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact mul_nonneg Real.pi_pos.le hx'.1
    · nlinarith [Real.pi_pos]
  rw [show (((2 * Real.pi * (-x) : ℝ) : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) * ((-x : ℝ) : ℂ) * Complex.I by
        push_cast
        ring,
    GaloisForLFunctions.HTGeometry.norm_exp_two_pi_sub_one (-x)]
  rw [mul_neg, Real.sin_neg, abs_neg, abs_of_nonneg hsin]

lemma intervalIntegral_two_sin_pi :
    (∫ x in (0 : ℝ)..1, 2 * Real.sin (Real.pi * x)) = 4 / Real.pi := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => -(2 / Real.pi) * Real.cos (Real.pi * x))
        (2 * Real.sin (Real.pi * x)) x := by
    intro x hx
    have hinner : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x :=
      by simpa using (hasDerivAt_id x).const_mul Real.pi
    have hcos := (Real.hasDerivAt_cos (Real.pi * x)).comp x hinner
    have hscaled := hcos.const_mul (-(2 / Real.pi))
    refine hscaled.congr_deriv ?_
    field_simp [Real.pi_ne_zero]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  rw [mul_zero, Real.cos_zero, mul_one, Real.cos_pi]
  field_simp [Real.pi_ne_zero]
  ring

theorem integral_primePhaseChord_mertensPrimeCircleHaar :
    (∫ x : AddCircle (1 : ℝ), primePhaseChord x ∂mertensPrimeCircleHaar) =
      ((4 / Real.pi : ℝ) : ℂ) := by
  rw [AddCircle.integral_haarAddCircle, inv_one, one_smul,
    ← AddCircle.intervalIntegral_preimage (1 : ℝ) 0, zero_add]
  rw [intervalIntegral.integral_congr
    (fun x hx => primePhaseChord_coe_eq_two_sin hx)]
  rw [intervalIntegral.integral_ofReal, intervalIntegral_two_sin_pi]

theorem tendsto_mertensPrimeCircleAverage_primePhaseChord
    (delta : ℝ) (hdelta : delta ≠ 0) :
    Tendsto (fun N : ℕ =>
      mertensPrimeCircleAverage delta primePhaseChord N) atTop
      (nhds ((4 / Real.pi : ℝ) : ℂ)) := by
  rw [← integral_primePhaseChord_mertensPrimeCircleHaar]
  exact tendsto_mertensPrimeCircleAverage_haar delta hdelta primePhaseChord

/-! ## Asymptotic cutoff norms descend isometrically to the finite-tail quotient -/

theorem mertensPrimeMean_absField_eq_complexMarcinkiewiczQuotient
    (b : ℕ → ℂ) (X : ℕ) :
    mertensPrimeMean (absField b) X = complexMarcinkiewiczQuotient b X := by
  unfold mertensPrimeMean complexMarcinkiewiczQuotient
  congr 1
  unfold primeLogMass
  apply Finset.sum_congr rfl
  intro n hn
  simp [absField]

theorem tendsto_complexMarcinkiewiczQuotient_zero_of_finiteSupport
    (f : MarcinkiewiczLogPre) (hf : f ∈ marcinkiewiczFiniteSupportPre) :
    Tendsto (fun X : ℕ => complexMarcinkiewiczQuotient f X) atTop (nhds 0) := by
  have h := tendsto_mertensPrimeMean_zero_of_vanishingTail
    (memVanishingTailLayer_absField_of_finiteSupport hf)
  exact h.congr' (Filter.Eventually.of_forall fun X =>
    mertensPrimeMean_absField_eq_complexMarcinkiewiczQuotient f X)

theorem le_marcinkiewiczPreNorm_sub_finite_of_tendsto
    (b f : MarcinkiewiczLogPre) (hf : f ∈ marcinkiewiczFiniteSupportPre)
    {L : ℝ}
    (hlimit : Tendsto (fun X : ℕ => complexMarcinkiewiczQuotient b X)
      atTop (nhds L)) :
    L ≤ marcinkiewiczPreNorm (b - f) := by
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  have hbEventually : ∀ᶠ X : ℕ in atTop,
      L - epsilon / 2 < complexMarcinkiewiczQuotient b X :=
    hlimit.eventually (Ioi_mem_nhds (by linarith))
  have hfEventually : ∀ᶠ X : ℕ in atTop,
      complexMarcinkiewiczQuotient f X < epsilon / 2 :=
    (tendsto_complexMarcinkiewiczQuotient_zero_of_finiteSupport f hf).eventually
      (Iio_mem_nhds (by linarith))
  have hcombined : ∀ᶠ X : ℕ in atTop,
      2 ≤ X ∧ L - epsilon / 2 < complexMarcinkiewiczQuotient b X ∧
        complexMarcinkiewiczQuotient f X < epsilon / 2 := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hbEventually, hfEventually]
      with X hX2 hbX hfX
    exact ⟨hX2, hbX, hfX⟩
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hcombined
  obtain ⟨hX2, hbX, hfX⟩ := hX X le_rfl
  have htriangle : complexMarcinkiewiczQuotient b X ≤
      complexMarcinkiewiczQuotient (b - f) X +
        complexMarcinkiewiczQuotient f X := by
    have h := marcinkiewiczLogQuotient_absField_add_le
      ((b - f : MarcinkiewiczLogPre) : ℕ → ℂ) f hX2
    simpa [complexMarcinkiewiczQuotient] using h
  have hpre := complexMarcinkiewiczQuotient_le_preNorm (b - f) hX2
  have hcoe : (((b - f : MarcinkiewiczLogPre) : ℕ → ℂ)) =
      (b : ℕ → ℂ) - (f : ℕ → ℂ) := rfl
  rw [hcoe] at hpre
  linarith

theorem norm_marcinkiewiczLogQuotientMk_mk_eq_of_tendsto_cutoff
    (b : MarcinkiewiczLogPre) {L : ℝ} (hL : 0 ≤ L)
    (hlimit : Tendsto (fun X : ℕ => complexMarcinkiewiczQuotient b X)
      atTop (nhds L)) :
    ‖marcinkiewiczLogQuotientMk (marcinkiewiczLogMk b)‖ = L := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    have hEventually : ∀ᶠ X : ℕ in atTop,
        complexMarcinkiewiczQuotient b X < L + epsilon :=
      hlimit.eventually (Iio_mem_nhds (by linarith))
    obtain ⟨P, hP⟩ := eventually_atTop.mp hEventually
    have htail :
        marcinkiewiczPreNorm (marcinkiewiczTailPre b P) ≤ L + epsilon := by
      apply marcinkiewiczPreNorm_le
      intro X hX
      by_cases hXP : X ≤ P
      · rw [complexMarcinkiewiczQuotient, marcinkiewiczTailPre_coe,
          absField_primeFieldTail, marcinkiewiczLogQuotient]
        have hmass0 : primeLogMass
            (primeCoefficientTail (absField (b : ℕ → ℂ)) P) X = 0 := by
          unfold primeLogMass
          apply Finset.sum_eq_zero
          intro n hn
          rw [Finset.mem_filter, Finset.mem_Icc] at hn
          have hnP : ¬P < n := not_lt_of_ge (hn.1.2.trans hXP)
          simp [primeCoefficientTail, hnP]
        rw [hmass0, zero_div]
        linarith
      · exact (complexMarcinkiewiczQuotient_tail_le b P hX).trans
          (hP X (Nat.le_of_lt (lt_of_not_ge hXP))).le
    have hhead0 : marcinkiewiczLogQuotientMk
        (marcinkiewiczLogMk (marcinkiewiczHeadPre b P)) = 0 :=
      marcinkiewiczLogQuotientMk_mk_eq_zero_of_finiteSupport _
        (marcinkiewiczHeadPre_mem_finiteSupport _ _)
    have hclass : marcinkiewiczLogQuotientMk (marcinkiewiczLogMk b) =
        marcinkiewiczLogQuotientMk
          (marcinkiewiczLogMk (marcinkiewiczTailPre b P)) := by
      rw [← marcinkiewiczPre_sub_head]
      simp only [map_sub, hhead0, sub_zero]
    rw [hclass]
    exact (Submodule.Quotient.norm_mk_le MarcinkiewiczZero
      (marcinkiewiczLogMk (marcinkiewiczTailPre b P))).trans
        ((marcinkiewiczLogMk_norm _).trans_le htail)
  · rw [marcinkiewiczLogQuotientMk, Submodule.mkQ_apply]
    have hnorm : ‖(Submodule.Quotient.mk (marcinkiewiczLogMk b) :
        MarcinkiewiczLogQuotient)‖ =
        Metric.infDist (marcinkiewiczLogMk b)
          (MarcinkiewiczZero : Set MarcinkiewiczLog) :=
      QuotientAddGroup.norm_mk (marcinkiewiczLogMk b)
    rw [hnorm, Metric.le_infDist ⟨0, MarcinkiewiczZero.zero_mem⟩]
    intro m hm
    apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    change m ∈
      (marcinkiewiczFiniteSupportPre.map marcinkiewiczLogMk).topologicalClosure at hm
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hm
    obtain ⟨y, hy, hmy⟩ := Metric.mem_closure_iff.mp hm epsilon hepsilon
    obtain ⟨f, hf, rfl⟩ := hy
    have hlower : L ≤ dist (marcinkiewiczLogMk b) (marcinkiewiczLogMk f) := by
      rw [dist_eq_norm, ← map_sub, marcinkiewiczLogMk_norm]
      exact le_marcinkiewiczPreNorm_sub_finite_of_tendsto b f hf hlimit
    have htriangle :=
      dist_triangle (marcinkiewiczLogMk b) m (marcinkiewiczLogMk f)
    linarith

/-! ## Exact critical phase distance -/

/-- Unit-modulus logarithmic phase as an algebraic Marcinkiewicz field. -/
def logarithmicPhasePre (t : ℝ) : MarcinkiewiczLogPre := by
  refine ⟨fun n => logarithmicPhase t n, ?_⟩
  have habs : absField (fun n : ℕ => logarithmicPhase t n) =
      fun _ => (1 : ℝ) := by
    funext n
    simp [absField, norm_logarithmicPhase]
  change MemMarcinkiewiczLogLayer
    (absField (fun n : ℕ => logarithmicPhase t n))
  rw [habs]
  exact unitField_memMarcinkiewiczLogLayer

@[simp] theorem logarithmicPhasePre_apply (t : ℝ) (n : ℕ) :
    (logarithmicPhasePre t : ℕ → ℂ) n = logarithmicPhase t n := rfl

/-- Difference of two critical logarithmic phases in the bounded carrier. -/
def logarithmicPhaseDifferencePre (t u : ℝ) : MarcinkiewiczLogPre :=
  logarithmicPhasePre t - logarithmicPhasePre u

@[simp] theorem logarithmicPhaseDifferencePre_apply (t u : ℝ) (n : ℕ) :
    (logarithmicPhaseDifferencePre t u : ℕ → ℂ) n =
      logarithmicPhase t n - logarithmicPhase u n := rfl

theorem logarithmicPhase_add (t u x : ℝ) :
    logarithmicPhase (t + u) x =
      logarithmicPhase t x * logarithmicPhase u x := by
  rw [logarithmicPhase, logarithmicPhase, logarithmicPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_logarithmicPhase_sub_eq_two_abs_sin (t u x : ℝ) :
    ‖logarithmicPhase t x - logarithmicPhase u x‖ =
      2 * |Real.sin ((t - u) * Real.log x / 2)| := by
  have hfactor : logarithmicPhase t x - logarithmicPhase u x =
      logarithmicPhase u x * (logarithmicPhase (t - u) x - 1) := by
    rw [mul_sub, mul_one, ← logarithmicPhase_add]
    congr 2
    ring
  rw [hfactor, norm_mul, norm_logarithmicPhase, one_mul]
  have hexp : logarithmicPhase (t - u) x =
      Complex.exp
        (2 * Real.pi * (((t - u) * Real.log x) / (2 * Real.pi)) * Complex.I) := by
    rw [logarithmicPhase]
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hexp]
  convert GaloisForLFunctions.HTGeometry.norm_exp_two_pi_sub_one
    (((t - u) * Real.log x) / (2 * Real.pi)) using 1
  · congr 3
    push_cast
    rfl
  · congr 2
    field_simp [Real.pi_ne_zero]

theorem primePhaseChord_primeLogPoint_eq_phaseDistance (t u : ℝ) (n : ℕ) :
    primePhaseChord
        ((((t - u) * Real.log n) / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ)) =
      ((‖logarithmicPhase t n - logarithmicPhase u n‖ : ℝ) : ℂ) := by
  rw [primePhaseChord_coe_eq_two_abs_sin,
    norm_logarithmicPhase_sub_eq_two_abs_sin]
  congr 3
  field_simp [Real.pi_ne_zero]

def logarithmicPrimePhaseDistanceSumIoc (t u : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 2 N,
    mertensPrimeWeight n * ‖logarithmicPhase t n - logarithmicPhase u n‖

theorem mertensPrimeCircleAverage_primePhaseChord_eq_distanceSum
    (t u : ℝ) (N : ℕ) :
    mertensPrimeCircleAverage (t - u) primePhaseChord N =
      ((logarithmicPrimePhaseDistanceSumIoc t u N / Real.log N : ℝ) : ℂ) := by
  rw [mertensPrimeCircleAverage, logarithmicPrimePhaseDistanceSumIoc,
    Complex.ofReal_div, Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [primePhaseChord_primeLogPoint_eq_phaseDistance]
  push_cast
  rfl

theorem tendsto_logarithmicPrimePhaseDistanceSumIoc_div_log
    {t u : ℝ} (htu : t ≠ u) :
    Tendsto (fun N : ℕ =>
      logarithmicPrimePhaseDistanceSumIoc t u N / Real.log N)
      atTop (nhds (4 / Real.pi)) := by
  have hcomplex :=
    tendsto_mertensPrimeCircleAverage_primePhaseChord (t - u) (sub_ne_zero.mpr htu)
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  exact hreal.congr' (Filter.Eventually.of_forall fun N => by
    rw [Function.comp_apply,
      mertensPrimeCircleAverage_primePhaseChord_eq_distanceSum]
    exact Complex.ofReal_re _)

def logarithmicPrimePhaseDistanceSum (t u : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N with n.Prime,
    Real.log n / n * ‖logarithmicPhase t n - logarithmicPhase u n‖

theorem logarithmicPrimePhaseDistanceSum_eq_two_add_Ioc
    (t u : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    logarithmicPrimePhaseDistanceSum t u N =
      Real.log 2 / 2 * ‖logarithmicPhase t 2 - logarithmicPhase u 2‖ +
        logarithmicPrimePhaseDistanceSumIoc t u N := by
  have hset :
      (Finset.Icc 1 N).filter Nat.Prime =
        ({2} : Finset ℕ) ∪ (Finset.Ioc 2 N).filter Nat.Prime := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_Ioc]
    constructor
    · rintro ⟨hn, hprime⟩
      have hn2 := hprime.two_le
      by_cases hnEq : n = 2
      · exact Or.inl hnEq
      · exact Or.inr ⟨⟨lt_of_le_of_ne hn2 (Ne.symm hnEq), hn.2⟩, hprime⟩
    · rintro (rfl | ⟨hn, hprime⟩)
      · exact ⟨⟨by norm_num, hN⟩, by norm_num⟩
      · exact ⟨⟨by omega, hn.2⟩, hprime⟩
  rw [logarithmicPrimePhaseDistanceSum, hset,
    Finset.sum_union (by
      rw [Finset.disjoint_left]
      intro n hn hnp
      simp only [Finset.mem_singleton] at hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hnp
      omega)]
  rw [Finset.sum_singleton]
  congr 1
  rw [logarithmicPrimePhaseDistanceSumIoc]
  simp only [mertensPrimeWeight, ite_mul, zero_mul]
  rw [← Finset.sum_filter]

theorem complexMarcinkiewiczQuotient_logarithmicPhaseDifferencePre
    (t u : ℝ) (N : ℕ) :
    complexMarcinkiewiczQuotient (logarithmicPhaseDifferencePre t u) N =
      logarithmicPrimePhaseDistanceSum t u N / Real.log N := by
  unfold complexMarcinkiewiczQuotient marcinkiewiczLogQuotient
  congr 1
  unfold primeLogMass logarithmicPrimePhaseDistanceSum
  apply Finset.sum_congr rfl
  intro n hn
  simp [absField]

theorem tendsto_complexMarcinkiewiczQuotient_logarithmicPhaseDifferencePre
    {t u : ℝ} (htu : t ≠ u) :
    Tendsto (fun N : ℕ =>
      complexMarcinkiewiczQuotient (logarithmicPhaseDifferencePre t u) N)
      atTop (nhds (4 / Real.pi)) := by
  let C : ℝ :=
    Real.log 2 / 2 * ‖logarithmicPhase t 2 - logarithmicPhase u 2‖
  have hconst := tendsto_const_div_log_nat C
  have hioc := tendsto_logarithmicPrimePhaseDistanceSumIoc_div_log htu
  have hadd := hconst.add hioc
  have hsum : Tendsto (fun N : ℕ =>
      logarithmicPrimePhaseDistanceSum t u N / Real.log N)
      atTop (nhds (4 / Real.pi)) := by
    simpa only [zero_add] using hadd.congr' (by
      filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
      rw [logarithmicPrimePhaseDistanceSum_eq_two_add_Ioc t u hN]
      dsimp only [C]
      ring)
  exact hsum.congr' (Filter.Eventually.of_forall fun N =>
    (complexMarcinkiewiczQuotient_logarithmicPhaseDifferencePre t u N).symm)

theorem norm_logarithmicPhaseDifferenceClass {t u : ℝ} (htu : t ≠ u) :
    ‖marcinkiewiczLogQuotientMk
        (marcinkiewiczLogMk (logarithmicPhaseDifferencePre t u))‖ =
      4 / Real.pi := by
  apply norm_marcinkiewiczLogQuotientMk_mk_eq_of_tendsto_cutoff
  · positivity
  · exact tendsto_complexMarcinkiewiczQuotient_logarithmicPhaseDifferencePre htu

/-! ## FE--Schwarz prime quartet and exact quotient separation -/

theorem primeShiftCharacter_mul (z w : ℂ) :
    primeShiftCharacter z * primeShiftCharacter w =
      primeShiftCharacter (z + w - 1 / 2) := by
  change primeShiftMultiplier z (primeShiftCharacter w) = _
  exact primeShiftMultiplier_primeShiftCharacter z w

def feSchwarzPoint (a t : ℝ) : ℂ :=
  (1 : ℂ) / 2 + a + t * Complex.I

@[simp] theorem feSchwarzPoint_re (a t : ℝ) :
    (feSchwarzPoint a t).re = 1 / 2 + a := by
  simp [feSchwarzPoint]

@[simp] theorem feSchwarzPoint_conj (a t : ℝ) :
    starRingEnd ℂ (feSchwarzPoint a t) = (1 : ℂ) / 2 + a - t * Complex.I := by
  apply Complex.ext <;> simp [feSchwarzPoint]

def criticalPrimePhase (t : ℝ) : ℕ → ℂ :=
  primeShiftCharacter ((1 : ℂ) / 2 + t * Complex.I)

theorem criticalPrimePhase_zero :
    criticalPrimePhase 0 = primeShiftCharacter (1 / 2) := by
  simp [criticalPrimePhase]

theorem feSchwarz_fePair_product (a t : ℝ) :
    primeShiftCharacter (feSchwarzPoint a t) *
        primeShiftCharacter (1 - starRingEnd ℂ (feSchwarzPoint a t)) =
      criticalPrimePhase (2 * t) := by
  rw [primeShiftCharacter_mul]
  congr 1
  apply Complex.ext <;> simp [feSchwarzPoint] <;> ring

theorem feSchwarz_oppositeFePair_product (a t : ℝ) :
    primeShiftCharacter (starRingEnd ℂ (feSchwarzPoint a t)) *
        primeShiftCharacter (1 - feSchwarzPoint a t) =
      criticalPrimePhase (-2 * t) := by
  rw [primeShiftCharacter_mul]
  congr 1
  apply Complex.ext <;> simp [feSchwarzPoint] <;> ring

theorem feSchwarz_schwarzPair_product (a t : ℝ) :
    primeShiftCharacter (feSchwarzPoint a t) *
        primeShiftCharacter (starRingEnd ℂ (feSchwarzPoint a t)) =
      primeShiftCharacter ((1 : ℂ) / 2 + 2 * a) := by
  rw [primeShiftCharacter_mul]
  congr 1
  apply Complex.ext <;> simp [feSchwarzPoint] <;> try ring

theorem feSchwarz_quartet_product (a t : ℝ) :
    primeShiftCharacter (feSchwarzPoint a t) *
        primeShiftCharacter (1 - feSchwarzPoint a t) *
        primeShiftCharacter (starRingEnd ℂ (feSchwarzPoint a t)) *
        primeShiftCharacter (1 - starRingEnd ℂ (feSchwarzPoint a t)) =
      primeShiftCharacter ((1 : ℂ) / 2) := by
  rw [primeShiftCharacter_mul, primeShiftCharacter_mul, primeShiftCharacter_mul]
  congr 1
  ring

theorem marcinkiewiczPreNorm_eq_zero_of_eq_on_primes
    (b c : MarcinkiewiczLogPre)
    (hbc : ∀ p : ℕ, p.Prime → (b : ℕ → ℂ) p = (c : ℕ → ℂ) p) :
    marcinkiewiczPreNorm (b - c) = 0 := by
  apply le_antisymm
  · apply marcinkiewiczPreNorm_le
    intro X hX
    unfold complexMarcinkiewiczQuotient marcinkiewiczLogQuotient primeLogMass
    have hsum :
        (∑ p ∈ Finset.Icc 1 X with p.Prime,
          Real.log p / p *
            |absField ((b - c : MarcinkiewiczLogPre) : ℕ → ℂ) p|) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_filter] at hp
      have heq := hbc p hp.2
      simp [absField, heq]
    rw [hsum, zero_div]
  · exact marcinkiewiczPreNorm_nonneg _

theorem marcinkiewiczLogMk_eq_of_eq_on_primes
    (b c : MarcinkiewiczLogPre)
    (hbc : ∀ p : ℕ, p.Prime → (b : ℕ → ℂ) p = (c : ℕ → ℂ) p) :
    marcinkiewiczLogMk b = marcinkiewiczLogMk c := by
  apply sub_eq_zero.mp
  rw [← map_sub, ← norm_eq_zero, marcinkiewiczLogMk_norm,
    marcinkiewiczPreNorm_eq_zero_of_eq_on_primes b c hbc]

theorem marcinkiewiczLogQuotientMk_mk_eq_of_eq_on_primes
    (b c : MarcinkiewiczLogPre)
    (hbc : ∀ p : ℕ, p.Prime → (b : ℕ → ℂ) p = (c : ℕ → ℂ) p) :
    marcinkiewiczLogQuotientMk (marcinkiewiczLogMk b) =
      marcinkiewiczLogQuotientMk (marcinkiewiczLogMk c) := by
  rw [marcinkiewiczLogMk_eq_of_eq_on_primes b c hbc]

def criticalPrimePhaseClass (t : ℝ) : MarcinkiewiczLogQuotient :=
  marcinkiewiczPrimeShiftClass ((1 : ℂ) / 2 + t * Complex.I) (by simp)

theorem criticalPrimePhaseClass_eq_logarithmicPhaseClass (t : ℝ) :
    criticalPrimePhaseClass t =
      marcinkiewiczLogQuotientMk (marcinkiewiczLogMk (logarithmicPhasePre (-t))) := by
  rw [criticalPrimePhaseClass, marcinkiewiczPrimeShiftClass]
  apply marcinkiewiczLogQuotientMk_mk_eq_of_eq_on_primes
  intro p hp
  simp [marcinkiewiczPrimeShiftPre, primeShiftCharacter, hp,
    logarithmicPhasePre, logarithmicPhase]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne_zero),
    ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem criticalPrimePhaseClass_sub (t u : ℝ) :
    criticalPrimePhaseClass t - criticalPrimePhaseClass u =
      marcinkiewiczLogQuotientMk
        (marcinkiewiczLogMk (logarithmicPhaseDifferencePre (-t) (-u))) := by
  rw [criticalPrimePhaseClass_eq_logarithmicPhaseClass,
    criticalPrimePhaseClass_eq_logarithmicPhaseClass,
    logarithmicPhaseDifferencePre, map_sub, map_sub]

theorem dist_criticalPrimePhaseClass {t u : ℝ} (htu : t ≠ u) :
    dist (criticalPrimePhaseClass t) (criticalPrimePhaseClass u) =
      4 / Real.pi := by
  rw [dist_eq_norm, criticalPrimePhaseClass_sub]
  exact norm_logarithmicPhaseDifferenceClass (fun h => htu (neg_injective h))

theorem norm_criticalPrimePhaseClass (t : ℝ) :
    ‖criticalPrimePhaseClass t‖ = 1 := by
  apply norm_marcinkiewiczPrimeShiftClass_of_re_eq_half
  simp

theorem marcinkiewiczPrimeShiftClass_half_eq_unitClass :
    marcinkiewiczPrimeShiftClass ((1 : ℂ) / 2) (by simp) =
      marcinkiewiczUnitClass := by
  rw [marcinkiewiczPrimeShiftClass, marcinkiewiczUnitClass, marcinkiewiczUnit]
  apply marcinkiewiczLogQuotientMk_mk_eq_of_eq_on_primes
  intro p hp
  simp [marcinkiewiczPrimeShiftPre, primeShiftCharacter, marcinkiewiczUnitPre, hp]

theorem criticalPrimePhaseClass_zero :
    criticalPrimePhaseClass 0 = marcinkiewiczUnitClass := by
  simpa [criticalPrimePhaseClass] using
    marcinkiewiczPrimeShiftClass_half_eq_unitClass

def feSchwarzSchwarzPairClass (a : ℝ) (ha : 0 < a) :
    MarcinkiewiczLogQuotient :=
  marcinkiewiczPrimeShiftClass ((1 : ℂ) / 2 + 2 * a) (by simp; linarith)

theorem feSchwarzSchwarzPairClass_eq_zero (a : ℝ) (ha : 0 < a) :
    feSchwarzSchwarzPairClass a ha = 0 := by
  apply marcinkiewiczPrimeShiftClass_eq_zero_of_half_lt_re
  simp
  linarith

theorem feSchwarz_completeQuartetClass_eq_unit (_a _t : ℝ) :
    marcinkiewiczPrimeShiftClass ((1 : ℂ) / 2) (by simp) =
      marcinkiewiczUnitClass :=
  marcinkiewiczPrimeShiftClass_half_eq_unitClass

end RHTower

end
