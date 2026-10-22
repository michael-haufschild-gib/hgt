import GaloisForLFunctions.RHTower.Sieve.MertensFirstExpRate
import GaloisForLFunctions.RHTower.MertensPrimeMeanReader
import GaloisForLFunctions.RHTower.MertensPrimeWindowWeakConvergence
import GaloisForLFunctions.RHTower.MarcinkiewiczPrimeTailBanach
import GaloisForLFunctions.RHTower.PrimeRpowAbelSummation
import GaloisForLFunctions.HTGeometry.HarmonicLogEquidistribution
import GaloisForLFunctions.HTGeometry.CircleEmbeddingBiLipschitz
import GaloisForLFunctions.HTGeometry.TrigPolyLogVanishing
import GaloisForLFunctions.RHTower.TrigPolyOrthogonality
import GaloisForLFunctions.RHTower.XiMassPrimeWindowAbel
import GaloisForLFunctions.RHTower.Deninger.DeningerAllPrimeFloquetRadical
import GaloisForLFunctions.HTGeometry.PeriodicRotationEnergy

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
    ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (primeLogWeight_primeRpowAbelSummation k : ℂ) =
      (Chebyshev.theta t : ℂ) := by
  rw [← Complex.ofReal_sum, sum_primeLogWeight_eq_theta]

theorem logarithmicPhaseOverId_mul_primeLogWeight {xi : ℝ} {k : ℕ} (hk : 2 < k) :
    logarithmicPhaseOverId xi k * (primeLogWeight_primeRpowAbelSummation k : ℂ) =
      if k.Prime then ((Real.log k / k : ℝ) : ℂ) * logarithmicPhase xi k else 0 := by
  rw [primeLogWeight_primeRpowAbelSummation]
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
    (fun k : ℕ => (primeLogWeight_primeRpowAbelSummation k : ℂ))
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
  unfold primeLogMass_weightedEulerCoefficientSpaces
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
        have hmass0 : primeLogMass_weightedEulerCoefficientSpaces
            (primeCoefficientTail (absField (b : ℕ → ℂ)) P) X = 0 := by
          unfold primeLogMass_weightedEulerCoefficientSpaces
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
  unfold primeLogMass_weightedEulerCoefficientSpaces logarithmicPrimePhaseDistanceSum
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
  apply Complex.ext
  · simp [feSchwarzPoint]
    ring
  · simp [feSchwarzPoint]

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
    unfold complexMarcinkiewiczQuotient marcinkiewiczLogQuotient primeLogMass_weightedEulerCoefficientSpaces
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

/-! ## Finite horizontal-grade exponential fields -/

/-- The complex exponent carried by horizontal grade `m` and vertical frequency `n`. -/
def horizontalExponent (a t : ℝ) (m n : ℤ) : ℂ :=
  (((m : ℝ) * a : ℝ) : ℂ) + (((n : ℝ) * t : ℝ) : ℂ) * Complex.I

/-- The normalized shift point whose prime character has exponent `horizontalExponent`. -/
def horizontalShiftPoint (a t : ℝ) (m n : ℤ) : ℂ :=
  (1 : ℂ) / 2 - horizontalExponent a t m n

@[simp] theorem horizontalShiftPoint_re (a t : ℝ) (m n : ℤ) :
    (horizontalShiftPoint a t m n).re = 1 / 2 - (m : ℝ) * a := by
  simp [horizontalShiftPoint, horizontalExponent]

/-- A finite exponential polynomial written in normalized prime characters. -/
def horizontalPrimeExponentialField (M S : Finset ℤ) (c : ℤ → ℤ → ℂ)
    (a t : ℝ) : ℕ → ℂ :=
  ∑ m ∈ M, ∑ n ∈ S, c m n • primeShiftCharacter (horizontalShiftPoint a t m n)

/-- Its logarithmic-height exponential-polynomial realization. -/
def horizontalLogPolynomial (M S : Finset ℤ) (c : ℤ → ℤ → ℂ)
    (a t x : ℝ) : ℂ :=
  ∑ m ∈ M, ∑ n ∈ S,
    c m n * Complex.exp (horizontalExponent a t m n * (x : ℂ))

/-- Horizontal-grade profile. -/
def horizontalGradeProfile (S : Finset ℤ) (c : ℤ → ℤ → ℂ)
    (t : ℝ) (m : ℤ) : ℝ → ℂ :=
  GaloisForLFunctions.HTGeometry.trigPoly S (c m) t

theorem horizontalLogPolynomial_eq_gradeSum
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t x : ℝ) :
    horizontalLogPolynomial M S c a t x =
      ∑ m ∈ M, Complex.exp ((((m : ℝ) * a * x : ℝ) : ℂ)) *
        horizontalGradeProfile S c t m x := by
  classical
  unfold horizontalLogPolynomial horizontalGradeProfile
    GaloisForLFunctions.HTGeometry.trigPoly
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    c m n * Complex.exp (horizontalExponent a t m n * (x : ℂ)) =
        c m n * (Complex.exp ((((m : ℝ) * a * x : ℝ) : ℂ)) *
          Complex.exp (((t * (n : ℝ) * x : ℝ) : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]
      congr 2
      simp [horizontalExponent]
      ring
    _ = Complex.exp ((((m : ℝ) * a * x : ℝ) : ℂ)) *
        (c m n * Complex.exp (((t * (n : ℝ) * x : ℝ) : ℂ) * Complex.I)) := by
      ring

theorem primeShiftCharacter_horizontalShiftPoint_on_prime
    (a t : ℝ) (m n : ℤ) {p : ℕ} (hp : p.Prime) :
    primeShiftCharacter (horizontalShiftPoint a t m n) p =
      Complex.exp (horizontalExponent a t m n * (Real.log p : ℂ)) := by
  simp only [primeShiftCharacter, if_pos hp, horizontalShiftPoint]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne_zero), ← Complex.natCast_log]
  congr 1
  ring

theorem horizontalPrimeExponentialField_on_prime
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t : ℝ) {p : ℕ} (hp : p.Prime) :
    horizontalPrimeExponentialField M S c a t p =
      horizontalLogPolynomial M S c a t (Real.log p) := by
  classical
  unfold horizontalPrimeExponentialField horizontalLogPolynomial
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [primeShiftCharacter_horizontalShiftPoint_on_prime a t m n hp]

/-- Vanishing-tail complex fields are closed under complex scaling. -/
theorem memVanishingTailLayer_absField_smul_complex {b : ℕ → ℂ}
    (hb : MemVanishingTailLayer (absField b)) (z : ℂ) :
    MemVanishingTailLayer (absField (z • b)) := by
  have heq : absField (z • b) = fun n => ‖z‖ * absField b n := by
    funext n
    simp [absField]
  rw [heq]
  exact memVanishingTailLayer_smul hb ‖z‖

/-- Vanishing-tail complex fields are closed under addition. -/
theorem memVanishingTailLayer_absField_add_complex {b d : ℕ → ℂ}
    (hb : MemVanishingTailLayer (absField b))
    (hd : MemVanishingTailLayer (absField d)) :
    MemVanishingTailLayer (absField (b + d)) := by
  intro ε hε
  obtain ⟨Pb, hPb⟩ := hb (ε / 2) (by linarith)
  obtain ⟨Pd, hPd⟩ := hd (ε / 2) (by linarith)
  refine ⟨max Pb Pd, fun X hX => ?_⟩
  let P := max Pb Pd
  have htail : primeFieldTail (b + d) P =
      primeFieldTail b P + primeFieldTail d P := by
    funext n
    by_cases hPn : P < n <;> simp [primeFieldTail, hPn]
  rw [← absField_primeFieldTail, htail]
  calc
    marcinkiewiczLogQuotient
        (absField (primeFieldTail b P + primeFieldTail d P)) X
        ≤ marcinkiewiczLogQuotient (absField (primeFieldTail b P)) X +
            marcinkiewiczLogQuotient (absField (primeFieldTail d P)) X :=
      marcinkiewiczLogQuotient_absField_add_le _ _ hX
    _ ≤ ε / 2 + ε / 2 := add_le_add
      (by
        rw [absField_primeFieldTail]
        exact le_trans (by
          unfold marcinkiewiczLogQuotient
          exact div_le_div_of_nonneg_right
            (primeLogMass_tail_anti (absField b) (le_max_left Pb Pd) X)
            (log_cutoff_pos hX).le) (hPb X hX))
      (by
        rw [absField_primeFieldTail]
        exact le_trans (by
          unfold marcinkiewiczLogQuotient
          exact div_le_div_of_nonneg_right
            (primeLogMass_tail_anti (absField d) (le_max_right Pb Pd) X)
            (log_cutoff_pos hX).le) (hPd X hX))
    _ = ε := by ring

/-- Finite sums of vanishing-tail complex fields remain vanishing-tail. -/
theorem memVanishingTailLayer_absField_finsetSum_complex
    {ι : Type*} (s : Finset ι) (f : ι → (ℕ → ℂ))
    (hf : ∀ i ∈ s, MemVanishingTailLayer (absField (f i))) :
    MemVanishingTailLayer (absField (∑ i ∈ s, f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro ε hε
      refine ⟨0, fun X hX => ?_⟩
      simpa [absField, marcinkiewiczLogQuotient, primeLogMass_weightedEulerCoefficientSpaces,
        primeCoefficientTail] using hε.le
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      apply memVanishingTailLayer_absField_add_complex
      · exact hf i (Finset.mem_insert_self i s)
      · apply ih
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)

theorem horizontalPrimeExponentialField_memVanishingTailLayer
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t : ℝ}
    (ha : 0 < a) (hM : ∀ m ∈ M, m < 0) :
    MemVanishingTailLayer
      (absField (horizontalPrimeExponentialField M S c a t)) := by
  classical
  unfold horizontalPrimeExponentialField
  apply memVanishingTailLayer_absField_finsetSum_complex M
  intro m hm
  apply memVanishingTailLayer_absField_finsetSum_complex S
  intro n hn
  apply memVanishingTailLayer_absField_smul_complex
  apply memVanishingTailLayer_absField_primeShiftCharacter_of_half_lt_re
  simp
  have hmneg := hM m hm
  have hmreal : (m : ℝ) < 0 := by exact_mod_cast hmneg
  nlinarith

/-- The bounded preclass of a finite field with no positive horizontal grades. -/
def horizontalPrimeExponentialPre
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t : ℝ)
    (ha : 0 ≤ a) (hM : ∀ m ∈ M, m ≤ 0) : MarcinkiewiczLogPre :=
  ∑ m ∈ M.attach, ∑ n ∈ S, c m.1 n •
    marcinkiewiczPrimeShiftPre (horizontalShiftPoint a t m.1 n) (by
      simp
      have hm := hM m.1 m.2
      have hmreal : (m.1 : ℝ) ≤ 0 := by exact_mod_cast hm
      nlinarith)

theorem coe_horizontalPrimeExponentialPre
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t : ℝ)
    (ha : 0 ≤ a) (hM : ∀ m ∈ M, m ≤ 0) :
    ((horizontalPrimeExponentialPre M S c a t ha hM : MarcinkiewiczLogPre) :
        ℕ → ℂ) = horizontalPrimeExponentialField M S c a t := by
  classical
  unfold horizontalPrimeExponentialPre horizontalPrimeExponentialField
  funext p
  simp only [Finset.sum_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower,
    Pi.smul_apply, marcinkiewiczPrimeShiftPre]
  exact Finset.sum_attach M (fun m =>
    ∑ n ∈ S, c m n • primeShiftCharacter (horizontalShiftPoint a t m n) p)

theorem horizontalPrimeExponentialField_memMarcinkiewiczLogLayer
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t : ℝ}
    (ha : 0 ≤ a) (hM : ∀ m ∈ M, m ≤ 0) :
    MemMarcinkiewiczLogLayer
      (absField (horizontalPrimeExponentialField M S c a t)) := by
  have hpre := (horizontalPrimeExponentialPre M S c a t ha hM).property
  rwa [coe_horizontalPrimeExponentialPre M S c a t ha hM] at hpre

/-- Corona class of a finite field having no positive horizontal grade. -/
def horizontalPrimeExponentialClass
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t : ℝ)
    (ha : 0 ≤ a) (hM : ∀ m ∈ M, m ≤ 0) : MarcinkiewiczLogQuotient :=
  marcinkiewiczLogQuotientMk
    (marcinkiewiczLogMk (horizontalPrimeExponentialPre M S c a t ha hM))

/-- The horizontal-grade-zero corona component; its definition contains no displacement `a`. -/
def horizontalGradeZeroClass (S : Finset ℤ) (c : ℤ → ℤ → ℂ) (t : ℝ) :
    MarcinkiewiczLogQuotient :=
  ∑ n ∈ S, c 0 n • marcinkiewiczPrimeShiftClass
    (horizontalShiftPoint 0 t 0 n) (by simp)

theorem horizontalPrimeExponentialClass_eq_characterSum
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t : ℝ)
    (ha : 0 ≤ a) (hM : ∀ m ∈ M, m ≤ 0) :
    horizontalPrimeExponentialClass M S c a t ha hM =
      ∑ m ∈ M.attach, ∑ n ∈ S, c m.1 n • marcinkiewiczPrimeShiftClass
        (horizontalShiftPoint a t m.1 n) (by
          simp
          have hm := hM m.1 m.2
          have hmreal : (m.1 : ℝ) ≤ 0 := by exact_mod_cast hm
          nlinarith) := by
  classical
  unfold horizontalPrimeExponentialClass horizontalPrimeExponentialPre
  simp only [map_sum, map_smul, marcinkiewiczPrimeShiftClass]

theorem horizontalPrimeExponentialClass_eq_zero_of_negative
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t : ℝ}
    (ha : 0 < a) (hM : ∀ m ∈ M, m < 0) :
    horizontalPrimeExponentialClass M S c a t ha.le
      (fun m hm => (hM m hm).le) = 0 := by
  classical
  rw [horizontalPrimeExponentialClass_eq_characterSum]
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  have hmneg := hM m.1 m.2
  have hmreal : (m.1 : ℝ) < 0 := by exact_mod_cast hmneg
  have hz : 1 / 2 < (horizontalShiftPoint a t m.1 n).re := by
    rw [horizontalShiftPoint_re]
    nlinarith
  have hclass := marcinkiewiczPrimeShiftClass_eq_zero_of_half_lt_re
    (horizontalShiftPoint a t m.1 n) hz
  simpa using congrArg (fun q : MarcinkiewiczLogQuotient => c m.1 n • q) hclass

theorem horizontalPrimeExponentialClass_eq_gradeZero
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t : ℝ}
    (ha : 0 < a) (hM : ∀ m ∈ M, m ≤ 0) (hzero : 0 ∈ M) :
    horizontalPrimeExponentialClass M S c a t ha.le hM =
      horizontalGradeZeroClass S c t := by
  classical
  rw [horizontalPrimeExponentialClass_eq_characterSum]
  unfold horizontalGradeZeroClass
  let m0 : {m // m ∈ M} := ⟨0, hzero⟩
  rw [Finset.sum_eq_single m0]
  · apply Finset.sum_congr rfl
    intro n hn
    change c 0 n • marcinkiewiczPrimeShiftClass
        (horizontalShiftPoint a t 0 n) _ = _
    congr 2
    simp [horizontalShiftPoint, horizontalExponent]
  · intro m hm hm0
    have hmle := hM m.1 m.2
    have hmne : m.1 ≠ 0 := by
      intro hval
      apply hm0
      apply Subtype.ext
      exact hval
    have hmneg : m.1 < 0 := lt_of_le_of_ne hmle hmne
    apply Finset.sum_eq_zero
    intro n hn
    have hmreal : (m.1 : ℝ) < 0 := by exact_mod_cast hmneg
    have hz : 1 / 2 < (horizontalShiftPoint a t m.1 n).re := by
      rw [horizontalShiftPoint_re]
      nlinarith
    have hclass := marcinkiewiczPrimeShiftClass_eq_zero_of_half_lt_re
      (horizontalShiftPoint a t m.1 n) hz
    simpa using congrArg (fun q : MarcinkiewiczLogQuotient => c m.1 n • q) hclass
  · simp [m0]

/-! ## Differential and uniform bounds for the leading-grade detector -/

def horizontalLogPolynomialDeriv (M S : Finset ℤ) (c : ℤ → ℤ → ℂ)
    (a t x : ℝ) : ℂ :=
  ∑ m ∈ M, ∑ n ∈ S, c m n * horizontalExponent a t m n *
    Complex.exp (horizontalExponent a t m n * (x : ℂ))

theorem hasDerivAt_horizontalLogPolynomial
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t x : ℝ) :
    HasDerivAt (horizontalLogPolynomial M S c a t)
      (horizontalLogPolynomialDeriv M S c a t x) x := by
  classical
  unfold horizontalLogPolynomial horizontalLogPolynomialDeriv
  have hterm : ∀ m : ℤ, ∀ n : ℤ,
      HasDerivAt
        (fun y : ℝ => c m n *
          Complex.exp (horizontalExponent a t m n * (y : ℂ)))
        (c m n * horizontalExponent a t m n *
          Complex.exp (horizontalExponent a t m n * (x : ℂ))) x := by
    intro m n
    have harg : HasDerivAt
        (fun y : ℝ => horizontalExponent a t m n * (y : ℂ))
        (horizontalExponent a t m n) x := by
      simpa using (hasDerivAt_id x).ofReal_comp.const_mul (horizontalExponent a t m n)
    have hexp := (Complex.hasDerivAt_exp
      (horizontalExponent a t m n * (x : ℂ))).scomp x harg
    have hbase : HasDerivAt
        (fun y : ℝ => c m n *
          Complex.exp (horizontalExponent a t m n * (y : ℂ)))
        (c m n * (horizontalExponent a t m n •
          Complex.exp (horizontalExponent a t m n * (x : ℂ)))) x := by
      simpa only [Function.comp_apply] using hexp.const_mul (c m n)
    apply hbase.congr_deriv
    simp [smul_eq_mul]
    ring
  have hsum := HasDerivAt.sum (u := M) (fun m hm =>
    HasDerivAt.sum (u := S) (fun n hn => hterm m n))
  have hfun : (fun y : ℝ => ∑ m ∈ M, ∑ n ∈ S, c m n *
      Complex.exp (horizontalExponent a t m n * (y : ℂ))) =
      ∑ m ∈ M, ∑ n ∈ S, fun y : ℝ => c m n *
        Complex.exp (horizontalExponent a t m n * (y : ℂ)) := by
    funext y
    simp only [Finset.sum_apply]
  rw [hfun]
  exact hsum

def horizontalGradeProfileDeriv (S : Finset ℤ) (c : ℤ → ℤ → ℂ)
    (t : ℝ) (m : ℤ) (x : ℝ) : ℂ :=
  ∑ n ∈ S, c m n * ((((t * (n : ℝ) : ℝ) : ℂ) * Complex.I)) *
    Complex.exp (((t * (n : ℝ) * x : ℝ) : ℂ) * Complex.I)

theorem hasDerivAt_horizontalGradeProfile
    (S : Finset ℤ) (c : ℤ → ℤ → ℂ) (t : ℝ) (m : ℤ) (x : ℝ) :
    HasDerivAt (horizontalGradeProfile S c t m)
      (horizontalGradeProfileDeriv S c t m x) x := by
  classical
  unfold horizontalGradeProfile horizontalGradeProfileDeriv
    GaloisForLFunctions.HTGeometry.trigPoly
  have hterm : ∀ n : ℤ,
      HasDerivAt
        (fun y : ℝ => c m n *
          Complex.exp (((t * (n : ℝ) * y : ℝ) : ℂ) * Complex.I))
        (c m n * (((t * (n : ℝ) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((t * (n : ℝ) * x : ℝ) : ℂ) * Complex.I)) x := by
    intro n
    have hlin : HasDerivAt (fun y : ℝ => t * (n : ℝ) * y) (t * (n : ℝ)) x := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id x).const_mul (t * (n : ℝ))
    have harg : HasDerivAt
        (fun y : ℝ => (((t * (n : ℝ) * y : ℝ) : ℂ) * Complex.I))
        ((((t * (n : ℝ) : ℝ) : ℂ) * Complex.I)) x :=
      hlin.ofReal_comp.mul_const Complex.I
    have hexp := (Complex.hasDerivAt_exp
      ((((t * (n : ℝ) * x : ℝ) : ℂ) * Complex.I))).scomp x harg
    have hbase : HasDerivAt
        (fun y : ℝ => c m n *
          Complex.exp (((t * (n : ℝ) * y : ℝ) : ℂ) * Complex.I))
        (c m n * ((((t * (n : ℝ) : ℝ) : ℂ) * Complex.I) •
          Complex.exp (((t * (n : ℝ) * x : ℝ) : ℂ) * Complex.I))) x := by
      simpa only [Function.comp_apply] using hexp.const_mul (c m n)
    apply hbase.congr_deriv
    simp [smul_eq_mul]
    ring
  have hsum := HasDerivAt.sum (u := S) (fun n hn => hterm n)
  have hfun : (fun y : ℝ => ∑ n ∈ S, c m n *
      Complex.exp (((t * (n : ℝ) * y : ℝ) : ℂ) * Complex.I)) =
      ∑ n ∈ S, fun y : ℝ => c m n *
        Complex.exp (((t * (n : ℝ) * y : ℝ) : ℂ) * Complex.I) := by
    funext y
    simp only [Finset.sum_apply]
  rw [hfun]
  exact hsum

def horizontalCoefficientNormSum (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) : ℝ :=
  ∑ m ∈ M, ∑ n ∈ S, ‖c m n‖

def horizontalDerivativeCoefficientNormSum
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t : ℝ) : ℝ :=
  ∑ m ∈ M, ∑ n ∈ S, ‖c m n‖ * ‖horizontalExponent a t m n‖

def horizontalProfileNormSum (S : Finset ℤ) (c : ℤ → ℤ → ℂ) (m : ℤ) : ℝ :=
  ∑ n ∈ S, ‖c m n‖

def horizontalProfileDerivNormSum
    (S : Finset ℤ) (c : ℤ → ℤ → ℂ) (t : ℝ) (m : ℤ) : ℝ :=
  ∑ n ∈ S, ‖c m n‖ * |t * (n : ℝ)|

theorem norm_horizontalGradeProfile_le
    (S : Finset ℤ) (c : ℤ → ℤ → ℂ) (t : ℝ) (m : ℤ) (x : ℝ) :
    ‖horizontalGradeProfile S c t m x‖ ≤ horizontalProfileNormSum S c m := by
  classical
  unfold horizontalGradeProfile horizontalProfileNormSum
    GaloisForLFunctions.HTGeometry.trigPoly
  calc
    ‖∑ n ∈ S, c m n * Complex.exp (((t * (n : ℝ) * x : ℝ) : ℂ) * Complex.I)‖
        ≤ ∑ n ∈ S, ‖c m n *
          Complex.exp (((t * (n : ℝ) * x : ℝ) : ℂ) * Complex.I)‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ S, ‖c m n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, Complex.norm_exp]
      simp

theorem norm_horizontalGradeProfileDeriv_le
    (S : Finset ℤ) (c : ℤ → ℤ → ℂ) (t : ℝ) (m : ℤ) (x : ℝ) :
    ‖horizontalGradeProfileDeriv S c t m x‖ ≤
      horizontalProfileDerivNormSum S c t m := by
  classical
  unfold horizontalGradeProfileDeriv horizontalProfileDerivNormSum
  calc
    ‖∑ n ∈ S, c m n * (((t * (n : ℝ) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((t * (n : ℝ) * x : ℝ) : ℂ) * Complex.I)‖
        ≤ ∑ n ∈ S, ‖c m n * (((t * (n : ℝ) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((t * (n : ℝ) * x : ℝ) : ℂ) * Complex.I)‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ S, ‖c m n‖ * |t * (n : ℝ)| := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, norm_mul, Complex.norm_exp]
      simp [Real.norm_eq_abs]

theorem norm_exp_horizontalExponent
    (a t x : ℝ) (m n : ℤ) :
    ‖Complex.exp (horizontalExponent a t m n * (x : ℂ))‖ =
      Real.exp ((m : ℝ) * a * x) := by
  rw [Complex.norm_exp]
  congr 1
  simp [horizontalExponent]

theorem norm_normalized_horizontalLogPolynomial_le
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a x : ℝ} {t : ℝ} {mStar : ℤ}
    (ha : 0 ≤ a) (hx : 0 ≤ x) (hM : ∀ m ∈ M, m ≤ mStar) :
    ‖(((Real.exp (-((mStar : ℝ) * a * x)) : ℝ) : ℂ) *
        horizontalLogPolynomial M S c a t x)‖ ≤
      horizontalCoefficientNormSum M S c := by
  classical
  unfold horizontalLogPolynomial horizontalCoefficientNormSum
  rw [Finset.mul_sum]
  calc
    ‖∑ m ∈ M, ((Real.exp (-((mStar : ℝ) * a * x)) : ℝ) : ℂ) *
        ∑ n ∈ S, c m n * Complex.exp (horizontalExponent a t m n * (x : ℂ))‖
        ≤ ∑ m ∈ M, ‖((Real.exp (-((mStar : ℝ) * a * x)) : ℝ) : ℂ) *
          ∑ n ∈ S, c m n * Complex.exp (horizontalExponent a t m n * (x : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m ∈ M, ∑ n ∈ S, ‖c m n‖ := by
      apply Finset.sum_le_sum
      intro m hm
      rw [Finset.mul_sum]
      calc
        ‖∑ n ∈ S, ((Real.exp (-((mStar : ℝ) * a * x)) : ℝ) : ℂ) *
            (c m n * Complex.exp (horizontalExponent a t m n * (x : ℂ)))‖
            ≤ ∑ n ∈ S, ‖((Real.exp (-((mStar : ℝ) * a * x)) : ℝ) : ℂ) *
              (c m n * Complex.exp (horizontalExponent a t m n * (x : ℂ)))‖ :=
          norm_sum_le _ _
        _ ≤ ∑ n ∈ S, ‖c m n‖ := by
          apply Finset.sum_le_sum
          intro n hn
          rw [norm_mul, norm_mul, norm_exp_horizontalExponent]
          simp only [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _)]
          have hmcast : (m : ℝ) ≤ (mStar : ℝ) := by exact_mod_cast hM m hm
          have hexp : Real.exp (-((mStar : ℝ) * a * x) + (m : ℝ) * a * x) ≤ 1 := by
            rw [← Real.exp_zero]
            apply Real.exp_le_exp.mpr
            have hprod : 0 ≤ ((mStar : ℝ) - (m : ℝ)) * a * x :=
              mul_nonneg (mul_nonneg (sub_nonneg.mpr hmcast) ha) hx
            linarith
          calc
            Real.exp (-((mStar : ℝ) * a * x)) *
                (‖c m n‖ * Real.exp ((m : ℝ) * a * x)) =
                ‖c m n‖ * Real.exp
                  (-((mStar : ℝ) * a * x) + (m : ℝ) * a * x) := by
              rw [Real.exp_add]
              ring
            _ ≤ ‖c m n‖ * 1 :=
              mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
            _ = ‖c m n‖ := mul_one _

theorem norm_normalized_horizontalLogPolynomialDeriv_le
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a x : ℝ} {t : ℝ} {mStar : ℤ}
    (ha : 0 ≤ a) (hx : 0 ≤ x) (hM : ∀ m ∈ M, m ≤ mStar) :
    ‖(((Real.exp (-((mStar : ℝ) * a * x)) : ℝ) : ℂ) *
        horizontalLogPolynomialDeriv M S c a t x)‖ ≤
      horizontalDerivativeCoefficientNormSum M S c a t := by
  classical
  unfold horizontalLogPolynomialDeriv horizontalDerivativeCoefficientNormSum
  rw [Finset.mul_sum]
  calc
    ‖∑ m ∈ M, ((Real.exp (-((mStar : ℝ) * a * x)) : ℝ) : ℂ) *
        ∑ n ∈ S, c m n * horizontalExponent a t m n *
          Complex.exp (horizontalExponent a t m n * (x : ℂ))‖
        ≤ ∑ m ∈ M, ‖((Real.exp (-((mStar : ℝ) * a * x)) : ℝ) : ℂ) *
          ∑ n ∈ S, c m n * horizontalExponent a t m n *
            Complex.exp (horizontalExponent a t m n * (x : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m ∈ M, ∑ n ∈ S, ‖c m n‖ * ‖horizontalExponent a t m n‖ := by
      apply Finset.sum_le_sum
      intro m hm
      rw [Finset.mul_sum]
      calc
        ‖∑ n ∈ S, ((Real.exp (-((mStar : ℝ) * a * x)) : ℝ) : ℂ) *
            (c m n * horizontalExponent a t m n *
              Complex.exp (horizontalExponent a t m n * (x : ℂ)))‖
            ≤ ∑ n ∈ S, ‖((Real.exp (-((mStar : ℝ) * a * x)) : ℝ) : ℂ) *
              (c m n * horizontalExponent a t m n *
                Complex.exp (horizontalExponent a t m n * (x : ℂ)))‖ :=
          norm_sum_le _ _
        _ ≤ ∑ n ∈ S, ‖c m n‖ * ‖horizontalExponent a t m n‖ := by
          apply Finset.sum_le_sum
          intro n hn
          rw [norm_mul, norm_mul, norm_mul, norm_exp_horizontalExponent]
          simp only [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _)]
          have hmcast : (m : ℝ) ≤ (mStar : ℝ) := by exact_mod_cast hM m hm
          have hexp : Real.exp (-((mStar : ℝ) * a * x) + (m : ℝ) * a * x) ≤ 1 := by
            rw [← Real.exp_zero]
            apply Real.exp_le_exp.mpr
            have hprod : 0 ≤ ((mStar : ℝ) - (m : ℝ)) * a * x :=
              mul_nonneg (mul_nonneg (sub_nonneg.mpr hmcast) ha) hx
            linarith
          let A := ‖c m n‖ * ‖horizontalExponent a t m n‖
          have hA : 0 ≤ A := mul_nonneg (norm_nonneg _) (norm_nonneg _)
          calc
            Real.exp (-((mStar : ℝ) * a * x)) *
                (‖c m n‖ * ‖horizontalExponent a t m n‖ *
                  Real.exp ((m : ℝ) * a * x)) =
                A * Real.exp
                  (-((mStar : ℝ) * a * x) + (m : ℝ) * a * x) := by
              dsimp [A]
              rw [Real.exp_add]
              ring
            _ ≤ A * 1 := mul_le_mul_of_nonneg_left hexp hA
            _ = ‖c m n‖ * ‖horizontalExponent a t m n‖ := by
              simp [A]

def horizontalConjugateCoefficients (c : ℤ → ℤ → ℂ) : ℤ → ℤ → ℂ :=
  fun m n => starRingEnd ℂ (c m n)

def horizontalConjugateProfile (S : Finset ℤ) (c : ℤ → ℤ → ℂ)
    (t : ℝ) (m : ℤ) : ℝ → ℂ :=
  horizontalGradeProfile S (horizontalConjugateCoefficients c) (-t) m

theorem horizontalConjugateProfile_eq_conj
    (S : Finset ℤ) (c : ℤ → ℤ → ℂ) (t : ℝ) (m : ℤ) (x : ℝ) :
    horizontalConjugateProfile S c t m x =
      starRingEnd ℂ (horizontalGradeProfile S c t m x) := by
  classical
  unfold horizontalConjugateProfile horizontalConjugateCoefficients
    horizontalGradeProfile GaloisForLFunctions.HTGeometry.trigPoly
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  rw [Complex.ofReal_neg]
  ring

def horizontalConjugateProfileDeriv (S : Finset ℤ) (c : ℤ → ℤ → ℂ)
    (t : ℝ) (m : ℤ) (x : ℝ) : ℂ :=
  horizontalGradeProfileDeriv S (horizontalConjugateCoefficients c) (-t) m x

theorem hasDerivAt_horizontalConjugateProfile
    (S : Finset ℤ) (c : ℤ → ℤ → ℂ) (t : ℝ) (m : ℤ) (x : ℝ) :
    HasDerivAt (horizontalConjugateProfile S c t m)
      (horizontalConjugateProfileDeriv S c t m x) x :=
  hasDerivAt_horizontalGradeProfile S (horizontalConjugateCoefficients c) (-t) m x

theorem norm_horizontalConjugateProfile_le
    (S : Finset ℤ) (c : ℤ → ℤ → ℂ) (t : ℝ) (m : ℤ) (x : ℝ) :
    ‖horizontalConjugateProfile S c t m x‖ ≤ horizontalProfileNormSum S c m := by
  rw [horizontalConjugateProfile_eq_conj, norm_conj]
  exact norm_horizontalGradeProfile_le S c t m x

theorem norm_horizontalConjugateProfileDeriv_le
    (S : Finset ℤ) (c : ℤ → ℤ → ℂ) (t : ℝ) (m : ℤ) (x : ℝ) :
    ‖horizontalConjugateProfileDeriv S c t m x‖ ≤
      horizontalProfileDerivNormSum S c t m := by
  have h := norm_horizontalGradeProfileDeriv_le S
    (horizontalConjugateCoefficients c) (-t) m x
  unfold horizontalConjugateProfileDeriv
  simpa [horizontalConjugateCoefficients, horizontalProfileDerivNormSum,
    norm_conj, abs_mul] using h

/-- The damped detector which extracts the leading horizontal profile on a moving log window. -/
def horizontalLeadingTest
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t : ℝ) (mStar : ℤ) (x : ℝ) : ℂ :=
  ((Real.exp (-(((mStar : ℝ) * a + 1) * x)) : ℝ) : ℂ) *
    horizontalLogPolynomial M S c a t x *
    horizontalConjugateProfile S c t mStar x

def horizontalLeadingTestDeriv
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t : ℝ) (mStar : ℤ) (x : ℝ) : ℂ :=
  let q := (mStar : ℝ) * a + 1
  ((-q * Real.exp (-(q * x)) : ℝ) : ℂ) *
      horizontalLogPolynomial M S c a t x *
      horizontalConjugateProfile S c t mStar x +
    ((Real.exp (-(q * x)) : ℝ) : ℂ) *
      horizontalLogPolynomialDeriv M S c a t x *
      horizontalConjugateProfile S c t mStar x +
    ((Real.exp (-(q * x)) : ℝ) : ℂ) *
      horizontalLogPolynomial M S c a t x *
      horizontalConjugateProfileDeriv S c t mStar x

theorem hasDerivAt_horizontalLeadingTest
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t : ℝ) (mStar : ℤ) (x : ℝ) :
    HasDerivAt (horizontalLeadingTest M S c a t mStar)
      (horizontalLeadingTestDeriv M S c a t mStar x) x := by
  let q : ℝ := (mStar : ℝ) * a + 1
  have hlin : HasDerivAt (fun y : ℝ => -(q * y)) (-q) x := by
    simpa only [id_eq, mul_one, neg_mul] using
      (hasDerivAt_id x).const_mul (-q)
  have hexpR := (Real.hasDerivAt_exp (-(q * x))).scomp x hlin
  have hexpC : HasDerivAt
      (fun y : ℝ => ((Real.exp (-(q * y)) : ℝ) : ℂ))
      (((-q * Real.exp (-(q * x)) : ℝ) : ℂ)) x := by
    simpa only [Function.comp_apply, smul_eq_mul] using hexpR.ofReal_comp
  have hpoly := hasDerivAt_horizontalLogPolynomial M S c a t x
  have hprof := hasDerivAt_horizontalConjugateProfile S c t mStar x
  have hprod := (hexpC.mul hpoly).mul hprof
  apply hprod.congr_deriv
  dsimp [horizontalLeadingTestDeriv, q]
  ring

def horizontalLeadingTestBound
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (mStar : ℤ) : ℝ :=
  horizontalCoefficientNormSum M S c * horizontalProfileNormSum S c mStar

def horizontalLeadingTestDerivBound
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t : ℝ) (mStar : ℤ) : ℝ :=
  |(mStar : ℝ) * a + 1| * horizontalCoefficientNormSum M S c *
      horizontalProfileNormSum S c mStar +
    horizontalDerivativeCoefficientNormSum M S c a t *
      horizontalProfileNormSum S c mStar +
    horizontalCoefficientNormSum M S c *
      horizontalProfileDerivNormSum S c t mStar

theorem norm_exp_mul_horizontalLeadingTest_le
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t x : ℝ} {mStar : ℤ}
    (ha : 0 ≤ a) (hx : 0 ≤ x) (hM : ∀ m ∈ M, m ≤ mStar) :
    ‖((Real.exp x : ℝ) : ℂ) * horizontalLeadingTest M S c a t mStar x‖ ≤
      horizontalLeadingTestBound M S c mStar := by
  have hfactor : Real.exp x * Real.exp (-(((mStar : ℝ) * a + 1) * x)) =
      Real.exp (-((mStar : ℝ) * a * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpoly := norm_normalized_horizontalLogPolynomial_le
    (M := M) (S := S) (c := c) (a := a) (t := t) (x := x)
    (mStar := mStar) ha hx hM
  have hprof := norm_horizontalConjugateProfile_le S c t mStar x
  unfold horizontalLeadingTest horizontalLeadingTestBound
  rw [norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [show Real.exp x *
      (Real.exp (-(((mStar : ℝ) * a + 1) * x)) *
        ‖horizontalLogPolynomial M S c a t x‖ *
        ‖horizontalConjugateProfile S c t mStar x‖) =
      Real.exp (-((mStar : ℝ) * a * x)) *
        ‖horizontalLogPolynomial M S c a t x‖ *
        ‖horizontalConjugateProfile S c t mStar x‖ by
        rw [← hfactor]
        ring]
  have hpoly' : Real.exp (-((mStar : ℝ) * a * x)) *
      ‖horizontalLogPolynomial M S c a t x‖ ≤
      horizontalCoefficientNormSum M S c := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at hpoly
    exact hpoly
  exact mul_le_mul hpoly' hprof (norm_nonneg _) (by
    unfold horizontalCoefficientNormSum
    positivity)

theorem norm_exp_mul_horizontalLeadingTestDeriv_le
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t x : ℝ} {mStar : ℤ}
    (ha : 0 ≤ a) (hx : 0 ≤ x) (hM : ∀ m ∈ M, m ≤ mStar) :
    ‖((Real.exp x : ℝ) : ℂ) *
        horizontalLeadingTestDeriv M S c a t mStar x‖ ≤
      horizontalLeadingTestDerivBound M S c a t mStar := by
  let q : ℝ := (mStar : ℝ) * a + 1
  have hfactor : Real.exp x * Real.exp (-(q * x)) =
      Real.exp (-((mStar : ℝ) * a * x)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [q]
    ring
  have hpoly0 := norm_normalized_horizontalLogPolynomial_le
    (M := M) (S := S) (c := c) (a := a) (t := t) (x := x)
    (mStar := mStar) ha hx hM
  have hpolyD0 := norm_normalized_horizontalLogPolynomialDeriv_le
    (M := M) (S := S) (c := c) (a := a) (t := t) (x := x)
    (mStar := mStar) ha hx hM
  have hpoly : Real.exp (-((mStar : ℝ) * a * x)) *
      ‖horizontalLogPolynomial M S c a t x‖ ≤
      horizontalCoefficientNormSum M S c := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at hpoly0
    exact hpoly0
  have hpolyD : Real.exp (-((mStar : ℝ) * a * x)) *
      ‖horizontalLogPolynomialDeriv M S c a t x‖ ≤
      horizontalDerivativeCoefficientNormSum M S c a t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at hpolyD0
    exact hpolyD0
  have hprof := norm_horizontalConjugateProfile_le S c t mStar x
  have hprofD := norm_horizontalConjugateProfileDeriv_le S c t mStar x
  let E : ℂ := ((Real.exp x : ℝ) : ℂ)
  let T₁ : ℂ := ((-q * Real.exp (-(q * x)) : ℝ) : ℂ) *
    horizontalLogPolynomial M S c a t x *
    horizontalConjugateProfile S c t mStar x
  let T₂ : ℂ := ((Real.exp (-(q * x)) : ℝ) : ℂ) *
    horizontalLogPolynomialDeriv M S c a t x *
    horizontalConjugateProfile S c t mStar x
  let T₃ : ℂ := ((Real.exp (-(q * x)) : ℝ) : ℂ) *
    horizontalLogPolynomial M S c a t x *
    horizontalConjugateProfileDeriv S c t mStar x
  have hT₁ : ‖E * T₁‖ ≤ |q| * horizontalCoefficientNormSum M S c *
      horizontalProfileNormSum S c mStar := by
    dsimp [E, T₁]
    simp only [norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_neg,
      abs_of_pos (Real.exp_pos _)]
    rw [show Real.exp x * (|q| * Real.exp (-(q * x)) *
        ‖horizontalLogPolynomial M S c a t x‖ *
        ‖horizontalConjugateProfile S c t mStar x‖) =
        |q| * (Real.exp (-((mStar : ℝ) * a * x)) *
          ‖horizontalLogPolynomial M S c a t x‖) *
          ‖horizontalConjugateProfile S c t mStar x‖ by
      rw [← hfactor]
      ring]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly (abs_nonneg q)) hprof
      (norm_nonneg _) (mul_nonneg (abs_nonneg q) (by
        unfold horizontalCoefficientNormSum
        positivity))
  have hT₂ : ‖E * T₂‖ ≤ horizontalDerivativeCoefficientNormSum M S c a t *
      horizontalProfileNormSum S c mStar := by
    dsimp [E, T₂]
    simp only [norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    rw [show Real.exp x * (Real.exp (-(q * x)) *
        ‖horizontalLogPolynomialDeriv M S c a t x‖ *
        ‖horizontalConjugateProfile S c t mStar x‖) =
        (Real.exp (-((mStar : ℝ) * a * x)) *
          ‖horizontalLogPolynomialDeriv M S c a t x‖) *
          ‖horizontalConjugateProfile S c t mStar x‖ by
      rw [← hfactor]
      ring]
    exact mul_le_mul hpolyD hprof (norm_nonneg _) (by
      unfold horizontalDerivativeCoefficientNormSum
      positivity)
  have hT₃ : ‖E * T₃‖ ≤ horizontalCoefficientNormSum M S c *
      horizontalProfileDerivNormSum S c t mStar := by
    dsimp [E, T₃]
    simp only [norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    rw [show Real.exp x * (Real.exp (-(q * x)) *
        ‖horizontalLogPolynomial M S c a t x‖ *
        ‖horizontalConjugateProfileDeriv S c t mStar x‖) =
        (Real.exp (-((mStar : ℝ) * a * x)) *
          ‖horizontalLogPolynomial M S c a t x‖) *
          ‖horizontalConjugateProfileDeriv S c t mStar x‖ by
      rw [← hfactor]
      ring]
    exact mul_le_mul hpoly hprofD (norm_nonneg _) (by
      unfold horizontalCoefficientNormSum
      positivity)
  change ‖E * (T₁ + T₂ + T₃)‖ ≤ _
  rw [mul_add, mul_add]
  exact (norm_add_le _ _).trans
    ((add_le_add (norm_add_le _ _) le_rfl).trans
      (add_le_add (add_le_add hT₁ hT₂) hT₃))

def normalizedXiMassThetaLogDiscrepancy (h : ℝ) : ℝ :=
  |xiMassThetaLogDiscrepancy h| / Real.exp h

theorem tendsto_normalizedXiMassThetaLogDiscrepancy_zero :
    Tendsto normalizedXiMassThetaLogDiscrepancy atTop (nhds 0) := by
  obtain ⟨c, C, h₀, hc, hC, hh₀, hE⟩ :=
    exists_norm_xiMassThetaLogDiscrepancy_le
  have hpow : Tendsto (fun h : ℝ => h ^ ((1 : ℝ) / 10)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hctop : Tendsto (fun h : ℝ => c * h ^ ((1 : ℝ) / 10)) atTop atTop :=
    hpow.const_mul_atTop hc
  have hdec : Tendsto
      (fun h : ℝ => C * Real.exp (-(c * h ^ ((1 : ℝ) / 10))))
      atTop (nhds 0) := by
    have hneg : Tendsto (fun h : ℝ => -(c * h ^ ((1 : ℝ) / 10))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hctop
    have hexp := Real.tendsto_exp_atBot.comp hneg
    simpa using (tendsto_const_nhds.mul hexp :
      Tendsto (fun h : ℝ => C * Real.exp (-(c * h ^ ((1 : ℝ) / 10))))
        atTop (nhds (C * 0)))
  rw [Metric.tendsto_atTop] at hdec ⊢
  intro ε hε
  obtain ⟨H, hH⟩ := hdec ε hε
  refine ⟨max h₀ H, fun h hh => ?_⟩
  have hh0 : h₀ ≤ h := le_trans (le_max_left _ _) hh
  have hhH : H ≤ h := le_trans (le_max_right _ _) hh
  have hbound : normalizedXiMassThetaLogDiscrepancy h ≤
      C * Real.exp (-(c * h ^ ((1 : ℝ) / 10))) := by
    unfold normalizedXiMassThetaLogDiscrepancy
    calc
      |xiMassThetaLogDiscrepancy h| / Real.exp h ≤
          (C * Real.exp h * Real.exp (-(c * h ^ ((1 : ℝ) / 10)))) /
            Real.exp h :=
        div_le_div_of_nonneg_right (hE h hh0) (Real.exp_pos _).le
      _ = C * Real.exp (-(c * h ^ ((1 : ℝ) / 10))) := by
        field_simp
  have hdecε : C * Real.exp (-(c * h ^ ((1 : ℝ) / 10))) < ε := by
    have := hH h hhH
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg hC,
      abs_of_pos (Real.exp_pos _)] at this
    exact this
  have hnonneg : 0 ≤ normalizedXiMassThetaLogDiscrepancy h := by
    unfold normalizedXiMassThetaLogDiscrepancy
    positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact lt_of_le_of_lt hbound hdecε

theorem tendsto_xiMassThetaLogDiscrepancy_mul_of_exp_bound
    {G : ℝ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ h : ℝ, 0 ≤ h → ‖((Real.exp h : ℝ) : ℂ) * G h‖ ≤ B) :
    Tendsto (fun h : ℝ => ((xiMassThetaLogDiscrepancy h : ℝ) : ℂ) * G h)
      atTop (nhds 0) := by
  have hmajor : Tendsto (fun h : ℝ => normalizedXiMassThetaLogDiscrepancy h * B)
      atTop (nhds 0) := by
    simpa using tendsto_normalizedXiMassThetaLogDiscrepancy_zero.mul_const B
  rw [Metric.tendsto_atTop] at hmajor ⊢
  intro ε hε
  obtain ⟨H, hH⟩ := hmajor ε hε
  refine ⟨max H 0, fun h hh => ?_⟩
  have hhH : H ≤ h := le_trans (le_max_left _ _) hh
  have hh0 : 0 ≤ h := le_trans (le_max_right _ _) hh
  have hnormG : Real.exp h * ‖G h‖ ≤ B := by
    have := hG h hh0
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at this
    exact this
  have hfactor : ‖((xiMassThetaLogDiscrepancy h : ℝ) : ℂ) * G h‖ ≤
      normalizedXiMassThetaLogDiscrepancy h * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have heq : |xiMassThetaLogDiscrepancy h| * ‖G h‖ =
        normalizedXiMassThetaLogDiscrepancy h * (Real.exp h * ‖G h‖) := by
      unfold normalizedXiMassThetaLogDiscrepancy
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hnormG (by
      unfold normalizedXiMassThetaLogDiscrepancy
      positivity)
  rw [dist_zero_right]
  exact lt_of_le_of_lt hfactor (by
    have := hH h hhH
    rw [Real.dist_eq, sub_zero, abs_of_nonneg
      (mul_nonneg (by
        unfold normalizedXiMassThetaLogDiscrepancy
        positivity) hB)] at this
    exact this)

theorem intervalIntegral_forwardWindow_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Tendsto f atTop (nhds 0)) {L : ℝ} (hL : 0 ≤ L) :
    Tendsto (fun H : ℝ => ∫ x in H..(H + L), f x) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at hf ⊢
  intro ε hε
  have hL1 : 0 < L + 1 := by linarith
  obtain ⟨T, hT⟩ := hf (ε / (L + 1)) (div_pos hε hL1)
  refine ⟨T, fun H hHT => ?_⟩
  rw [dist_zero_right]
  have hHH : H ≤ H + L := le_add_of_nonneg_right hL
  calc
    ‖∫ x in H..(H + L), f x‖ ≤ (ε / (L + 1)) * |H + L - H| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le hHH] at hx
      have hTx : T ≤ x := hHT.trans hx.1.le
      have hxlt : ‖f x‖ < ε / (L + 1) := by
        simpa [dist_zero_right] using hT x hTx
      exact hxlt.le
    _ = (ε / (L + 1)) * L := by
      rw [show H + L - H = L by ring, abs_of_nonneg hL]
    _ < ε := by
      calc
        (ε / (L + 1)) * L < (ε / (L + 1)) * (L + 1) :=
          mul_lt_mul_of_pos_left (by linarith) (div_pos hε hL1)
        _ = ε := div_mul_cancel₀ ε hL1.ne'

def horizontalLeadingPrimeWindowSum
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t : ℝ) (mStar : ℤ)
    (H L : ℝ) : ℂ :=
  ∑ p ∈ primeLogWindow H (H + L), ((Real.log p : ℝ) : ℂ) *
    horizontalLeadingTest M S c a t mStar (Real.log p)

def horizontalLeadingContinuumWindow
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t : ℝ) (mStar : ℤ)
    (H L : ℝ) : ℂ :=
  ∫ h in H..(H + L), horizontalLeadingTest M S c a t mStar h *
    ((Real.exp h : ℝ) : ℂ)

def horizontalLeadingQuadratureDefect
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t : ℝ) (mStar : ℤ)
    (H L : ℝ) : ℂ :=
  horizontalLeadingPrimeWindowSum M S c a t mStar H L -
    horizontalLeadingContinuumWindow M S c a t mStar H L

theorem tendsto_horizontalLeadingQuadratureDefect_zero
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t L : ℝ} {mStar : ℤ}
    (ha : 0 ≤ a) (hL : 0 ≤ L) (hM : ∀ m ∈ M, m ≤ mStar) :
    Tendsto (fun H : ℝ =>
      horizontalLeadingQuadratureDefect M S c a t mStar H L)
      atTop (nhds 0) := by
  have hB : 0 ≤ horizontalLeadingTestBound M S c mStar := by
    unfold horizontalLeadingTestBound horizontalCoefficientNormSum
      horizontalProfileNormSum
    positivity
  have hBD : 0 ≤ horizontalLeadingTestDerivBound M S c a t mStar := by
    unfold horizontalLeadingTestDerivBound horizontalCoefficientNormSum
      horizontalProfileNormSum horizontalDerivativeCoefficientNormSum
      horizontalProfileDerivNormSum
    positivity
  have hstart : Tendsto (fun H : ℝ =>
      ((xiMassThetaLogDiscrepancy H : ℝ) : ℂ) *
        horizontalLeadingTest M S c a t mStar H) atTop (nhds 0) :=
    tendsto_xiMassThetaLogDiscrepancy_mul_of_exp_bound hB
      (fun h hh => norm_exp_mul_horizontalLeadingTest_le ha hh hM)
  have hderiv : Tendsto (fun H : ℝ =>
      ((xiMassThetaLogDiscrepancy H : ℝ) : ℂ) *
        horizontalLeadingTestDeriv M S c a t mStar H) atTop (nhds 0) :=
    tendsto_xiMassThetaLogDiscrepancy_mul_of_exp_bound hBD
      (fun h hh => norm_exp_mul_horizontalLeadingTestDeriv_le ha hh hM)
  have hshift : Tendsto (fun H : ℝ => H + L) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with H hH
    exact hH.trans (le_add_of_nonneg_right hL)
  have hend : Tendsto (fun H : ℝ =>
      ((xiMassThetaLogDiscrepancy (H + L) : ℝ) : ℂ) *
        horizontalLeadingTest M S c a t mStar (H + L)) atTop (nhds 0) :=
    hstart.comp hshift
  have hint : Tendsto (fun H : ℝ =>
      ∫ h in H..(H + L), ((xiMassThetaLogDiscrepancy h : ℝ) : ℂ) *
        horizontalLeadingTestDeriv M S c a t mStar h) atTop (nhds 0) :=
    intervalIntegral_forwardWindow_tendsto_zero hderiv hL
  have hlim := (hend.sub hstart).sub hint
  have hlim0 : Tendsto (fun H : ℝ =>
      ((xiMassThetaLogDiscrepancy (H + L) : ℝ) : ℂ) *
          horizontalLeadingTest M S c a t mStar (H + L) -
        ((xiMassThetaLogDiscrepancy H : ℝ) : ℂ) *
          horizontalLeadingTest M S c a t mStar H -
        ∫ h in H..(H + L), ((xiMassThetaLogDiscrepancy h : ℝ) : ℂ) *
          horizontalLeadingTestDeriv M S c a t mStar h) atTop (nhds 0) := by
    simpa using hlim
  apply hlim0.congr'
  filter_upwards with H
  unfold horizontalLeadingQuadratureDefect horizontalLeadingPrimeWindowSum
    horizontalLeadingContinuumWindow
  rw [primeLogWindow_quadrature_eq (le_add_of_nonneg_right hL)
    (fun x hx => hasDerivAt_horizontalLeadingTest M S c a t mStar x)
    (by
      apply Continuous.intervalIntegrable
      unfold horizontalLeadingTestDeriv horizontalLogPolynomialDeriv
        horizontalLogPolynomial horizontalConjugateProfile
        horizontalConjugateProfileDeriv horizontalGradeProfile
        horizontalGradeProfileDeriv horizontalConjugateCoefficients
        GaloisForLFunctions.HTGeometry.trigPoly
      fun_prop)]

def horizontalPhasePeriod (t : ℝ) : ℝ :=
  if t = 0 then 1 else 2 * Real.pi / |t|

theorem horizontalPhasePeriod_pos (t : ℝ) : 0 < horizontalPhasePeriod t := by
  unfold horizontalPhasePeriod
  split_ifs with ht
  · norm_num
  · positivity

theorem periodic_horizontalGradeProfile
    (S : Finset ℤ) (c : ℤ → ℤ → ℂ) (t : ℝ) (m : ℤ) :
    Function.Periodic (horizontalGradeProfile S c t m) (horizontalPhasePeriod t) := by
  by_cases ht : t = 0
  · subst t
    intro x
    simp [horizontalGradeProfile, horizontalPhasePeriod,
      GaloisForLFunctions.HTGeometry.trigPoly]
  · simpa only [horizontalPhasePeriod, ht, if_false, horizontalGradeProfile] using
      GaloisForLFunctions.HTGeometry.periodic_trigPoly ht S (c m)

theorem periodic_horizontalConjugateProfile
    (S : Finset ℤ) (c : ℤ → ℤ → ℂ) (t : ℝ) (m : ℤ) :
    Function.Periodic (horizontalConjugateProfile S c t m) (horizontalPhasePeriod t) := by
  intro x
  rw [horizontalConjugateProfile_eq_conj, horizontalConjugateProfile_eq_conj,
    (periodic_horizontalGradeProfile S c t m) x]

theorem horizontalLeadingTest_mul_exp_eq_gradeSum
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t : ℝ) (mStar : ℤ) (x : ℝ) :
    horizontalLeadingTest M S c a t mStar x * ((Real.exp x : ℝ) : ℂ) =
      ∑ m ∈ M, Complex.exp
          (((((m : ℝ) - (mStar : ℝ)) * a * x : ℝ) : ℂ)) *
        horizontalGradeProfile S c t m x *
        horizontalConjugateProfile S c t mStar x := by
  classical
  unfold horizontalLeadingTest
  rw [horizontalLogPolynomial_eq_gradeSum]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Complex.ofReal_exp, Complex.ofReal_exp]
  have hexp :
      Complex.exp (((-(((mStar : ℝ) * a + 1) * x) : ℝ) : ℂ)) *
          Complex.exp ((((m : ℝ) * a * x : ℝ) : ℂ)) *
          Complex.exp ((x : ℂ)) =
        Complex.exp (((((m : ℝ) - (mStar : ℝ)) * a * x : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    Complex.exp (((-(((mStar : ℝ) * a + 1) * x) : ℝ) : ℂ)) *
          (Complex.exp ((((m : ℝ) * a * x : ℝ) : ℂ)) *
            horizontalGradeProfile S c t m x) *
        horizontalConjugateProfile S c t mStar x * Complex.exp (x : ℂ) =
        (Complex.exp (((-(((mStar : ℝ) * a + 1) * x) : ℝ) : ℂ)) *
          Complex.exp ((((m : ℝ) * a * x : ℝ) : ℂ)) * Complex.exp (x : ℂ)) *
          horizontalGradeProfile S c t m x *
          horizontalConjugateProfile S c t mStar x := by ring
    _ = _ := by rw [hexp]

theorem horizontalLeadingGradeTerm
    (S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t : ℝ) (mStar : ℤ) (x : ℝ) :
    Complex.exp (((((mStar : ℝ) - (mStar : ℝ)) * a * x : ℝ) : ℂ)) *
        horizontalGradeProfile S c t mStar x *
        horizontalConjugateProfile S c t mStar x =
      ((‖horizontalGradeProfile S c t mStar x‖ ^ 2 : ℝ) : ℂ) := by
  rw [horizontalConjugateProfile_eq_conj]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

def horizontalLeadingEnergy
    (S : Finset ℤ) (c : ℤ → ℤ → ℂ) (t : ℝ) (mStar : ℤ) : ℝ :=
  ∫ x in (0 : ℝ)..horizontalPhasePeriod t,
    ‖horizontalGradeProfile S c t mStar x‖ ^ 2

theorem horizontalLeadingEnergy_pos
    {S : Finset ℤ} {c : ℤ → ℤ → ℂ} {t : ℝ} {mStar : ℤ}
    (hnonzero : ∃ x ∈ Set.Ioo (0 : ℝ) (horizontalPhasePeriod t),
      horizontalGradeProfile S c t mStar x ≠ 0) :
    0 < horizontalLeadingEnergy S c t mStar := by
  have hL := horizontalPhasePeriod_pos t
  have hcont : Continuous (horizontalGradeProfile S c t mStar) := by
    unfold horizontalGradeProfile
    exact GaloisForLFunctions.HTGeometry.continuous_trigPoly S (c mStar) t
  have hnonneg : 0 ≤ horizontalLeadingEnergy S c t mStar := by
    unfold horizontalLeadingEnergy
    apply intervalIntegral.integral_nonneg hL.le
    intro x hx
    positivity
  apply lt_of_le_of_ne hnonneg
  intro hzero
  obtain ⟨x, hx, hne⟩ := hnonzero
  exact hne (continuous_eq_zero_of_intervalIntegral_normSq hcont hL hzero.symm x hx)

theorem intervalIntegral_horizontalLeadingGrade_eq_energy
    (S : Finset ℤ) (c : ℤ → ℤ → ℂ) (t : ℝ) (mStar : ℤ) (H : ℝ) :
    (∫ x in H..(H + horizontalPhasePeriod t),
        ((‖horizontalGradeProfile S c t mStar x‖ ^ 2 : ℝ) : ℂ)) =
      ((horizontalLeadingEnergy S c t mStar : ℝ) : ℂ) := by
  let P : ℝ → ℂ := horizontalGradeProfile S c t mStar
  have hper : Function.Periodic (fun x : ℝ => ‖P x‖ ^ 2) (horizontalPhasePeriod t) := by
    intro x
    change ‖horizontalGradeProfile S c t mStar (x + horizontalPhasePeriod t)‖ ^ 2 =
      ‖horizontalGradeProfile S c t mStar x‖ ^ 2
    rw [(periodic_horizontalGradeProfile S c t mStar) x]
  have hshift := hper.intervalIntegral_add_eq H 0
  have hreal : (∫ x in H..(H + horizontalPhasePeriod t), ‖P x‖ ^ 2) =
      horizontalLeadingEnergy S c t mStar := by
    unfold horizontalLeadingEnergy
    simpa only [zero_add] using hshift
  rw [intervalIntegral.integral_ofReal, hreal]

theorem tendsto_real_exp_neg_mul_atTop_zero {d : ℝ} (hd : 0 < d) :
    Tendsto (fun x : ℝ => Real.exp (-(d * x))) atTop (nhds 0) := by
  have hlin : Tendsto (fun x : ℝ => x * (-d)) atTop atBot :=
    by simpa [mul_comm] using
      tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.mpr hd)
  convert Real.tendsto_exp_atBot.comp hlin using 1
  funext x
  congr 1
  ring

def horizontalLeadingRemainder
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (a t : ℝ) (mStar : ℤ) (x : ℝ) : ℂ :=
  ∑ m ∈ M.erase mStar,
    Complex.exp (((((m : ℝ) - (mStar : ℝ)) * a * x : ℝ) : ℂ)) *
      horizontalGradeProfile S c t m x *
      horizontalConjugateProfile S c t mStar x

theorem tendsto_horizontalLowerGradeTerm_zero
    {S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t : ℝ} {m mStar : ℤ}
    (ha : 0 < a) (hm : m < mStar) :
    Tendsto (fun x : ℝ =>
      Complex.exp (((((m : ℝ) - (mStar : ℝ)) * a * x : ℝ) : ℂ)) *
        horizontalGradeProfile S c t m x *
        horizontalConjugateProfile S c t mStar x) atTop (nhds 0) := by
  let d : ℝ := ((mStar : ℝ) - (m : ℝ)) * a
  let K : ℝ := horizontalProfileNormSum S c m *
    horizontalProfileNormSum S c mStar
  have hmc : (m : ℝ) < (mStar : ℝ) := by exact_mod_cast hm
  have hd : 0 < d := mul_pos (sub_pos.mpr hmc) ha
  have hK : 0 ≤ K := by
    dsimp [K]
    unfold horizontalProfileNormSum
    positivity
  have hdec : Tendsto (fun x : ℝ => Real.exp (-(d * x)) * K) atTop (nhds 0) := by
    simpa using (tendsto_real_exp_neg_mul_atTop_zero hd).mul_const K
  rw [Metric.tendsto_atTop] at hdec ⊢
  intro ε hε
  obtain ⟨H, hH⟩ := hdec ε hε
  refine ⟨H, fun x hx => ?_⟩
  rw [dist_zero_right]
  have hterm : ‖Complex.exp
      (((((m : ℝ) - (mStar : ℝ)) * a * x : ℝ) : ℂ)) *
        horizontalGradeProfile S c t m x *
        horizontalConjugateProfile S c t mStar x‖ ≤
      Real.exp (-(d * x)) * K := by
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have hre :
        (((((m : ℝ) - (mStar : ℝ)) * a * x : ℝ) : ℂ)).re = -(d * x) := by
      simp only [Complex.ofReal_re]
      dsimp [d]
      ring
    rw [hre]
    change Real.exp (-(d * x)) * ‖horizontalGradeProfile S c t m x‖ *
        ‖horizontalConjugateProfile S c t mStar x‖ ≤
      Real.exp (-(d * x)) *
        (horizontalProfileNormSum S c m * horizontalProfileNormSum S c mStar)
    have hsumM : 0 ≤ horizontalProfileNormSum S c m := by
      unfold horizontalProfileNormSum
      positivity
    calc
      Real.exp (-(d * x)) * ‖horizontalGradeProfile S c t m x‖ *
          ‖horizontalConjugateProfile S c t mStar x‖ ≤
          (Real.exp (-(d * x)) * horizontalProfileNormSum S c m) *
            horizontalProfileNormSum S c mStar :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left
            (norm_horizontalGradeProfile_le S c t m x) (Real.exp_pos _).le)
          (norm_horizontalConjugateProfile_le S c t mStar x)
          (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le hsumM)
      _ = Real.exp (-(d * x)) *
          (horizontalProfileNormSum S c m * horizontalProfileNormSum S c mStar) := by
        ring
  exact lt_of_le_of_lt hterm (by
    have := hH x hx
    rw [Real.dist_eq, sub_zero, abs_of_nonneg
      (mul_nonneg (Real.exp_pos _).le hK)] at this
    exact this)

theorem tendsto_horizontalLeadingRemainder_zero
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t : ℝ} {mStar : ℤ}
    (ha : 0 < a) (hM : ∀ m ∈ M, m ≤ mStar) :
    Tendsto (horizontalLeadingRemainder M S c a t mStar) atTop (nhds 0) := by
  classical
  unfold horizontalLeadingRemainder
  have hsum : Tendsto (fun x : ℝ =>
      ∑ m ∈ M.erase mStar,
        Complex.exp (((((m : ℝ) - (mStar : ℝ)) * a * x : ℝ) : ℂ)) *
          horizontalGradeProfile S c t m x *
          horizontalConjugateProfile S c t mStar x)
      atTop (nhds (∑ m ∈ M.erase mStar, (0 : ℂ))) :=
    tendsto_finsetSum (M.erase mStar) (fun m hm => by
      have hmM := Finset.mem_of_mem_erase hm
      have hmne := Finset.ne_of_mem_erase hm
      exact tendsto_horizontalLowerGradeTerm_zero
        (S := S) (c := c) (a := a) (t := t) ha
        (lt_of_le_of_ne (hM m hmM) hmne))
  simpa using hsum

theorem horizontalLeadingTest_mul_exp_eq_energy_add_remainder
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t : ℝ} {mStar : ℤ}
    (hstar : mStar ∈ M) (x : ℝ) :
    horizontalLeadingTest M S c a t mStar x * ((Real.exp x : ℝ) : ℂ) =
      ((‖horizontalGradeProfile S c t mStar x‖ ^ 2 : ℝ) : ℂ) +
        horizontalLeadingRemainder M S c a t mStar x := by
  classical
  rw [horizontalLeadingTest_mul_exp_eq_gradeSum]
  let f : ℤ → ℂ := fun m => Complex.exp
      (((((m : ℝ) - (mStar : ℝ)) * a * x : ℝ) : ℂ)) *
    horizontalGradeProfile S c t m x *
    horizontalConjugateProfile S c t mStar x
  have hsplit := Finset.sum_erase_add M f hstar
  rw [← hsplit]
  dsimp [f]
  unfold horizontalLeadingRemainder
  rw [horizontalLeadingGradeTerm]
  ring

theorem horizontalLeadingContinuumWindow_eq_energy_add_remainder
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t H : ℝ} {mStar : ℤ}
    (hstar : mStar ∈ M) :
    horizontalLeadingContinuumWindow M S c a t mStar H (horizontalPhasePeriod t) =
      ((horizontalLeadingEnergy S c t mStar : ℝ) : ℂ) +
        ∫ x in H..(H + horizontalPhasePeriod t),
          horizontalLeadingRemainder M S c a t mStar x := by
  unfold horizontalLeadingContinuumWindow
  rw [intervalIntegral.integral_congr
    (fun x hx => horizontalLeadingTest_mul_exp_eq_energy_add_remainder hstar x)]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral_horizontalLeadingGrade_eq_energy]
  · apply Continuous.intervalIntegrable
    unfold horizontalGradeProfile GaloisForLFunctions.HTGeometry.trigPoly
    fun_prop
  · apply Continuous.intervalIntegrable
    unfold horizontalLeadingRemainder
    apply continuous_finsetSum
    intro m hm
    have h₁ : Continuous (fun x : ℝ => Complex.exp
        (((((m : ℝ) - (mStar : ℝ)) * a * x : ℝ) : ℂ))) := by
      fun_prop
    have h₂ : Continuous (horizontalGradeProfile S c t m) := by
      unfold horizontalGradeProfile
      exact GaloisForLFunctions.HTGeometry.continuous_trigPoly S (c m) t
    have h₃ : Continuous (horizontalConjugateProfile S c t mStar) := by
      unfold horizontalConjugateProfile horizontalGradeProfile
      exact GaloisForLFunctions.HTGeometry.continuous_trigPoly S
        (horizontalConjugateCoefficients c mStar) (-t)
    exact (h₁.mul h₂).mul h₃

theorem tendsto_horizontalLeadingContinuumWindow_energy
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t : ℝ} {mStar : ℤ}
    (ha : 0 < a) (hM : ∀ m ∈ M, m ≤ mStar) (hstar : mStar ∈ M) :
    Tendsto (fun H : ℝ => horizontalLeadingContinuumWindow M S c a t mStar H
      (horizontalPhasePeriod t)) atTop
      (nhds ((horizontalLeadingEnergy S c t mStar : ℝ) : ℂ)) := by
  have hrem := tendsto_horizontalLeadingRemainder_zero
    (M := M) (S := S) (c := c) (a := a) (t := t) ha hM
  have hremInt := intervalIntegral_forwardWindow_tendsto_zero hrem
    (horizontalPhasePeriod_pos t).le
  have hconst : Tendsto
      (fun _ : ℝ => ((horizontalLeadingEnergy S c t mStar : ℝ) : ℂ))
      atTop (nhds ((horizontalLeadingEnergy S c t mStar : ℝ) : ℂ)) :=
    tendsto_const_nhds
  have hlim := hconst.add hremInt
  have hlim0 : Tendsto (fun H : ℝ =>
      ((horizontalLeadingEnergy S c t mStar : ℝ) : ℂ) +
        ∫ x in H..(H + horizontalPhasePeriod t),
          horizontalLeadingRemainder M S c a t mStar x) atTop
      (nhds ((horizontalLeadingEnergy S c t mStar : ℝ) : ℂ)) := by
    simpa using hlim
  apply hlim0.congr'
  filter_upwards with H
  exact (horizontalLeadingContinuumWindow_eq_energy_add_remainder hstar).symm

theorem tendsto_horizontalLeadingPrimeWindowSum_energy
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t : ℝ} {mStar : ℤ}
    (ha : 0 < a) (hM : ∀ m ∈ M, m ≤ mStar) (hstar : mStar ∈ M) :
    Tendsto (fun H : ℝ => horizontalLeadingPrimeWindowSum M S c a t mStar H
      (horizontalPhasePeriod t)) atTop
      (nhds ((horizontalLeadingEnergy S c t mStar : ℝ) : ℂ)) := by
  have hdefect := tendsto_horizontalLeadingQuadratureDefect_zero
    (M := M) (S := S) (c := c) (a := a) (t := t)
    (L := horizontalPhasePeriod t) (mStar := mStar) ha.le
    (horizontalPhasePeriod_pos t).le hM
  have hcontinuum := tendsto_horizontalLeadingContinuumWindow_energy
    (M := M) (S := S) (c := c) (a := a) (t := t) ha hM hstar
  have hlim := hdefect.add hcontinuum
  have hlim0 : Tendsto (fun H : ℝ =>
      horizontalLeadingQuadratureDefect M S c a t mStar H (horizontalPhasePeriod t) +
        horizontalLeadingContinuumWindow M S c a t mStar H (horizontalPhasePeriod t))
      atTop (nhds ((horizontalLeadingEnergy S c t mStar : ℝ) : ℂ)) := by
    simpa using hlim
  apply hlim0.congr'
  filter_upwards with H
  unfold horizontalLeadingQuadratureDefect
  ring

theorem tendsto_id_add_mul_exp_neg_mul_atTop_zero {r L K : ℝ} (hr : 0 < r) :
    Tendsto (fun H : ℝ => K * (H + L) * Real.exp (-(r * H)))
      atTop (nhds 0) := by
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.const_mul_atTop hr)
  have hscaled := hbase.const_mul (K / r)
  have hexp := tendsto_real_exp_neg_mul_atTop_zero hr
  have hconst := hexp.const_mul (K * L)
  have hsum := hscaled.add hconst
  have hsum0 : Tendsto (fun H : ℝ =>
      K / r * ((fun x : ℝ => x ^ 1 * Real.exp (-x)) (r * H)) +
        K * L * Real.exp (-(r * H))) atTop (nhds 0) := by
    simpa [Function.comp_def] using hsum
  apply hsum0.congr'
  filter_upwards with H
  simp only [pow_one]
  have hr0 : r ≠ 0 := hr.ne'
  rw [Real.exp_neg]
  field_simp

theorem norm_log_mul_horizontalLeadingTest_on_prime_le
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t H T : ℝ} {mStar : ℤ} {p : ℕ}
    (ha : 0 < a) (hmStar : 0 < mStar) (hp : p ∈ primeLogWindow H T) :
    ‖((Real.log p : ℝ) : ℂ) *
        horizontalLeadingTest M S c a t mStar (Real.log p)‖ ≤
      Real.exp (-(((mStar : ℝ) * a) * H)) *
        horizontalProfileNormSum S c mStar *
        (Real.log p / p * absField (horizontalPrimeExponentialField M S c a t) p) := by
  have hpprime : p.Prime := (mem_primeLogWindow.1 hp).2
  have hlogH : H < Real.log p := primeLogWindow_log_lt hp
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.pos
  have hp2 : (2 : ℕ) ≤ p := hpprime.two_le
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.one_le
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp1R
  let r : ℝ := (mStar : ℝ) * a
  have hmR : (0 : ℝ) < (mStar : ℝ) := by exact_mod_cast hmStar
  have hr : 0 < r := mul_pos hmR ha
  have hdamp : Real.exp (-((((mStar : ℝ) * a + 1) * Real.log p))) =
      Real.exp (-(r * Real.log p)) / (p : ℝ) := by
    have hexplog : Real.exp (-(Real.log p)) = 1 / (p : ℝ) := by
      rw [Real.exp_neg, Real.exp_log hpR]
      simp [one_div]
    rw [show -((((mStar : ℝ) * a + 1) * Real.log p)) =
        -(r * Real.log p) + (-(Real.log p)) by
      dsimp [r]
      ring, Real.exp_add, hexplog]
    simp [div_eq_mul_inv]
  have hdec : Real.exp (-(r * Real.log p)) ≤ Real.exp (-(r * H)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hprof := norm_horizontalConjugateProfile_le S c t mStar (Real.log p)
  have hfield := horizontalPrimeExponentialField_on_prime M S c a t hpprime
  unfold horizontalLeadingTest
  rw [← hfield]
  rw [norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0,
    abs_of_pos (Real.exp_pos _)]
  rw [hdamp]
  let W : ℝ := Real.log p / p *
    absField (horizontalPrimeExponentialField M S c a t) p
  have hW : 0 ≤ W := by
    dsimp [W, absField]
    positivity
  have heq : Real.log p *
      (Real.exp (-(r * Real.log p)) / (p : ℝ) *
        ‖horizontalPrimeExponentialField M S c a t p‖) *
        ‖horizontalConjugateProfile S c t mStar (Real.log p)‖ =
      (Real.exp (-(r * Real.log p)) *
        ‖horizontalConjugateProfile S c t mStar (Real.log p)‖) * W := by
    dsimp [W, absField]
    field_simp
  rw [show Real.log p *
      (Real.exp (-(r * Real.log p)) / (p : ℝ) *
        ‖horizontalPrimeExponentialField M S c a t p‖ *
        ‖horizontalConjugateProfile S c t mStar (Real.log p)‖) =
      Real.log p *
        (Real.exp (-(r * Real.log p)) / (p : ℝ) *
          ‖horizontalPrimeExponentialField M S c a t p‖) *
        ‖horizontalConjugateProfile S c t mStar (Real.log p)‖ by ring,
    heq]
  change (Real.exp (-(r * Real.log p)) *
      ‖horizontalConjugateProfile S c t mStar (Real.log p)‖) * W ≤
    (Real.exp (-(r * H)) * horizontalProfileNormSum S c mStar) * W
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hdec hprof (norm_nonneg _)
      (Real.exp_pos _).le) hW

theorem norm_horizontalLeadingPrimeWindowSum_le_of_marcinkiewicz_bound
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t H L : ℝ} {mStar : ℤ}
    (ha : 0 < a) (hmStar : 0 < mStar) (hL : 0 ≤ L)
    (hH : Real.log 2 ≤ H)
    (C₀ : ℝ)
    (hC₀ : ∀ X : ℕ, 2 ≤ X →
      marcinkiewiczLogQuotient
        (absField (horizontalPrimeExponentialField M S c a t)) X ≤ C₀) :
    ‖horizontalLeadingPrimeWindowSum M S c a t mStar H L‖ ≤
      (horizontalProfileNormSum S c mStar * |C₀|) * (H + L) *
        Real.exp (-(((mStar : ℝ) * a) * H)) := by
  classical
  let X : ℕ := ⌊Real.exp (H + L)⌋₊
  have htwoExp : (2 : ℝ) ≤ Real.exp (H + L) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    linarith
  have hX : (2 : ℕ) ≤ X := by
    dsimp [X]
    exact Nat.le_floor htwoExp
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hX)
  have hlogX : Real.log X ≤ H + L := by
    apply (Real.log_le_iff_le_exp hXpos).2
    exact Nat.floor_le (Real.exp_pos _).le
  let b : ℕ → ℂ := horizontalPrimeExponentialField M S c a t
  let w : ℕ → ℝ := fun p => Real.log p / p * absField b p
  have hsubset : primeLogWindow H (H + L) ⊆
      (Finset.Icc 1 X).filter (fun p => p.Prime) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hmem := mem_primeLogWindow.1 hp
    exact ⟨⟨hmem.2.one_le, hmem.1.2⟩, hmem.2⟩
  have hwindowMass : (∑ p ∈ primeLogWindow H (H + L), w p) ≤
      primeLogMass_weightedEulerCoefficientSpaces (absField b) X := by
    unfold primeLogMass_weightedEulerCoefficientSpaces
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun p : ℕ => Real.log p / (p : ℝ) * absField b p) hsubset
      (fun p hp hpn => by
        have hponeN : 1 ≤ p := (Finset.mem_Icc.1 (Finset.mem_filter.1 hp).1).1
        have hponeR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hponeN
        exact mul_nonneg (div_nonneg (Real.log_nonneg hponeR) (Nat.cast_nonneg p))
          (absField_nonneg b p))
    simpa only [w, abs_of_nonneg (absField_nonneg b _)] using hsub
  have hmass : primeLogMass_weightedEulerCoefficientSpaces (absField b) X ≤ |C₀| * Real.log X := by
    have hq := hC₀ X hX
    unfold marcinkiewiczLogQuotient at hq
    have hq' : primeLogMass_weightedEulerCoefficientSpaces (absField b) X ≤ C₀ * Real.log X := by
      exact (div_le_iff₀ (log_cutoff_pos hX)).mp hq
    have hXone : (1 : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast (le_trans (by omega : (1 : ℕ) ≤ 2) hX)
    exact hq'.trans (mul_le_mul_of_nonneg_right (le_abs_self C₀)
      (Real.log_nonneg hXone))
  let A : ℝ := Real.exp (-(((mStar : ℝ) * a) * H)) *
    horizontalProfileNormSum S c mStar
  have hA : 0 ≤ A := by
    dsimp [A]
    unfold horizontalProfileNormSum
    positivity
  unfold horizontalLeadingPrimeWindowSum
  calc
    ‖∑ p ∈ primeLogWindow H (H + L), ((Real.log p : ℝ) : ℂ) *
        horizontalLeadingTest M S c a t mStar (Real.log p)‖ ≤
        ∑ p ∈ primeLogWindow H (H + L),
          ‖((Real.log p : ℝ) : ℂ) *
            horizontalLeadingTest M S c a t mStar (Real.log p)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ primeLogWindow H (H + L), A * w p := by
      apply Finset.sum_le_sum
      intro p hp
      exact norm_log_mul_horizontalLeadingTest_on_prime_le ha hmStar hp
    _ = A * ∑ p ∈ primeLogWindow H (H + L), w p := by
      rw [Finset.mul_sum]
    _ ≤ A * primeLogMass_weightedEulerCoefficientSpaces (absField b) X :=
      mul_le_mul_of_nonneg_left hwindowMass hA
    _ ≤ A * (|C₀| * Real.log X) :=
      mul_le_mul_of_nonneg_left hmass hA
    _ ≤ A * (|C₀| * (H + L)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlogX (abs_nonneg C₀)) hA
    _ = (horizontalProfileNormSum S c mStar * |C₀|) * (H + L) *
        Real.exp (-(((mStar : ℝ) * a) * H)) := by
      dsimp [A]
      ring

theorem norm_horizontalLeadingPrimeWindowSum_le_of_memMarcinkiewicz
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t H L : ℝ} {mStar : ℤ}
    (ha : 0 < a) (hmStar : 0 < mStar) (hL : 0 ≤ L)
    (hH : Real.log 2 ≤ H)
    (hb : MemMarcinkiewiczLogLayer
      (absField (horizontalPrimeExponentialField M S c a t))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖horizontalLeadingPrimeWindowSum M S c a t mStar H L‖ ≤
        C * (H + L) * Real.exp (-(((mStar : ℝ) * a) * H)) := by
  obtain ⟨C₀, hC₀⟩ := hb
  refine ⟨horizontalProfileNormSum S c mStar * |C₀|, ?_, ?_⟩
  · unfold horizontalProfileNormSum
    positivity
  · exact norm_horizontalLeadingPrimeWindowSum_le_of_marcinkiewicz_bound
      ha hmStar hL hH C₀ hC₀

theorem tendsto_horizontalLeadingPrimeWindowSum_zero_of_memMarcinkiewicz
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t : ℝ} {mStar : ℤ}
    (ha : 0 < a) (hmStar : 0 < mStar)
    (hb : MemMarcinkiewiczLogLayer
      (absField (horizontalPrimeExponentialField M S c a t))) :
    Tendsto (fun H : ℝ => horizontalLeadingPrimeWindowSum M S c a t mStar H
      (horizontalPhasePeriod t)) atTop (nhds 0) := by
  obtain ⟨C₀, hC₀⟩ := hb
  let K : ℝ := horizontalProfileNormSum S c mStar * |C₀|
  have hmReal : 0 < (mStar : ℝ) := by exact_mod_cast hmStar
  have hr : 0 < (mStar : ℝ) * a := mul_pos hmReal ha
  have hmajor := tendsto_id_add_mul_exp_neg_mul_atTop_zero
    (L := horizontalPhasePeriod t) (K := K) hr
  apply tendsto_zero_iff_norm_tendsto_zero.2
  refine squeeze_zero' (Filter.Eventually.of_forall (fun H => norm_nonneg _)) ?_ hmajor
  filter_upwards [eventually_ge_atTop (Real.log 2)] with H hH
  simpa only [K] using
    norm_horizontalLeadingPrimeWindowSum_le_of_marcinkiewicz_bound
      (M := M) (S := S) (c := c) (a := a) (t := t) (mStar := mStar)
      ha hmStar (horizontalPhasePeriod_pos t).le hH C₀ hC₀

theorem horizontalPrimeExponentialField_not_memMarcinkiewiczLogLayer_of_positive_leading
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t : ℝ} {mStar : ℤ}
    (ha : 0 < a) (hmStar : 0 < mStar)
    (hM : ∀ m ∈ M, m ≤ mStar) (hstar : mStar ∈ M)
    (hnonzero : ∃ x ∈ Set.Ioo (0 : ℝ) (horizontalPhasePeriod t),
      horizontalGradeProfile S c t mStar x ≠ 0) :
    ¬ MemMarcinkiewiczLogLayer
      (absField (horizontalPrimeExponentialField M S c a t)) := by
  intro hb
  have hzero := tendsto_horizontalLeadingPrimeWindowSum_zero_of_memMarcinkiewicz
    (M := M) (S := S) (c := c) (a := a) (t := t) (mStar := mStar)
    ha hmStar hb
  have henergy := tendsto_horizontalLeadingPrimeWindowSum_energy
    (M := M) (S := S) (c := c) (a := a) (t := t) (mStar := mStar)
    ha hM hstar
  have heq : ((horizontalLeadingEnergy S c t mStar : ℝ) : ℂ) = 0 :=
    tendsto_nhds_unique henergy hzero
  have henergyZero : horizontalLeadingEnergy S c t mStar = 0 := by
    exact Complex.ofReal_injective heq
  exact (horizontalLeadingEnergy_pos hnonzero).ne' henergyZero

theorem exists_ne_zero_mem_Ioo_of_continuous_periodic
    {f : ℝ → ℂ} {L : ℝ} (hcont : Continuous f) (hL : 0 < L)
    (hper : Function.Periodic f L) (hne : ∃ x : ℝ, f x ≠ 0) :
    ∃ y ∈ Set.Ioo (0 : ℝ) L, f y ≠ 0 := by
  obtain ⟨x, hx⟩ := hne
  let y : ℝ := L * Int.fract (x / L)
  have hy0 : 0 ≤ y := mul_nonneg hL.le (Int.fract_nonneg _)
  have hyL : y < L := by
    have := Int.fract_lt_one (x / L)
    nlinarith
  have hxy : x = y + (⌊x / L⌋ : ℝ) * L := by
    have hfrac := Int.floor_add_fract (x / L)
    calc
      x = (x / L) * L := by field_simp
      _ = ((⌊x / L⌋ : ℝ) + Int.fract (x / L)) * L := by rw [hfrac]
      _ = y + (⌊x / L⌋ : ℝ) * L := by dsimp [y]; ring
  have hfy : f y ≠ 0 := by
    have hshift := (hper.int_mul ⌊x / L⌋) y
    rw [← hxy] at hshift
    exact fun hy => hx (hshift.trans hy)
  by_cases hypos : 0 < y
  · exact ⟨y, ⟨hypos, hyL⟩, hfy⟩
  · have hyzero : y = 0 := le_antisymm (not_lt.mp hypos) hy0
    have hfzero : f 0 ≠ 0 := by simpa only [hyzero] using hfy
    have hopen : IsOpen {z : ℝ | f z ≠ 0} := by
      have hclosed : IsClosed {z : ℝ | f z = 0} :=
        isClosed_singleton.preimage hcont
      simpa only [Set.compl_setOf] using hclosed.isOpen_compl
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen 0 hfzero
    let z : ℝ := min (L / 2) (ε / 2)
    have hzpos : 0 < z := by
      dsimp [z]
      positivity
    have hzL : z < L := by
      have hzle : z ≤ L / 2 := min_le_left _ _
      linarith
    have hzball : z ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hzle : z ≤ ε / 2 := min_le_right _ _
      rw [sub_zero, abs_of_pos hzpos]
      linarith
    exact ⟨z, ⟨hzpos, hzL⟩, hball hzball⟩

theorem exists_horizontalGradeProfile_ne_zero_mem_Ioo
    {S : Finset ℤ} {c : ℤ → ℤ → ℂ} {t : ℝ} {m : ℤ}
    (hne : ∃ x : ℝ, horizontalGradeProfile S c t m x ≠ 0) :
    ∃ x ∈ Set.Ioo (0 : ℝ) (horizontalPhasePeriod t),
      horizontalGradeProfile S c t m x ≠ 0 := by
  apply exists_ne_zero_mem_Ioo_of_continuous_periodic
    (f := horizontalGradeProfile S c t m)
  · unfold horizontalGradeProfile
    exact GaloisForLFunctions.HTGeometry.continuous_trigPoly S (c m) t
  · exact horizontalPhasePeriod_pos t
  · exact periodic_horizontalGradeProfile S c t m
  · exact hne

theorem horizontalPrimeExponentialField_not_memMarcinkiewiczLogLayer_of_positive_grade
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t : ℝ} {mStar : ℤ}
    (ha : 0 < a) (hmStar : 0 < mStar)
    (hM : ∀ m ∈ M, m ≤ mStar) (hstar : mStar ∈ M)
    (hnonzero : ∃ x : ℝ, horizontalGradeProfile S c t mStar x ≠ 0) :
    ¬ MemMarcinkiewiczLogLayer
      (absField (horizontalPrimeExponentialField M S c a t)) := by
  exact horizontalPrimeExponentialField_not_memMarcinkiewiczLogLayer_of_positive_leading
    ha hmStar hM hstar (exists_horizontalGradeProfile_ne_zero_mem_Ioo hnonzero)

/-- Corona class of the grade-zero part actually present in the finite grade support. -/
def horizontalGradeZeroPartClass
    (M S : Finset ℤ) (c : ℤ → ℤ → ℂ) (t : ℝ) :
    MarcinkiewiczLogQuotient :=
  if 0 ∈ M then horizontalGradeZeroClass S c t else 0

theorem horizontalPrimeExponentialClass_eq_gradeZeroPart
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t : ℝ}
    (ha : 0 < a) (hM : ∀ m ∈ M, m ≤ 0) :
    horizontalPrimeExponentialClass M S c a t ha.le hM =
      horizontalGradeZeroPartClass M S c t := by
  classical
  by_cases hzero : 0 ∈ M
  · rw [horizontalGradeZeroPartClass, if_pos hzero]
    exact horizontalPrimeExponentialClass_eq_gradeZero ha hM hzero
  · rw [horizontalGradeZeroPartClass, if_neg hzero]
    exact horizontalPrimeExponentialClass_eq_zero_of_negative ha (fun m hm => by
      have hmle := hM m hm
      have hmne : m ≠ 0 := fun h => hzero (h ▸ hm)
      omega)

/-- **Theorem A: leading horizontal-grade classification.** -/
theorem horizontalLeadingGradeClassification
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t : ℝ} {mStar : ℤ}
    (ha : 0 < a) (hM : ∀ m ∈ M, m ≤ mStar) (hstar : mStar ∈ M)
    (hnonzero : ∃ x : ℝ, horizontalGradeProfile S c t mStar x ≠ 0) :
    (mStar < 0 ∧ MemVanishingTailLayer
        (absField (horizontalPrimeExponentialField M S c a t))) ∨
      (mStar = 0 ∧ MemMarcinkiewiczLogLayer
          (absField (horizontalPrimeExponentialField M S c a t)) ∧
        ∃ hnonpos : ∀ m ∈ M, m ≤ 0,
          horizontalPrimeExponentialClass M S c a t ha.le hnonpos =
            horizontalGradeZeroClass S c t) ∨
      (0 < mStar ∧ ¬ MemMarcinkiewiczLogLayer
        (absField (horizontalPrimeExponentialField M S c a t))) := by
  rcases lt_trichotomy mStar 0 with hmneg | hmzero | hmpos
  · left
    exact ⟨hmneg, horizontalPrimeExponentialField_memVanishingTailLayer ha
      (fun m hm => lt_of_le_of_lt (hM m hm) hmneg)⟩
  · right; left
    have hmstar : mStar = 0 := hmzero
    subst mStar
    let hnonpos : ∀ m ∈ M, m ≤ 0 := hM
    refine ⟨rfl,
      horizontalPrimeExponentialField_memMarcinkiewiczLogLayer ha.le hnonpos,
      ⟨hnonpos, ?_⟩⟩
    exact horizontalPrimeExponentialClass_eq_gradeZero ha hnonpos hstar
  · right; right
    exact ⟨hmpos, horizontalPrimeExponentialField_not_memMarcinkiewiczLogLayer_of_positive_grade
      ha hmpos hM hstar hnonzero⟩

/-- **Theorem B: finite algebraic corona blindness.**  Any admitted finite field has no positive
leading grade, and its quotient class is exactly its grade-zero part, whose definition is
independent of horizontal displacement `a`. -/
theorem horizontalFiniteAlgebraicCoronaBlindness
    {M S : Finset ℤ} {c : ℤ → ℤ → ℂ} {a t : ℝ} {mStar : ℤ}
    (ha : 0 < a) (hM : ∀ m ∈ M, m ≤ mStar) (hstar : mStar ∈ M)
    (hnonzero : ∃ x : ℝ, horizontalGradeProfile S c t mStar x ≠ 0)
    (hb : MemMarcinkiewiczLogLayer
      (absField (horizontalPrimeExponentialField M S c a t))) :
    ∃ hnonpos : ∀ m ∈ M, m ≤ 0,
      horizontalPrimeExponentialClass M S c a t ha.le hnonpos =
        horizontalGradeZeroPartClass M S c t := by
  have hmStarNonpos : mStar ≤ 0 := by
    by_contra hnot
    have hmStarPos : 0 < mStar := lt_of_not_ge hnot
    exact (horizontalPrimeExponentialField_not_memMarcinkiewiczLogLayer_of_positive_grade
      ha hmStarPos hM hstar hnonzero) hb
  let hnonpos : ∀ m ∈ M, m ≤ 0 := fun m hm => (hM m hm).trans hmStarNonpos
  exact ⟨hnonpos, horizontalPrimeExponentialClass_eq_gradeZeroPart ha hnonpos⟩

/-! ## Exact FE--Schwarz polynomial and Laurent-monomial bookkeeping -/

theorem feSchwarzPoint_eq_horizontalShiftPoint (a t : ℝ) :
    feSchwarzPoint a t = horizontalShiftPoint a t (-1) (-1) := by
  apply Complex.ext <;> simp [feSchwarzPoint, horizontalShiftPoint, horizontalExponent]

theorem one_sub_feSchwarzPoint_eq_horizontalShiftPoint (a t : ℝ) :
    1 - feSchwarzPoint a t = horizontalShiftPoint a t 1 1 := by
  apply Complex.ext
  · simp [feSchwarzPoint, horizontalShiftPoint, horizontalExponent]
    ring
  · simp [feSchwarzPoint, horizontalShiftPoint, horizontalExponent]

theorem conj_feSchwarzPoint_eq_horizontalShiftPoint (a t : ℝ) :
    starRingEnd ℂ (feSchwarzPoint a t) =
      horizontalShiftPoint a t (-1) 1 := by
  apply Complex.ext <;> simp [feSchwarzPoint, horizontalShiftPoint, horizontalExponent]

theorem one_sub_conj_feSchwarzPoint_eq_horizontalShiftPoint (a t : ℝ) :
    1 - starRingEnd ℂ (feSchwarzPoint a t) =
      horizontalShiftPoint a t 1 (-1) := by
  apply Complex.ext
  · simp [feSchwarzPoint, horizontalShiftPoint, horizontalExponent]
    ring
  · simp [feSchwarzPoint, horizontalShiftPoint, horizontalExponent]

/-- Horizontal grade of a Laurent monomial in the ordered quartet
`rho, 1-rho, conj(rho), 1-conj(rho)`. -/
def feSchwarzLaurentHorizontalGrade (k₀ k₁ k₂ k₃ : ℤ) : ℤ :=
  -k₀ + k₁ - k₂ + k₃

/-- Vertical frequency of the same quartet Laurent monomial. -/
def feSchwarzLaurentVerticalFrequency (k₀ k₁ k₂ k₃ : ℤ) : ℤ :=
  -k₀ + k₁ + k₂ - k₃

def feSchwarzQuartetLaurentMonomial
    (a t : ℝ) (k₀ k₁ k₂ k₃ : ℤ) : ℕ → ℂ := fun p =>
  primeShiftCharacter (feSchwarzPoint a t) p ^ k₀ *
    primeShiftCharacter (1 - feSchwarzPoint a t) p ^ k₁ *
    primeShiftCharacter (starRingEnd ℂ (feSchwarzPoint a t)) p ^ k₂ *
    primeShiftCharacter (1 - starRingEnd ℂ (feSchwarzPoint a t)) p ^ k₃

/-- Every polynomial or Laurent-polynomial quartet monomial has an integral horizontal/vertical
lattice exponent.  Negative powers are legitimate on primes, where every character is nonzero. -/
theorem feSchwarzQuartetLaurentMonomial_on_prime
    (a t : ℝ) (k₀ k₁ k₂ k₃ : ℤ) {p : ℕ} (hp : p.Prime) :
    feSchwarzQuartetLaurentMonomial a t k₀ k₁ k₂ k₃ p =
      primeShiftCharacter
        (horizontalShiftPoint a t
          (feSchwarzLaurentHorizontalGrade k₀ k₁ k₂ k₃)
          (feSchwarzLaurentVerticalFrequency k₀ k₁ k₂ k₃)) p := by
  rw [feSchwarzQuartetLaurentMonomial,
    one_sub_feSchwarzPoint_eq_horizontalShiftPoint,
    one_sub_conj_feSchwarzPoint_eq_horizontalShiftPoint,
    conj_feSchwarzPoint_eq_horizontalShiftPoint,
    feSchwarzPoint_eq_horizontalShiftPoint,
    primeShiftCharacter_horizontalShiftPoint_on_prime a t (-1) (-1) hp,
    primeShiftCharacter_horizontalShiftPoint_on_prime a t 1 1 hp,
    primeShiftCharacter_horizontalShiftPoint_on_prime a t (-1) 1 hp,
    primeShiftCharacter_horizontalShiftPoint_on_prime a t 1 (-1) hp,
    primeShiftCharacter_horizontalShiftPoint_on_prime a t
      (feSchwarzLaurentHorizontalGrade k₀ k₁ k₂ k₃)
      (feSchwarzLaurentVerticalFrequency k₀ k₁ k₂ k₃) hp]
  rw [← Complex.exp_int_mul, ← Complex.exp_int_mul,
    ← Complex.exp_int_mul, ← Complex.exp_int_mul,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold feSchwarzLaurentHorizontalGrade feSchwarzLaurentVerticalFrequency
    horizontalExponent
  push_cast
  ring

/-- Boundary phase orbit is nowhere norm-continuous: all distinct nearby phases remain exactly
`4 / pi` apart in the quotient. -/
theorem criticalPrimePhaseClass_not_continuousAt (t : ℝ) :
    ¬ ContinuousAt criticalPrimePhaseClass t := by
  intro hcont
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hmap⟩ := hcont (2 / Real.pi) (by positivity)
  let u : ℝ := t + δ / 2
  have hut : u ≠ t := by
    dsimp [u]
    linarith
  have hdist : dist u t < δ := by
    rw [Real.dist_eq]
    dsimp [u]
    rw [show t + δ / 2 - t = δ / 2 by ring, abs_of_pos (by linarith)]
    linarith
  have himage := hmap hdist
  rw [dist_criticalPrimePhaseClass hut] at himage
  have hpi : 0 < Real.pi := Real.pi_pos
  have htwo : 0 < 2 / Real.pi := div_pos (by norm_num) hpi
  have hfour : 4 / Real.pi = 2 * (2 / Real.pi) := by ring
  rw [hfour] at himage
  linarith

end RHTower

end
