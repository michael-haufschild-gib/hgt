import GaloisForLFunctions.HTGeometry.TorusTrigPolynomial
import GaloisForLFunctions.HTGeometry.WindowAverageApproximation
import GaloisForLFunctions.HTGeometry.CharacterLatticeFrequencyRank
import GaloisForLFunctions.HTGeometry.KroneckerWeylDensity
import GaloisForLFunctions.HTGeometry.TorusDerivationJets

/-!
# The Bohr coefficients of a quasiperiodic phase function

A character of the product torus becomes a pure exponential along the phase
flow, with frequency the detuning of the character against the frequency
family.  The Bohr mean of a pure exponential is the Kronecker delta of its
frequency, so the Bohr coefficients of a trigonometric polynomial along the
flow are its Fourier coefficients read at the corresponding detunings.

Uniform approximation transfers this to every phase observable: the Bohr
coefficient of the quasiperiodic function at a detuning is the corresponding
active coefficient, and it vanishes at every frequency which is not a detuning.
The Bohr spectrum of the quasiperiodic function is therefore the set of
detunings of its active characters.
-/

open Complex Set Filter Topology MeasureTheory

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance isProbabilityMeasureCirclePhaseBohr : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance isAddHaarMeasureCirclePhaseBohr : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### Rational independence is injectivity of the detuning -/

omit [DecidableEq d] in
theorem injective_finiteTorusCharacterDetuning {omega : d → ℝ}
    (h : RationallyIndependentFrequency omega) :
    Function.Injective fun m : d → ℤ => finiteTorusCharacterDetuning m omega := by
  intro a b hab
  have hsub : finiteTorusCharacterDetuning (a - b) omega = 0 := by
    rw [finiteTorusCharacterDetuning]
    have hsplit : ∀ i : d, ((a - b) i : ℝ) * omega i
        = (a i : ℝ) * omega i - (b i : ℝ) * omega i := by
      intro i
      show ((a i - b i : ℤ) : ℝ) * omega i = _
      push_cast
      ring
    rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_sub_distrib]
    have ha : ∑ i, (a i : ℝ) * omega i = finiteTorusCharacterDetuning a omega := rfl
    have hb : ∑ i, (b i : ℝ) * omega i = finiteTorusCharacterDetuning b omega := rfl
    have hab' : finiteTorusCharacterDetuning a omega
        = finiteTorusCharacterDetuning b omega := hab
    rw [ha, hb, hab', sub_self]
  exact sub_eq_zero.1 (h _ hsub)

/-! ### Characters along the phase flow -/

omit [DecidableEq d] in
theorem mFourier_finiteClockPhasePoint_expChar (m : d → ℤ) (omega : d → ℝ) (t : ℝ) :
    UnitAddTorus.mFourier m (finiteClockPhasePoint omega t)
      = expChar (finiteTorusCharacterDetuning m omega) t := by
  rw [mFourier_finiteClockPhasePoint, expChar,
    mul_comm (finiteTorusCharacterDetuning m omega) t]

/-! ### The quasiperiodic function on the real line -/

/-- The quasiperiodic function of a phase observable, on real time. -/
def realPhaseFunction (omega : d → ℝ) (F : (d → ℂ) → ℂ) : ℝ → ℂ :=
  fun t => phaseFunction omega F (t : ℂ)

omit [DecidableEq d] in
theorem realPhaseFunction_eq (omega : d → ℝ) (F : (d → ℂ) → ℂ) (t : ℝ) :
    realPhaseFunction omega F t = torusRestriction F (finiteClockPhasePoint omega t) := by
  rw [realPhaseFunction, phaseFunction, phasePoint_ofReal, torusRestriction,
    circleCoords_finiteClockPhasePoint]

omit [DecidableEq d] in
theorem continuous_realPhaseFunction {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) :
    Continuous (realPhaseFunction omega F) := by
  have hfun : realPhaseFunction omega F
      = fun t => torusRestriction F (finiteClockPhasePoint omega t) :=
    funext fun t => realPhaseFunction_eq omega F t
  rw [hfun]
  exact (continuous_torusRestriction hρ hF).comp
    (finiteClockPhasePoint_continuous omega)

/-! ### The window averages of a trigonometric polynomial along the flow -/

omit [DecidableEq d] in
theorem tendsto_windowAverage_trigPoly (c : (d → ℤ) →₀ ℂ) (omega : d → ℝ)
    (lam : ℝ) :
    Tendsto (windowAverage fun t =>
        torusTrigPoly c (finiteClockPhasePoint omega t) * bohrChar lam t) atTop
      (nhds (∑ m ∈ c.support,
        if finiteTorusCharacterDetuning m omega = lam then c m else 0)) := by
  classical
  have hfun : (fun t : ℝ =>
      torusTrigPoly c (finiteClockPhasePoint omega t) * bohrChar lam t)
      = fun t => ∑ m ∈ c.support,
        c m * expChar (finiteTorusCharacterDetuning m omega - lam) t := by
    funext t
    rw [torusTrigPoly, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mFourier_finiteClockPhasePoint_expChar, mul_assoc]
    have hchar : bohrChar lam t = expChar (-lam) t := by
      rw [expChar_eq_bohrChar, neg_neg]
    rw [hchar, expChar_add, ← sub_eq_add_neg]
  rw [hfun]
  have hwin : ∀ T : ℝ, windowAverage (fun t => ∑ m ∈ c.support,
      c m * expChar (finiteTorusCharacterDetuning m omega - lam) t) T
      = ∑ m ∈ c.support, c m *
        windowAverage (expChar (finiteTorusCharacterDetuning m omega - lam)) T := by
    intro T
    rw [windowAverage_finset_sum (g := fun m : d → ℤ => fun t : ℝ =>
        c m * expChar (finiteTorusCharacterDetuning m omega - lam) t)
      c.support (fun m _ => continuous_const.mul (continuous_expChar _)) T]
    exact Finset.sum_congr rfl fun m _ =>
      windowAverage_const_mul (c m) _ T
  refine Tendsto.congr (fun T => (hwin T).symm) ?_
  refine tendsto_finsetSum _ fun m _ => ?_
  have hlim : Tendsto (windowAverage
      (expChar (finiteTorusCharacterDetuning m omega - lam))) atTop
      (nhds (bohrMean (expChar (finiteTorusCharacterDetuning m omega - lam)))) :=
    tendsto_windowAverage_bohrMean (continuous_expChar _)
      (isBohrAlmostPeriodic_expChar _)
  rw [bohrMean_expChar] at hlim
  have hval : (c m * if finiteTorusCharacterDetuning m omega - lam = 0 then 1 else 0)
      = if finiteTorusCharacterDetuning m omega = lam then c m else 0 := by
    by_cases hm : finiteTorusCharacterDetuning m omega = lam
    · rw [if_pos (sub_eq_zero.2 hm), if_pos hm, mul_one]
    · rw [if_neg fun hc => hm (sub_eq_zero.1 hc), if_neg hm, mul_zero]
  rw [← hval]
  exact tendsto_const_nhds.mul hlim

/-! ### The Bohr coefficients of a quasiperiodic function -/

omit [DecidableEq d] in
/-- The core estimate: the window averages of the modulated quasiperiodic
function converge to any value approximated by the trigonometric coefficients
at the given frequency. -/
theorem tendsto_windowAverage_realPhaseFunction {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {lam : ℝ} {A : ℂ}
    (hcoef : ∀ (c : (d → ℤ) →₀ ℂ) (ε : ℝ), 0 < ε →
      (∀ x, ‖torusRestriction F x - torusTrigPoly c x‖ ≤ ε) →
      ‖(∑ m ∈ c.support,
        if finiteTorusCharacterDetuning m omega = lam then c m else 0) - A‖ ≤ ε) :
    Tendsto (windowAverage fun t => realPhaseFunction omega F t * bohrChar lam t)
      atTop (nhds A) := by
  refine tendsto_of_approx fun ε hε => ?_
  obtain ⟨c, hc⟩ := exists_torusTrigPoly_approx (torusRestrictionC hρ F hF) hε
  have hcx : ∀ x, ‖torusRestriction F x - torusTrigPoly c x‖ ≤ ε := hc
  refine ⟨windowAverage fun t =>
      torusTrigPoly c (finiteClockPhasePoint omega t) * bohrChar lam t,
    ∑ m ∈ c.support,
      if finiteTorusCharacterDetuning m omega = lam then c m else 0,
    ?_, hcoef c ε hε hcx, tendsto_windowAverage_trigPoly c omega lam⟩
  intro T
  have hcont1 : Continuous fun t : ℝ => realPhaseFunction omega F t * bohrChar lam t :=
    (continuous_realPhaseFunction hρ hF).mul (continuous_bohrChar lam)
  have hcont2 : Continuous fun t : ℝ =>
      torusTrigPoly c (finiteClockPhasePoint omega t) * bohrChar lam t :=
    ((continuous_torusTrigPoly c).comp
      (finiteClockPhasePoint_continuous omega)).mul (continuous_bohrChar lam)
  rw [← windowAverage_sub hcont1 hcont2 T]
  refine norm_windowAverage_le (fun t => ?_) T
  have hdiff : realPhaseFunction omega F t * bohrChar lam t
      - torusTrigPoly c (finiteClockPhasePoint omega t) * bohrChar lam t
      = (torusRestriction F (finiteClockPhasePoint omega t)
        - torusTrigPoly c (finiteClockPhasePoint omega t)) * bohrChar lam t := by
    rw [realPhaseFunction_eq, sub_mul]
  rw [hdiff, norm_mul, norm_bohrChar, mul_one]
  exact hcx _

/-- **The Bohr coefficient at a detuning is the active coefficient.** -/
theorem bohrCoefficient_realPhaseFunction {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (m : d → ℤ) :
    bohrCoefficient (realPhaseFunction omega F)
      (finiteTorusCharacterDetuning m omega) = activeCoeff F m := by
  classical
  refine bohrMean_eq_of_tendsto (tendsto_windowAverage_realPhaseFunction hρ hF ?_)
  intro c ε hε hcx
  have hsum : (∑ m' ∈ c.support,
      if finiteTorusCharacterDetuning m' omega
        = finiteTorusCharacterDetuning m omega then c m' else 0) = c m := by
    have hterm : ∀ m' ∈ c.support,
        (if finiteTorusCharacterDetuning m' omega
          = finiteTorusCharacterDetuning m omega then c m' else 0)
        = if m' = m then c m' else 0 := by
      intro m' _
      by_cases hm : m' = m
      · rw [if_pos hm, if_pos (by rw [hm])]
      · rw [if_neg hm, if_neg fun hc =>
          hm (injective_finiteTorusCharacterDetuning hindep hc)]
    rw [Finset.sum_congr rfl hterm]
    by_cases hmem : m ∈ c.support
    · rw [Finset.sum_ite_eq' c.support m c, if_pos hmem]
    · rw [Finset.sum_ite_eq' c.support m c, if_neg hmem]
      exact (Finsupp.notMem_support_iff.1 hmem).symm
  rw [hsum]
  have hcoeff : c m = UnitAddTorus.mFourierCoeff (torusTrigPoly c) m :=
    (mFourierCoeff_torusTrigPoly c m).symm
  rw [hcoeff, activeCoeff, ← mFourierCoeff_sub_torusTrigPolynomial (continuous_torusTrigPoly c)
    (continuous_torusRestriction hρ hF) m]
  refine norm_mFourierCoeff_le (fun x => ?_) m
  rw [← norm_neg, neg_sub]
  exact hcx x

omit [DecidableEq d] in
/-- **The Bohr coefficient vanishes off the detunings.** -/
theorem bohrCoefficient_realPhaseFunction_eq_zero {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {lam : ℝ}
    (hlam : ∀ m : d → ℤ, finiteTorusCharacterDetuning m omega ≠ lam) :
    bohrCoefficient (realPhaseFunction omega F) lam = 0 := by
  refine bohrMean_eq_of_tendsto (tendsto_windowAverage_realPhaseFunction hρ hF ?_)
  intro c ε hε _
  have hzero : (∑ m ∈ c.support,
      if finiteTorusCharacterDetuning m omega = lam then c m else 0) = 0 :=
    Finset.sum_eq_zero fun m _ => if_neg (hlam m)
  rw [hzero, sub_zero, norm_zero]
  exact le_of_lt hε

/-! ### The Bohr spectrum -/

/-- **The Bohr spectrum of a quasiperiodic function is the set of detunings of
its active characters.** -/
theorem bohrSpectrum_realPhaseFunction {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) :
    bohrSpectrum (realPhaseFunction omega F)
      = characterFrequencySet omega (activeSupport F) := by
  ext lam
  constructor
  · intro hlam
    by_cases hex : ∃ m : d → ℤ, finiteTorusCharacterDetuning m omega = lam
    · obtain ⟨m, hm⟩ := hex
      refine ⟨m, ?_, hm⟩
      have hco := bohrCoefficient_realPhaseFunction hρ hindep hF m
      rw [hm] at hco
      show activeCoeff F m ≠ 0
      rw [← hco]
      exact hlam
    · exact absurd (bohrCoefficient_realPhaseFunction_eq_zero hρ hF
        (fun m hm => hex ⟨m, hm⟩)) hlam
  · rintro ⟨m, hm, rfl⟩
    show bohrCoefficient (realPhaseFunction omega F)
      (finiteTorusCharacterDetuning m omega) ≠ 0
    rw [bohrCoefficient_realPhaseFunction hρ hindep hF m]
    exact hm

end

end GaloisForLFunctions.HTGeometry
