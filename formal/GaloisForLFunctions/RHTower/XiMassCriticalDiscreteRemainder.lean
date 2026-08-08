import GaloisForLFunctions.RHTower.XiMassCriticalOutgoingOpenCore
import GaloisForLFunctions.RHTower.PsiRemainderSignChange

/-!
# Discrete remainder form of the critical Xi mass outgoing current

The normalized continuous Chebyshev error on logarithmic time splits exactly into

`exp (-h/2) * R(floor (exp h))`

plus the elementary floor sawtooth, where `R(N) = psi(N) - N`.  Pairing this identity with the
actual Xi mass outgoing derivative produces two currents.  The sawtooth current is uniformly
bounded in vertical height because its coefficient has modulus at most `exp (-h/2)` and the
zero-shift outgoing derivative has a height-independent integral majorant.

Consequently the mass-shifted spectral-face open core is equivalent to uniform boundedness of the
raw *discrete* Selberg remainder current.  This is an unconditional proof-burden reduction: it
removes continuous interpolation and the floor error, but does not assume or prove the remaining
arithmetic cancellation.
-/

open Filter MeasureTheory Set Topology
open ArithmeticFunction Finset

namespace RHTower

noncomputable section

/-- Exact split of the logarithmic normalized Chebyshev error into the discrete Selberg remainder
and the floor sawtooth. -/
theorem criticalMellinNormalizedChebyshevError_eq_discrete_add_floor (h : ℝ) :
    criticalMellinNormalizedChebyshevError h =
      Real.exp (-h / 2) * psiRemainder ⌊Real.exp h⌋₊ +
        Real.exp (-h / 2) * (⌊Real.exp h⌋₊ - Real.exp h) := by
  let N : ℕ := ⌊Real.exp h⌋₊
  have hpsi :
      criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp h) =
        chebyshevPsi N := by
    rw [criticalCumulative_vonMangoldt_eq_psi, chebyshevPsi_eq_psi]
    unfold Chebyshev.psi
    simp only [N, Nat.floor_natCast]
  have hsqrt : Real.sqrt (Real.exp h) = Real.exp (h / 2) := by
    rw [← Real.exp_half]
  have hinv : (Real.exp (h / 2))⁻¹ = Real.exp (-h / 2) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [criticalMellinNormalizedChebyshevError, criticalMellinError, hpsi,
    psiRemainder, hsqrt, div_eq_mul_inv, hinv]
  dsimp only [N]
  ring

/-- The real floor error of `exp h` has modulus at most one. -/
theorem abs_natFloor_exp_sub_le_one (h : ℝ) :
    |(⌊Real.exp h⌋₊ : ℝ) - Real.exp h| ≤ 1 := by
  have hlo : (⌊Real.exp h⌋₊ : ℝ) ≤ Real.exp h :=
    Nat.floor_le (Real.exp_pos h).le
  have hhi : Real.exp h < (⌊Real.exp h⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
  linarith

/-- Raw discrete `psi - id` density paired with the actual Xi mass outgoing derivative. -/
noncomputable def xiMassCriticalDiscreteRemainderDensity (a sigma u h : ℝ) : ℂ :=
  ((Real.exp (-h / 2) * psiRemainder ⌊Real.exp h⌋₊ : ℝ) : ℂ) *
    xiMassCriticalOutgoingDerivative a sigma u h

/-- Elementary floor-sawtooth density left by replacing `exp h` with its natural floor. -/
noncomputable def xiMassCriticalFloorSawtoothDensity (a sigma u h : ℝ) : ℂ :=
  ((Real.exp (-h / 2) * ((⌊Real.exp h⌋₊ : ℝ) - Real.exp h) : ℝ) : ℂ) *
    xiMassCriticalOutgoingDerivative a sigma u h

/-- Infinite discrete Selberg-remainder current. -/
noncomputable def xiMassCriticalDiscreteRemainderFlux (a sigma u : ℝ) : ℂ :=
  ∫ h in Ioi (0 : ℝ), xiMassCriticalDiscreteRemainderDensity a sigma u h

/-- Infinite floor-sawtooth current. -/
noncomputable def xiMassCriticalFloorSawtoothFlux (a sigma u : ℝ) : ℂ :=
  ∫ h in Ioi (0 : ℝ), xiMassCriticalFloorSawtoothDensity a sigma u h

/-- Height-independent zero-strip-shift majorant for the outgoing derivative. -/
noncomputable def xiMassCriticalOutgoingZeroShiftBound (sigma : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∫ x : ℝ, Real.exp (-(sigma * |x|))) +
    ∫ x : ℝ, |x| * Real.exp (-(sigma * |x|))

theorem xiMassCriticalOutgoingZeroShiftBound_nonneg (sigma : ℝ) :
    0 ≤ xiMassCriticalOutgoingZeroShiftBound sigma := by
  unfold xiMassCriticalOutgoingZeroShiftBound
  exact add_nonneg
    (mul_nonneg (by norm_num) (integral_nonneg fun _ => Real.exp_nonneg _))
    (integral_nonneg fun x => mul_nonneg (abs_nonneg x) (Real.exp_nonneg _))

/-- Actual integral-kernel estimate at zero strip shift, uniform in height and frequency. -/
theorem norm_xiMassCriticalOutgoingDerivative_le_zeroShift
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u h : ℝ) :
    ‖xiMassCriticalOutgoingDerivative a sigma u h‖ ≤
      xiMassCriticalOutgoingZeroShiftBound sigma := by
  have hD := norm_xiMassCriticalOutgoingDerivative_deepShift_le
    (a := a) (sigma := sigma) (d := 0) (by norm_num) ha hsigma u h
  simpa [xiMassCriticalOutgoingZeroShiftBound] using hD

theorem continuous_xiMassCriticalOutgoingDerivative
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u : ℝ) :
    Continuous (xiMassCriticalOutgoingDerivative a sigma u) := by
  change Continuous (fun h : ℝ =>
    (1 / 2 : ℂ) *
        stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * Complex.I)) (h : ℂ) -
      xiMassFourierDerivative a sigma u h)
  apply Continuous.sub
  · apply Continuous.const_mul
    rw [continuous_iff_continuousAt]
    intro h
    exact (hasDerivAt_xiMassRealFourierProfile ha hsigma u h).continuousAt
  · exact continuous_xiMassFourierDerivative ha hsigma u

theorem measurable_xiMassCriticalFloorSawtoothCoefficient :
    Measurable (fun h : ℝ =>
      ((Real.exp (-h / 2) * ((⌊Real.exp h⌋₊ : ℝ) - Real.exp h) : ℝ) : ℂ)) := by
  apply Complex.continuous_ofReal.measurable.comp
  have hfloor : Measurable (fun h : ℝ => (⌊Real.exp h⌋₊ : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      Real.measurable_exp.nat_floor
  exact ((Real.continuous_exp.comp (by fun_prop)).measurable.mul
    (hfloor.sub Real.measurable_exp))

theorem integrableOn_xiMassCriticalFloorSawtoothDensity
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u : ℝ) :
    IntegrableOn (xiMassCriticalFloorSawtoothDensity a sigma u) (Ioi 0) := by
  let J : ℝ := xiMassCriticalOutgoingZeroShiftBound sigma
  have hJ : 0 ≤ J := xiMassCriticalOutgoingZeroShiftBound_nonneg sigma
  have hexp : IntegrableOn (fun h : ℝ => Real.exp ((-1 / 2 : ℝ) * h)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (show (-1 / 2 : ℝ) < 0 by norm_num) 0
  have hmajor : IntegrableOn
      (fun h : ℝ => J * Real.exp ((-1 / 2 : ℝ) * h)) (Ioi 0) :=
    hexp.const_mul J
  have hmeas : AEStronglyMeasurable
      (xiMassCriticalFloorSawtoothDensity a sigma u) :=
    (measurable_xiMassCriticalFloorSawtoothCoefficient.mul
      (continuous_xiMassCriticalOutgoingDerivative ha hsigma u).measurable).aestronglyMeasurable
  apply Integrable.mono' hmajor hmeas.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  rw [xiMassCriticalFloorSawtoothDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  have hfloor := abs_natFloor_exp_sub_le_one h
  have hD := norm_xiMassCriticalOutgoingDerivative_le_zeroShift ha hsigma u h
  calc
    Real.exp (-h / 2) * |(⌊Real.exp h⌋₊ : ℝ) - Real.exp h| *
          ‖xiMassCriticalOutgoingDerivative a sigma u h‖ ≤
        Real.exp (-h / 2) * 1 *
          ‖xiMassCriticalOutgoingDerivative a sigma u h‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfloor (Real.exp_pos _).le) (norm_nonneg _)
    _ ≤ Real.exp (-h / 2) * 1 * J :=
      mul_le_mul_of_nonneg_left (by simpa only [J] using hD)
        (mul_nonneg (Real.exp_pos _).le zero_le_one)
    _ = J * Real.exp ((-1 / 2 : ℝ) * h) := by ring

/-- The entire floor-sawtooth current is uniformly bounded in vertical height. -/
theorem norm_xiMassCriticalFloorSawtoothFlux_le
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u : ℝ) :
    ‖xiMassCriticalFloorSawtoothFlux a sigma u‖ ≤
      2 * xiMassCriticalOutgoingZeroShiftBound sigma := by
  let J : ℝ := xiMassCriticalOutgoingZeroShiftBound sigma
  have hleft := (integrableOn_xiMassCriticalFloorSawtoothDensity ha hsigma u).norm
  have hexp : IntegrableOn (fun h : ℝ => Real.exp ((-1 / 2 : ℝ) * h)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (show (-1 / 2 : ℝ) < 0 by norm_num) 0
  have hright : IntegrableOn
      (fun h : ℝ => J * Real.exp ((-1 / 2 : ℝ) * h)) (Ioi 0) :=
    hexp.const_mul J
  have hmono :
      (∫ h in Ioi (0 : ℝ), ‖xiMassCriticalFloorSawtoothDensity a sigma u h‖) ≤
        ∫ h in Ioi (0 : ℝ), J * Real.exp ((-1 / 2 : ℝ) * h) := by
    apply integral_mono_ae hleft hright
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    rw [xiMassCriticalFloorSawtoothDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_pos (Real.exp_pos _)]
    have hfloor := abs_natFloor_exp_sub_le_one h
    have hD := norm_xiMassCriticalOutgoingDerivative_le_zeroShift ha hsigma u h
    calc
      Real.exp (-h / 2) * |(⌊Real.exp h⌋₊ : ℝ) - Real.exp h| *
            ‖xiMassCriticalOutgoingDerivative a sigma u h‖ ≤
          Real.exp (-h / 2) * 1 *
            ‖xiMassCriticalOutgoingDerivative a sigma u h‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfloor (Real.exp_pos _).le) (norm_nonneg _)
      _ ≤ Real.exp (-h / 2) * 1 * J :=
        mul_le_mul_of_nonneg_left (by simpa only [J] using hD)
          (mul_nonneg (Real.exp_pos _).le zero_le_one)
      _ = J * Real.exp ((-1 / 2 : ℝ) * h) := by ring
  calc
    ‖xiMassCriticalFloorSawtoothFlux a sigma u‖ ≤
        ∫ h in Ioi (0 : ℝ), ‖xiMassCriticalFloorSawtoothDensity a sigma u h‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ h in Ioi (0 : ℝ), J * Real.exp ((-1 / 2 : ℝ) * h) := hmono
    _ = J * 2 := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (show (-1 / 2 : ℝ) < 0 by norm_num) 0]
      norm_num
    _ = 2 * xiMassCriticalOutgoingZeroShiftBound sigma := by simp only [J]; ring

theorem xiMassCriticalOutgoingIntegrand_eq_discrete_add_floor
    (a sigma u h : ℝ) :
    (criticalMellinNormalizedChebyshevError h : ℂ) *
        xiMassCriticalOutgoingDerivative a sigma u h =
      xiMassCriticalDiscreteRemainderDensity a sigma u h +
        xiMassCriticalFloorSawtoothDensity a sigma u h := by
  rw [criticalMellinNormalizedChebyshevError_eq_discrete_add_floor]
  unfold xiMassCriticalDiscreteRemainderDensity xiMassCriticalFloorSawtoothDensity
  push_cast
  ring

theorem integrableOn_xiMassCriticalDiscreteRemainderDensity
    {a sigma : ℝ} (hhalf : 1 / 2 < a) (hsigma : 0 < sigma) (u : ℝ) :
    IntegrableOn (xiMassCriticalDiscreteRemainderDensity a sigma u) (Ioi 0) := by
  have hout := integrableOn_xiMassCriticalOutgoingFlux hhalf hsigma u
  have hsaw := integrableOn_xiMassCriticalFloorSawtoothDensity
    (lt_trans (by norm_num) hhalf) hsigma u
  have hsub := hout.sub hsaw
  refine hsub.congr_fun ?_ measurableSet_Ioi
  intro h _hh
  change
    (criticalMellinNormalizedChebyshevError h : ℂ) *
        xiMassCriticalOutgoingDerivative a sigma u h -
      xiMassCriticalFloorSawtoothDensity a sigma u h =
        xiMassCriticalDiscreteRemainderDensity a sigma u h
  rw [xiMassCriticalOutgoingIntegrand_eq_discrete_add_floor]
  ring

/-- Exact current split: only the discrete Selberg-remainder current can carry unbounded height
growth. -/
theorem xiMassCriticalOutgoingFlux_eq_discrete_add_floor
    {a sigma : ℝ} (hhalf : 1 / 2 < a) (hsigma : 0 < sigma) (u : ℝ) :
    xiMassCriticalOutgoingFlux a sigma u =
      xiMassCriticalDiscreteRemainderFlux a sigma u +
        xiMassCriticalFloorSawtoothFlux a sigma u := by
  have hdisc := integrableOn_xiMassCriticalDiscreteRemainderDensity hhalf hsigma u
  have hsaw := integrableOn_xiMassCriticalFloorSawtoothDensity
    (lt_trans (by norm_num) hhalf) hsigma u
  rw [xiMassCriticalOutgoingFlux, xiMassCriticalDiscreteRemainderFlux,
    xiMassCriticalFloorSawtoothFlux, ← integral_add hdisc hsaw]
  apply integral_congr_ae
  filter_upwards with h
  exact xiMassCriticalOutgoingIntegrand_eq_discrete_add_floor a sigma u h

/-- Uniform vertical bound for the raw discrete Selberg-remainder current. -/
def XiMassCriticalDiscreteRemainderFluxLineBound (a sigma : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, ‖xiMassCriticalDiscreteRemainderFlux a sigma u‖ ≤ C

/-- The bounded floor sawtooth can be removed from or restored to the outgoing current. -/
theorem xiMassCriticalOutgoingFluxLineBound_iff_discreteRemainderFluxLineBound
    {a sigma : ℝ} (hhalf : 1 / 2 < a) (hsigma : 0 < sigma) :
    XiMassCriticalOutgoingFluxLineBound a sigma ↔
      XiMassCriticalDiscreteRemainderFluxLineBound a sigma := by
  let B : ℝ := 2 * xiMassCriticalOutgoingZeroShiftBound sigma
  have hsaw : ∀ u : ℝ, ‖xiMassCriticalFloorSawtoothFlux a sigma u‖ ≤ B :=
    fun u => norm_xiMassCriticalFloorSawtoothFlux_le
      (lt_trans (by norm_num) hhalf) hsigma u
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u => ?_⟩
    have heq := xiMassCriticalOutgoingFlux_eq_discrete_add_floor hhalf hsigma u
    have hdisc : xiMassCriticalDiscreteRemainderFlux a sigma u =
        xiMassCriticalOutgoingFlux a sigma u -
          xiMassCriticalFloorSawtoothFlux a sigma u := by
      rw [heq]
      ring
    rw [hdisc]
    exact (norm_sub_le _ _).trans (add_le_add (hC u) (hsaw u))
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u => ?_⟩
    rw [xiMassCriticalOutgoingFlux_eq_discrete_add_floor hhalf hsigma u]
    exact (norm_add_le _ _).trans (add_le_add (hC u) (hsaw u))

/-- **Discrete exact open core.**  The mass-shifted spectral-face route now asks only for a uniform
bound on the raw discrete `psi(N) - N` current.  The continuous Chebyshev interpolation and its
floor sawtooth are no longer source obligations. -/
theorem riemannHypothesis_iff_xiMassCriticalDiscreteRemainderFluxLineBound
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) :
    RiemannHypothesis ↔ XiMassCriticalDiscreteRemainderFluxLineBound a sigma := by
  exact (riemannHypothesis_iff_xiMassCriticalOutgoingFluxLineBound
    hhalf hca hsigma).trans
      (xiMassCriticalOutgoingFluxLineBound_iff_discreteRemainderFluxLineBound
        (lt_trans hhalf hca) hsigma)

end

end RHTower
