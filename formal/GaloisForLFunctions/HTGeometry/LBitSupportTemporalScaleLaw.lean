import GaloisForLFunctions.HTGeometry.LBitReplicaInteractionFractureLaw
import GaloisForLFunctions.HTGeometry.ObserverTemporalPhaseSupportLaw

/-!
# Support-resolved finite-time law for scaled l-bit spectra

Every nonempty l-bit support defines a balanced integer Walsh character on
the full Boolean configuration cube. Its spectral detuning extracts exactly
that support coefficient. If support `S` is scaled as
`g ^ birthOrder S`, its centered finite-time Fourier response is an exact
sinc law.

At the inverse-power horizon `τ / g ^ birthOrder S`, the response is
independent of `g`. Shorter inverse-power horizons converge to one and
longer horizons converge to zero. Thus coefficient birth order is realized
as an elapsed-time wall crossing in the ideal scaled diagonal family.

The character acts on the full configuration cube. This file does not claim
a support-local or scalable measurement protocol, a microscopic
Anderson/MBL transfer, or robustness under device noise.
-/

open Set Filter NormedSpace Topology MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable local instance lbitSupportScaleFintypeForallBool
    {I : Type*} [Fintype I] :
    Fintype (I → Bool) :=
  Fintype.ofFinite _

def lbitSupportIntegerCharacter
    {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (x : I → Bool) : ℤ :=
  ∏ i : I, if i ∈ S then lbitIntegerSign (x i) else 1

theorem lbitSupportIntegerCharacter_cast_rat
    {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (x : I → Bool) :
    ((lbitSupportIntegerCharacter S x : ℤ) : ℚ) =
      lbitWalshCharacter S x := by
  simp [lbitSupportIntegerCharacter, lbitWalshCharacter,
    lbitIntegerSign_cast_rat]

theorem lbitSupportIntegerCharacter_cast_real
    {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (x : I → Bool) :
    ((lbitSupportIntegerCharacter S x : ℤ) : ℝ) =
      (lbitWalshCharacter S x : ℚ) := by
  exact_mod_cast lbitSupportIntegerCharacter_cast_rat S x

theorem lbitSupportIntegerCharacter_balanced
    {I : Type*} [Fintype I] [DecidableEq I]
    {S : Finset I} (hS : S.Nonempty) :
    SpectralCharacterBalanced
      (lbitSupportIntegerCharacter S : (I → Bool) → ℤ) := by
  have h := sum_lbitWalshCharacter_eq_zero hS
  unfold SpectralCharacterBalanced
  have hcast :
      (∑ x : I → Bool,
        ((lbitSupportIntegerCharacter S x : ℤ) : ℚ)) = 0 := by
    simpa [lbitSupportIntegerCharacter_cast_rat] using h
  exact_mod_cast hcast

theorem lbitSupportIntegerCharacter_detuning
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (S : Finset I) :
    finiteTorusCharacterDetuning
        (lbitSupportIntegerCharacter S : (I → Bool) → ℤ)
        (lbitEnergy J) =
      ((2 : ℚ) ^ Fintype.card I) • J S := by
  have h := lbitEnergy_walshCoefficient J S
  unfold finiteTorusCharacterDetuning
  simpa [lbitSupportIntegerCharacter_cast_real, Rat.smul_def] using h

def scaledLBitCoefficient
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (g : ℝ) (S : Finset I) : ℝ :=
  g ^ birthOrder S * J S

def scaledLBitSupportDetuning
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (S : Finset I) (g : ℝ) : ℝ :=
  finiteTorusCharacterDetuning
    (lbitSupportIntegerCharacter S : (I → Bool) → ℤ)
    (lbitEnergy (scaledLBitCoefficient birthOrder J g))

theorem scaledLBitSupportDetuning_eq
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (S : Finset I) (g : ℝ) :
    scaledLBitSupportDetuning birthOrder J S g =
      ((2 : ℚ) ^ Fintype.card I) •
        (g ^ birthOrder S * J S) := by
  exact lbitSupportIntegerCharacter_detuning
    (scaledLBitCoefficient birthOrder J g) S

theorem scaledLBitSupportDetuning_abs_hasPositiveBirthProfile
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (S : Finset I)
    (hJ : J S ≠ 0) :
    HasPositiveBirthProfile
      (fun g => |scaledLBitSupportDetuning birthOrder J S g|)
      (birthOrder S)
      |((2 : ℚ) ^ Fintype.card I) • J S| := by
  constructor
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    rw [scaledLBitSupportDetuning_eq]
    simp only [Rat.smul_def, Rat.cast_pow, Rat.cast_ofNat,
      abs_mul, abs_pow, abs_of_pos hg]
    field_simp [pow_ne_zero _ (ne_of_gt hg)]
  · exact abs_pos.mpr (by simp [Rat.smul_def, hJ])

theorem lbitSupport_scaled_finitePhaseResponse
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (S : Finset I)
    (g A : ℝ) :
    (∫ x,
      UnitAddTorus.mFourier
        (lbitSupportIntegerCharacter S : (I → Bool) → ℤ) x
      ∂(finiteTorusPhaseProbabilityMeasure
        (lbitEnergy (scaledLBitCoefficient birthOrder J g)) A :
        Measure (UnitAddTorus (I → Bool)))) =
      Real.sinc
        (A * (((2 : ℚ) ^ Fintype.card I) •
          (g ^ birthOrder S * J S))) := by
  rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral,
    lbitSupportIntegerCharacter_detuning]
  rfl

theorem lbitSupport_scaled_finitePhaseResponse_birth_exact
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (S : Finset I)
    (g τ : ℝ) (hg : g ≠ 0) :
    (∫ x,
      UnitAddTorus.mFourier
        (lbitSupportIntegerCharacter S : (I → Bool) → ℤ) x
      ∂(finiteTorusPhaseProbabilityMeasure
        (lbitEnergy (scaledLBitCoefficient birthOrder J g))
        (τ / g ^ birthOrder S) :
        Measure (UnitAddTorus (I → Bool)))) =
      Real.sinc
        (τ * (((2 : ℚ) ^ Fintype.card I) • J S)) := by
  rw [lbitSupport_scaled_finitePhaseResponse]
  congr 2
  simp only [Rat.smul_def, Rat.cast_pow, Rat.cast_ofNat]
  field_simp [pow_ne_zero _ hg]

theorem lbitSupport_scaledReporter_wallCrossing
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (S : Finset I)
    (hJ : J S ≠ 0) {τ : ℝ} (hτ : 0 < τ) :
    (∀ r < birthOrder S,
      Tendsto
        (fun g =>
          Real.sinc
            (τ *
              (|scaledLBitSupportDetuning birthOrder J S g| /
                g ^ r)))
        (𝓝[>] 0) (𝓝 1)) ∧
    Tendsto
      (fun g =>
        Real.sinc
          (τ *
            (|scaledLBitSupportDetuning birthOrder J S g| /
              g ^ birthOrder S)))
      (𝓝[>] 0)
      (𝓝 (Real.sinc
        (τ * |((2 : ℚ) ^ Fintype.card I) • J S|))) ∧
    (∀ r, birthOrder S < r →
      Tendsto
        (fun g =>
          Real.sinc
            (τ *
              (|scaledLBitSupportDetuning birthOrder J S g| /
                g ^ r)))
        (𝓝[>] 0) (𝓝 0)) := by
  exact spectralCharacterReporter_wallCrossing
    (scaledLBitSupportDetuning_abs_hasPositiveBirthProfile
      birthOrder J S hJ) hτ

/-- The exact finite-time Fourier response of one support undergoes the
same three-regime wall crossing at its interaction birth order. -/
theorem lbitSupport_scaled_finitePhaseResponse_wallCrossing
    {I : Type*} [Fintype I] [DecidableEq I]
    (birthOrder : Finset I → ℕ)
    (J : Finset I → ℝ) (S : Finset I)
    (hJ : J S ≠ 0) {τ : ℝ} (hτ : 0 < τ) :
    (∀ r < birthOrder S,
      Tendsto
        (fun g =>
          ∫ x,
            UnitAddTorus.mFourier
              (lbitSupportIntegerCharacter S :
                (I → Bool) → ℤ) x
            ∂(finiteTorusPhaseProbabilityMeasure
              (lbitEnergy
                (scaledLBitCoefficient birthOrder J g))
              (τ / g ^ r) :
              Measure (UnitAddTorus (I → Bool))))
        (𝓝[>] 0) (𝓝 1)) ∧
    Tendsto
      (fun g =>
        ∫ x,
          UnitAddTorus.mFourier
            (lbitSupportIntegerCharacter S :
              (I → Bool) → ℤ) x
          ∂(finiteTorusPhaseProbabilityMeasure
            (lbitEnergy
              (scaledLBitCoefficient birthOrder J g))
            (τ / g ^ birthOrder S) :
            Measure (UnitAddTorus (I → Bool))))
      (𝓝[>] 0)
      (𝓝 (Real.sinc
        (τ * |((2 : ℚ) ^ Fintype.card I) • J S|) : ℂ)) ∧
    (∀ r, birthOrder S < r →
      Tendsto
        (fun g =>
          ∫ x,
            UnitAddTorus.mFourier
              (lbitSupportIntegerCharacter S :
                (I → Bool) → ℤ) x
            ∂(finiteTorusPhaseProbabilityMeasure
              (lbitEnergy
                (scaledLBitCoefficient birthOrder J g))
              (τ / g ^ r) :
              Measure (UnitAddTorus (I → Bool))))
        (𝓝[>] 0) (𝓝 0)) := by
  have hwall :=
    lbitSupport_scaledReporter_wallCrossing
      birthOrder J S hJ hτ
  constructor
  · intro r hr
    have hc :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        (hwall.1 r hr)
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    rw [lbitSupport_scaled_finitePhaseResponse]
    change
      (Real.sinc
        (τ *
          (|scaledLBitSupportDetuning birthOrder J S g| /
            g ^ r)) : ℂ) = _
    rw [← scaledLBitSupportDetuning_eq]
    exact
      (coe_real_sinc_scaled_abs τ
        (scaledLBitSupportDetuning birthOrder J S g)
        g r hτ.le hg).symm
  constructor
  · have hc :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        hwall.2.1
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    rw [lbitSupport_scaled_finitePhaseResponse]
    change
      (Real.sinc
        (τ *
          (|scaledLBitSupportDetuning birthOrder J S g| /
            g ^ birthOrder S)) : ℂ) = _
    rw [← scaledLBitSupportDetuning_eq]
    exact
      (coe_real_sinc_scaled_abs τ
        (scaledLBitSupportDetuning birthOrder J S g)
        g (birthOrder S) hτ.le hg).symm
  · intro r hr
    have hc :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        (hwall.2.2 r hr)
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    rw [lbitSupport_scaled_finitePhaseResponse]
    change
      (Real.sinc
        (τ *
          (|scaledLBitSupportDetuning birthOrder J S g| /
            g ^ r)) : ℂ) = _
    rw [← scaledLBitSupportDetuning_eq]
    exact
      (coe_real_sinc_scaled_abs τ
        (scaledLBitSupportDetuning birthOrder J S g)
        g r hτ.le hg).symm

end

end GaloisForLFunctions.HTGeometry
