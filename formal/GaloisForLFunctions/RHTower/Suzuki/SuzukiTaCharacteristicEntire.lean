import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaCharacteristicZeros
import GaloisForLFunctions.RHTower.Suzuki.SuzukiApertureL2Equivalence

/-!
# Entire Fourier realization of Suzuki's characteristic function

The abstract energy-space Riesz moment is identified with the literal compactly supported `L²`
Fourier integral of the physical aperture representative.  This closes the analytic part of
Suzuki v2, Theorem 1.5 without selecting pointwise representatives or assuming extra regularity
of the deficiency vectors.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform LinearPMap

noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- Literal whole-line Fourier transform of an energy vector after physical zero extension. -/
def suzukiTaPhysicalFourier
    (a : SuzukiPositiveAperture) (x : SuzukiTaHilbert a) (z : ℂ) : ℂ :=
  suzukiCompactL2Fourier a.1
    (suzukiApertureZeroExtendL2 (suzukiTaPhysicalEmbedding a x)) z

theorem differentiable_suzukiTaPhysicalFourier
    (a : SuzukiPositiveAperture) (x : SuzukiTaHilbert a) :
    Differentiable ℂ (suzukiTaPhysicalFourier a x) :=
  differentiable_suzukiCompactL2Fourier a.2.le _

/-- Exact bridge between Riesz evaluation in `H(T_a)` and the literal compact `L²` Fourier
integral. -/
theorem suzukiTaSpectralMoment_star_eq_physicalFourier
    (a : SuzukiPositiveAperture) (x : SuzukiTaHilbert a) (z : ℂ) :
    suzukiTaSpectralMoment a (star z) x = suzukiTaPhysicalFourier a x z := by
  rw [suzukiTaSpectralMoment, ContinuousLinearMap.comp_apply]
  change inner ℂ (suzukiTaSpectralExponentialL2 a (star z))
      (suzukiTaPhysicalEmbedding a x) = _
  rw [MeasureTheory.L2.inner_def]
  have hinterval :
      (∫ u : SuzukiApertureInterval a.1,
          inner ℂ
            ((suzukiTaSpectralExponentialL2 a (star z) :
              SuzukiApertureInterval a.1 → ℂ) u)
            ((suzukiTaPhysicalEmbedding a x :
              SuzukiApertureInterval a.1 → ℂ) u)) =
        ∫ u : SuzukiApertureInterval a.1,
          (suzukiTaPhysicalEmbedding a x :
            SuzukiApertureInterval a.1 → ℂ) u *
            Complex.exp (I * z * (((u : ℝ) : ℂ))) := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
        (suzukiTaSpectralExponentialContinuous a (star z))] with u hu
    change inner ℂ
        ((ContinuousMap.toLp 2 volume ℂ
          (suzukiTaSpectralExponentialContinuous a (star z)) :
            SuzukiApertureInterval a.1 → ℂ) u)
        ((suzukiTaPhysicalEmbedding a x :
          SuzukiApertureInterval a.1 → ℂ) u) = _
    rw [hu]
    simp only [suzukiTaSpectralExponentialContinuous, RCLike.inner_apply]
    change (suzukiTaPhysicalEmbedding a x :
        SuzukiApertureInterval a.1 → ℂ) u *
      (starRingEnd ℂ) (Complex.exp
        (-I * star z * (((u : ℝ) : ℂ)))) = _
    rw [← Complex.exp_conj]
    simp only [map_mul, map_neg, starRingEnd_apply, star_star]
    have hstarI : star (I : ℂ) = -I := by
      change (starRingEnd ℂ) I = -I
      exact Complex.conj_I
    have hstarReal : star (((u : ℝ) : ℂ)) = (((u : ℝ) : ℂ)) := by
      change (starRingEnd ℂ) (((u : ℝ) : ℂ)) = (((u : ℝ) : ℂ))
      exact Complex.conj_ofReal (u : ℝ)
    have harg : -star I * z * star (((u : ℝ) : ℂ)) =
        I * z * (((u : ℝ) : ℂ)) := by
      rw [hstarI, hstarReal]
      ring
    rw [harg]
  rw [hinterval]
  rw [suzukiTaPhysicalFourier, suzukiCompactL2Fourier]
  change (∫ u : SuzukiApertureInterval a.1,
      (suzukiTaPhysicalEmbedding a x :
        SuzukiApertureInterval a.1 → ℂ) u *
        Complex.exp (I * z * (((u : ℝ) : ℂ)))) =
    ∫ t : ℝ,
      (suzukiCutoff a.1
        (suzukiApertureZeroExtendL2 (suzukiTaPhysicalEmbedding a x)) :
          ℝ → ℂ) t * Complex.exp (I * z * (t : ℂ))
  rw [suzukiApertureZeroExtendL2_cutoff]
  have hzero := suzukiApertureZeroExtendL2_coeFn
    (suzukiTaPhysicalEmbedding a x)
  calc
    (∫ u : SuzukiApertureInterval a.1,
        (suzukiTaPhysicalEmbedding a x :
          SuzukiApertureInterval a.1 → ℂ) u *
          Complex.exp (I * z * (((u : ℝ) : ℂ)))) =
      ∫ t : ℝ, suzukiApertureZeroExtend
          (suzukiTaPhysicalEmbedding a x) t *
          Complex.exp (I * z * (t : ℂ)) := by
        exact (integral_suzukiApertureZeroExtend_mul a.1
          (suzukiTaPhysicalEmbedding a x)
          (fun t : ℝ => Complex.exp (I * z * (t : ℂ)))).symm
    _ = ∫ t : ℝ,
        (suzukiApertureZeroExtendL2 (suzukiTaPhysicalEmbedding a x) :
          ℝ → ℂ) t * Complex.exp (I * z * (t : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [hzero] with t ht
      rw [ht]

/-- The literal Suzuki formula (111), now using actual zero-extended physical `L²` vectors. -/
def suzukiTaCharacteristicFourier
    (a : SuzukiPositiveAperture) (theta : ℝ) (z : ℂ) : ℂ :=
  (z - I) * suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a) z +
    suzukiTaBoundaryPhase theta * (z + I) *
      suzukiTaPhysicalFourier a (suzukiTaMinusDeficiency a) z

theorem suzukiTaCharacteristic_eq_fourier
    (a : SuzukiPositiveAperture) (theta : ℝ) (z : ℂ) :
    suzukiTaCharacteristic a theta z =
      suzukiTaCharacteristicFourier a theta z := by
  rw [suzukiTaCharacteristic, suzukiTaCharacteristicFourier,
    suzukiTaSpectralMoment_star_eq_physicalFourier,
    suzukiTaSpectralMoment_star_eq_physicalFourier]

/-- Suzuki's finite-aperture characteristic function is entire. -/
theorem differentiable_suzukiTaCharacteristic
    (a : SuzukiPositiveAperture) (theta : ℝ) :
    Differentiable ℂ (suzukiTaCharacteristic a theta) := by
  have hplus := differentiable_suzukiTaPhysicalFourier a
    (suzukiTaPlusDeficiency a)
  have hminus := differentiable_suzukiTaPhysicalFourier a
    (suzukiTaMinusDeficiency a)
  have hfourier : Differentiable ℂ (suzukiTaCharacteristicFourier a theta) := by
    exact (differentiable_id.sub_const I).mul hplus |>.add
      (((differentiable_const (c := suzukiTaBoundaryPhase theta)).mul
        (differentiable_id.add_const I)).mul hminus)
  have heq : suzukiTaCharacteristic a theta =
      suzukiTaCharacteristicFourier a theta := by
    funext z
    exact suzukiTaCharacteristic_eq_fourier a theta z
  rw [heq]
  exact hfourier

end RHTower
