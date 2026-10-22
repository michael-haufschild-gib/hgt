import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaCharacteristicEntire
import GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteApertureHermiteBiehler

/-!
# Literal finite-aperture Suzuki v2 Livsic characteristic

This module isolates the actual finite-aperture characteristic pair and its Schur/Livšic
coordinate from Xi-target normalization.  The finite source layer depends only on Suzuki's
completed covariance realization and all-angle self-adjoint spectral theorem.
-/

open Complex Metric Set Filter Topology

noncomputable section
namespace RHTower

open GaloisForLFunctions.RHTower

/-- `Aₐ` coordinate of the literal Suzuki characteristic pencil. -/
def suzukiTaV2CharacteristicA (a : SuzukiPositiveAperture) (z : ℂ) : ℂ :=
  (z - I) * suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a) z

/-- `Eₐ` coordinate of the literal Suzuki characteristic pencil. -/
def suzukiTaV2CharacteristicE (a : SuzukiPositiveAperture) (z : ℂ) : ℂ :=
  (z + I) * suzukiTaPhysicalFourier a (suzukiTaMinusDeficiency a) z

/-- Exact identification of Suzuki's real-angle characteristic with the unitary pencil. -/
theorem suzukiTaCharacteristic_eq_v2Pencil
    (a : SuzukiPositiveAperture) (theta : ℝ) (z : ℂ) :
    suzukiTaCharacteristic a theta z =
      suzukiCharacteristicPencil
        (suzukiTaV2CharacteristicA a) (suzukiTaV2CharacteristicE a)
        (suzukiTaBoundaryPhase theta) z := by
  rw [suzukiTaCharacteristic_eq_fourier]
  simp only [suzukiTaCharacteristicFourier, suzukiCharacteristicPencil,
    suzukiTaV2CharacteristicA, suzukiTaV2CharacteristicE]
  ring

theorem differentiable_suzukiTaV2CharacteristicA (a : SuzukiPositiveAperture) :
    Differentiable ℂ (suzukiTaV2CharacteristicA a) := by
  exact (differentiable_id.sub_const I).mul
    (differentiable_suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a))

theorem differentiable_suzukiTaV2CharacteristicE (a : SuzukiPositiveAperture) :
    Differentiable ℂ (suzukiTaV2CharacteristicE a) := by
  exact (differentiable_id.add_const I).mul
    (differentiable_suzukiTaPhysicalFourier a (suzukiTaMinusDeficiency a))

@[simp] theorem suzukiTaV2CharacteristicA_I (a : SuzukiPositiveAperture) :
    suzukiTaV2CharacteristicA a I = 0 := by
  simp [suzukiTaV2CharacteristicA]

/-- Suzuki's literal all-angle spectral reality theorem supplies the generic pencil predicate. -/
theorem suzukiTaV2_allAngleRealZeros (a : SuzukiPositiveAperture) :
    SuzukiAllAngleRealZeros
      (suzukiTaV2CharacteristicA a) (suzukiTaV2CharacteristicE a) := by
  intro u hu z hz
  obtain ⟨theta, htheta⟩ := (Complex.norm_eq_one_iff u).mp hu
  have hphase : suzukiTaBoundaryPhase theta = u := by
    rw [suzukiTaBoundaryPhase]
    convert htheta using 1
    ring
  apply suzukiTaCharacteristic_zero_im_eq_zero a theta z
  rw [suzukiTaCharacteristic_eq_v2Pencil, hphase]
  exact hz

/-- Actual normalized finite-aperture Livšic coordinate. -/
def suzukiTaV2Livsic (a : SuzukiPositiveAperture) : ℂ → ℂ :=
  suzukiLivsicQuotient (suzukiTaV2CharacteristicA a) (suzukiTaV2CharacteristicE a)

/-- Actual finite-aperture Livšic coordinates are strictly Schur on the upper half-plane. -/
theorem norm_suzukiTaV2Livsic_lt_one
    (a : SuzukiPositiveAperture) {z : ℂ} (hz : 0 < z.im) :
    ‖suzukiTaV2Livsic a z‖ < 1 := by
  exact norm_suzukiLivsicQuotient_lt_one
    (differentiable_suzukiTaV2CharacteristicA a).continuous
    (differentiable_suzukiTaV2CharacteristicE a).continuous
    (suzukiTaV2CharacteristicA_I a) (suzukiTaV2_allAngleRealZeros a) hz

/-- Canonical cofinal positive-aperture schedule, independent of target normalization. -/
def suzukiTaV2CanonicalAperture (n : ℕ) : SuzukiPositiveAperture :=
  ⟨(n : ℝ) + 1, by positivity⟩

theorem tendsto_suzukiTaV2CanonicalAperture_atTop :
    Tendsto (fun n => (suzukiTaV2CanonicalAperture n).1) atTop atTop := by
  exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

end RHTower

end
