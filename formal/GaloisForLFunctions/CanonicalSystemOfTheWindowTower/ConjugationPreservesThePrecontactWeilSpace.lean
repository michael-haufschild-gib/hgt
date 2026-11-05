import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.ZeroMovingIsUnitaryBeforeContact
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilParityHankelBridge
import GaloisForLFunctions.RHTower.CCM.CCMZetaWeilSmoothIdentity

/-!
# Conjugation in the pre-contact Weil space

Conjugate reflection of a compact source realizes the entire-function involution
`F(z) ↦ conj(F(conj z))`. Each diagonal Weil summand is unchanged. The resulting norm-preserving
semilinear involution extends from the dense smooth core to the unshifted Weil Hilbert space.
-/

open Complex MeasureTheory Set Topology Zeta23

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact

open _root_.RHTower

variable (a : PrecontactAperture)

/-- Conjugate reflection preserves the literal open-aperture smooth source space. -/
def sharpCore (u : SuzukiTaSmoothCore a.1) : SuzukiTaSmoothCore a.1 :=
  ccmComplexSmoothInteriorSourceToSuzukiTaSmoothCore a.1
    (CCMParityHankel.hermitianReflection (suzukiTaSmoothCoreToSource a.1 u))

theorem sharpCore_apply (u : SuzukiTaSmoothCore a.1) (x : ℝ) :
    sharpCore a u x = (starRingEnd ℂ) (u (-x)) := rfl

theorem sharpCore_involutive (u : SuzukiTaSmoothCore a.1) :
    sharpCore a (sharpCore a u) = u := by
  ext x
  simp only [sharpCore_apply, neg_neg, starRingEnd_self_apply]

def sharpCoreEquiv : SuzukiTaSmoothCore a.1 ≃ₛₗ[starRingEnd ℂ] SuzukiTaSmoothCore a.1 where
  toFun := sharpCore a
  invFun := sharpCore a
  left_inv := sharpCore_involutive a
  right_inv := sharpCore_involutive a
  map_add' u v := by
    ext x
    change (starRingEnd ℂ) (u (-x) + v (-x)) =
      (starRingEnd ℂ) (u (-x)) + (starRingEnd ℂ) (v (-x))
    exact map_add _ _ _
  map_smul' c u := by
    ext x
    change (starRingEnd ℂ) (c * u (-x)) =
      (starRingEnd ℂ) c * (starRingEnd ℂ) (u (-x))
    exact map_mul _ _ _

/-- Conjugate reflection implements the sharp involution of the entire Fourier transform. -/
theorem paperFT_sharpCore (u : SuzukiTaSmoothCore a.1) (z : ℂ) :
    paperFT (sharpCore a u) z =
      (starRingEnd ℂ) (paperFT u ((starRingEnd ℂ) z)) := by
  let f : ℝ → ℂ := fun x => u x * Complex.exp (I * (starRingEnd ℂ) z * (x : ℂ))
  calc
    paperFT (sharpCore a u) z = ∫ x : ℝ, (starRingEnd ℂ) (f (-x)) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [f, paperFT]
      rw [sharpCore_apply, map_mul, ← Complex.exp_conj]
      congr 2
      simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal,
        starRingEnd_self_apply, Complex.ofReal_neg]
      ring
    _ = (starRingEnd ℂ) (∫ x : ℝ, f (-x)) := integral_conj
    _ = (starRingEnd ℂ) (paperFT u ((starRingEnd ℂ) z)) := by
      rw [integral_neg_eq_self f volume]
      rfl

/-- The diagonal form is unchanged term by term, including off-line zeros. -/
theorem weilForm_sharpCore (u : SuzukiTaSmoothCore a.1) :
    ccmRestrictedWeilForm a.1 (toForm a (smoothCore a (sharpCore a u)))
        (toForm a (smoothCore a (sharpCore a u))) =
      ccmRestrictedWeilForm a.1 (toForm a (smoothCore a u)) (toForm a (smoothCore a u)) := by
  simp only [toForm_smoothCore]
  change ccmRestrictedWeilForm a.1
      (suzukiTaSmoothCoreToSource a.1 (sharpCore a u)).toCCMFormVector
      (suzukiTaSmoothCoreToSource a.1 (sharpCore a u)).toCCMFormVector =
    ccmRestrictedWeilForm a.1 (suzukiTaSmoothCoreToSource a.1 u).toCCMFormVector
      (suzukiTaSmoothCoreToSource a.1 u).toCCMFormVector
  rw [ccmRestrictedWeilForm_complexSmooth_eq_zetaWeil,
    ccmRestrictedWeilForm_complexSmooth_eq_zetaWeil]
  change zetaZeroConfig.W (sharpCore a u) (sharpCore a u) = zetaZeroConfig.W u u
  unfold ZeroConfig.W
  apply tsum_congr
  intro ρ
  simp only [ZeroConfig.Wsummand, paperFT_sharpCore, starRingEnd_self_apply]
  ring

theorem norm_smoothCore_sharp (u : SuzukiTaSmoothCore a.1) :
    ‖smoothCore a (sharpCore a u)‖ = ‖smoothCore a u‖ := by
  have hsq : ‖smoothCore a (sharpCore a u)‖ ^ 2 = ‖smoothCore a u‖ ^ 2 := by
    rw [norm_sq_eq_weil, norm_sq_eq_weil, weilForm_sharpCore]
  exact le_antisymm
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq.le)
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq.ge)

/-- The antiunitary sharp operation on the exact completed Weil space. -/
def sharp : WeilHilbertBeforeContact a ≃ₛₗᵢ[starRingEnd ℂ] WeilHilbertBeforeContact a :=
  (sharpCoreEquiv a).extendOfIsometry (smoothCore a) (smoothCore a)
    (denseRange_nativeSmoothCore a) (denseRange_nativeSmoothCore a)
    (norm_smoothCore_sharp a)

theorem sharp_smoothCore (u : SuzukiTaSmoothCore a.1) :
    sharp a (smoothCore a u) = smoothCore a (sharpCore a u) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ u

theorem fourier_smoothCore (u : SuzukiTaSmoothCore a.1) (z : ℂ) :
    fourier a (smoothCore a u) z = paperFT u z := by
  rw [fourier, eval_smoothCore_eq_integral]
  apply integral_congr_ae
  filter_upwards with x
  exact mul_comm _ _

/-- The antiunitary acts by conjugation of the entire transform. -/
theorem fourier_sharp (x : WeilHilbertBeforeContact a) (z : ℂ) :
    fourier a (sharp a x) z = (starRingEnd ℂ) (fourier a x ((starRingEnd ℂ) z)) := by
  have hf : Continuous (fun x : WeilHilbertBeforeContact a => fourier a (sharp a x) z) :=
    (eval a z).continuous.comp (sharp a).continuous
  have hg : Continuous (fun x : WeilHilbertBeforeContact a =>
      (starRingEnd ℂ) (fourier a x ((starRingEnd ℂ) z))) :=
    Complex.continuous_conj.comp (eval a ((starRingEnd ℂ) z)).continuous
  have heq := hf.ext_on (denseRange_nativeSmoothCore a) hg (by
    rintro _ ⟨u, rfl⟩
    dsimp only
    rw [sharp_smoothCore, fourier_smoothCore, fourier_smoothCore, paperFT_sharpCore])
  exact congrFun heq x

theorem sharp_involutive (x : WeilHilbertBeforeContact a) : sharp a (sharp a x) = x := by
  apply fourier_injective a
  funext z
  simp only [fourier_sharp, starRingEnd_self_apply]

#print axioms weilForm_sharpCore
#print axioms sharp
#print axioms fourier_sharp
#print axioms sharp_involutive

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
