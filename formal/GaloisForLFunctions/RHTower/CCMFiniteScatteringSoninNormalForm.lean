import GaloisForLFunctions.RHTower.CCMGammaSoninNormalForm
import GaloisForLFunctions.RHTower.FieldOneFiniteStageConnesMarcolliLocalRatio

/-!
# The joint finite Euler–Gamma differential on the physical Sonin carrier

The source is the existing spherical scattering unitary, retaining every Euler
ratio and the Gamma phase. Its logarithmic projection differential is exactly
a finite Euler conjugate of the Fourier cutoff plus the physical cutoff minus one.
No cofinal convergence or trace-ideal hypothesis is built into this construction.
-/

noncomputable section

open IsDedekindDomain MeasureTheory
open scoped BigOperators

namespace RHTower

private abbrev fullScattering (S : Finset (HeightOneSpectrum ℤ)) :=
  GaloisForLFunctions.RHTower.fieldOneFiniteStageSphericalScatteringUnitary S

/-- Remove the actual Gamma factor from the full finite spherical source. -/
def ccmFiniteEulerSpectralUnitary (S : Finset (HeightOneSpectrum ℤ)) :
    SoninL2 ≃ₗᵢ[ℂ] SoninL2 :=
  (fullScattering S).trans ccmArchimedeanScatteringL2Unitary.symm

/-- The finite Euler unitary on the same physical carrier as the Sonin projections. -/
def ccmFiniteEulerPhysicalUnitary (S : Finset (HeightOneSpectrum ℤ)) :
    evenSubspace ≃ₗᵢ[ℂ] evenSubspace :=
  archimedeanMellinUnitary.trans
    ((ccmFiniteEulerSpectralUnitary S).trans archimedeanMellinUnitary.symm)

/-- Literal source provenance: the remaining multiplier is the product of all finite Euler ratios. -/
theorem ccmFiniteEulerSpectralUnitary_ae (S : Finset (HeightOneSpectrum ℤ))
    (f : SoninL2) :
    ccmFiniteEulerSpectralUnitary S f =ᵐ[volume] fun t =>
      (∏ v : ↥S, GaloisForLFunctions.RHTower.primeRatio
        (Rat.HeightOneSpectrum.primesEquiv v.1) t) * f t := by
  change ccmArchimedeanScatteringConjL2Multiplier (fullScattering S f) =ᵐ[volume] _
  filter_upwards [ccmArchimedeanScatteringConjL2Multiplier_ae (fullScattering S f),
    GaloisForLFunctions.RHTower.fieldOneFiniteStageSphericalScatteringUnitary_ae S f]
    with t hΓ hfull
  rw [hΓ, hfull]
  unfold GaloisForLFunctions.RHTower.fieldOneFiniteStageSphericalScatteringSymbol
  have hu : star (ccmArchimedeanScatteringPhase t) *
      ccmArchimedeanScatteringPhase t = 1 := by
    change (starRingEnd ℂ) (ccmArchimedeanScatteringPhase t) *
      ccmArchimedeanScatteringPhase t = 1
    rw [← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, norm_ccmArchimedeanScatteringPhase]
    norm_num
  calc
    _ = (star (ccmArchimedeanScatteringPhase t) * ccmArchimedeanScatteringPhase t) *
        ((∏ v : ↥S, GaloisForLFunctions.RHTower.primeRatio
          (Rat.HeightOneSpectrum.primesEquiv v.1) t) * f t) := by ring
    _ = _ := by rw [hu, one_mul]

/-- Exact Mellin intertwining of the finite Euler source. -/
theorem archimedeanMellinUnitary_ccmFiniteEulerPhysicalUnitary
    (S : Finset (HeightOneSpectrum ℤ)) (f : evenSubspace) :
    archimedeanMellinUnitary (ccmFiniteEulerPhysicalUnitary S f) =
      ccmFiniteEulerSpectralUnitary S (archimedeanMellinUnitary f) := by
  exact archimedeanMellinUnitary.apply_symm_apply _

private theorem mellin_inverse_finiteEuler
    (S : Finset (HeightOneSpectrum ℤ)) (f : evenSubspace) :
    archimedeanMellinUnitary ((ccmFiniteEulerPhysicalUnitary S).symm f) =
      (ccmFiniteEulerSpectralUnitary S).symm (archimedeanMellinUnitary f) := by
  exact archimedeanMellinUnitary.apply_symm_apply _

/-- Physical logarithmic projection differential of the full finite Euler–Gamma unitary. -/
def ccmFiniteScatteringLogDifferential (S : Finset (HeightOneSpectrum ℤ)) :
    evenSubspace →L[ℂ] evenSubspace :=
  ccmArchimedeanMellinInvCLM ∘L
    (((fullScattering S).symm.toLinearIsometry.toContinuousLinearMap ∘L
      ccmHardyProjection ∘L (fullScattering S).toLinearIsometry.toContinuousLinearMap -
        ccmHardyProjection) ∘L ccmArchimedeanMellinCLM)

/-- The full mixed source is the Euler conjugate of the Fourier wall plus the physical wall. -/
theorem ccmFiniteScatteringLogDifferential_eq_cutoffs
    (S : Finset (HeightOneSpectrum ℤ)) :
    ccmFiniteScatteringLogDifferential S =
      (ccmFiniteEulerPhysicalUnitary S).symm.toLinearIsometry.toContinuousLinearMap *
        evenFourierCutoff 1 *
        (ccmFiniteEulerPhysicalUnitary S).toLinearIsometry.toContinuousLinearMap +
          evenIndicatorCutoff 1 - 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply archimedeanMellinUnitary.injective
  change archimedeanMellinUnitary
      (archimedeanMellinUnitary.symm ((fullScattering S).symm
        (ccmHardyProjection (fullScattering S (archimedeanMellinUnitary f))) -
          ccmHardyProjection (archimedeanMellinUnitary f))) =
    archimedeanMellinUnitary
      ((ccmFiniteEulerPhysicalUnitary S).symm
        (evenFourierCutoff 1 (ccmFiniteEulerPhysicalUnitary S f)) +
          evenIndicatorCutoff 1 f - f)
  rw [archimedeanMellinUnitary.apply_symm_apply, map_sub, map_add,
    mellin_inverse_finiteEuler, archimedeanMellinUnitary_evenFourierCutoff_one,
    archimedeanMellinUnitary_ccmFiniteEulerPhysicalUnitary,
    archimedeanMellinUnitary_evenIndicatorCutoff_one]
  have hterm : (ccmFiniteEulerSpectralUnitary S).symm
      (ccmArchimedeanScatteringConjL2Multiplier
        (ccmHardyProjection (ccmArchimedeanScatteringL2Multiplier
          (ccmFiniteEulerSpectralUnitary S (archimedeanMellinUnitary f))))) =
      (fullScattering S).symm
        (ccmHardyProjection (fullScattering S (archimedeanMellinUnitary f))) := by
    have hforward (x : SoninL2) : ccmArchimedeanScatteringL2Multiplier
        (ccmFiniteEulerSpectralUnitary S x) = fullScattering S x :=
      ccmArchimedeanScatteringL2Unitary.apply_symm_apply _
    have hinverse (x : SoninL2) : (ccmFiniteEulerSpectralUnitary S).symm
        (ccmArchimedeanScatteringConjL2Multiplier x) = (fullScattering S).symm x := by
      change (fullScattering S).symm
        (ccmArchimedeanScatteringL2Unitary (ccmArchimedeanScatteringL2Unitary.symm x)) = _
      rw [ccmArchimedeanScatteringL2Unitary.apply_symm_apply]
    rw [hforward, hinverse]
  rw [hterm]
  abel

private theorem unitCutoff_mul_sonin {b : ℝ} (hb : 1 ≤ b) :
    evenIndicatorCutoff 1 * evenCentralSoninProjection b = 0 := by
  rw [← (evenCentralSoninProjection_mul_of_le hb).2, ← mul_assoc,
    evenIndicatorCutoff_mul_evenCentralSoninProjection, zero_mul]

/-- Literal complementary Fourier channel of the finite Euler-ratio source. -/
def ccmFiniteScatteringSoninResidual
    (S : Finset (HeightOneSpectrum ℤ)) (b : ℝ) :
    evenSubspace →L[ℂ] evenSubspace :=
  (1 - evenFourierCutoff 1) *
    (ccmFiniteEulerPhysicalUnitary S).toLinearIsometry.toContinuousLinearMap *
      evenCentralSoninProjection b

/-- Source-derived exact positive residual, retaining the full finite Euler product. -/
theorem ccmFiniteScatteringLogDifferential_sonin_gram
    (S : Finset (HeightOneSpectrum ℤ)) {b : ℝ} (hb : 1 ≤ b) :
    -(evenCentralSoninProjection b * ccmFiniteScatteringLogDifferential S *
        evenCentralSoninProjection b) =
      ContinuousLinearMap.adjoint (ccmFiniteScatteringSoninResidual S b) *
        ccmFiniteScatteringSoninResidual S b := by
  let V := ccmFiniteEulerPhysicalUnitary S
  let v := V.toLinearIsometry.toContinuousLinearMap
  let w := V.symm.toLinearIsometry.toContinuousLinearMap
  let R := evenFourierCutoff 1
  let Q := evenCentralSoninProjection b
  have hQ : Q * Q = Q := (evenCentralSoninProjection_mul_of_le (le_refl b)).1
  have hR : R * R = R := evenFourierCutoff_mul_of_le 1 1 le_rfl
  have hRstar : ContinuousLinearMap.adjoint R = R := adjoint_evenFourierCutoff 1
  have hQstar : ContinuousLinearMap.adjoint Q = Q := adjoint_evenCentralSoninProjection b
  have hvstar : ContinuousLinearMap.adjoint v = w := LinearIsometryEquiv.adjoint_eq_symm V
  have hI : ContinuousLinearMap.adjoint (1 : evenSubspace →L[ℂ] evenSubspace) = 1 :=
    ContinuousLinearMap.adjoint_id
  have hwv : w * v = 1 := by
    apply ContinuousLinearMap.ext
    intro f
    exact V.symm_apply_apply f
  have hA : Q * evenIndicatorCutoff 1 * Q = 0 := by
    rw [mul_assoc, unitCutoff_mul_sonin hb, mul_zero]
  have hD : Q * ccmFiniteScatteringLogDifferential S * Q = Q * w * R * v * Q - Q := by
    rw [ccmFiniteScatteringLogDifferential_eq_cutoffs]
    change Q * (w * R * v + evenIndicatorCutoff 1 - 1) * Q = _
    rw [mul_sub, mul_add, sub_mul, add_mul, mul_one, hA, add_zero, hQ]
    simp only [mul_assoc]
  have hcomplement : (1 - R) * (1 - R) = 1 - R := by
    rw [mul_sub, mul_one, sub_mul, one_mul, hR, sub_self, sub_zero]
  have hstar : ContinuousLinearMap.adjoint ((1 - R) * v * Q) = Q * w * (1 - R) := by
    have hC : ContinuousLinearMap.adjoint (1 - R) = 1 - R :=
      (ContinuousLinearMap.adjoint.map_sub 1 R).trans (congrArg₂ (· - ·) hI hRstar)
    have hinner : ContinuousLinearMap.adjoint ((1 - R) ∘L v) = w ∘L (1 - R) :=
      (ContinuousLinearMap.adjoint_comp (1 - R) v).trans
        (congrArg₂ (fun X Y : evenSubspace →L[ℂ] evenSubspace => X ∘L Y) hvstar hC)
    exact ((ContinuousLinearMap.adjoint_comp ((1 - R) ∘L v) Q).trans
      (congrArg₂ (fun X Y : evenSubspace →L[ℂ] evenSubspace => X ∘L Y) hQstar hinner)).trans
        (mul_assoc Q w (1 - R)).symm
  change -(Q * ccmFiniteScatteringLogDifferential S * Q) =
    ContinuousLinearMap.adjoint ((1 - R) * v * Q) * ((1 - R) * v * Q)
  rw [hD, neg_sub, hstar]
  symm
  calc
    _ = Q * w * ((1 - R) * (1 - R)) * v * Q := by simp only [mul_assoc]
    _ = Q * w * (1 - R) * v * Q := by rw [hcomplement]
    _ = Q - Q * w * R * v * Q := by
      rw [mul_sub, mul_one, sub_mul, sub_mul]
      have hbase : Q * w * v * Q = Q := by
        rw [mul_assoc Q w v, hwv, mul_one, hQ]
      rw [hbase]

/-- The sign is proved from the actual source, not assumed as a completion premise. -/
theorem ccmFiniteScatteringLogDifferential_sonin_negative_isPositive
    (S : Finset (HeightOneSpectrum ℤ)) {b : ℝ} (hb : 1 ≤ b) :
    (-(evenCentralSoninProjection b * ccmFiniteScatteringLogDifferential S *
      evenCentralSoninProjection b)).IsPositive := by
  rw [ccmFiniteScatteringLogDifferential_sonin_gram S hb]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self
    (ccmFiniteScatteringSoninResidual S b)

/-- Every lost-channel term of the full source is the actual finite Euler Fourier-wall cross term. -/
theorem ccmFiniteScatteringLogDifferential_lost_transition
    (S : Finset (HeightOneSpectrum ℤ)) {a b : ℝ} (hab : a ≤ b) (hb : 1 ≤ b) :
    evenSoninApertureLayer a b * ccmFiniteScatteringLogDifferential S *
        evenCentralSoninProjection b =
      evenSoninApertureLayer a b *
        (ccmFiniteEulerPhysicalUnitary S).symm.toLinearIsometry.toContinuousLinearMap *
        evenFourierCutoff 1 *
        (ccmFiniteEulerPhysicalUnitary S).toLinearIsometry.toContinuousLinearMap *
        evenCentralSoninProjection b := by
  have hEQ : evenSoninApertureLayer a b * evenCentralSoninProjection b = 0 := by
    rw [evenSoninApertureLayer, sub_mul, (evenCentralSoninProjection_mul_of_le hab).2,
      (evenCentralSoninProjection_mul_of_le (le_refl b)).1, sub_self]
  have hEAQ : evenSoninApertureLayer a b * evenIndicatorCutoff 1 *
      evenCentralSoninProjection b = 0 := by
    rw [mul_assoc, unitCutoff_mul_sonin hb, mul_zero]
  rw [ccmFiniteScatteringLogDifferential_eq_cutoffs, mul_sub, mul_add,
    sub_mul, add_mul, mul_one, hEAQ, hEQ, add_zero, sub_zero]
  simp only [mul_assoc]

end RHTower
