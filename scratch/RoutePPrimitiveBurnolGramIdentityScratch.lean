import GaloisForLFunctions.RHTower.PrimeBurnolFiniteModularSupport
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolMatrixCompleteColligation
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolWardResolvedGeneratorGraph
import GaloisForLFunctions.RHTower.RoutePPrimitiveJointDepthGammaJuliaLogKreinMatrixCompletion
import GaloisForLFunctions.RHTower.SoninSemilocalFluxSource

open Complex Matrix Set MeasureTheory

namespace RHTower

noncomputable section

private theorem amplitude_eq (pe : Nat.Primes × ℕ) :
    primeBurnolAmplitude pe =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) := by
  unfold primeBurnolAmplitude finiteVonMangoldtDepthOneAmplitude
  rw [xiGammaEulerValuationNat, vonMangoldt_prime_pow_succ_eq_log]
  rfl

private theorem feature_eq (pe : Nat.Primes × ℕ) (kappa L : ℝ) :
    routePPrimitiveBurnolWindowFeature pe kappa L =
      primeBurnolWindowFeature pe kappa L := by
  rw [routePPrimitiveBurnolWindowFeature_eq_resolvedRadialGeneratorMode,
    primeBurnolWindowFeature, amplitude_eq]
  unfold xiWardResolvedRadialGeneratorMode xiWardResolvedRadialMode
    primeBurnolComplexExponent primeBurnolLogFrequency
    primeBurnolValuation xiGammaEulerPrimitiveLogFrequency
    xiGammaEulerValuationNat
  ring

private theorem featureLp_eq (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    routePPrimitiveBurnolWindowFeatureLp pe kappa =
      primeBurnolWindowFeatureLp pe kappa := by
  unfold routePPrimitiveBurnolWindowFeatureLp routePBurnolHalfLineL2Of
    primeBurnolWindowFeatureLp
  simp only [funext (feature_eq pe kappa)]

private theorem gram_eq {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    routePPrimitiveBurnolWindowGramMatrix pe kappa =
      primeBurnolWindowGramMatrix pe kappa := by
  rw [routePPrimitiveBurnolWindowGramMatrix_eq_gram_L2]
  unfold primeBurnolWindowGramMatrix
  congr 1
  funext i
  exact featureLp_eq (pe i) (kappa i)

theorem routePPrimitiveBurnolWindowGramMatrix_det_ne_zero_test
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ)
    (hpe : Function.Injective pe) (kappa : Fin N → ℝ) :
    (routePPrimitiveBurnolWindowGramMatrix pe kappa).det ≠ 0 := by
  rw [gram_eq]
  exact det_primeBurnolWindowGramMatrix_ne_zero pe hpe kappa

theorem routePPrimitiveJointDepthPrimeLogConjugate_burnol_isUnit_test
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ)
    (hpe : Function.Injective pe) (kappa : Fin N → ℝ) :
    IsUnit (routePPrimitiveJointDepthPrimeLogConjugate pe
      (routePPrimitiveBurnolWindowGramMatrix pe kappa)) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_iff_ne_zero.mpr
  rw [routePPrimitiveJointDepthPrimeLogConjugate_det]
  exact mul_ne_zero
    (pow_ne_zero _ (routePPrimitiveJointDepthPrimeLogDiagonal_det_ne_zero pe))
    (routePPrimitiveBurnolWindowGramMatrix_det_ne_zero_test pe hpe kappa)

end
end RHTower
