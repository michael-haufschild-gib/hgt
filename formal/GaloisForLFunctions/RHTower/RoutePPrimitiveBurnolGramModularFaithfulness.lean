import GaloisForLFunctions.RHTower.PrimeBurnolFiniteModularSupport
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolMatrixCompleteColligation
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolWardResolvedGeneratorGraph
import GaloisForLFunctions.RHTower.RoutePPrimitiveJointDepthGammaJuliaLogKreinMatrixCompletion
import GaloisForLFunctions.RHTower.SoninSemilocalFluxSource

/-!
# P-G186 finite modular faithfulness

The canonical P-G186 Burnol column is exactly the source-native prime Burnol
column, not merely equal after a diagonal trace. Prime-power evaluation of
von Mangoldt matches their amplitudes, while both have the same conormal
exponent for every ordinate clock. Thus the independently proved finite
modular-support theorem applies to P-G186's complete Gram. Prime-log
conjugation preserves this invertibility.

This finite result prevents a signed source direction from being annihilated
by the two P-G186 incidence legs. It does not supply uniform inverse bounds
or close the cofinal graph-to-Xi transport.
-/

open Complex Matrix Set MeasureTheory

namespace RHTower

noncomputable section

private theorem primeBurnolAmplitude_eq_routeP (pe : Nat.Primes × ℕ) :
    primeBurnolAmplitude pe =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) := by
  unfold primeBurnolAmplitude finiteVonMangoldtDepthOneAmplitude
  rw [xiGammaEulerValuationNat, vonMangoldt_prime_pow_succ_eq_log]
  rfl

/-- P-G186's canonical physical column equals the source-native prime Burnol
column pointwise, including its von Mangoldt amplitude and ordinate phase. -/
theorem routePPrimitiveBurnolWindowFeature_eq_primeBurnolWindowFeature
    (pe : Nat.Primes × ℕ) (kappa L : ℝ) :
    routePPrimitiveBurnolWindowFeature pe kappa L =
      primeBurnolWindowFeature pe kappa L := by
  rw [routePPrimitiveBurnolWindowFeature_eq_resolvedRadialGeneratorMode,
    primeBurnolWindowFeature, primeBurnolAmplitude_eq_routeP]
  unfold xiWardResolvedRadialGeneratorMode xiWardResolvedRadialMode
    primeBurnolComplexExponent primeBurnolLogFrequency
    primeBurnolValuation xiGammaEulerPrimitiveLogFrequency
    xiGammaEulerValuationNat
  ring

/-- Equality also holds in literal half-line L², so it retains all mixed
inner products rather than only diagonal integrals. -/
theorem routePPrimitiveBurnolWindowFeatureLp_eq_primeBurnolWindowFeatureLp
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    routePPrimitiveBurnolWindowFeatureLp pe kappa =
      primeBurnolWindowFeatureLp pe kappa := by
  unfold routePPrimitiveBurnolWindowFeatureLp routePBurnolHalfLineL2Of
    primeBurnolWindowFeatureLp
  simp only [funext (routePPrimitiveBurnolWindowFeature_eq_primeBurnolWindowFeature
    pe kappa)]

/-- The complete P-G186 Gram is the pre-existing source-native modular Gram,
entrywise and for arbitrary clocks. -/
theorem routePPrimitiveBurnolWindowGramMatrix_eq_primeBurnolWindowGramMatrix
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    routePPrimitiveBurnolWindowGramMatrix pe kappa =
      primeBurnolWindowGramMatrix pe kappa := by
  rw [routePPrimitiveBurnolWindowGramMatrix_eq_gram_L2]
  unfold primeBurnolWindowGramMatrix
  congr 1
  funext i
  exact routePPrimitiveBurnolWindowFeatureLp_eq_primeBurnolWindowFeatureLp
    (pe i) (kappa i)

/-- Distinct physical prime-power labels give a nondegenerate P-G186 Gram. -/
theorem routePPrimitiveBurnolWindowGramMatrix_det_ne_zero
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ)
    (hpe : Function.Injective pe) (kappa : Fin N → ℝ) :
    (routePPrimitiveBurnolWindowGramMatrix pe kappa).det ≠ 0 := by
  rw [routePPrimitiveBurnolWindowGramMatrix_eq_primeBurnolWindowGramMatrix]
  exact det_primeBurnolWindowGramMatrix_ne_zero pe hpe kappa

/-- Prime-log conjugation leaves the actual P-G186 incidence matrix invertible
on every injectively labelled finite packet. -/
theorem routePPrimitiveJointDepthPrimeLogConjugate_burnol_isUnit
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ)
    (hpe : Function.Injective pe) (kappa : Fin N → ℝ) :
    IsUnit (routePPrimitiveJointDepthPrimeLogConjugate pe
      (routePPrimitiveBurnolWindowGramMatrix pe kappa)) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_iff_ne_zero.mpr
  rw [routePPrimitiveJointDepthPrimeLogConjugate_det]
  exact mul_ne_zero
    (pow_ne_zero _ (routePPrimitiveJointDepthPrimeLogDiagonal_det_ne_zero pe))
    (routePPrimitiveBurnolWindowGramMatrix_det_ne_zero pe hpe kappa)

end
end RHTower
