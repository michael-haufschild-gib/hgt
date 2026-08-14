import GaloisForLFunctions.RHTower.FieldOneFiniteStageConnesMarcolliLemma233
import GaloisForLFunctions.RHTower.CCMLocalRatioCompleted
import GaloisForLFunctions.RHTower.CCMArchimedeanPhaseOperatorProduct
import GaloisForLFunctions.RHTower.HardyTitchmarshSemilocalSquare

/-!
# Connes--Marcolli local-factor product on the spherical spectrum

This file closes the trivial-angular-character part of equations (2.258)--(2.260).
It proves that the finite-place phases already present in the corpus are literally
the ratios of the two critical-line local Euler factors, identifies the separately
constructed archimedean Gamma ratio with the literal CCM scattering phase, and
packages their product over every place in a finite stage as an actual unitary
multiplier on radial spectral `L²`.

This is not called Lemma 2.34: characters ramified on the compact module-one
factor still require their local Tate functional equations and the full
multiplicative Fourier transform of that factor.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain MeasureTheory
open scoped BigOperators

/-- The finite critical-line phase is exactly the quotient of the two local
Euler factors. This is the unramified instance of equation (2.258). -/
theorem primeRatio_eq_localLFactor_ratio
    (p : ℕ) (hp : 1 < p) (t : ℝ) :
    primeRatio p t =
      _root_.RHTower.primeEulerFactor (p : ℝ) t /
        _root_.RHTower.primeEulerFactor (p : ℝ) (-t) := by
  rw [primeRatio, primeRadius, if_pos hp]
  unfold primeLocalRatio _root_.RHTower.primeEulerFactor
    _root_.RHTower.semilocalPrimeSymbol
  have hsqrt : ((Real.sqrt (p : ℝ) : ℝ) : ℂ)⁻¹ =
      (((1 / Real.sqrt p : ℝ) : ℂ)) := by
    push_cast
    rw [one_div]
  rw [hsqrt]
  have hmt : (_root_.RHTower.MellinL2.mellinCharacter (p : ℝ) t)⁻¹ =
      Complex.exp (-(((Real.log (p : ℝ) * t : ℝ) : ℂ) * Complex.I)) := by
    unfold _root_.RHTower.MellinL2.mellinCharacter
    rw [Complex.exp_neg]
  have hmneg : (_root_.RHTower.MellinL2.mellinCharacter (p : ℝ) (-t))⁻¹ =
      Complex.exp (((Real.log (p : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
    unfold _root_.RHTower.MellinL2.mellinCharacter
    rw [show (((Real.log (p : ℝ) * -t : ℝ) : ℂ) * Complex.I) =
        -(((Real.log (p : ℝ) * t : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring,
      Complex.exp_neg, inv_inv]
  rw [hmt, hmneg]
  simp only [div_eq_mul_inv, inv_inv]
  ring

/-- The explicit exponential definition of the archimedean factor agrees with
mathlib's completed real Gamma factor. -/
theorem gammaArch_eq_GammaR (s : ℂ) :
    gammaArch s = Complex.Gammaℝ s := by
  rw [gammaArch_eq_cpow]
  rfl

/-- The Gamma local ratio and the independently constructed literal CCM
archimedean scattering phase are the same function. -/
theorem archRatio_eq_ccmArchimedeanScatteringPhase (t : ℝ) :
    archRatio t = _root_.RHTower.ccmArchimedeanScatteringPhase t := by
  rw [archRatio, _root_.RHTower.ccmArchimedeanScatteringPhase,
    _root_.RHTower.zetaChi]
  simp only [map_div₀, ← gammaArch_eq_GammaR]
  rw [gammaArch_conj, gammaArch_conj]
  have hplus : (starRingEnd ℂ) (1 - _root_.RHTower.linePt t) =
      1 / 2 + (t : ℂ) * Complex.I := by
    unfold _root_.RHTower.linePt
    rw [map_sub, map_one, map_add, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    simp only [Complex.conj_ofReal]
    push_cast
    ring
  have hminus : (starRingEnd ℂ) (_root_.RHTower.linePt t) =
      1 / 2 - (t : ℂ) * Complex.I := by
    unfold _root_.RHTower.linePt
    rw [map_add, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    simp only [Complex.conj_ofReal]
    push_cast
    ring
  rw [hplus, hminus]

/-- Equation (2.260) on the genuine trivial-angular spectral component: the
archimedean phase times every finite unramified local phase in `S`. -/
def fieldOneFiniteStageSphericalScatteringSymbol
    (S : Finset (HeightOneSpectrum ℤ)) (t : ℝ) : ℂ :=
  _root_.RHTower.ccmArchimedeanScatteringPhase t *
    ∏ v : ↥S, primeRatio (Rat.HeightOneSpectrum.primesEquiv v.1) t

theorem continuous_primeRatio (p : ℕ) : Continuous (primeRatio p) := by
  unfold primeRatio primeLocalRatio
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    exact primeLocalRatio_den_ne_zero (abs_primeRadius_lt_one p) (Real.log p) t

theorem continuous_fieldOneFiniteStageSphericalScatteringSymbol
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageSphericalScatteringSymbol S) := by
  unfold fieldOneFiniteStageSphericalScatteringSymbol
  apply _root_.RHTower.ccmArchimedeanScatteringPhase_hasTemperateGrowth.1.continuous.mul
  exact continuous_finsetProd _ fun v _ =>
    continuous_primeRatio (Rat.HeightOneSpectrum.primesEquiv v.1)

theorem norm_fieldOneFiniteStageSphericalScatteringSymbol
    (S : Finset (HeightOneSpectrum ℤ)) (t : ℝ) :
    ‖fieldOneFiniteStageSphericalScatteringSymbol S t‖ = 1 := by
  rw [fieldOneFiniteStageSphericalScatteringSymbol, norm_mul,
    _root_.RHTower.norm_ccmArchimedeanScatteringPhase, one_mul, norm_prod]
  exact Finset.prod_eq_one fun v _ => by
    simpa [placeRatio] using norm_placeRatio (some
      (Rat.HeightOneSpectrum.primesEquiv v.1 : ℕ)) t

/-- Equation (2.260), with every spherical local phase displayed as the
literal ratio of local `L`-factors. -/
theorem fieldOneFiniteStageSphericalScatteringSymbol_eq_localFactorProduct
    (S : Finset (HeightOneSpectrum ℤ)) (t : ℝ) :
    fieldOneFiniteStageSphericalScatteringSymbol S t =
      archRatio t * ∏ v : ↥S,
        (_root_.RHTower.primeEulerFactor
            (Rat.HeightOneSpectrum.primesEquiv v.1 : ℝ) t /
          _root_.RHTower.primeEulerFactor
            (Rat.HeightOneSpectrum.primesEquiv v.1 : ℝ) (-t)) := by
  rw [fieldOneFiniteStageSphericalScatteringSymbol,
    ← archRatio_eq_ccmArchimedeanScatteringPhase]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  exact primeRatio_eq_localLFactor_ratio
    (Rat.HeightOneSpectrum.primesEquiv v.1)
    (Rat.HeightOneSpectrum.primesEquiv v.1).property.one_lt t

/-- The source product of local ratios as a measurable unit-modulus phase. -/
def fieldOneFiniteStageSphericalScatteringPhase
    (S : Finset (HeightOneSpectrum ℤ)) :
    UnitModulusL2Phase ℝ (volume : Measure ℝ) where
  toFun := fieldOneFiniteStageSphericalScatteringSymbol S
  aestronglyMeasurable :=
    (continuous_fieldOneFiniteStageSphericalScatteringSymbol S).aestronglyMeasurable
  norm_eq_one := Filter.Eventually.of_forall
    (norm_fieldOneFiniteStageSphericalScatteringSymbol S)

/-- Multiplication by the complete spherical product of local ratios is an
onto linear isometry of radial spectral `L²`. -/
def fieldOneFiniteStageSphericalScatteringUnitary
    (S : Finset (HeightOneSpectrum ℤ)) :
    Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (fieldOneFiniteStageSphericalScatteringPhase S).mulUnitary

theorem fieldOneFiniteStageSphericalScatteringUnitary_ae
    (S : Finset (HeightOneSpectrum ℤ))
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    fieldOneFiniteStageSphericalScatteringUnitary S f =ᵐ[volume]
      fun t => fieldOneFiniteStageSphericalScatteringSymbol S t * f t :=
  (fieldOneFiniteStageSphericalScatteringPhase S).mulUnitary_ae f

end
end GaloisForLFunctions.RHTower
