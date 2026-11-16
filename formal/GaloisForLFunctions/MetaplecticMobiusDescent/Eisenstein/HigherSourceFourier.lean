import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.HigherSourceCuspJets
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.BesselFourierJets
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.SourceCuspMellinReflection
import GaloisForLFunctions.FamilyContinuationTheory.TheSexticGrossencharacterFactorizesTheProbeCorrection

/-!
# Higher source jets and angular Fourier weights

The actual higher source profiles have exact Fourier expansions obtained by raising their
linear Wirtinger frequency weights. At orders congruent to one modulo six, these powers
split into a radial norm power and the sextic archimedean character, with opposite angular
orientations on the two sides of cusp reflection.
-/

open Complex Set
open scoped ContDiff ComplexConjugate Classical MatrixGroups
open HTGeometry
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource
open GaloisForLFunctions.FamilyContinuationTheory
noncomputable section

/-- The normalized antiholomorphic source jet has exact conjugate-frequency powers. -/
theorem higherSourceBarProfile_eq_besselPlaneSeries (n : ℕ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    higherSourceBarProfile n z v = (v : ℂ) ^ (n + 1) *
      conj (besselPlaneSeries (1 / 3)
        (fun h => cuspHolWeight h ^ (n + 1) * rationalSourceResidualFourierCoefficient h)
          (v, z)) := by
  have hs : ContDiff ℝ ∞ (fun w => conj (cubicSourceResidualFunction
      (cuspCoordinateLift (v, w)))) :=
    Complex.conjCLE.contDiff.comp (cubicSource_horizontal_contDiff v hv)
  have ht := congrFun (iteratedDzbar_comp_affine hs 1 z (n + 1)) 0
  simp only [map_one, one_mul, one_pow, add_zero] at ht
  have hswap : (fun w => conj (cubicSourceResidualFunction (cuspCoordinateLift (v, w + z)))) =
      fun w => conj (cubicSourceResidualFunction (cuspCoordinateLift (v, z + w))) := by
    funext w
    rw [add_comm w z]
  rw [higherSourceBarProfile, hswap, ht, conjugate_cubicSource_iteratedDzbar_bessel v hv]
  rw [pow_succ]
  ring

/-- The three first-order cusp representatives belong to the same Fourier–Bessel family. -/
lemma sourceCuspZFamily_eq_conjugate_besselPlaneSeries (j : Fin 3) (v : ℝ) (hv : 0 < v)
    (z : ℂ) :
    sourceCuspZFamily j z v = ((v / sourceCuspScale j : ℝ) : ℂ) *
      conj (besselPlaneSeries (1 / 3) (sourceCuspBarCoefficient j)
        (v / sourceCuspScale j, z / (sourceCuspScale j : ℂ))) := by
  rw [sourceCuspZFamily_series j z v hv]
  simp only [sourceCuspZTerm, cubicBesselTerm_eq_besselPlaneTerm _ _
    (v / sourceCuspScale j, z / (sourceCuspScale j : ℂ))
    (div_pos hv (sourceCuspScale_pos j))]
  rw [← tsum_star, tsum_mul_left]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal, besselPlaneSeries]
  exact mul_comm _ _

/-- Exact higher holomorphic cusp coefficients, including the cusp width. -/
theorem higherSourceZFamily_eq_besselPlaneSeries (n : ℕ) (j : Fin 3) (z : ℂ)
    (v : ℝ) (hv : 0 < v) :
    higherSourceZFamily n j z v = (v : ℂ) ^ n *
      ((v / sourceCuspScale j : ℝ) : ℂ) * ((sourceCuspScale j : ℂ)⁻¹) ^ n *
        conj (besselPlaneSeries (1 / 3)
          (fun h => cuspAntiholWeight h ^ n * sourceCuspBarCoefficient j h)
          (v / sourceCuspScale j, z / (sourceCuspScale j : ℂ))) := by
  have hc : CuspSubexponential (sourceCuspBarCoefficient j) :=
    sourceCuspBarCoefficient_subexponential j
  have hvq := div_pos hv (sourceCuspScale_pos j)
  have hs := contDiff_besselPlaneSeries_slice (1 / 3) hc (v / sourceCuspScale j) hvq
  have hg : ContDiff ℝ ∞ (fun w => conj (besselPlaneSeries (1 / 3)
      (sourceCuspBarCoefficient j) (v / sourceCuspScale j, w))) :=
    Complex.conjCLE.contDiff.comp hs
  have hbase : dz (fun w => conj (cubicSourceResidualFunction
      (integralComplexMatrix (cuspRepresentative j) • cuspCoordinateLift (v, w)))) =
      fun w => sourceCuspZFamily j w v := by
    funext w
    simpa only [higherSourceZFamily, pow_zero, one_mul, iteratedDz] using
      higherSourceZFamily_zero j w v hv
  have hfamily : (fun w => sourceCuspZFamily j w v) =
      fun w => ((v / sourceCuspScale j : ℝ) : ℂ) *
        conj (besselPlaneSeries (1 / 3) (sourceCuspBarCoefficient j)
          (v / sourceCuspScale j, 0 + (sourceCuspScale j : ℂ)⁻¹ * w)) := by
    funext w
    rw [sourceCuspZFamily_eq_conjugate_besselPlaneSeries j v hv]
    simp only [zero_add, div_eq_mul_inv, mul_comm w]
  have hcomp : ContDiff ℝ ∞ (fun w => conj (besselPlaneSeries (1 / 3)
      (sourceCuspBarCoefficient j)
      (v / sourceCuspScale j, 0 + (sourceCuspScale j : ℂ)⁻¹ * w))) :=
    hg.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  rw [higherSourceZFamily, iteratedDz_succ_right, hbase, hfamily,
    HTGeometry.iteratedDz_const_mul hcomp, iteratedDz_comp_affine hg,
    iteratedDz_conjugate hs, iteratedDzbar_besselPlaneSeries _ hc _ hvq]
  simp only [zero_add, div_eq_mul_inv, mul_comm z]
  ring

/-- Every higher initial source is a frequency-power twist of the first-order source. -/
theorem higherSourceBarProfile_fourier (n : ℕ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    higherSourceBarProfile n z v = (v : ℂ) ^ n *
      ∑' h : O, conj (cuspHolWeight h) ^ n *
        conj (cubicBesselTerm sourceZBesselCoefficient h (v, z)) := by
  rw [higherSourceBarProfile_eq_besselPlaneSeries n z v hv]
  have he : (fun h => cuspHolWeight h ^ (n + 1) * rationalSourceResidualFourierCoefficient h) =
      fun h => cuspHolWeight h ^ n * sourceZBesselCoefficient h := by
    funext h
    simp only [pow_succ, sourceZBesselCoefficient, cuspHolWeight]
    ring
  rw [he, conjugate_besselPlaneSeries_weight]
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro h
  rw [cubicBesselTerm_eq_besselPlaneTerm _ _ _ hv]
  simp only [map_mul, map_pow, Complex.conj_ofReal, pow_succ]
  ring

/-- Every higher dual source has exact cusp-width-scaled antiholomorphic frequency powers. -/
theorem higherSourceZFamily_fourier (n : ℕ) (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    higherSourceZFamily n j z v = (v : ℂ) ^ n *
      ∑' h : O, (conj (cuspAntiholWeight h) / (sourceCuspScale j : ℂ)) ^ n *
        sourceCuspZTerm j z v h := by
  rw [higherSourceZFamily_eq_besselPlaneSeries n j z v hv,
    conjugate_besselPlaneSeries_weight]
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro h
  rw [sourceCuspZTerm, cubicBesselTerm_eq_besselPlaneTerm _ _ _
    (div_pos hv (sourceCuspScale_pos j))]
  simp only [map_pow, star_mul, Complex.star_def, Complex.conj_ofReal,
    div_eq_mul_inv]
  ring

/-- A sixth-power conjugate frequency is the angular character times a radial norm cube. -/
lemma conjugate_ringComplex_six_mul (h : O) (hh : h ≠ 0) (k : ℕ) :
    conj (ringComplex h) ^ (6 * k) =
      (sourceCuspRadialLength h : ℂ) ^ (3 * k) * elemPsiSix h ^ k := by
  have hn : (‖ringComplex h‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (ringComplex_ne_zero hh))
  have hp : conj (ringComplex h) = (‖ringComplex h‖ : ℂ) * complexUnitConj (ringComplex h) := by
    rw [complexUnitConj_apply]
    field_simp
  rw [hp, mul_pow, elemPsiSix_apply, ← pow_mul,
    sourceCuspRadialLength, if_neg hh, Complex.ofReal_pow, ← pow_mul]
  congr 1
  congr 1
  omega

/-- The initial source carries precisely positive sextic angular weight. -/
lemma conjugate_cuspHolWeight_six_mul (h : O) (hh : h ≠ 0) (k : ℕ) :
    conj (cuspHolWeight h) ^ (6 * k) =
      conj ((2 * Real.pi * Complex.I) * thetaFrequencyScale) ^ (6 * k) *
        (sourceCuspRadialLength h : ℂ) ^ (3 * k) * elemPsiSix h ^ k := by
  rw [cuspHolWeight, cuspFrequency_eq_thetaFrequencyScale, ← mul_assoc, map_mul, mul_pow,
    conjugate_ringComplex_six_mul h hh k]
  ring

/-- The dual cusp has the opposite angular orientation. -/
lemma ringComplex_six_mul (h : O) (hh : h ≠ 0) (k : ℕ) :
    ringComplex h ^ (6 * k) =
      (sourceCuspRadialLength h : ℂ) ^ (3 * k) * conj (elemPsiSix h) ^ k := by
  have he := congrArg conj (conjugate_ringComplex_six_mul h hh k)
  have hcc (z : ℂ) : conj (conj z) = z := star_star z
  simpa only [map_pow, map_mul, Complex.conj_ofReal, hcc] using he

lemma conjugate_cuspAntiholWeight_six_mul (j : Fin 3) (h : O) (hh : h ≠ 0) (k : ℕ) :
    (conj (cuspAntiholWeight h) / (sourceCuspScale j : ℂ)) ^ (6 * k) =
      ((-2 * Real.pi * Complex.I * thetaFrequencyScale) / (sourceCuspScale j : ℂ)) ^ (6 * k) *
        (sourceCuspRadialLength h : ℂ) ^ (3 * k) * conj (elemPsiSix h) ^ k := by
  have he : conj (cuspAntiholWeight h) / (sourceCuspScale j : ℂ) =
      ((-2 * Real.pi * Complex.I * thetaFrequencyScale) / (sourceCuspScale j : ℂ)) *
        ringComplex h := by
    simp only [cuspAntiholWeight, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
      show ∀ z : ℂ, conj (conj z) = z from fun z => star_star z,
      cuspFrequency_eq_thetaFrequencyScale, div_eq_mul_inv]
    ring
  rw [he, mul_pow, ringComplex_six_mul h hh k]
  ring

/-- The radial kernel for derivative order `6k+1`, with its unchanged Dirichlet exponent. -/
def angularRadialBesselProfile {ι : Type*} (k : ℕ) (r : ι → ℝ) (a : ι → ℂ)
    (q v : ℝ) : ℂ :=
  (v : ℂ) ^ (6 * k) * radialBesselProfile r (fun h => (r h : ℂ) ^ (3 * k) * a h) q v

/-- The higher initial source is the positive sextic twist of the radial Bessel source. -/
theorem higherSourceBarProfile_eq_angularRadial (k : ℕ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    higherSourceBarProfile (6 * k) z v =
      conj ((2 * Real.pi * Complex.I) * thetaFrequencyScale) ^ (6 * k) *
        angularRadialBesselProfile k sourceCuspRadialLength
          (fun h => elemPsiSix h ^ k * sourceBarRadialCoefficient z h)
          (sourceCuspRadialScale 0) v := by
  rw [higherSourceBarProfile_fourier _ z v hv, angularRadialBesselProfile, radialBesselProfile]
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro h
  by_cases hh : h = 0
  · subst h
    simp only [cubicBesselTerm, cubicBesselAmplitude, if_true, zero_mul,
      map_zero, mul_zero, sourceBarRadialCoefficient, sourceCuspRadialCoefficient_zero]
  · rw [conjugate_cuspHolWeight_six_mul h hh k]
    change _ * (_ * star (cubicBesselTerm sourceZBesselCoefficient h (v, z))) = _
    rw [sourceZBesselTerm_eq_rotated, sourceCuspZTerm_eq_radial 0 z v hv h]
    unfold sourceBarRadialCoefficient
    ring

/-- The three higher dual sources are the negative sextic twists of their radial sources. -/
theorem higherSourceZFamily_eq_angularRadial (k : ℕ) (j : Fin 3) (z : ℂ)
    (v : ℝ) (hv : 0 < v) :
    higherSourceZFamily (6 * k) j z v =
      ((-2 * Real.pi * Complex.I * thetaFrequencyScale) / (sourceCuspScale j : ℂ)) ^ (6 * k) *
        angularRadialBesselProfile k sourceCuspRadialLength
          (fun h => conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient j z h)
          (sourceCuspRadialScale j) v := by
  rw [higherSourceZFamily_fourier _ j z v hv, angularRadialBesselProfile, radialBesselProfile]
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro h
  by_cases hh : h = 0
  · subst h
    simp only [sourceCuspZTerm_zero, mul_zero, zero_mul, sourceCuspRadialCoefficient_zero]
  · rw [conjugate_cuspAntiholWeight_six_mul j h hh k, sourceCuspZTerm_eq_radial j z v hv h]
    ring

/-- The cusp frequency scale is purely imaginary. -/
lemma thetaFrequencyScale_conjugate : conj thetaFrequencyScale = -thetaFrequencyScale := by
  simp only [thetaFrequencyScale, map_div₀, map_one, map_mul, map_ofNat,
    complex_traceLambda_conjugate, mul_neg, div_neg]

/-- The initial angular normalization is real. -/
lemma sourceAngularNormalization_conjugate :
    conj ((2 * Real.pi * Complex.I) * thetaFrequencyScale) =
      (2 * Real.pi * Complex.I) * thetaFrequencyScale := by
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    thetaFrequencyScale_conjugate]
  ring

/-- Cusp-width powers cancel the complete higher-order Fourier normalization. -/
lemma sourceCuspAngularNormalization_cancel (j : Fin 3) (k : ℕ) :
    ((-2 * Real.pi * Complex.I * thetaFrequencyScale) / (sourceCuspScale j : ℂ)) ^ (6 * k) *
        (sourceCuspScale j : ℂ) ^ (6 * k) =
      conj ((2 * Real.pi * Complex.I) * thetaFrequencyScale) ^ (6 * k) := by
  rw [← mul_pow, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne'),
    sourceAngularNormalization_conjugate]
  have he : -2 * Real.pi * Complex.I * thetaFrequencyScale =
      -((2 * Real.pi * Complex.I) * thetaFrequencyScale) := by ring
  rw [he, pow_mul, pow_mul]
  congr 1
  ring

lemma sourceAngularNormalization_ne_zero :
    conj ((2 * Real.pi * Complex.I) * thetaFrequencyScale) ≠ 0 := by
  have ht : thetaFrequencyScale ≠ 0 := norm_pos_iff.mp thetaBesselScale_pos
  exact star_ne_zero.mpr (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero) ht)

/-- Higher cusp multipliers differ from the order-one multiplier by a pure unit phase. -/
lemma SourceCuspDatum.jetMultiplier_six_mul (d : SourceCuspDatum) (k : ℕ) :
    d.jetMultiplier (6 * k) = d.multiplier *
      (-conj (d.matrix 1 0) / d.matrix 1 0) ^ (6 * k) := by
  rw [← d.jetMultiplier_zero]
  simp only [SourceCuspDatum.jetMultiplier, zero_add, pow_succ]
  ring


end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
