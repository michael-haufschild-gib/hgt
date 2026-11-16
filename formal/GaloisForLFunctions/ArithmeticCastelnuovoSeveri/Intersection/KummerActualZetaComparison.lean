import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Intersection.KummerFrobeniusDefect
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRegularDifferentialDimension
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTentActualZetaDetectionAndFullZeroFormBridge

/-!
# Kummer square sums and the actual zeta Weil form

The genus-one Kummer curve over the field of four elements realizes one
complex squared norm by two real Frobenius-span forms. Evaluating these
forms at the literal zeta zeros, with their multiplicities, gives positive
finite sums converging to the square mass. The actual von Mangoldt Weil
functional is their limit minus the reflection defect. Thus the comparison
preserves the square mass, while its correction retains the arithmetic
positivity question.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open Complex Filter Topology
open scoped BigOperators ComplexConjugate
open ArithmeticHarmonicAnalysis ArithmeticPositivityTheory SquareRootThreshold
open _root_.Zeta23

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Two singleton Frobenius forms of the actual genus-one Kummer calibration over `𝔽₄`. -/
def kummerComplexSquare (z : ℂ) : ℝ :=
  ((primePowerKummerCurveDatum 2 0 0 1).toeplitz {0} (fun _ => z.re) +
    (primePowerKummerCurveDatum 2 0 0 1).toeplitz {0} (fun _ => z.im)) / 2

/-- The actual differential dimension supplies precisely the multiplicity two. -/
theorem kummerComplexSquare_eq (z : ℂ) : kummerComplexSquare z = ‖z‖ ^ 2 := by
  let g := Module.finrank (SquareConstantField 2 (kummerSquareIndex 0 0))
    (globalRegularDifferentials (SquareConstantField 2 (kummerSquareIndex 0 0))
      (SquareKummerField 2 (kummerSquareIndex 0 0)
        ((kummerTraceConstant 2 (kummerSquareIndex 0 0))⁻¹ ^ kummerExponent (2 ^ (0 + 1)) 1)
        (2 ^ (0 + 1) - 2) (kummerExponent (2 ^ (0 + 1)) 1)))
  have hg := squareKummer_regularDifferential_finrank_twice 2 (kummerSquareIndex 0 0)
    ((kummerTraceConstant 2 (kummerSquareIndex 0 0))⁻¹ ^ kummerExponent (2 ^ (0 + 1)) 1)
    0 1
  norm_num [kummerSquareIndex, kummerExponent] at hg
  have hg' : ((2 * g : ℕ) : ℝ) = 2 := by exact_mod_cast hg
  rw [kummerComplexSquare, primePowerKummerCurveDatum_toeplitz,
    primePowerKummerCurveDatum_toeplitz]
  simp only [Finset.sum_singleton, pow_zero, mul_one]
  change (((2 * g : ℕ) : ℝ) * ‖(z.re : ℂ)‖ ^ 2 +
    ((2 * g : ℕ) : ℝ) * ‖(z.im : ℂ)‖ ^ 2) / 2 = ‖z‖ ^ 2
  rw [hg']
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Positive Kummer forms sampled at a finite set of literal zeta zeros. -/
def zetaKummerSquareSum (S : Finset zetaZeroConfig.carrier) (f : ℝ → ℂ) : ℝ :=
  ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * kummerComplexSquare (paperFT f (gammaOf ρ))

/-- Reflection displacement measured by the same finite-field forms. -/
def zetaKummerReflectionSum (S : Finset zetaZeroConfig.carrier) (f : ℝ → ℂ) : ℝ :=
  ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) / 2 *
    kummerComplexSquare (paperFT f (gammaOf ρ) - paperFT f (conj (gammaOf ρ)))

theorem zetaKummerSquareSum_nonneg (S : Finset zetaZeroConfig.carrier) (f : ℝ → ℂ) :
    0 ≤ zetaKummerSquareSum S f := by
  unfold zetaKummerSquareSum
  exact Finset.sum_nonneg fun ρ _ =>
    mul_nonneg (Nat.cast_nonneg _) (by rw [kummerComplexSquare_eq]; positivity)

theorem zetaKummerReflectionSum_nonneg (S : Finset zetaZeroConfig.carrier) (f : ℝ → ℂ) :
    0 ≤ zetaKummerReflectionSum S f := by
  unfold zetaKummerReflectionSum
  exact Finset.sum_nonneg fun ρ _ =>
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num))
      (by rw [kummerComplexSquare_eq]; positivity)

/-- The positive finite-field sums converge unconditionally to the actual zeta square mass. -/
theorem zetaKummerSquareSum_tendsto {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Tendsto (fun S : Finset zetaZeroConfig.carrier => zetaKummerSquareSum S f)
      atTop (𝓝 (configurationSquareMass zetaZeroConfig f)) := by
  simpa only [zetaKummerSquareSum, kummerComplexSquare_eq, configurationSquareMass] using
    (summable_squareMass_of_temperedConfig zetaZeroConfig temperedConfig_zetaZeroConfig
      hf hfc).hasSum

/-- The reflection corrections are themselves positive finite-field sums with an
unconditionally convergent limit. -/
theorem zetaKummerReflectionSum_tendsto {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Tendsto (fun S : Finset zetaZeroConfig.carrier => zetaKummerReflectionSum S f)
      atTop (𝓝 (configurationReflectionDefect zetaZeroConfig f)) := by
  let s : zetaZeroConfig.carrier → ℝ := fun ρ =>
    (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2
  let e := zeroConfigReflectPerm zetaZeroConfig
  have hs : Summable s :=
    summable_squareMass_of_temperedConfig zetaZeroConfig temperedConfig_zetaZeroConfig hf hfc
  have hse : Summable (fun ρ => s (e ρ)) := hs.comp_injective e.injective
  have hd : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) / 2 *
        ‖paperFT f (gammaOf ρ) - paperFT f (conj (gammaOf ρ))‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun ρ => mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (by norm_num)) (sq_nonneg _))
      (fun ρ => ?_) (hs.add hse)
    set u := paperFT f (gammaOf ρ)
    set v := paperFT f (conj (gammaOf ρ))
    have hnorm : ‖u - v‖ ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
      nlinarith only [norm_sub_le u v, norm_nonneg (u - v), norm_nonneg u,
        norm_nonneg v, sq_nonneg (‖u‖ - ‖v‖)]
    calc (zetaZeroConfig.mult ρ : ℝ) / 2 * ‖u - v‖ ^ 2
        ≤ (zetaZeroConfig.mult ρ : ℝ) / 2 * (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hnorm (div_nonneg (Nat.cast_nonneg _) (by norm_num))
      _ = s ρ + s (e ρ) := by
        dsimp only [s, e]
        rw [zeroConfigSquareSummand_reflectPerm]
        dsimp only [u, v]
        ring
  simpa only [zetaKummerReflectionSum, kummerComplexSquare_eq,
    configurationReflectionDefect] using hd.hasSum

/-- The literal arithmetic functional differs from the positive finite-field limit by
exactly the zero-reflection defect. -/
theorem zetaKummerSquareSum_tendsto_weil_add_reflection {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Tendsto (fun S : Finset zetaZeroConfig.carrier => zetaKummerSquareSum S f) atTop
      (𝓝 ((RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f f)).re + configurationReflectionDefect zetaZeroConfig f)) := by
  have h := zeta_squareMass_sub_re_W_eq_reflectionDefect hf hfc
  rw [RHTower.zeta_W_eq_weilFullFunctional_mixed hf hfc hf hfc] at h
  have heq : (RHTower.weilFullFunctional
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (EF.weilTest f f)).re +
      configurationReflectionDefect zetaZeroConfig f = configurationSquareMass zetaZeroConfig f := by
    linarith only [h]
  rw [heq]
  exact zetaKummerSquareSum_tendsto hf hfc

/-- Subtracting the finite reflection sums recovers the literal von Mangoldt functional. -/
theorem zetaKummer_difference_tendsto_actualWeil {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Tendsto (fun S : Finset zetaZeroConfig.carrier =>
      zetaKummerSquareSum S f - zetaKummerReflectionSum S f) atTop
      (𝓝 ((RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f f)).re)) := by
  have h := zeta_squareMass_sub_re_W_eq_reflectionDefect hf hfc
  rw [RHTower.zeta_W_eq_weilFullFunctional_mixed hf hfc hf hfc] at h
  have heq : configurationSquareMass zetaZeroConfig f -
      configurationReflectionDefect zetaZeroConfig f =
      (RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f f)).re := by linarith only [h]
  rw [← heq]
  exact (zetaKummerSquareSum_tendsto hf hfc).sub (zetaKummerReflectionSum_tendsto hf hfc)

/-- On each test, positivity of the actual arithmetic form is precisely the reflection
defect being no larger than the limiting positive finite-field square mass. -/
theorem actualZeta_weil_nonneg_iff_reflection_le_squareMass {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    0 ≤ (RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest f f)).re ↔
      configurationReflectionDefect zetaZeroConfig f ≤ configurationSquareMass zetaZeroConfig f := by
  have h := zeta_squareMass_sub_re_W_eq_reflectionDefect hf hfc
  rw [RHTower.zeta_W_eq_weilFullFunctional_mixed hf hfc hf hfc] at h
  linarith

/-- The global bound needed to transfer the sign is exactly the Riemann hypothesis. -/
theorem riemannHypothesis_iff_zeta_reflection_le_squareMass :
    RiemannHypothesis ↔ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      configurationReflectionDefect zetaZeroConfig f ≤ configurationSquareMass zetaZeroConfig f := by
  rw [RHTower.riemannHypothesis_iff_weilPositiveFull_vonMangoldt]
  constructor
  · intro h f hf hfc
    exact (actualZeta_weil_nonneg_iff_reflection_le_squareMass hf hfc).mp (h f hf hfc)
  · intro h f hf hfc
    exact (actualZeta_weil_nonneg_iff_reflection_le_squareMass hf hfc).mpr (h f hf hfc)

/-- The positive finite-field sums converge to the uncorrected arithmetic Weil form on
every admissible test if and only if the Riemann hypothesis holds. -/
theorem riemannHypothesis_iff_kummer_positive_limit_actualWeil :
    RiemannHypothesis ↔ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Tendsto (fun S : Finset zetaZeroConfig.carrier => zetaKummerSquareSum S f) atTop
        (𝓝 ((RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest f f)).re)) := by
  constructor
  · intro hRH f hf hfc
    have hd : configurationReflectionDefect zetaZeroConfig f = 0 := by
      unfold configurationReflectionDefect
      apply tsum_eq_zero
      intro ρ
      have hre := SquareRootThreshold.riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH ρ ρ.2
      have hc : conj (gammaOf ρ) = gammaOf ρ := by
        apply Complex.ext
        · simp only [Complex.conj_re]
        · simp only [Complex.conj_im, im_gammaOf, hre]
          norm_num
      rw [hc, sub_self, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero]
    simpa only [hd, add_zero] using zetaKummerSquareSum_tendsto_weil_add_reflection hf hfc
  · intro h
    apply RHTower.riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr
    intro f hf hfc
    rw [tendsto_nhds_unique (h f hf hfc) (zetaKummerSquareSum_tendsto hf hfc)]
    exact tsum_nonneg fun ρ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
