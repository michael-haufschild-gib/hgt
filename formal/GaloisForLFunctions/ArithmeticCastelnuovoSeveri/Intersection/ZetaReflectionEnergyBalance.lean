import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTentActualZetaDetectionAndFullZeroFormBridge

/-!
# The unconditional reflection energy balance for the zeta form

Reflection preserves the multiplicity-weighted square mass. The parallelogram
identity therefore splits twice that mass into the squared symmetric sum and
the squared reflection difference. This proves the unconditional bound
`D ≤ 2M`; positivity of the actual Weil form requires the stronger `D ≤ M`.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Complex
open scoped ComplexConjugate
open ArithmeticPositivityTheory SquareRootThreshold
open _root_.Zeta23

private theorem weighted_norm_add_sq_le (m : ℝ) (hm : 0 ≤ m) (u v : ℂ) :
    m / 2 * ‖u + v‖ ^ 2 ≤ m * ‖u‖ ^ 2 + m * ‖v‖ ^ 2 := by
  have hn : ‖u + v‖ ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    nlinarith only [norm_add_le u v, norm_nonneg (u + v), norm_nonneg u,
      norm_nonneg v, sq_nonneg (‖u‖ - ‖v‖)]
  have h := mul_le_mul_of_nonneg_left hn (div_nonneg hm (by norm_num : (0 : ℝ) ≤ 2))
  nlinarith only [h]

private theorem summable_weighted_pair {ι : Type*} (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i)
    (u v : ι → ℂ) (hu : Summable (fun i => m i * ‖u i‖ ^ 2))
    (hv : Summable (fun i => m i * ‖v i‖ ^ 2)) :
    Summable (fun i => m i / 2 * ‖u i + v i‖ ^ 2) :=
  Summable.of_nonneg_of_le
    (fun i => mul_nonneg (div_nonneg (hm i) (by norm_num)) (sq_nonneg _))
    (fun i => weighted_norm_add_sq_le (m i) (hm i) (u i) (v i)) (hu.add hv)

/-- The positive energy of the sum of each transformed value and its reflected value. -/
def configurationReflectionSymmetricMass (Z : ZeroConfig) (f : ℝ → ℂ) : ℝ :=
  ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / 2 *
    ‖paperFT f (gammaOf ρ) + paperFT f (conj (gammaOf ρ))‖ ^ 2

/-- Reflection splits twice the square mass into its symmetric and difference energies. -/
theorem configuration_reflection_energy_balance (Z : ZeroConfig) (f : ℝ → ℂ)
    (hf : Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2)) :
    configurationReflectionSymmetricMass Z f + configurationReflectionDefect Z f =
      2 * configurationSquareMass Z f := by
  let m : Z.carrier → ℝ := fun ρ => Z.mult ρ
  let u : Z.carrier → ℂ := fun ρ => paperFT f (gammaOf ρ)
  let v : Z.carrier → ℂ := fun ρ => paperFT f (conj (gammaOf ρ))
  let e := zeroConfigReflectPerm Z
  have hm (ρ : Z.carrier) : 0 ≤ m ρ := Nat.cast_nonneg _
  have hrefl (ρ : Z.carrier) : m ρ * ‖v ρ‖ ^ 2 = m (e ρ) * ‖u (e ρ)‖ ^ 2 :=
    (zeroConfigSquareSummand_reflectPerm Z f ρ).symm
  have hv : Summable (fun ρ => m ρ * ‖v ρ‖ ^ 2) := by
    simp only [hrefl]
    exact hf.comp_injective e.injective
  have hs := summable_weighted_pair m hm u v hf hv
  have hvneg : Summable (fun ρ => m ρ * ‖-v ρ‖ ^ 2) := by
    simpa only [norm_neg] using hv
  have hd : Summable (fun ρ => m ρ / 2 * ‖u ρ - v ρ‖ ^ 2) := by
    simpa only [sub_eq_add_neg] using summable_weighted_pair m hm u (fun ρ => -v ρ) hf hvneg
  have hpoint (ρ : Z.carrier) :
      m ρ / 2 * ‖u ρ + v ρ‖ ^ 2 + m ρ / 2 * ‖u ρ - v ρ‖ ^ 2 =
        m ρ * ‖u ρ‖ ^ 2 + m ρ * ‖v ρ‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    ring
  change (∑' ρ, m ρ / 2 * ‖u ρ + v ρ‖ ^ 2) +
    (∑' ρ, m ρ / 2 * ‖u ρ - v ρ‖ ^ 2) = 2 * ∑' ρ, m ρ * ‖u ρ‖ ^ 2
  rw [← hs.tsum_add hd, tsum_congr hpoint, hf.tsum_add hv]
  have he : (∑' ρ, m ρ * ‖v ρ‖ ^ 2) = ∑' ρ, m ρ * ‖u ρ‖ ^ 2 := by
    simp only [hrefl]
    exact e.tsum_eq (fun ρ : Z.carrier => m ρ * ‖u ρ‖ ^ 2)
  rw [he]
  ring

/-- Both reflection energies are nonnegative independently of any critical-line claim. -/
theorem configurationReflectionSymmetricMass_nonneg (Z : ZeroConfig) (f : ℝ → ℂ) :
    0 ≤ configurationReflectionSymmetricMass Z f :=
  tsum_nonneg fun ρ => mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num)) (sq_nonneg _)

/-- The literal zeta reflection defect is at most twice its square mass. -/
theorem zeta_reflectionDefect_le_twice_squareMass {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    configurationReflectionDefect zetaZeroConfig f ≤ 2 * configurationSquareMass zetaZeroConfig f := by
  have he := configuration_reflection_energy_balance zetaZeroConfig f
    (summable_squareMass_of_temperedConfig zetaZeroConfig temperedConfig_zetaZeroConfig hf hfc)
  linarith only [he, configurationReflectionSymmetricMass_nonneg zetaZeroConfig f]

/-- The arithmetic Weil form is also the symmetric reflection energy minus square mass. -/
theorem actualZeta_weil_eq_symmetricMass_sub_squareMass {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest f f)).re =
        configurationReflectionSymmetricMass zetaZeroConfig f - configurationSquareMass zetaZeroConfig f := by
  have he := configuration_reflection_energy_balance zetaZeroConfig f
    (summable_squareMass_of_temperedConfig zetaZeroConfig temperedConfig_zetaZeroConfig hf hfc)
  have hw := zeta_squareMass_sub_re_W_eq_reflectionDefect hf hfc
  rw [RHTower.zeta_W_eq_weilFullFunctional_mixed hf hfc hf hfc] at hw
  linarith only [he, hw]

/-- The actual arithmetic form lies between the negative and positive square mass. -/
theorem actualZeta_weil_squareMass_bounds {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    -configurationSquareMass zetaZeroConfig f ≤
      (RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f f)).re ∧
      (RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f f)).re ≤ configurationSquareMass zetaZeroConfig f := by
  have hw := zeta_squareMass_sub_re_W_eq_reflectionDefect hf hfc
  rw [RHTower.zeta_W_eq_weilFullFunctional_mixed hf hfc hf hfc] at hw
  have hd : 0 ≤ configurationReflectionDefect zetaZeroConfig f :=
    tsum_nonneg fun ρ => mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num)) (sq_nonneg _)
  have hb := zeta_reflectionDefect_le_twice_squareMass hf hfc
  constructor <;> linarith only [hw, hd, hb]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
