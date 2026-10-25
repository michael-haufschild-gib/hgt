import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PoissonPrincipalCyclesOnTheScalingSurface
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerConvolutionTopology

/-!
# Positive origin degree does not descend through Poisson boundaries

Origin evaluation of an actual source sharp square is its strictly positive exponential
mass. A nonzero Xi cap supplies a genuine boundary with positive square degree. Thus this
linear positive source degree cannot factor through the actual Poisson cohomology.
-/

noncomputable section
open Complex MeasureTheory Zeta23 RHTower
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Origin evaluation is a linear degree on actual logarithmic sources. -/
def meyerOriginDegree : DeningerMeyerStrongLogTarget →ₗ[ℂ] ℂ where
  toFun g := g.val 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem sharp_product_integrand (g : DeningerMeyerStrongLogTarget) (t : ℝ) :
    g.val t * (deningerMeyerSourceSharp g).val (0 - t) =
      ((Real.exp t * Complex.normSq (g.val t) : ℝ) : ℂ) := by
  simp only [deningerMeyerSourceSharp, deningerMeyerStrongLogJ_apply,
    deningerMeyerStrongLogConj_apply, zero_sub, neg_neg]
  change g.val t * ((Real.exp t : ℂ) * (starRingEnd ℂ) (g.val t)) = _
  rw [← mul_assoc, mul_comm (g.val t) (Real.exp t : ℂ), mul_assoc, Complex.mul_conj]
  exact (Complex.ofReal_mul _ _).symm

private theorem weighted_mass_integrable (g : DeningerMeyerStrongLogTarget) :
    Integrable (fun t : ℝ => Real.exp t * Complex.normSq (g.val t)) := by
  have hi := (deningerMeyerSourceConvolution_integrable g (deningerMeyerSourceSharp g) 0).re
  change Integrable (fun t : ℝ =>
    (g.val t * (deningerMeyerSourceSharp g).val (0 - t)).re) at hi
  simpa only [sharp_product_integrand, Complex.ofReal_re] using hi

/-- The linear origin degree of a sharp square is its exact positive weighted source mass. -/
theorem meyerOriginDegree_sharp_square (g : DeningerMeyerStrongLogTarget) :
    meyerOriginDegree (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)) =
      ((∫ t : ℝ, Real.exp t * Complex.normSq (g.val t) : ℝ) : ℂ) := by
  change (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)).val 0 = _
  rw [deningerMeyerSourceConvolution_apply, ← integral_complex_ofReal]
  exact integral_congr_ae (Filter.Eventually.of_forall (sharp_product_integrand g))

/-- Origin square degree vanishes precisely for the zero actual source. -/
theorem meyerOriginDegree_sharp_square_eq_zero_iff (g : DeningerMeyerStrongLogTarget) :
    (meyerOriginDegree (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g))).re = 0 ↔
      g = 0 := by
  rw [meyerOriginDegree_sharp_square, Complex.ofReal_re]
  constructor
  · intro hz
    have hn : 0 ≤ fun t : ℝ => Real.exp t * Complex.normSq (g.val t) :=
      fun t => mul_nonneg (Real.exp_pos t).le (Complex.normSq_nonneg _)
    have hae := (integral_eq_zero_iff_of_nonneg hn (weighted_mass_integrable g)).mp hz
    have hc : Continuous (fun t : ℝ => Real.exp t * Complex.normSq (g.val t)) :=
      Real.continuous_exp.mul (Complex.continuous_normSq.comp g.property.smooth.continuous)
    have he := MeasureTheory.Measure.eq_of_ae_eq hae hc continuous_zero
    apply Subtype.ext
    funext t
    have ht := congrFun he t
    change Real.exp t * Complex.normSq (g.val t) = 0 at ht
    exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp ht).resolve_left (Real.exp_ne_zero t))
  · rintro rfl
    simp only [Submodule.coe_zero, Pi.zero_apply, Complex.normSq_zero, mul_zero, integral_zero]

/-- This arithmetic square degree is strictly positive on every nonzero source, without RH. -/
theorem meyerOriginDegree_sharp_square_pos {g : DeningerMeyerStrongLogTarget} (hg : g ≠ 0) :
    0 < (meyerOriginDegree (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g))).re := by
  have hn : 0 ≤ (meyerOriginDegree
      (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g))).re := by
    rw [meyerOriginDegree_sharp_square, Complex.ofReal_re]
    exact integral_nonneg fun t => mul_nonneg (Real.exp_pos t).le (Complex.normSq_nonneg _)
  by_contra h
  exact hg ((meyerOriginDegree_sharp_square_eq_zero_iff g).mp
    (le_antisymm (le_of_not_gt h) hn))

/-- A genuine Poisson boundary has strictly positive origin degree after taking its sharp square. -/
theorem exists_meyer_boundary_positive_originDegree :
    ∃ q : DeningerMeyerStrongLogTarget,
      q ∈ LinearMap.range deningerMeyerStrongLogSumLM ∧ 0 < (meyerOriginDegree q).re := by
  let g := deningerMeyerStrongLogSumLM deningerMeyerXiCapSource
  have hg : g ≠ 0 := by
    intro hz
    have hM := deningerMeyerXiCapSource_mellin 1
    change deningerMeyerStrongLogMellinLM 1 g = xi 1 at hM
    rw [hz, map_zero, xi_one] at hM
    norm_num at hM
  refine ⟨deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g), ?_,
    meyerOriginDegree_sharp_square_pos hg⟩
  obtain ⟨k, hk⟩ := deningerMeyerSourceConvolution_boundary
    (deningerMeyerSourceSharp g) deningerMeyerXiCapSource
  refine ⟨k, ?_⟩
  rw [hk, deningerMeyerSourceConvolution_comm]

/-- Strictly positive origin degree cannot descend through genuine Poisson boundaries. -/
theorem meyerOriginDegree_not_cohomology_degree :
    ¬ ∃ d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ,
      ∀ g : DeningerMeyerStrongLogTarget, d (Submodule.Quotient.mk g) = meyerOriginDegree g := by
  rintro ⟨d, hd⟩
  obtain ⟨q, hq, hpos⟩ := exists_meyer_boundary_positive_originDegree
  have hz : (Submodule.Quotient.mk q : DeningerMeyerStrongLogCohomology) = 0 :=
    (Submodule.Quotient.mk_eq_zero (LinearMap.range deningerMeyerStrongLogSumLM)).mpr hq
  have he := hd q
  rw [hz, map_zero] at he
  rw [← he, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
