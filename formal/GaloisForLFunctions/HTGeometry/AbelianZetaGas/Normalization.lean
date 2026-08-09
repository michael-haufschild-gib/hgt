import GaloisForLFunctions.HTGeometry.AbelianZetaGas.GibbsLaw
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.ENNReal.BigOperators

/-!
# Abelian zeta gas: Erdős--Szekeres normalization

This file identifies the global zero-occupation product with the inverse of the complete zeta
depth ladder.  It also factors every product-measure atom into that same normalizer times the
intrinsic order/socle Gibbs weight.  All products remain countably infinite.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

namespace AbelianZetaConvergentParameters

/-- All prime-depth failure ratios are summable in the exact first-depth chamber. -/
theorem summable_ratio (θ : AbelianZetaConvergentParameters) :
    Summable θ.toAbelianZetaParameters.ratio := by
  have hs := summable_abelianZetaRatio_indicator_depth θ.toAbelianZetaParameters
    (g := 1) (by omega) (by simpa using θ.firstDepth)
  refine hs.congr fun m => ?_
  rw [Set.indicator_of_mem]
  exact AbelianZetaMode.depth_pos m

/-- Complex zero-occupation normalizer.  It is real and positive, but the complex carrier is the
natural codomain for its zeta-product identity. -/
def complexNormalizer (θ : AbelianZetaConvergentParameters) : ℂ :=
  ∏' m : AbelianZetaMode, (1 - (θ.toAbelianZetaParameters.ratio m : ℂ))

/-- Complete infinite-depth zeta partition function. -/
def zetaPartition (θ : AbelianZetaConvergentParameters) : ℂ :=
  ∏' n : ℕ, riemannZeta
    ((((n + 1 : ℕ) : ℝ) * θ.sigma + θ.tau : ℝ) : ℂ)

private theorem depth_exponent_gt_one (θ : AbelianZetaConvergentParameters) (n : ℕ) :
    1 < ((n + 1 : ℕ) : ℝ) * θ.sigma + θ.tau := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmul : 0 ≤ (n : ℝ) * θ.sigma := mul_nonneg hn θ.sigma_pos.le
  have heq : ((n + 1 : ℕ) : ℝ) * θ.sigma + θ.tau =
      (θ.sigma + θ.tau) + (n : ℝ) * θ.sigma := by
    push_cast
    ring
  rw [heq]
  linarith [θ.firstDepth]

set_option maxHeartbeats 800000 in
private theorem hasProd_prime_zeroFactor
    (θ : AbelianZetaConvergentParameters) (n : ℕ) :
    HasProd
      (fun p : Nat.Primes =>
        1 - (θ.toAbelianZetaParameters.ratio (p, n) : ℂ))
      (riemannZeta ((((n + 1 : ℕ) : ℝ) * θ.sigma + θ.tau : ℝ) : ℂ))⁻¹ := by
  let s : ℂ := ((((n + 1 : ℕ) : ℝ) * θ.sigma + θ.tau : ℝ) : ℂ)
  have hs : 1 < s.re := by
    simpa [s] using θ.depth_exponent_gt_one n
  have h := (riemannZeta_eulerProduct_hasProd hs).inv
  refine h.congr fun p => ?_
  simp only [inv_inv]
  have hratio : (θ.toAbelianZetaParameters.ratio (p, n) : ℂ) =
      (p : ℂ) ^ (-s) := by
    rw [AbelianZetaParameters.ratio, AbelianZetaParameters.exponent]
    simp only [AbelianZetaMode.depth_mk]
    rw [Complex.ofReal_cpow (by exact_mod_cast p.prop.pos.le)]
    congr 2
    simp [s]
  rw [hratio]

set_option maxHeartbeats 800000 in
/-- **Erdős--Szekeres normalization.**  The exact countable zero-occupation constant is the
inverse of the complete zeta ladder `prod_{j>=1} zeta(j sigma + tau)`. -/
theorem complexNormalizer_eq_zetaPartition_inv (θ : AbelianZetaConvergentParameters) :
    θ.complexNormalizer = θ.zetaPartition⁻¹ := by
  have hsComplex : Summable
      (fun m : AbelianZetaMode => -((θ.toAbelianZetaParameters.ratio m : ℂ))) := by
    exact ((Complex.summable_ofReal).2 θ.summable_ratio).neg
  have hmul : Multipliable
      (fun m : AbelianZetaMode => 1 - (θ.toAbelianZetaParameters.ratio m : ℂ)) := by
    simpa only [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable hsComplex
  have hglobal : HasProd
      (fun m : AbelianZetaMode => 1 - (θ.toAbelianZetaParameters.ratio m : ℂ))
      θ.complexNormalizer := hmul.hasProd
  have hreindexed : HasProd
      (fun x : ℕ × Nat.Primes =>
        1 - (θ.toAbelianZetaParameters.ratio (x.2, x.1) : ℂ))
      θ.complexNormalizer := by
    exact ((Equiv.prodComm ℕ Nat.Primes).hasProd_iff).2 hglobal
  have houter : HasProd
      (fun n : ℕ =>
        (riemannZeta ((((n + 1 : ℕ) : ℝ) * θ.sigma + θ.tau : ℝ) : ℂ))⁻¹)
      θ.complexNormalizer :=
    hreindexed.prod_fiberwise (θ.hasProd_prime_zeroFactor)
  have hinv := houter.inv
  have hzeta : HasProd
      (fun n : ℕ =>
        riemannZeta ((((n + 1 : ℕ) : ℝ) * θ.sigma + θ.tau : ℝ) : ℂ))
      θ.complexNormalizer⁻¹ := by
    simpa only [inv_inv] using hinv
  rw [zetaPartition, hzeta.tprod_eq]

/-- Finite positive zero factor in the probability codomain. -/
def nnZeroFactor (θ : AbelianZetaConvergentParameters) (m : AbelianZetaMode) : ℝ≥0 :=
  ⟨1 - θ.toAbelianZetaParameters.ratio m,
    sub_nonneg.mpr (θ.toAbelianZetaParameters.ratio_le_one m)⟩

/-- NNReal zero-occupation normalizer. -/
def nnNormalizer (θ : AbelianZetaConvergentParameters) : ℝ≥0 :=
  ∏' m : AbelianZetaMode, θ.nnZeroFactor m

/-- ENNReal zero-occupation normalizer appearing in the actual product probability measure. -/
def ennNormalizer (θ : AbelianZetaConvergentParameters) : ℝ≥0∞ := θ.nnNormalizer

private theorem nnZeroFactor_multipliable (θ : AbelianZetaConvergentParameters) :
    Multipliable θ.nnZeroFactor := by
  have hlog : Summable (fun m : AbelianZetaMode =>
      Real.log (1 - θ.toAbelianZetaParameters.ratio m)) := by
    simpa only [sub_eq_add_neg] using
      Real.summable_log_one_add_of_summable θ.summable_ratio.neg
  let a : ℝ≥0 := ⟨Real.exp (∑' m : AbelianZetaMode,
    Real.log (1 - θ.toAbelianZetaParameters.ratio m)), Real.exp_nonneg _⟩
  have hreal : HasProd
      (fun m : AbelianZetaMode => (θ.nnZeroFactor m : ℝ)) (a : ℝ) := by
    apply Real.hasProd_of_hasSum_log
    · intro m
      exact sub_pos.mpr (θ.toAbelianZetaParameters.ratio_lt_one m)
    · exact hlog.hasSum
  exact (NNReal.isClosedEmbedding_coe.isInducing.hasProd_iff
    (g := NNReal.toRealHom.toMonoidHom) θ.nnZeroFactor a).mp hreal
    |>.multipliable

/-- **Exact zeta-Gibbs atom law.**  Every canonical finite abelian group class has probability
`C * |A|^-sigma * |soc A|^-tau`, with the same infinite zero-occupation normalizer `C`. -/
theorem classMass_eq_ennNormalizer_mul_twoObservableWeight
    (θ : AbelianZetaConvergentParameters) (A : AbelianZetaGroupClass) :
    abelianZetaClassMass θ.toAbelianZetaParameters A =
      θ.ennNormalizer *
        ENNReal.ofReal (abelianZetaTwoObservableWeight θ.toAbelianZetaParameters A) := by
  let c : AbelianZetaMode → ℝ≥0∞ := fun m =>
    θ.nnZeroFactor m
  let cNN : AbelianZetaMode → ℝ≥0 := θ.nnZeroFactor
  let gNN : AbelianZetaMode → ℝ≥0 := fun m =>
    ⟨(θ.toAbelianZetaParameters.ratio m) ^ (A m),
      pow_nonneg (θ.toAbelianZetaParameters.ratio_nonneg m) _⟩
  let g : AbelianZetaMode → ℝ≥0∞ := fun m => gNN m
  have hcNN : Multipliable cNN := by simpa [cNN] using θ.nnZeroFactor_multipliable
  have hgNN : Multipliable gNN := by
    apply multipliable_of_hasFiniteMulSupport
    apply A.support.finite_toSet.subset
    intro m hm
    by_contra hmsupp
    have hAm : A m = 0 := by simpa using hmsupp
    exact hm (by ext; simp [gNN, hAm])
  have hcgNN : Multipliable (fun m => cNN m * gNN m) := hcNN.mul hgNN
  have hlocal : (fun m : AbelianZetaMode =>
      ENNReal.ofReal ((θ.toAbelianZetaParameters.ratio m) ^ (A m) *
        (1 - θ.toAbelianZetaParameters.ratio m))) = fun m => c m * g m := by
    funext m
    rw [ENNReal.ofReal_mul (pow_nonneg (θ.toAbelianZetaParameters.ratio_nonneg m) _)]
    simp only [c, g, gNN, nnZeroFactor, ENNReal.coe_nnreal_eq]
    rw [mul_comm]
  have htgNN : ((∏' m : AbelianZetaMode, gNN m : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (abelianZetaModeWeight θ.toAbelianZetaParameters A) := by
    rw [tprod_eq_prod (s := A.support)]
    · rw [ENNReal.coe_finsetProd]
      rw [← ENNReal.ofReal_prod_of_nonneg]
      · rfl
      · intro m hm
        exact pow_nonneg (θ.toAbelianZetaParameters.ratio_nonneg m) _
    · intro m hm
      have hAm : A m = 0 := by simpa using hm
      ext
      simp [gNN, hAm]
  have hmap : ((∏' m : AbelianZetaMode, cNN m * gNN m : ℝ≥0) : ℝ≥0∞) =
      ∏' m : AbelianZetaMode, c m * g m := by
    simpa [c, cNN, g] using
      hcgNN.map_tprod ENNReal.ofNNRealHom.toMonoidHom ENNReal.continuous_coe
  rw [abelianZetaClassMass_eq_tprod, hlocal, ← hmap, hcNN.tprod_mul hgNN]
  change (θ.nnNormalizer : ℝ≥0∞) *
    ((∏' m : AbelianZetaMode, gNN m : ℝ≥0) : ℝ≥0∞) = _
  rw [htgNN]
  rw [abelianZetaModeWeight_eq_twoObservableWeight]

end AbelianZetaConvergentParameters

end GaloisForLFunctions.HTGeometry
