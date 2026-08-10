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

private theorem hasProd_inv₀ {ι : Type*} {f : ι → ℂ} {a : ℂ}
    (h : HasProd f a) (ha : a ≠ 0) : HasProd (fun i => (f i)⁻¹) a⁻¹ := by
  rw [HasProd] at h ⊢
  simpa only [Finset.prod_inv_distrib] using h.inv₀ ha

private theorem complex_ratio_eq_cpow
    (θ : AbelianZetaConvergentParameters) (n : ℕ) (p : Nat.Primes) :
    (θ.toAbelianZetaParameters.ratio (p, n) : ℂ) =
      (p : ℂ) ^ (-((((n + 1 : ℕ) : ℝ) * θ.sigma + θ.tau : ℝ) : ℂ)) := by
  rw [AbelianZetaParameters.ratio, AbelianZetaParameters.exponent]
  simp only [AbelianZetaMode.depth_mk]
  rw [Complex.ofReal_cpow (by exact_mod_cast p.prop.pos.le)]
  congr 2
  simp

private theorem hasProd_prime_zeroFactor
    (θ : AbelianZetaConvergentParameters) (n : ℕ) :
    HasProd
      (fun p : Nat.Primes =>
        1 - (θ.toAbelianZetaParameters.ratio (p, n) : ℂ))
      (riemannZeta ((((n + 1 : ℕ) : ℝ) * θ.sigma + θ.tau : ℝ) : ℂ))⁻¹ := by
  let s : ℂ := ((((n + 1 : ℕ) : ℝ) * θ.sigma + θ.tau : ℝ) : ℂ)
  have hs : 1 < s.re := by
    simpa [s] using θ.depth_exponent_gt_one n
  have h := hasProd_inv₀ (riemannZeta_eulerProduct_hasProd hs)
    (riemannZeta_ne_zero_of_one_lt_re hs)
  have hfun :
      (fun p : Nat.Primes => 1 - (θ.toAbelianZetaParameters.ratio (p, n) : ℂ)) =
        (fun p : Nat.Primes => ((1 - (p : ℂ) ^ (-s))⁻¹)⁻¹) := by
    funext p
    rw [complex_ratio_eq_cpow]
    change 1 - (p : ℂ) ^ (-s) = ((1 - (p : ℂ) ^ (-s))⁻¹)⁻¹
    simp only [inv_inv]
  rw [hfun]
  exact h

/-- **The complete zeta ladder converges** to the inverse of the zero-occupation constant. -/
theorem hasProd_zetaLadder (θ : AbelianZetaConvergentParameters) :
    HasProd (fun n : ℕ => riemannZeta ((((n + 1 : ℕ) : ℝ) * θ.sigma + θ.tau : ℝ) : ℂ))
      θ.complexNormalizer⁻¹ := by
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
  have hnormalizer_ne : θ.complexNormalizer ≠ 0 := by
    rw [complexNormalizer]
    change (∏' m : AbelianZetaMode,
      (1 + -((θ.toAbelianZetaParameters.ratio m : ℂ)))) ≠ 0
    apply tprod_one_add_ne_zero_of_summable
    · intro m
      rw [← sub_eq_add_neg]
      exact sub_ne_zero.mpr (by
        intro h
        have hr := congrArg Complex.re h
        simp only [Complex.one_re, Complex.ofReal_re] at hr
        linarith [θ.toAbelianZetaParameters.ratio_lt_one m])
    · simpa only [norm_neg] using hsComplex.norm
  have hinv := hasProd_inv₀ houter hnormalizer_ne
  have hzeta : HasProd
      (fun n : ℕ =>
        riemannZeta ((((n + 1 : ℕ) : ℝ) * θ.sigma + θ.tau : ℝ) : ℂ))
      θ.complexNormalizer⁻¹ := by
    have hfun :
        (fun n : ℕ =>
          ((riemannZeta ((((n + 1 : ℕ) : ℝ) * θ.sigma + θ.tau : ℝ) : ℂ))⁻¹)⁻¹) =
        (fun n : ℕ =>
          riemannZeta ((((n + 1 : ℕ) : ℝ) * θ.sigma + θ.tau : ℝ) : ℂ)) := by
      funext n
      simp only [inv_inv]
    rw [← hfun]
    exact hinv
  exact hzeta

/-- **Erdős--Szekeres normalization.**  The exact countable zero-occupation constant is the
inverse of the complete zeta ladder `prod_{j>=1} zeta(j sigma + tau)`. -/
theorem complexNormalizer_eq_zetaPartition_inv (θ : AbelianZetaConvergentParameters) :
    θ.complexNormalizer = θ.zetaPartition⁻¹ := by
  rw [zetaPartition, (hasProd_zetaLadder θ).tprod_eq]
  simp only [inv_inv]

/-- The complete zeta ladder converges to the partition function. -/
theorem hasProd_zetaLadder_zetaPartition (θ : AbelianZetaConvergentParameters) :
    HasProd (fun n : ℕ => riemannZeta ((((n + 1 : ℕ) : ℝ) * θ.sigma + θ.tau : ℝ) : ℂ))
      θ.zetaPartition := by
  rw [zetaPartition, (hasProd_zetaLadder θ).tprod_eq]
  exact hasProd_zetaLadder θ

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
    exact hm (Subtype.ext (by simp [gNN, hAm]))
  have hcgNN : Multipliable (fun m => cNN m * gNN m) := hcNN.mul hgNN
  have hlocal : (fun m : AbelianZetaMode =>
      ENNReal.ofReal ((θ.toAbelianZetaParameters.ratio m) ^ (A m) *
        (1 - θ.toAbelianZetaParameters.ratio m))) = fun m => c m * g m := by
    funext m
    simp only [c, g, gNN, nnZeroFactor, ENNReal.coe_nnreal_eq]
    change ENNReal.ofReal
      ((θ.toAbelianZetaParameters.ratio m) ^ (A m) *
        (1 - θ.toAbelianZetaParameters.ratio m)) =
      ENNReal.ofReal (1 - θ.toAbelianZetaParameters.ratio m) *
        ENNReal.ofReal ((θ.toAbelianZetaParameters.ratio m) ^ (A m))
    rw [ENNReal.ofReal_mul (pow_nonneg (θ.toAbelianZetaParameters.ratio_nonneg m) _)]
    rw [mul_comm]
  have htgNN : ((∏' m : AbelianZetaMode, gNN m : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (abelianZetaModeWeight θ.toAbelianZetaParameters A) := by
    rw [tprod_eq_prod (s := A.support)]
    · rw [ENNReal.ofNNReal_finsetProd]
      simp only [ENNReal.coe_nnreal_eq]
      change (∏ m ∈ A.support,
          ENNReal.ofReal ((θ.toAbelianZetaParameters.ratio m) ^ (A m))) = _
      rw [← ENNReal.ofReal_prod_of_nonneg]
      · rfl
      · intro m hm
        exact pow_nonneg (θ.toAbelianZetaParameters.ratio_nonneg m) _
    · intro m hm
      have hAm : A m = 0 := by simpa using hm
      exact Subtype.ext (by simp [gNN, hAm])
  have hmap : ((∏' m : AbelianZetaMode, cNN m * gNN m : ℝ≥0) : ℝ≥0∞) =
      ∏' m : AbelianZetaMode, c m * g m := by
    change ((∏' m : AbelianZetaMode,
      θ.nnZeroFactor m * gNN m : ℝ≥0) : ℝ≥0∞) =
        ∏' m : AbelianZetaMode, (θ.nnZeroFactor m : ℝ≥0∞) * (gNN m : ℝ≥0∞)
    exact hcgNN.map_tprod ENNReal.ofNNRealHom.toMonoidHom ENNReal.continuous_coe
  rw [abelianZetaClassMass_eq_tprod, hlocal, ← hmap, hcNN.tprod_mul hgNN]
  change (θ.nnNormalizer : ℝ≥0∞) *
    ((∏' m : AbelianZetaMode, gNN m : ℝ≥0) : ℝ≥0∞) = _
  rw [htgNN]
  simp only [ennNormalizer]
  rw [abelianZetaModeWeight_eq_twoObservableWeight]

/-- Probability and complex-analytic normalizers are the same positive real product. -/
theorem coe_nnNormalizer_eq_complexNormalizer (θ : AbelianZetaConvergentParameters) :
    (θ.nnNormalizer : ℂ) = θ.complexNormalizer := by
  have hc := θ.nnZeroFactor_multipliable
  let e : ℝ≥0 →* ℂ :=
    Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom
  have hmap := hc.map_tprod e
    (Complex.continuous_ofReal.comp NNReal.continuous_coe)
  change e (∏' m : AbelianZetaMode, θ.nnZeroFactor m) = _
  rw [hmap, complexNormalizer]
  apply tprod_congr
  intro m
  change (((1 - θ.toAbelianZetaParameters.ratio m : ℝ)) : ℂ) =
    1 - (θ.toAbelianZetaParameters.ratio m : ℂ)
  rw [Complex.ofReal_sub, Complex.ofReal_one]

theorem complexNormalizer_ne_zero (θ : AbelianZetaConvergentParameters) :
    θ.complexNormalizer ≠ 0 := by
  rw [← θ.coe_nnNormalizer_eq_complexNormalizer]
  have hpos : 0 < (θ.nnNormalizer : ℝ) := by
    have hlog : Summable (fun m : AbelianZetaMode =>
        Real.log (1 - θ.toAbelianZetaParameters.ratio m)) := by
      simpa only [sub_eq_add_neg] using
        Real.summable_log_one_add_of_summable θ.summable_ratio.neg
    have hreal := Real.rexp_tsum_eq_tprod
      (fun m => sub_pos.mpr (θ.toAbelianZetaParameters.ratio_lt_one m)) hlog
    have hc := θ.nnZeroFactor_multipliable
    have hmap := hc.map_tprod NNReal.toRealHom.toMonoidHom NNReal.continuous_coe
    rw [nnNormalizer]
    have hmap' : ((∏' m : AbelianZetaMode, θ.nnZeroFactor m : ℝ≥0) : ℝ) =
        ∏' m : AbelianZetaMode, (θ.nnZeroFactor m : ℝ) := by
      simpa using hmap
    rw [hmap']
    have hfun : (fun m : AbelianZetaMode => (θ.nnZeroFactor m : ℝ)) =
        fun m => 1 - θ.toAbelianZetaParameters.ratio m := by
      funext m
      rfl
    rw [hfun]
    rw [← hreal]
    exact Real.exp_pos _
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)

/-- The group-class atoms exhaust total probability. -/
theorem tsum_classMass_eq_one (θ : AbelianZetaConvergentParameters) :
    (∑' A : AbelianZetaGroupClass,
      abelianZetaClassMass θ.toAbelianZetaParameters A) = 1 := by
  have hdisj : Pairwise (fun A B : AbelianZetaGroupClass =>
      Disjoint ({A.configuration} : Set (AbelianZetaMode → ℕ)) {B.configuration}) := by
    intro A B hAB
    rw [Set.disjoint_singleton]
    intro hconf
    apply hAB
    ext m
    exact congrFun hconf m
  have hmeasure : θ.toAbelianZetaParameters.gasMeasure
      (⋃ A : AbelianZetaGroupClass, ({A.configuration} : Set (AbelianZetaMode → ℕ))) = 1 := by
    rw [show (⋃ A : AbelianZetaGroupClass,
        ({A.configuration} : Set (AbelianZetaMode → ℕ))) =
        {k | ∃! A : AbelianZetaGroupClass, A.configuration = k} by
      ext k
      simp only [mem_iUnion, mem_singleton_iff, mem_setOf_eq]
      constructor
      · rintro ⟨A, hA⟩
        refine ⟨A, hA.symm, ?_⟩
        intro B hB
        ext m
        exact congrFun (hB.trans hA) m
      · rintro ⟨A, hA, _⟩
        exact ⟨A, hA.symm⟩]
    exact θ.measure_existsUnique_groupClass_eq_one
  change (∑' A : AbelianZetaGroupClass,
    θ.toAbelianZetaParameters.gasMeasure {A.configuration}) = 1
  rw [← MeasureTheory.measure_iUnion hdisj (fun _ => MeasurableSet.singleton _)]
  exact hmeasure

/-- Complete intrinsic group partition sum equals the inverse probability normalizer. -/
theorem tsum_twoObservableWeight_eq_ennNormalizer_inv
    (θ : AbelianZetaConvergentParameters) :
    (∑' A : AbelianZetaGroupClass,
      ENNReal.ofReal (abelianZetaTwoObservableWeight θ.toAbelianZetaParameters A)) =
        θ.ennNormalizer⁻¹ := by
  have hmass := θ.tsum_classMass_eq_one
  simp_rw [θ.classMass_eq_ennNormalizer_mul_twoObservableWeight] at hmass
  rw [ENNReal.tsum_mul_left] at hmass
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hmass)

/-- Zeta ladder and intrinsic group partition are one normalization, in their respective exact
codomains. -/
theorem zetaPartition_eq_complexNormalizer_inv (θ : AbelianZetaConvergentParameters) :
    θ.zetaPartition = θ.complexNormalizer⁻¹ := by
  rw [θ.complexNormalizer_eq_zetaPartition_inv]
  simp only [inv_inv]

end AbelianZetaConvergentParameters

end GaloisForLFunctions.HTGeometry
