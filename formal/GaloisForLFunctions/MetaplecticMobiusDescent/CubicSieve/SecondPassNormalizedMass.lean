/-
Normalized mass of the second pass adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.SecondPassTailBounds

/-!
# Normalized mass of the second pass

The arithmetic weight after extracting both column normalizations; every fixed residue term
is the radial kernel times an exact scalar. Common-divisor decay cancels its scale, and cube
parity keys `cubeParityKey` have controlled fibers.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration JointLogSeparation
open scoped Classical SchwartzMap ContDiff

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- Arithmetic weight after extracting both column normalizations. -/
def secondFixedOuterWeight (Ψ : O →* ℂ) (m c d : O) (X Y : ℝ)
    (negative : Bool) (r : QuadraticRayRing) (ray s q : QuadraticRayRing × QuadraticRayRing)
    (x : SecondExpansionData ι) : ℂ :=
  secondSourceCommonCoefficient p hg Ψ m c d x.sourceCommon x.divisor *
    secondTotalWeight p hg Ψ Ψ m (∏ i ∈ x.sourceCommon \ x.divisor, p i) c d
      (∏ i ∈ x.divisor, p i) x.frequency (ray, x.overlap) *
    twoPassResidueWeight p hg negative negative x.sourceCommon x.overlap r r ray s q *
    ((Y : ℂ) / X) * (X / primeProductNorm p x.sourceCommon : ℂ)⁻¹

/-- Every fixed residue term is the radial kernel times its exact scalar coefficient. -/
theorem secondFixedExpansionTerm_normalized (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (X Y : ℝ) (hX : 0 < X) (negative : Bool) (r : QuadraticRayRing)
    (ray s q : QuadraticRayRing × QuadraticRayRing) (x : SecondExpansionData ι)
    (hE : x.divisor ⊆ x.sourceCommon)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ, ℂ)) (hU : ∀ u, g u ≠ 0 → U u = 1) :
    secondFixedExpansionTerm p hg F Ψ m c d
      (normalizedColumn p (fun A => g (columnLog p X A))) W Y negative r ray s q x =
    (secondSourceCommonCoefficient p hg Ψ m c d x.sourceCommon x.divisor *
      secondTotalWeight p hg Ψ Ψ m (∏ i ∈ x.sourceCommon \ x.divisor, p i) c d
        (∏ i ∈ x.divisor, p i) x.frequency (ray, x.overlap) *
      twoPassResidueWeight p hg negative negative x.sourceCommon x.overlap r r ray s q *
      ((Y : ℂ) / X)) *
    fixedChildKernelPair p hg F Ψ Ψ (m * ∏ i ∈ x.sourceCommon \ x.divisor, p i)
      (c * (∏ i ∈ x.divisor, p i) * ∏ i ∈ x.overlap, p i)
      (d * (∏ i ∈ x.divisor, p i) * x.frequency) (d * (∏ i ∈ x.divisor, p i) * (-x.frequency))
      (combinedFixedColumn p hg negative q.1 s.1 (fun _ => 1))
      (combinedFixedColumn p hg negative q.2 s.2 (fun _ => 1))
      (fun N M => radialPairKernel p (∏ i ∈ x.divisor, p i) x.frequency W
        (halfNormalizationCLM U g) (halfNormalizationCLM U g)
        (X / primeProductNorm p x.sourceCommon) (X / primeProductNorm p x.sourceCommon) Y
        (x.overlap ∪ N) (x.overlap ∪ M)) := by
  have h := weighted_fixedChildKernelPair_normalized p hg hp x.sourceCommon x.divisor hE F x.overlap
    Ψ Ψ m c d x.frequency ray negative negative q.1 q.2 s.1 s.2 X Y hX U hUc hUs g g W hU hU
  have he := congrArg (fun z : ℂ =>
    (secondSourceCommonCoefficient p hg Ψ m c d x.sourceCommon x.divisor *
      twoPassResidueWeight p hg negative negative x.sourceCommon x.overlap r r ray s q) * z) h
  simpa only [secondFixedExpansionTerm, mul_assoc, mul_left_comm, mul_comm] using he

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
theorem secondSourceCommonCoefficient_norm_le_inv
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O) (G E : Finset ι) :
    ‖secondSourceCommonCoefficient p hg Ψ m c d G E‖ ≤ (primeProductNorm p E)⁻¹ := by
  have hA : ‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
      Ψ m c d (fun _ => 1) G‖ ≤ 1 := by
    simpa only [norm_one] using secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d (fun _ => 1) G
  have hA2 := (pow_le_pow_left₀ (norm_nonneg _) hA 2).trans_eq (one_pow 2)
  simp only [secondSourceCommonCoefficient, norm_mul, norm_div,
    Complex.norm_of_nonneg (sq_nonneg _), supportMobius_norm, one_div]
  exact mul_le_of_le_one_left (inv_nonneg.mpr (primeProductNorm_pos p hp E).le) hA2

include hp in
theorem secondPreColumn_norm_le_one
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d e k : O) (S : Finset ι) :
    ‖secondPreColumn p hg Ψ m c d e k (fun _ => 1) S‖ ≤ 1 := by
  have hprime (i : ι) : Prime (p i) :=
    (Ideal.span_singleton_prime (hp i)).mp (inferInstance : (Ideal.span {p i}).IsPrime)
  have hcop : Pairwise (Function.onFun IsCoprime p) := fun i j hij =>
    (Ideal.isCoprime_span_singleton_iff _ _).mp (Ideal.isCoprime_of_isMaximal (hinj.ne hij))
  have hcol := secondColumnCoefficient_norm_one p hprime hpr hcop S
  have hm := primeCoprimeMask_norm_le_one p S m
  have hr (a : O) := primeSubsetRow_norm_le_one p
    (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S a
  simp only [secondPreColumn, norm_mul, norm_pow, norm_star, norm_one, hcol, one_mul, mul_one]
  calc
    ‖Ψ (∏ i ∈ S, p i)‖ * ‖primeCoprimeMask p S m‖ *
        ‖primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S c‖ ^ 4 *
        ‖primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S d‖ *
        ‖primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S e‖ *
        ‖primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S k‖
      ≤ 1 * 1 * 1 ^ 4 * 1 * 1 * 1 := by
        gcongr <;> first | exact hΨ _ | exact hm | exact hr _
    _ = 1 := by norm_num

include hp in
theorem secondTotalWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ₁ Ψ₂ : O →* ℂ) (hΨ₁ : ∀ a, ‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a, ‖Ψ₂ a‖ ≤ 1)
    (m r c d e k : O) (ray : QuadraticRayRing × QuadraticRayRing) (V : Finset ι) :
    ‖secondTotalWeight p hg Ψ₁ Ψ₂ m r c d e k (ray,V)‖ ≤ ‖rayQuadraticPair ray.1 ray.2‖ := by
  have h₁ := secondPreColumn_norm_le_one p hp hg hinj hpr Ψ₁ hΨ₁ (m * (e * r)) c d e k V
  have h₂ := secondPreColumn_norm_le_one p hp hg hinj hpr Ψ₂ hΨ₂ (m * (e * r)) c d e (-k) V
  simp only [secondTotalWeight, secondCommonWeight, norm_mul, norm_star, supportMobius_norm, one_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    ((mul_le_mul h₁ h₂ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

include hp in
/-- Common-divisor decay cancels its scale in the normalized outer coefficient. -/
theorem secondFixedOuterWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O)
    (X Y : ℝ) (hX : 0 < X) (hY : 0 ≤ Y) (negative : Bool) (r : QuadraticRayRing)
    (ray s q : QuadraticRayRing × QuadraticRayRing) (x : SecondExpansionData ι)
    (hE : x.divisor ⊆ x.sourceCommon) :
    ‖secondFixedOuterWeight p hg Ψ m c d X Y negative r ray s q x‖ ≤
      Y * primeProductNorm p (x.sourceCommon \ x.divisor) / X ^ 2 * ‖rayQuadraticPair ray.1 ray.2‖ := by
  have hG := primeProductNorm_pos p hp x.sourceCommon
  have hEn := primeProductNorm_pos p hp x.divisor
  have hGn : primeProductNorm p x.sourceCommon =
      primeProductNorm p x.divisor * primeProductNorm p (x.sourceCommon \ x.divisor) := by
    rw [← primeProductNorm_union p _ _ disjoint_sdiff_self_right, Finset.union_sdiff_of_subset hE]
  have hc := secondSourceCommonCoefficient_norm_le_inv p hp hg Ψ hΨ m c d x.sourceCommon x.divisor
  have hw := secondTotalWeight_norm_le p hp hg hinj hpr Ψ Ψ hΨ hΨ m
    (∏ i ∈ x.sourceCommon \ x.divisor, p i) c d (∏ i ∈ x.divisor, p i) x.frequency ray x.overlap
  have hr := twoPassResidueWeight_norm_le p hg negative negative x.sourceCommon x.overlap r r ray s q
  simp only [secondFixedOuterWeight, norm_mul, norm_div, norm_inv,
    Complex.norm_of_nonneg hY, Complex.norm_of_nonneg hX.le, Complex.norm_of_nonneg hG.le]
  calc
    _ ≤ (primeProductNorm p x.divisor)⁻¹ * ‖rayQuadraticPair ray.1 ray.2‖ * 1 *
        (Y / X) * (X / primeProductNorm p x.sourceCommon)⁻¹ := by
      gcongr
    _ = _ := by rw [hGn]; field_simp [ne_of_gt hEn, ne_of_gt hX]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration JointLogSeparation
open scoped Classical SchwartzMap ContDiff

/-- One pair of compact profiles works for every prime family, residue and frequency twist. -/
theorem full_uniform_fixedExpansion_smooth_profiles
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ, ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hU : ∀ u, g u ≠ 0 → U u = 1) (hgA : ∀ u, g u ≠ 0 → |u| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧ (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j u, windows j u ≠ 0 → |u| ≤ A+B+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (hd : d ≠ 0)
        (X Y θ : ℝ) (hX : 0 < X) (negative : Bool) (r : QuadraticRayRing)
        (ray s q : QuadraticRayRing × QuadraticRayRing) (x : SecondExpansionData ι),
      x.divisor ⊆ x.sourceCommon → x.frequency ≠ 0 →
      ∀ (D E V₀ X₀ K : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X₀ → 0 < K →
      let X' := X / primeProductNorm p x.sourceCommon
      let e := ∏ i ∈ x.divisor, p i
      let z := Real.log (primeProductNorm p x.overlap * X₀ / X')
      let ud := Real.log (elementNorm d / D)
      let ue := Real.log (elementNorm e / E)
      let uv := Real.log (primeProductNorm p x.overlap / V₀)
      let kap := Real.log (elementNorm (d*e*x.frequency) / K)
      |z| ≤ B → |ud| ≤ B → |ue| ≤ B → |uv| ≤ B → |kap| ≤ B →
      secondFixedExpansionTerm p hg F Ψ m c d
        (normalizedColumn p (fun T => frequencyTwist g θ (columnLog p X T))) W Y negative r ray s q x =
      secondFixedOuterWeight p hg Ψ m c d X Y negative r ray s q x *
        postCommonSmoothPair p hg
          (combinedFixedColumn p hg negative q.1 s.1 (fun _ => 1))
          (combinedFixedColumn p hg negative q.2 s.2 (fun _ => 1))
          F Ψ Ψ (m * ∏ i ∈ x.sourceCommon \ x.divisor, p i)
          (c * e * ∏ i ∈ x.overlap, p i) (d*e*x.frequency) (d*e*(-x.frequency))
          (frequencyTwist A₁ (-θ)) (frequencyTwist A₂ θ) W windows
          z ud ue uv kap X₀ X₀ (Y*K/(D*E^2*V₀^2*X₀^2)) := by
  have hsupp := halfNormalization_support_bound U hUc hUs g A hgA
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := full_uniform_twisted_normalized_child_tests
    (halfNormalizationCLM U g) (halfNormalizationCLM U g) W A B hA hB hsupp hsupp
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hg F Ψ m c d hd X Y θ hX negative r ray s q x hE hk
    D E V₀ X₀ K hD hEn hV hX₀ hK
  dsimp only
  intro hz hud hue huv hkap
  have hUt : ∀ u, frequencyTwist g θ u ≠ 0 → U u = 1 := by
    intro u hu
    apply hU u
    intro hg0
    exact hu (by simp only [frequencyTwist_apply, hg0, mul_zero])
  have hn := secondFixedExpansionTerm_normalized p hg hp F Ψ m c d X Y hX negative r
    ray s q x hE U hUc hUs (frequencyTwist g θ) W hUt
  rw [halfNormalization_twist U hUc hUs] at hn
  have hi := hid p hp hg θ θ D E V₀ (X / primeProductNorm p x.sourceCommon) X₀ K Y
    hD hEn hV (div_pos hX (primeProductNorm_pos p hp _)) hX₀ hK
    F x.overlap Ψ Ψ m (∏ i ∈ x.sourceCommon \ x.divisor, p i) c d
    (∏ i ∈ x.divisor, p i) x.frequency
    (combinedFixedColumn p hg negative q.1 s.1 (fun _ => 1))
    (combinedFixedColumn p hg negative q.2 s.2 (fun _ => 1))
    hd (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) hk hz hud hue huv hkap
  rw [hi] at hn
  simpa only [secondFixedOuterWeight, Complex.ofReal_div, mul_assoc] using hn

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels JointLogSeparation
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

def globalSecondFixedLiteralTerm (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g V W : 𝓢(ℝ, ℂ)) (ell : ℝ) (side : Bool) (r : QuadraticRayRing) (t : ℝ)
    (Y : GlobalFirstData ι → ℝ) (ray s q : QuadraticRayRing × QuadraticRayRing)
    (x : GlobalSecondData ι) : ℂ :=
  (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    secondFixedExpansionTerm p hg (globalFirstRawPool pool x.first) Ψ
      (m * globalFirstBadLabel p x.first) (globalFirstRetainedLabel p x.first)
      (∏ i ∈ x.firstDivisor, p i)
      (normalizedColumn p (fun A => firstCoreModeProfile g V side t
        (columnLog p (globalFirstColumnScale p ell x side / primeProductNorm p x.firstCommon) A)))
      W (Y x.first) side r ray s q x.source

/-- Exact finite source in fixed residue columns and normalized first-pass profiles. -/
theorem globalFirstTruncatedSource_eq_normalized_fixed (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (s₀ : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ, ℂ)) (ell : ℝ) (hell : 0 < ell)
    (side : Bool) (r : QuadraticRayRing) (t : ℝ) (Y : GlobalFirstData ι → ℝ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) :
    globalFirstTruncatedSource p hp hg pool s₀ w Ψ m g V W ell side r t Y cutoff =
      ∑ ray : QuadraticRayRing × QuadraticRayRing,
        ∑ s : QuadraticRayRing × QuadraticRayRing, ∑ q : QuadraticRayRing × QuadraticRayRing,
          ∑ x ∈ globalFirstExpansionPool pool s₀ cutoff,
            w x.first * globalSecondFixedLiteralTerm p hg pool Ψ m g V W ell side r t Y ray s q x := by
  have hb (b : GlobalFirstData ι) :
      truncatedSecondSource p hp hg (globalFirstRawPool pool b) Ψ
        (m * globalFirstBadLabel p b) (globalFirstRetainedLabel p b) (∏ i ∈ b.firstDivisor, p i)
        (globalFirstInputTest p hg g V ell side r t b) W (Y b) (cutoff b) =
      ∑ ray : QuadraticRayRing × QuadraticRayRing,
        ∑ s : QuadraticRayRing × QuadraticRayRing, ∑ q : QuadraticRayRing × QuadraticRayRing,
          ∑ x ∈ secondExpansionPool (globalFirstRawPool pool b) (cutoff b),
            globalSecondFixedLiteralTerm p hg pool Ψ m g V W ell side r t Y ray s q (b.append x) := by
    unfold globalFirstInputTest
    have hdis : Disjoint b.firstCommon (globalFirstRawPool pool b) := disjoint_sdiff_self_right
    rw [truncatedSecondSource_firstCore_mode p hp hg (globalFirstRawPool pool b) b.firstCommon hdis
      Ψ _ _ _ g V W (globalFirstBlockColumnScale p ell side b) (Y b)
      (div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _)))
      side r t (cutoff b)]
    rw [truncatedSecondSource_eq_fixed_residues p hg hp hinj hc hpr]
    simp only [Finset.mul_sum]
    rfl
  unfold globalFirstTruncatedSource
  simp_rw [hb]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ray _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [sum_globalFirstExpansionPool]
  rfl

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration JointLogSeparation
open scoped Classical SchwartzMap ContDiff

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

def globalSecondFixedOuterWeight (Ψ : O →* ℂ) (m : O) (ell Y : ℝ)
    (side : Bool) (r : QuadraticRayRing) (ray s q : QuadraticRayRing × QuadraticRayRing)
    (x : GlobalSecondData ι) : ℂ :=
  (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    secondFixedOuterWeight p hg Ψ (m * globalFirstBadLabel p x.first)
      (globalFirstRetainedLabel p x.first) (∏ i ∈ x.firstDivisor, p i)
      (globalFirstColumnScale p ell x side / primeProductNorm p x.firstCommon) Y side r ray s q x.source

/-- Global logarithmic bins use fixed smooth profiles independent of arithmetic data and twists. -/
theorem full_uniform_globalFixedLiteral_profiles
    (g V W : 𝓢(ℝ, ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hgA : ∀ u, g u ≠ 0 → |u| ≤ A) (side : Bool) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧ (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j u, windows j u ≠ 0 → |u| ≤ A+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (ell : ℝ) (hell : 0 < ell)
        (r : QuadraticRayRing) (t : ℝ) (Y : GlobalFirstData ι → ℝ)
        (ray s q : QuadraticRayRing × QuadraticRayRing) (x : GlobalSecondData ι),
      x.source.divisor ⊆ x.source.sourceCommon → x.source.frequency ≠ 0 →
      let j := globalScaleIndex p side x
      globalSecondFixedLiteralTerm p hg pool Ψ m g V W ell side r t Y ray s q x =
        globalSecondFixedOuterWeight p hg Ψ m ell (Y x.first) side r ray s q x *
        postCommonSmoothPair p hg
          (combinedFixedColumn p hg side q.1 s.1 (fun _ => 1))
          (combinedFixedColumn p hg side q.2 s.2 (fun _ => 1))
          (globalFirstRawPool pool x.first) Ψ Ψ
          ((m * globalFirstBadLabel p x.first) * ∏ i ∈ x.source.sourceCommon \ x.source.divisor, p i)
          (globalSecondLabel p x)
          (SecondPassFiber.newRow (globalSecondTuple p x)) (-SecondPassFiber.newRow (globalSecondTuple p x))
          (frequencyTwist A₁ (-firstSignedHeight side t)) (frequencyTwist A₂ (firstSignedHeight side t)) W windows
          (globalBinZ p ell side j x) (globalBinUd p j x) (globalBinUe p j x)
          (globalBinUv p j x) (globalBinKap p j x)
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell (Y x.first) j) := by
  obtain ⟨U,hUc,hUs,hUone,_,_⟩ := exists_complex_smooth_cutoff A hA
  have hbase : ∀ u, firstCoreBaseProfile g V side u ≠ 0 → |u| ≤ A := by
    intro u hu
    apply hgA u
    intro hz
    exact hu (by simp only [firstCoreBaseProfile_apply, hz, zero_mul])
  have hU : ∀ u, firstCoreBaseProfile g V side u ≠ 0 → U u = 1 :=
    fun u hu => hUone u (hbase u hu)
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := full_uniform_fixedExpansion_smooth_profiles
    U hUc hUs (firstCoreBaseProfile g V side) W A 6 hA (by norm_num) hU hbase
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hg pool Ψ m ell hell r t Y ray s q x hE hk
  dsimp only
  let j := globalScaleIndex p side x
  let X := globalFirstColumnScale p ell x side / primeProductNorm p x.firstCommon
  have hX : 0 < X := div_pos (globalFirstColumnScale_pos p hp ell hell x side)
    (primeProductNorm_pos p hp _)
  have hcoords := globalPooled_log_coordinates p hp ell hell side x hk
  have hi := hid p hp hg (globalFirstRawPool pool x.first) Ψ
    (m * globalFirstBadLabel p x.first) (globalFirstRetainedLabel p x.first)
    (∏ i ∈ x.firstDivisor, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
    X (Y x.first) (firstSignedHeight side t) hX side r ray s q x.source hE hk
    (globalLogRep j 5) (globalLogRep j 6) (globalLogRep j 7) (globalPooledColumnScale ell j) (globalLogRep j 8)
    (globalLogRep_pos j 5) (globalLogRep_pos j 6) (globalLogRep_pos j 7)
    (globalPooledColumnScale_pos ell hell j) (globalLogRep_pos j 8)
  dsimp only at hi
  have hscale : X / primeProductNorm p x.source.sourceCommon = globalActualResidualScale p ell side x :=
    globalResidualScale_eq p ell side x hE
  rw [hscale] at hi
  have hrow : SecondPassFiber.newRow (globalSecondTuple p x) =
      (∏ i ∈ x.firstDivisor, p i) * (∏ i ∈ x.source.divisor, p i) * x.source.frequency := by
    exact actualSecondTuple_newRow p x.cube.support x.common x.firstDivisor x.source.divisor x.source.overlap
      x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit x.source.frequency
  have hkap : Real.log (elementNorm ((∏ i ∈ x.firstDivisor, p i) *
      (∏ i ∈ x.source.divisor, p i) * x.source.frequency) / globalLogRep j 8) = globalBinKap p j x := by
    simp only [globalBinKap, hrow, elementNorm]
  rw [hkap] at hi
  have hh := hi hcoords.1 hcoords.2.1 hcoords.2.2.1 hcoords.2.2.2.1 hcoords.2.2.2.2
  have he := congrArg (fun z : ℂ => (primeProductNorm p x.firstCommon : ℂ)⁻¹ * z) hh
  simpa only [globalSecondFixedLiteralTerm, globalSecondFixedOuterWeight, globalSecondLabel,
    globalFirstRetainedLabel, GlobalSecondData.first, globalBinZ, globalBinUd, globalBinUe,
    globalBinUv, globalBinRadial, firstCoreModeProfile, primeProductNorm, elementNorm,
    hrow, X, j, mul_neg, mul_assoc] using he

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem fixedChildKernelPair_masked_pool (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    fixedChildKernelPair p hg (F \ G) Ψ₁ Ψ₂ m f y₁ y₂ H₁ H₂ K =
      fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m * ∏ i ∈ G, p i) f y₁ y₂ H₁ H₂ K := by
  unfold fixedChildKernelPair
  rw [sum_pair_remove_common_pool p hinj]
  simp only [secondChildColumn_fixed_mask, star_mul, star_primeCoprimeMask]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro T _
  ring

theorem fixedChildKernelPair_restore_killed_pool
    (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ)
    (hG : ∀ i ∈ G, m * f ∈ Ideal.span {p i}) :
    fixedChildKernelPair p hg (F \ G) Ψ₁ Ψ₂ m f y₁ y₂ H₁ H₂ K =
      fixedChildKernelPair p hg F Ψ₁ Ψ₂ m f y₁ y₂ H₁ H₂ K := by
  have hz (Ψ : O →* ℂ) (y : O) (H : Finset ι → ℂ)
      (S : Finset ι) (hS : S ∈ F.powerset) (hn : S ∉ (F \ G).powerset) :
      secondChildColumn p hg Ψ m f y H S = 0 := by
    have hd : ¬ Disjoint G S := by
      intro hd
      apply hn
      apply Finset.mem_powerset.mpr
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hS) hi,
        fun hiG => Finset.disjoint_left.mp hd hiG hi⟩
    obtain ⟨i, hiG, hiS⟩ := Finset.not_disjoint_iff.mp hd
    exact secondChildColumn_zero_of_mask_label_mem p hg Ψ m f y H S i hiS (hG i hiG)
  unfold fixedChildKernelPair
  calc
    _ = ∑ S ∈ (F \ G).powerset, ∑ T ∈ F.powerset,
        star (secondChildColumn p hg Ψ₁ m f y₁ H₁ S) *
          secondChildColumn p hg Ψ₂ m f y₂ H₂ T * K S T := by
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
      intro T hT hn
      rw [hz Ψ₂ y₂ H₂ T hT hn, mul_zero, zero_mul]
    _ = _ := by
      apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
      intro S hS hn
      rw [hz Ψ₁ y₁ H₁ S hS hn, star_zero]
      simp only [zero_mul, Finset.sum_const_zero]

theorem globalSecondRawKernel_fixed_pool (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m y₁ y₂ : O)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) (x : GlobalSecondData ι) :
    fixedChildKernelPair p hg (globalFirstRawPool F x.first) Ψ₁ Ψ₂
      (m * globalFirstBadLabel p x.first * ∏ i ∈ x.source.sourceCommon \ x.source.divisor, p i)
      (globalSecondLabel p x) y₁ y₂ H₁ H₂ K =
      fixedChildKernelPair p hg F Ψ₁ Ψ₂ (fixedTripleMask m (globalSecondFixedTriple p x))
        (globalSecondLabel p x) y₁ y₂ H₁ H₂ K := by
  rw [globalFirstRawPool, fixedChildKernelPair_masked_pool p hg hinj]
  change fixedChildKernelPair p hg (F \ (x.cube.support ∪ x.common)) Ψ₁ Ψ₂
    (globalSecondMask p m x) (globalSecondLabel p x) y₁ y₂ H₁ H₂ K = _
  rw [fixedChildKernelPair_restore_killed_pool p hg F (x.cube.support ∪ x.common) Ψ₁ Ψ₂
    (globalSecondMask p m x) (globalSecondLabel p x) y₁ y₂ H₁ H₂ K
    (globalSecondMask_kills_cube_common p m x)]
  simp only [fixedChildKernelPair, secondChildColumn_congr_mask_span p hg Ψ₁ (globalSecondMask_span p m x),
    secondChildColumn_congr_mask_span p hg Ψ₂ (globalSecondMask_span p m x)]

/-- Fixing the three divisor ideals fixes the full smooth descendant kernel's prime pool and mask. -/
theorem globalSecondRawSmoothPair_fixed_pool (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m y₁ y₂ : O) (H₁ H₂ : Finset ι → ℂ)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap X₁ X₂ R : ℝ) (x : GlobalSecondData ι) :
    postCommonSmoothPair p hg H₁ H₂ (globalFirstRawPool F x.first) Ψ₁ Ψ₂
      (m * globalFirstBadLabel p x.first * ∏ i ∈ x.source.sourceCommon \ x.source.divisor, p i)
      (globalSecondLabel p x) y₁ y₂ A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
      postCommonSmoothPair p hg H₁ H₂ F Ψ₁ Ψ₂ (fixedTripleMask m (globalSecondFixedTriple p x))
        (globalSecondLabel p x) y₁ y₂ A₁ A₂ W V z ud ue uv kap X₁ X₂ R :=
  globalSecondRawKernel_fixed_pool p hg hinj F Ψ₁ Ψ₂ m y₁ y₂ H₁ H₂ _ x

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
theorem globalSecondFixedOuterWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : O) (ell Y : ℝ)
    (hell : 0 < ell) (hY : 0 ≤ Y) (side : Bool) (r : QuadraticRayRing)
    (ray s q : QuadraticRayRing × QuadraticRayRing) (x : GlobalSecondData ι)
    (hE : x.source.divisor ⊆ x.source.sourceCommon) :
    ‖globalSecondFixedOuterWeight p hg Ψ m ell Y side r ray s q x‖ ≤
      (Y * primeProductNorm p x.firstCommon * primeProductNorm p (x.source.sourceCommon \ x.source.divisor) /
        (globalFirstColumnScale p ell x side)^2) * ‖rayQuadraticPair ray.1 ray.2‖ := by
  have ht := primeProductNorm_pos p hp x.firstCommon
  have hX := globalFirstColumnScale_pos p hp ell hell x side
  have hh := secondFixedOuterWeight_norm_le p hp hg hinj hpr Ψ hΨ
    (m * globalFirstBadLabel p x.first) (globalFirstRetainedLabel p x.first)
    (∏ i ∈ x.firstDivisor, p i) (globalFirstColumnScale p ell x side / primeProductNorm p x.firstCommon)
    Y (div_pos hX ht) hY side r ray s q x.source hE
  unfold globalSecondFixedOuterWeight
  rw [norm_mul, norm_inv, Complex.norm_of_nonneg ht.le]
  apply (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr ht.le)).trans_eq
  field_simp [ne_of_gt ht, ne_of_gt hX]

def globalPooledOuterBound (ray : QuadraticRayRing × QuadraticRayRing) (ell Y : ℝ)
    (j : GlobalLogIndex) : ℝ :=
  (Y * (Real.exp 1)^6 * globalLogRep j 2 * globalLogRep j 3 *
    (globalLogRep j 0)^2 * (globalLogRep j 1)^2 / ell^2) * ‖rayQuadraticPair ray.1 ray.2‖

include hp in
theorem globalSecondFixedOuterWeight_bin_bound
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : O) (ell Y : ℝ)
    (hell : 0 < ell) (hY : 0 ≤ Y) (side : Bool) (r : QuadraticRayRing)
    (ray s q : QuadraticRayRing × QuadraticRayRing) (x : GlobalSecondData ι)
    (hE : x.source.divisor ⊆ x.source.sourceCommon) (hk : x.source.frequency ≠ 0) :
    ‖globalSecondFixedOuterWeight p hg Ψ m ell Y side r ray s q x‖ ≤
      globalPooledOuterBound ray ell Y (globalScaleIndex p side x) := by
  apply (globalSecondFixedOuterWeight_norm_le p hp hg hinj hpr Ψ hΨ m ell Y hell hY side r ray s q x hE).trans
  let j := globalScaleIndex p side x
  have ha := (globalScaleIndex_bounds p hp side x hk 0).2
  have hc := (globalScaleIndex_bounds p hp side x hk 1).2
  have ht := (globalScaleIndex_bounds p hp side x hk 2).2
  have hr := (globalScaleIndex_bounds p hp side x hk 3).2
  change primeProductNorm p (x.cube.sideDivisor side) ≤ globalLogRep j 0 * Real.exp 1 at ha
  change primeProductNorm p x.common ≤ globalLogRep j 1 * Real.exp 1 at hc
  change primeProductNorm p x.firstCommon ≤ globalLogRep j 2 * Real.exp 1 at ht
  change primeProductNorm p (x.source.sourceCommon \ x.source.divisor) ≤ globalLogRep j 3 * Real.exp 1 at hr
  have hn : Y * primeProductNorm p x.firstCommon * primeProductNorm p (x.source.sourceCommon \ x.source.divisor) /
      (globalFirstColumnScale p ell x side)^2 =
      Y * primeProductNorm p x.firstCommon * primeProductNorm p (x.source.sourceCommon \ x.source.divisor) *
        (primeProductNorm p (x.cube.sideDivisor side))^2 * (primeProductNorm p x.common)^2 / ell^2 := by
    have hA := (primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
    have hC := (primeProductNorm_pos p hp x.common).ne'
    unfold globalFirstColumnScale
    field_simp [hA,hC,ne_of_gt hell]
  rw [hn]
  have h0 := (primeProductNorm_pos p hp (x.cube.sideDivisor side)).le
  have h1 := (primeProductNorm_pos p hp x.common).le
  have h2 := (primeProductNorm_pos p hp x.firstCommon).le
  have h3 := (primeProductNorm_pos p hp (x.source.sourceCommon \ x.source.divisor)).le
  have hj0 := globalLogRep_pos j 0
  have hj1 := globalLogRep_pos j 1
  have hj2 := globalLogRep_pos j 2
  have hj3 := globalLogRep_pos j 3
  calc
    _ ≤ (Y * (globalLogRep j 2 * Real.exp 1) * (globalLogRep j 3 * Real.exp 1) *
        (globalLogRep j 0 * Real.exp 1)^2 * (globalLogRep j 1 * Real.exp 1)^2 / ell^2) *
          ‖rayQuadraticPair ray.1 ray.2‖ := by gcongr <;> positivity
    _ = _ := by unfold globalPooledOuterBound; ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap FourierTransform

theorem full_uniform_twisted_postCommonSmoothPair_fixed_tests
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ₁ θ₂ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ, (1+R)^A * ‖(𝓕 (frequencyTwist A₁ θ₁)) t₁ * (𝓕 (frequencyTwist A₂ θ₂)) t₂ * b t₃‖ ≤
        (C * (1+‖θ₁‖)^(J+2) * (1+‖θ₂‖)^(J+2)) * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (H₁ H₂ : Finset ι → ℂ) (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
        (z ud ue uv kap X₁ X₂ : ℝ),
        postCommonSmoothPair p hg H₁ H₂ F Ψ₁ Ψ₂ m f y₁ y₂ (frequencyTwist A₁ θ₁) (frequencyTwist A₂ θ₂) W V
          z ud ue uv kap X₁ X₂ R =
        separatedPostCommon p hg H₁ H₂ F Ψ₁ Ψ₂ m f y₁ y₂ (frequencyTwist A₁ θ₁) (frequencyTwist A₂ θ₂) b V
          z ud ue uv kap X₁ X₂ := by
  obtain ⟨C, hC, hsep⟩ := JointLogSeparation.seven_twisted_kernel_separation A₁ A₂ W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro θ₁ θ₂ R hR
  obtain ⟨b, hb, hpoint, hint⟩ := hsep θ₁ θ₂ R hR
  refine ⟨b, hpoint, ?_⟩
  intro ι _ p _ hg H₁ H₂
    F Ψ₁ Ψ₂ m f y₁ y₂ z ud ue uv kap X₁ X₂
  exact postCommonSmoothPair_fixed_tests p hg H₁ H₂ F Ψ₁ Ψ₂ m f y₁ y₂ (frequencyTwist A₁ θ₁) (frequencyTwist A₂ θ₂) W V
    z ud ue uv kap X₁ X₂ R b (hb z ud ue uv kap)

end SecondPassArithmetic

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic SecondPassFiber JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap FourierTransform
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

theorem globalTupleSource_twisted_transfer (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∃ Cₛ : ℝ, 0 ≤ Cₛ ∧ ∀ θ₁ θ₂ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ, (1 + R)^A * ‖(𝓕 (frequencyTwist A₁ θ₁)) t₁ * (𝓕 (frequencyTwist A₂ θ₂)) t₂ * b t₃‖ ≤
        (Cₛ * (1+‖θ₁‖)^(J+2) * (1+‖θ₂‖)^(J+2)) * firstLogDensity J t₁ *
          firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (H₁ H₂ : Finset ι → ℂ) (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O)) (q0 : Ideal O × Ideal O × Ideal O)
        (w : (GlobalSecondData ι) → ℂ) (B lengthScale : ℝ) (label : (GlobalSecondData ι) → O)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : (GlobalSecondData ι) → ℝ) (X₁ X₂ : ℝ),
        q0.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x ∈ s, GlobalSecondAdmissible x) →
        (∀ x ∈ s, globalSecondFixedTriple p x = q0) →
        (∀ x ∈ s, (newLabel (globalSecondTuple p x), newRow (globalSecondTuple p x)) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        (∀ x ∈ s, Ideal.span {label x} = newLabel (globalSecondTuple p x)) →
        ‖globalTupleSourceSum p hg H₁ H₂ s w label F Ψ₁ Ψ₂ m (frequencyTwist A₁ θ₁) (frequencyTwist A₂ θ₂) W V z ud ue uv kap X₁ X₂ R‖ ≤
          (B * Cₐ * (lengthScale * Ideal.absNorm q0.1)^ε) *
          (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
            ‖tripleCoefficient (𝓕 (frequencyTwist A₁ θ₁)) (𝓕 (frequencyTwist A₂ θ₂)) b (t₁,t₂,t₃)‖ *
              childGeometricMean p hg H₁ H₂ F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ, hCₐ, htrans⟩ := globalSecond_integrated_mode_transfer ε hε
  obtain ⟨Cₛ, hCₛ, hsep⟩ := full_uniform_twisted_postCommonSmoothPair_fixed_tests A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ, hCₐ, Cₛ, hCₛ, ?_⟩
  intro θ₁ θ₂ R hR
  obtain ⟨b, hpoint, hid⟩ := hsep θ₁ θ₂ R hR
  refine ⟨b, hpoint, ?_⟩
  intro ι _ p _ hinj hg H₁ H₂
  have htrans := htrans p hinj hg H₁ H₂
  have hid := hid p hg H₁ H₂
  intro s T q0 w B lengthScale label F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hb0 hB hL hv htq hm ht hn hw hl
  have hsource := globalTupleSource_eq_globalIntegratedSecondMode p hg H₁ H₂ s w label F Ψ₁ Ψ₂ m (frequencyTwist A₁ θ₁) (frequencyTwist A₂ θ₂) W b
    V z ud ue uv kap X₁ X₂ R (fun x hx => hid F Ψ₁ Ψ₂ m (label x) (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
      (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂)
  rw [hsource]
  apply htrans s T q0 (tupleOuterWeight V w z ud ue uv kap) B lengthScale label F Ψ₁ Ψ₂ m
    (V 5) (V 6) X₁ X₂ (𝓕 (frequencyTwist A₁ θ₁)) (𝓕 (frequencyTwist A₂ θ₂)) b hb0 hB hL hv htq hm ht hn
  · intro q x hx
    rw [tupleOuterWeight_norm]
    exact hw x hx
  · intro x hx
    exact tupleOuterWeight_continuous V w z ud ue uv kap x
  · exact hl

end SecondPassIntegration

namespace SecondPassIntegration
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic SecondPassFiber JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap FourierTransform
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

/-- Uniform radial decay survives the divisor-tuple transfer to fixed descendant energies. -/
theorem full_uniform_global_twisted_density_transfer (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ₁ θ₂ R : ℝ, 0 < R →
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}) (H₁ H₂ : Finset ι → ℂ)
      (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O)) (q0 : Ideal O × Ideal O × Ideal O)
      (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ) (label : GlobalSecondData ι → O)
      (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
      (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ : ℝ),
      q0.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, GlobalSecondAdmissible x) →
      (∀ x ∈ s, globalSecondFixedTriple p x = q0) →
      (∀ x ∈ s, (newLabel (globalSecondTuple p x), newRow (globalSecondTuple p x)) ∈ T) →
      (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel (globalSecondTuple p x)) →
      (1 + R)^A * ‖globalTupleSourceSum p hg H₁ H₂ s w label F Ψ₁ Ψ₂ m
        (frequencyTwist A₁ θ₁) (frequencyTwist A₂ θ₂) W V z ud ue uv kap X₁ X₂ R‖ ≤
        B * C * (1+‖θ₁‖)^(J+2) * (1+‖θ₂‖)^(J+2) * (lengthScale * Ideal.absNorm q0.1)^ε *
          densityChildEnergy p hg H₁ H₂ F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ J := by
  obtain ⟨Cₐ, hCₐ, Cₛ, hCₛ, ht⟩ :=
    globalTupleSource_twisted_transfer ε hε A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ * Cₛ, mul_nonneg hCₐ.le hCₛ, ?_⟩
  intro θ₁ θ₂ R hR
  obtain ⟨b, hpoint, htransfer⟩ := ht θ₁ θ₂ R hR
  intro ι _ p _ hinj hg H₁ H₂ s T q0 w B lengthScale label F Ψ₁ Ψ₂ m
    z ud ue uv kap X₁ X₂ hb0 hB hL hv htq hm ht hn hw hl
  have hsource := htransfer p hinj hg H₁ H₂ s T q0 w B lengthScale label F Ψ₁ Ψ₂ m
    z ud ue uv kap X₁ X₂ hb0 hB hL hv htq hm ht hn hw hl
  have hdensity := child_coefficient_density_bound p hg H₁ H₂ F Ψ₁ Ψ₂ m T
    (V 5) (V 6) X₁ X₂ (𝓕 (frequencyTwist A₁ θ₁)) (𝓕 (frequencyTwist A₂ θ₂)) b J ((1 + R)^A) (Cₛ * (1+‖θ₁‖)^(J+2) * (1+‖θ₂‖)^(J+2)) hpoint
  calc
    _ ≤ (1 + R)^A * ((B * Cₐ * (lengthScale * Ideal.absNorm q0.1)^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient (𝓕 (frequencyTwist A₁ θ₁)) (𝓕 (frequencyTwist A₂ θ₂)) b (t₁,t₂,t₃)‖ *
            childGeometricMean p hg H₁ H₂ F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ (t₁,t₂,t₃))) :=
      mul_le_mul_of_nonneg_left hsource (by positivity)
    _ = (B * Cₐ * (lengthScale * Ideal.absNorm q0.1)^ε) * ((1 + R)^A *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient (𝓕 (frequencyTwist A₁ θ₁)) (𝓕 (frequencyTwist A₂ θ₂)) b (t₁,t₂,t₃)‖ *
            childGeometricMean p hg H₁ H₂ F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ (t₁,t₂,t₃))) := by ring
    _ ≤ (B * Cₐ * (lengthScale * Ideal.absNorm q0.1)^ε) *
        ((Cₛ * (1+‖θ₁‖)^(J+2) * (1+‖θ₂‖)^(J+2)) * densityChildEnergy p hg H₁ H₂ F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ J) :=
      mul_le_mul_of_nonneg_left hdensity (by positivity)
    _ = _ := by ring

end SecondPassIntegration

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem primeSpanProduct_squarefree (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (S : Finset ι) : Squarefree (∏ i ∈ S, Ideal.span {p i}) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    apply squarefree_mul_iff.mpr
    refine ⟨?_, (Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance).squarefree, ih⟩
    have hcop : IsCoprime (Ideal.span {p i}) (∏ j ∈ S, Ideal.span {p j}) := by
      apply IsCoprime.prod_right
      intro j hj
      apply Ideal.isCoprime_of_isMaximal
      apply hinj.ne
      intro hij
      subst j
      exact hi hj
    exact hcop.isRelPrime

theorem primeSubsetRow_nonzero_notMem (S : Finset ι) (c : O)
    (h : primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S c ≠ 0) :
    ∀ i ∈ S, c ∉ Ideal.span {p i} := by
  intro i hi hc
  apply h
  apply Finset.prod_eq_zero hi
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hc, MulChar.map_zero]

theorem primeSpanProduct_isCoprime_of_notMem (S : Finset ι) (c : O)
    (h : ∀ i ∈ S, c ∉ Ideal.span {p i}) :
    IsCoprime (∏ i ∈ S, Ideal.span {p i}) (Ideal.span {c}) := by
  apply IsCoprime.prod_left
  intro i hi
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra htop
  have he := Ideal.IsMaximal.eq_of_le (inferInstance : (Ideal.span {p i}).IsMaximal)
    htop (show Ideal.span {p i} ≤ Ideal.span {p i} ⊔ Ideal.span {c} from le_sup_left)
  apply h i hi
  rw [he]
  exact (show Ideal.span {c} ≤ Ideal.span {p i} ⊔ Ideal.span {c} from le_sup_right)
    (Ideal.subset_span (Set.mem_singleton c))

def firstRetainedSupport (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  B.filter (fun i => retained (parity (v i)) (ε₁ i) (ε₂ i))

theorem jLabel_eq_retainedProduct (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    jLabel p B v ε₁ ε₂ = ∏ i ∈ firstRetainedSupport B v ε₁ ε₂, p i := by
  unfold jLabel primeProduct firstRetainedSupport
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  cases hb : retained (parity (v i)) (ε₁ i) (ε₂ i) <;> simp only [bit, hb, Bool.false_eq_true,
    ite_false, ite_true, pow_zero, pow_one]

theorem firstBaseLabel_squarefree (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (B C : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hCB : Disjoint C B) :
    Squarefree (Ideal.span {(∏ i ∈ C, p i) * jLabel p B v ε₁ ε₂}) := by
  have hCJ : Disjoint C (firstRetainedSupport B v ε₁ ε₂) :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hCB
  rw [← Ideal.span_singleton_mul_span_singleton, jLabel_eq_retainedProduct,
    span_finset_prime_product, span_finset_prime_product, ← Finset.prod_union hCJ]
  exact primeSpanProduct_squarefree p hinj _

def secondArithmeticWeight (Ψ : O →* ℂ) (m c d : O) (ray : QuadraticRayRing × QuadraticRayRing)
    (x : SecondExpansionData ι) : ℂ :=
  secondSourceCommonCoefficient p hg Ψ m c d x.sourceCommon x.divisor *
    secondTotalWeight p hg Ψ Ψ m (∏ i ∈ x.sourceCommon \ x.divisor, p i) c d
      (∏ i ∈ x.divisor, p i) x.frequency (ray,x.overlap)

/-- A nonzero source weight forces the retained label and both new supports to be coprime. -/
theorem secondArithmeticWeight_coprime (Ψ : O →* ℂ) (m c d : O)
    (ray : QuadraticRayRing × QuadraticRayRing) (x : SecondExpansionData ι)
    (hE : x.divisor ⊆ x.sourceCommon) (h : secondArithmeticWeight p hg Ψ m c d ray x ≠ 0) :
    IsCoprime (Ideal.span {c}) (∏ i ∈ x.divisor, Ideal.span {p i}) ∧
    IsCoprime (Ideal.span {c}) (∏ i ∈ x.overlap, Ideal.span {p i}) ∧
    IsCoprime (∏ i ∈ x.divisor, Ideal.span {p i}) (∏ i ∈ x.overlap, Ideal.span {p i}) := by
  have hG : primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) x.sourceCommon c ≠ 0 := by
    intro hz
    apply h
    simp only [secondArithmeticWeight, secondSourceCommonCoefficient, secondInputCoefficient,
      hz, zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero, zero_mul, norm_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), Complex.ofReal_zero]
  have hV : primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) x.overlap c ≠ 0 := by
    intro hz
    apply h
    simp only [secondArithmeticWeight, secondTotalWeight, secondCommonWeight, secondPreColumn,
      hz, zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero, zero_mul, star_zero]
  have hVe : primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) x.overlap
      (∏ i ∈ x.divisor, p i) ≠ 0 := by
    intro hz
    apply h
    simp only [secondArithmeticWeight, secondTotalWeight, secondCommonWeight, secondPreColumn,
      hz, star_zero, mul_zero, zero_mul]
  have hEc := primeSpanProduct_isCoprime_of_notMem p x.divisor c
    (fun i hi => primeSubsetRow_nonzero_notMem p hg x.sourceCommon c hG i (hE hi))
  have hVc := primeSpanProduct_isCoprime_of_notMem p x.overlap c
    (primeSubsetRow_nonzero_notMem p hg x.overlap c hV)
  have hVE := primeSpanProduct_isCoprime_of_notMem p x.overlap (∏ i ∈ x.divisor, p i)
    (primeSubsetRow_nonzero_notMem p hg x.overlap _ hVe)
  rw [span_finset_prime_product] at hVE
  exact ⟨hEc.symm,hVc.symm,hVE.symm⟩

theorem secondArithmeticWeight_squarefree (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (Ψ : O →* ℂ) (m c d : O) (ray : QuadraticRayRing × QuadraticRayRing)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (hc : Squarefree (Ideal.span {c})) (h : secondArithmeticWeight p hg Ψ m c d ray x ≠ 0) :
    Squarefree (Ideal.span {c} * (∏ i ∈ x.divisor, Ideal.span {p i}) *
      (∏ i ∈ x.overlap, Ideal.span {p i})) := by
  obtain ⟨hcE,hcV,hEV⟩ := secondArithmeticWeight_coprime p hg Ψ m c d ray x hE h
  apply squarefree_mul_iff.mpr
  refine ⟨(hcV.mul_left hEV).isRelPrime,?_,primeSpanProduct_squarefree p hinj _⟩
  exact squarefree_mul_iff.mpr ⟨hcE.isRelPrime,hc,primeSpanProduct_squarefree p hinj _⟩

/-- Nonzero global weights have squarefree descendant labels. -/
theorem globalSecondFixedOuterWeight_squarefree (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (Ψ : O →* ℂ) (m : O) (ell Y : ℝ) (side : Bool) (r : QuadraticRayRing)
    (ray s q : QuadraticRayRing × QuadraticRayRing) (x : GlobalSecondData ι)
    (hx : GlobalSecondAdmissible x)
    (h : globalSecondFixedOuterWeight p hg Ψ m ell Y side r ray s q x ≠ 0) :
    Squarefree (SecondPassFiber.newLabel (globalSecondTuple p x)) := by
  have hw : secondArithmeticWeight p hg Ψ (m * globalFirstBadLabel p x.first)
      (globalFirstRetainedLabel p x.first) (∏ i ∈ x.firstDivisor, p i) ray x.source ≠ 0 := by
    intro hz
    apply h
    unfold secondArithmeticWeight at hz
    simp only [globalSecondFixedOuterWeight, secondFixedOuterWeight, hz, zero_mul, mul_zero]
  have hs := secondArithmeticWeight_squarefree p hg hinj Ψ (m * globalFirstBadLabel p x.first)
    (globalFirstRetainedLabel p x.first) (∏ i ∈ x.firstDivisor, p i) ray x.source hx.2.1
    (firstBaseLabel_squarefree p hinj x.cube.support x.common
      (fun i => x.cube.leftExponent i + x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit hx.2.2.1) hw
  simpa only [globalSecondTuple, actualSecondTuple_newLabel, actualSecondLabel, globalFirstRetainedLabel,
    GlobalSecondData.first, ← Ideal.span_singleton_mul_span_singleton, span_finset_prime_product,
    mul_comm, mul_left_comm, mul_assoc] using hs

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
theorem globalSecondLabel_ne_zero (x : GlobalSecondData ι) : globalSecondLabel p x ≠ 0 := by
  unfold globalSecondLabel
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) (primeProduct_ne_zero p hp _ _))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))

include hp in
theorem globalPooled_target_bounds (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    let j := globalScaleIndex p side x
    (Ideal.absNorm (SecondPassFiber.newLabel (globalSecondTuple p x)) : ℝ) ≤ globalPooledLabelScale j ∧
      ‖ringComplex (SecondPassFiber.newRow (globalSecondTuple p x))‖^2 ≤ globalLogRep j 8 * Real.exp 1 := by
  let j := globalScaleIndex p side x
  have hb (i : Fin 10) := (globalScaleIndex_bounds p hp side x hk i).2
  refine ⟨?_, hb 8⟩
  have he : (Ideal.absNorm (SecondPassFiber.newLabel (globalSecondTuple p x)) : ℝ) =
      globalScaleVector p side x 1 * globalScaleVector p side x 4 *
        globalScaleVector p side x 6 * globalScaleVector p side x 7 := by
    rw [← globalSecondLabel_span p x, ← ringComplex_norm_sq_eq_absNorm_span]
    simp only [globalSecondLabel, map_mul, norm_mul, mul_pow]
    rfl
  rw [he]
  calc
    _ ≤ (globalLogRep j 1 * Real.exp 1) * (globalLogRep j 4 * Real.exp 1) *
        (globalLogRep j 6 * Real.exp 1) * (globalLogRep j 7 * Real.exp 1) := by
      have hpos (i : Fin 10) : 0 ≤ globalScaleVector p side x i :=
        zero_le_one.trans (globalScaleVector_ge_one p hp side x hk i)
      have h1 := globalLogRep_pos j 1
      have h4 := globalLogRep_pos j 4
      have h6 := globalLogRep_pos j 6
      have h7 := globalLogRep_pos j 7
      gcongr <;> first | positivity | exact hpos _ | exact hb _
    _ = globalPooledLabelScale j := by
      unfold globalPooledLabelScale
      rw [show (4 : ℝ) = 1+1+1+1 by norm_num, Real.exp_add, Real.exp_add, Real.exp_add]
      ring

def globalArithmeticBin (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) : Finset (GlobalSecondData ι) :=
  s.filter (fun x => globalSecondFixedTriple p x = q ∧ globalScaleIndex p side x = j)

def globalSquarefreeBin (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) : Finset (GlobalSecondData ι) :=
  (globalArithmeticBin p s side q j).filter (fun x => Squarefree (SecondPassFiber.newLabel (globalSecondTuple p x)))

def globalArithmeticTargets (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) : Finset (Ideal O × O) :=
  (globalSquarefreeBin p s side q j).image
    (fun x => (SecondPassFiber.newLabel (globalSecondTuple p x), SecondPassFiber.newRow (globalSecondTuple p x)))

theorem globalArithmeticTargets_squarefree (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) :
    ∀ z ∈ globalArithmeticTargets p s side q j, Squarefree z.1 := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  exact (Finset.mem_filter.mp hx).2

include hp in
theorem globalArithmeticTargets_bounds (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) (hk : ∀ x ∈ s, x.source.frequency ≠ 0) :
    ∀ z ∈ globalArithmeticTargets p s side q j, z.1 ≠ ⊥ ∧
      (Ideal.absNorm z.1 : ℝ) ≤ globalPooledLabelScale j ∧
      ‖ringComplex z.2‖^2 ≤ globalLogRep j 8 * Real.exp 1 := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hx',_⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxs,hq,hj⟩ := Finset.mem_filter.mp hx'
  have hb := globalPooled_target_bounds p hp side x (hk x hxs)
  rw [hj] at hb
  refine ⟨?_,hb⟩
  rw [← globalSecondLabel_span p x]
  exact Ideal.span_singleton_eq_bot.not.mpr (globalSecondLabel_ne_zero p hp x)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration JointLogSeparation
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- A bin fixes the three arithmetic masks, logarithmic scales and all residue columns. -/
def globalFixedBinSource (s₀ : Finset (GlobalSecondData ι)) (a : GlobalSecondData ι → ℂ) (side : Bool)
    (q₀ : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (r : QuadraticRayRing)
    (ray s q : QuadraticRayRing × QuadraticRayRing) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (windows : Fin 7 → ℝ → ℂ) (ell Y t : ℝ) : ℂ :=
  globalTupleSourceSum p hg
    (combinedFixedColumn p hg side q.1 s.1 (fun _ => 1))
    (combinedFixedColumn p hg side q.2 s.2 (fun _ => 1))
    (globalArithmeticBin p s₀ side q₀ j)
    (fun x => a x * globalSecondFixedOuterWeight p hg Ψ m ell Y side r ray s q x) (globalSecondLabel p)
    F Ψ Ψ (fixedTripleMask m q₀)
    (frequencyTwist A₁ (-firstSignedHeight side t)) (frequencyTwist A₂ (firstSignedHeight side t)) W windows
    (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
    (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j)

theorem globalFixedBinSource_squarefree (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (s₀ : Finset (GlobalSecondData ι)) (a : GlobalSecondData ι → ℂ) (side : Bool)
    (q₀ : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (ha : ∀ x ∈ s₀, GlobalSecondAdmissible x)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (r : QuadraticRayRing)
    (ray s q : QuadraticRayRing × QuadraticRayRing) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (windows : Fin 7 → ℝ → ℂ) (ell Y t : ℝ) :
    globalFixedBinSource p hg s₀ a side q₀ j F Ψ m r ray s q A₁ A₂ W windows ell Y t =
    globalTupleSourceSum p hg
      (combinedFixedColumn p hg side q.1 s.1 (fun _ => 1))
      (combinedFixedColumn p hg side q.2 s.2 (fun _ => 1))
      (globalSquarefreeBin p s₀ side q₀ j)
      (fun x => a x * globalSecondFixedOuterWeight p hg Ψ m ell Y side r ray s q x) (globalSecondLabel p)
      F Ψ Ψ (fixedTripleMask m q₀)
      (frequencyTwist A₁ (-firstSignedHeight side t)) (frequencyTwist A₂ (firstSignedHeight side t)) W windows
      (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
      (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j) := by
  unfold globalFixedBinSource globalTupleSourceSum globalSquarefreeBin
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hsf : Squarefree (SecondPassFiber.newLabel (globalSecondTuple p x))
  · rw [if_pos hsf]
  · rw [if_neg hsf]
    have hz : globalSecondFixedOuterWeight p hg Ψ m ell Y side r ray s q x = 0 := by
      by_contra hn
      exact hsf (globalSecondFixedOuterWeight_squarefree p hg hinj Ψ m ell Y side r ray s q x
        (ha x (Finset.mem_filter.mp hx).1) hn)
    dsimp only
    rw [hz, mul_zero, zero_mul]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration JointLogSeparation
open scoped Classical SchwartzMap
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

/-- Each arithmetic bin has uniform radial decay and a fixed polynomial cost in the first frequency. -/
theorem full_uniform_globalFixedBin_density_bound (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i u, V i u ≠ 0 → |u| ≤ M i)
    (hVc : ∀ i, HasCompactSupport (V i)) (hVs : ∀ i, Continuous (V i)) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
      [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i})) (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
      (s₀ : Finset (GlobalSecondData ι)) (a : GlobalSecondData ι → ℂ) (Γ : ℝ) (side : Bool)
      (q₀ : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (r : QuadraticRayRing)
      (ray s q : QuadraticRayRing × QuadraticRayRing) (ell Y t : ℝ),
      0 ≤ Γ → (∀ x ∈ s₀, ‖a x‖ ≤ Γ) → 0 < ell → 0 < Y → q₀.1 ≠ ⊥ → (∀ a, ‖Ψ a‖ ≤ 1) →
      (∀ x ∈ s₀, GlobalSecondAdmissible x) → (∀ x ∈ s₀, x.source.frequency ≠ 0) →
      (1 + globalBinRadial ell Y j)^A *
        ‖globalFixedBinSource p hg s₀ a side q₀ j F Ψ m r ray s q A₁ A₂ W V ell Y t‖ ≤
      Γ * C * globalPooledOuterBound ray ell Y j * (globalPooledLabelScale j * Ideal.absNorm q₀.1)^ε *
        (1+‖t‖)^(2*(J+2)) *
        densityChildEnergy p hg
          (combinedFixedColumn p hg side q.1 s.1 (fun _ => 1))
          (combinedFixedColumn p hg side q.2 s.2 (fun _ => 1))
          F Ψ Ψ (fixedTripleMask m q₀) (globalArithmeticTargets p s₀ side q₀ j)
          (V 5) (V 6) (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J := by
  obtain ⟨C,hC,htrans⟩ := full_uniform_global_twisted_density_transfer ε hε A₁ A₂ W V M hM hV A J
  obtain ⟨Cw,hCw,hwglobal⟩ := outerWindow_global_bound V hVc hVs
  refine ⟨C*Cw, mul_nonneg hC hCw, ?_⟩
  intro ι _ p hp _ hg hinj hpr s₀ a Γ side q₀ j F Ψ m r ray s q ell Y t hΓ haΓ hell hY hq hΨ ha hk
  rw [globalFixedBinSource_squarefree p hg hinj s₀ a side q₀ j ha]
  let bin := globalSquarefreeBin p s₀ side q₀ j
  let T := globalArithmeticTargets p s₀ side q₀ j
  have ht (x : GlobalSecondData ι) (hx : x ∈ bin) :
      x ∈ s₀ ∧ globalSecondFixedTriple p x = q₀ ∧ globalScaleIndex p side x = j :=
    Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hbound := globalArithmeticTargets_bounds p hp s₀ side q₀ j hk
  have hB : 0 ≤ globalPooledOuterBound ray ell Y j := by
    have h0 := (globalLogRep_pos j 0).le
    have h1 := (globalLogRep_pos j 1).le
    have h2 := (globalLogRep_pos j 2).le
    have h3 := (globalLogRep_pos j 3).le
    unfold globalPooledOuterBound
    positivity
  have hw : ∀ x ∈ bin, ‖a x * globalSecondFixedOuterWeight p hg Ψ m ell Y side r ray s q x‖ *
      ‖outerWindow V (globalBinZ p ell side j x) (globalBinUd p j x)
        (globalBinUe p j x) (globalBinUv p j x) (globalBinKap p j x)‖ ≤
      (Γ * globalPooledOuterBound ray ell Y j) * Cw := by
    intro x hx
    have hh := globalSecondFixedOuterWeight_bin_bound p hp hg hinj hpr Ψ hΨ m ell Y hell hY.le side r
      ray s q x (ha x (ht x hx).1).2.1 (hk x (ht x hx).1)
    rw [(ht x hx).2.2] at hh
    rw [norm_mul]
    exact mul_le_mul (mul_le_mul (haΓ x (ht x hx).1) hh (norm_nonneg _) hΓ)
      (hwglobal _ _ _ _ _) (norm_nonneg _) (mul_nonneg hΓ hB)
  have hh := htrans (-firstSignedHeight side t) (firstSignedHeight side t) (globalBinRadial ell Y j)
    (globalBinRadial_pos ell Y hell hY j) p hinj hg
    (combinedFixedColumn p hg side q.1 s.1 (fun _ => 1))
    (combinedFixedColumn p hg side q.2 s.2 (fun _ => 1)) bin T q₀
    (fun x => a x * globalSecondFixedOuterWeight p hg Ψ m ell Y side r ray s q x)
    (Γ*globalPooledOuterBound ray ell Y j*Cw) (globalPooledLabelScale j) (globalSecondLabel p)
    F Ψ Ψ (fixedTripleMask m q₀)
    (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
    (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) hq (mul_nonneg (mul_nonneg hΓ hB) hCw)
    (zero_le_one.trans (globalPooledLabelScale_ge_one j))
    (fun x hx => ha x (ht x hx).1) (fun x hx => (ht x hx).2.1)
    (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    (fun z hz => (hbound z hz).1) (fun z hz => (hbound z hz).2.1) hw
    (fun x _ => globalSecondLabel_span p x)
  have hnorm : ‖firstSignedHeight side t‖ = ‖t‖ := by cases side <;> simp only [firstSignedHeight, Bool.false_eq_true, ite_false, ite_true, norm_neg]
  simp only [norm_neg, hnorm] at hh
  exact hh.trans_eq (by rw [two_mul, pow_add]; ring)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassIntegration JointLogSeparation
open scoped Classical SchwartzMap ContDiff
local instance : Finite Oˣ := cubic_units_finite
local instance : Fintype Oˣ := Fintype.ofFinite _

/-- The literal two-pass source in one bin is controlled by fixed descendant energy. -/
theorem full_uniform_globalLiteral_bin_bound
    (g V W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (side : Bool) (ε : ℝ) (hε : 0 < ε) (A J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C : ℝ), 0 ≤ C ∧
      (∀ i, HasCompactSupport (windows i)) ∧ (∀ i, ContDiff ℝ ∞ (windows i)) ∧
      (∀ i u, windows i u ≠ 0 → |u| ≤ M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (hinj : Function.Injective (fun i => Ideal.span {p i})) (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
        (s₀ : Finset (GlobalSecondData ι)) (a : GlobalSecondData ι → ℂ) (Γ : ℝ) (q₀ : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
        (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (r : QuadraticRayRing)
        (ray s q : QuadraticRayRing × QuadraticRayRing) (ell Y t : ℝ),
      0 ≤ Γ → (∀ x ∈ s₀, ‖a x‖ ≤ Γ) → 0 < ell → 0 < Y → q₀.1 ≠ ⊥ → (∀ a, ‖Ψ a‖ ≤ 1) →
      (∀ x ∈ s₀, GlobalSecondAdmissible x) → (∀ x ∈ s₀, x.source.frequency ≠ 0) →
      (1 + globalBinRadial ell Y j)^A *
        ‖∑ x ∈ globalArithmeticBin p s₀ side q₀ j,
          a x * globalSecondFixedLiteralTerm p hg pool Ψ m g V W ell side r t (fun _ => Y) ray s q x‖ ≤
      Γ * C * globalPooledOuterBound ray ell Y j * (globalPooledLabelScale j * Ideal.absNorm q₀.1)^ε *
        (1+‖t‖)^(2*(J+2)) *
        densityChildEnergy p hg
          (combinedFixedColumn p hg side q.1 s.1 (fun _ => 1))
          (combinedFixedColumn p hg side q.2 s.2 (fun _ => 1))
          pool Ψ Ψ (fixedTripleMask m q₀) (globalArithmeticTargets p s₀ side q₀ j)
          (windows 5) (windows 6) (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J := by
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := full_uniform_globalFixedLiteral_profiles g V W M hM hgM side
  obtain ⟨C,hC,hbound⟩ := full_uniform_globalFixedBin_density_bound ε hε A₁ A₂ W windows
    (fun _ => M+6+1) (fun _ => by linarith) hwb hwc (fun i => (hws i).continuous) A J
  refine ⟨windows,C,hC,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hg hinj hpr s₀ a Γ q₀ j pool Ψ m r ray s q ell Y t hΓ haΓ hell hY hq hΨ ha hk
  have he : (∑ x ∈ globalArithmeticBin p s₀ side q₀ j,
      a x * globalSecondFixedLiteralTerm p hg pool Ψ m g V W ell side r t (fun _ => Y) ray s q x) =
      globalFixedBinSource p hg s₀ a side q₀ j pool Ψ m r ray s q A₁ A₂ W windows ell Y t := by
    unfold globalFixedBinSource globalTupleSourceSum
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨hxs,hxq,hxj⟩ := Finset.mem_filter.mp hx
    have hh := hid p hp hg pool Ψ m ell hell r t (fun _ => Y) ray s q x (ha x hxs).2.1 (hk x hxs)
    dsimp only at hh
    rw [hxj] at hh
    rw [hh, globalSecondRawSmoothPair_fixed_pool p hg hinj, hxq]
    ring
  rw [he]
  exact hbound p hp hg hinj hpr s₀ a Γ side q₀ j pool Ψ m r ray s q ell Y t hΓ haΓ hell hY hq hΨ ha hk

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson TruncatedPrincipalPoisson
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The zero dual frequency is a diagonal column mass with an Euler density. -/
def truncatedSecondZero (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (K : Finset ι → Finset ι → Finset O) : ℂ :=
  (Y : ℂ) * paperRadialFourier W 0 *
    ∑ G ∈ F.powerset,
      (‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
        Ψ m c d (fun _ => 1) G‖ ^ 2 : ℝ) * star (H G) * H G *
      ∑ E ∈ G.powerset, if 0 ∈ K G E then
        supportMobius E / (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ) else 0

theorem truncatedSecondSource_eq_nonzero_add_zero (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg F Ψ m c d H W Y K =
      truncatedSecondSource p hp hg F Ψ m c d H W Y (fun G E => (K G E).erase 0) +
        truncatedSecondZero p hg F Ψ m c d H W Y K := by
  unfold truncatedSecondSource truncatedSecondZero
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro G hG
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  by_cases h0 : 0 ∈ K G E
  · rw [← Finset.sum_erase_add _ _ h0]
    congr 1
    simp only [if_pos h0, secondFrequencyKernel_zero, Finset.union_empty,
      secondSourceCommonCoefficient]
    ring
  · simp only [Finset.erase_eq_of_notMem h0, if_neg h0, mul_zero, add_zero]

theorem primeDensity_nonneg_le_one (G : Finset ι) :
    0 ≤ ∏ i ∈ G, (1 - (1 : ℝ) / Ideal.absNorm (Ideal.span {p i})) ∧
      (∏ i ∈ G, (1 - (1 : ℝ) / Ideal.absNorm (Ideal.span {p i}))) ≤ 1 := by
  have hn (i : ι) : (1 : ℝ) ≤ Ideal.absNorm (Ideal.span {p i}) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne (Ideal.span {p i})))
  have hnonneg (i : ι) : 0 ≤ 1 - (1 : ℝ) / Ideal.absNorm (Ideal.span {p i}) :=
    sub_nonneg.mpr ((div_le_one (zero_lt_one.trans_le (hn i))).mpr (hn i))
  exact ⟨Finset.prod_nonneg (fun i _ => hnonneg i),
    Finset.prod_le_one (fun i _ => hnonneg i)
      (fun i _ => sub_le_self _ (by positivity))⟩

def secondDiagonalMass (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) : ℝ :=
  ∑ G ∈ F.powerset, ‖secondInputCoefficient p
    (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d H G‖ ^ 2 *
    ∏ i ∈ G, (1 - (1 : ℝ) / Ideal.absNorm (Ideal.span {p i}))

theorem truncatedSecondZero_eq_density
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O)
    (hzero : ∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : O) ∈ K G E) :
    truncatedSecondZero p hg F Ψ m c d H W Y K =
      (Y : ℂ) * paperRadialFourier W 0 * (secondDiagonalMass p hg F Ψ m c d H : ℂ) := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  unfold truncatedSecondZero secondDiagonalMass
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_natCast]
  apply Finset.sum_congr rfl
  intro G hG
  have hd : (∑ E ∈ G.powerset, if (0 : O) ∈ K G E then
      supportMobius E / (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ) else 0) =
      ∏ i ∈ G, (1 - (1 : ℂ) / Ideal.absNorm (Ideal.span {p i})) := by
    rw [← primeSubset_moebius_norm_sum (fun i => Ideal.span {p i}) hprime hinj G]
    apply Finset.sum_congr rfl
    intro E hE
    rw [if_pos (hzero G hG E hE), ringComplex_norm_sq_eq_absNorm_span,
      span_finset_prime_product, prime_product_moebius _ hprime hinj]
    rfl
  rw [hd]
  have hi : secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
      Ψ m c d H G = secondInputCoefficient p
      (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d (fun _ => 1) G * H G := by
    simp only [secondInputCoefficient, mul_one]
  have hh : star (H G) * H G = (‖H G‖ ^ 2 : ℝ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hi, norm_mul, mul_pow, Complex.ofReal_mul]
  rw [mul_assoc (↑(‖secondInputCoefficient p
    (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d (fun _ => 1) G‖ ^ 2))
    (star (H G)), hh]

theorem secondDiagonalMass_nonneg_le
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) :
    0 ≤ secondDiagonalMass p hg F Ψ m c d H ∧
      secondDiagonalMass p hg F Ψ m c d H ≤
        ∑ G ∈ F.powerset, ‖secondInputCoefficient p
          (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d H G‖ ^ 2 := by
  constructor
  · exact Finset.sum_nonneg (fun G _ => mul_nonneg (sq_nonneg _)
      (primeDensity_nonneg_le_one p G).1)
  · apply Finset.sum_le_sum
    intro G hG
    exact mul_le_of_le_one_right (sq_nonneg _) (primeDensity_nonneg_le_one p G).2

theorem truncatedSecondZero_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O)
    (hzero : ∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : O) ∈ K G E) :
    ‖truncatedSecondZero p hg F Ψ m c d H W Y K‖ ≤
      |Y| * ‖paperRadialFourier W 0‖ *
        ∑ G ∈ F.powerset, ‖secondInputCoefficient p
          (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d H G‖ ^ 2 := by
  rw [truncatedSecondZero_eq_density p hg hinj F Ψ m c d H W Y K hzero]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_of_nonneg (secondDiagonalMass_nonneg_le p hg F Ψ m c d H).1]
  exact mul_le_mul_of_nonneg_left (secondDiagonalMass_nonneg_le p hg F Ψ m c d H).2
    (mul_nonneg (abs_nonneg _) (norm_nonneg _))

theorem zero_mem_secondTailCutoff (L Y H : ℝ) : (0 : O) ∈ secondTailCutoff L Y H := by
  simpa only [secondTailCutoff, Set.Finite.mem_toFinset, Set.mem_setOf_eq, map_zero, norm_zero]
    using Real.sqrt_nonneg (H * L ^ 3 / Y)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap
section
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem columnLog_norm_lower (X M : ℝ) (hX : 0<X) (S : Finset ι)
    (h : -M≤columnLog p X S) : X*Real.exp (-M)≤primeProductNorm p S := by
  have he := Real.exp_le_exp.mpr h
  rw [columnLog,Real.exp_log (div_pos (primeProductNorm_pos p hp S) hX)] at he
  simpa only [mul_comm] using (le_div_iff₀ hX).mp he

omit [DecidableEq ι] in
theorem normalized_second_coefficient_sq_le
    (Ψ : O→*ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
    (g : ℝ→ℂ) (G X : ℝ) (hG : ∀t,‖g t‖≤G) (S : Finset ι) :
    ‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d
      (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2≤G^2/primeProductNorm p S := by
  have hG0 : 0≤G := (norm_nonneg (g 0)).trans (hG 0)
  have ht := secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
    (normalizedColumn p (fun A => g (columnLog p X A))) S
  apply (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
  simp only [normalizedColumn,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_pow]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hG _) 2) (sq_nonneg _)

include hp in

omit [DecidableEq ι] in
theorem normalized_second_mass_zero
    (F : Finset ι) (Ψ : O→*ℂ) (m c d : O) (g : ℝ→ℂ)
    (M X : ℝ) (hX : 0<X) (hM : ∀t,g t≠0 → |t|≤M) (hsmall : X*Real.exp M<1) :
    (∑S∈F.powerset,‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d
      (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2)=0 := by
  apply Finset.sum_eq_zero
  intro S hS
  have hz : g (columnLog p X S)=0 := by
    by_contra hn
    have hh := columnLog_norm_upper p hp X M hX S ((le_abs_self _).trans (hM _ hn))
    have ho := primeProductNorm_ge_one p hp S
    linarith
  simp [secondInputCoefficient,normalizedColumn,hz]

include hp in

theorem normalized_second_mass_fixed_bound
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O→*ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
    (g : ℝ→ℂ) (G M X : ℝ) (hX : 0<X)
    (hG : ∀t,‖g t‖≤G) (hM : ∀t,g t≠0 → |t|≤M) :
    (∑S∈F.powerset,‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d
      (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2)≤
      (diagonalControl sieveCutoff)*Real.exp (2*M)*G^2 := by
  have hcontrol := diagonalControl_nonneg sieveCutoff
  by_cases hsmall : X*Real.exp M<1
  · rw [normalized_second_mass_zero p hp hg F Ψ m c d g M X hX hM hsmall]
    positivity
  have hH : 1≤X*Real.exp M := le_of_not_gt hsmall
  let T := F.powerset.filter (fun S => g (columnLog p X S)≠0)
  have hsub : T⊆boundedPrimeSupports p F (X*Real.exp M) := by
    intro S hS
    obtain ⟨hSF,hSn⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨hSF,columnLog_norm_upper p hp X M hX S
      ((le_abs_self _).trans (hM _ hSn))⟩
  have hcard : (T.card:ℝ)≤(diagonalControl sieveCutoff)*(X*Real.exp M) := by
    apply (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    exact boundedPrimeSupports_card p hinj F (X*Real.exp M) hH
  have he : (∑S∈F.powerset,‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d
        (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2)=
      ∑S∈T,‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d
        (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hn
    have hz : g (columnLog p X S)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hS,hh⟩)
    simp [secondInputCoefficient,normalizedColumn,hz]
  rw [he]
  calc
    _ ≤ ∑_S∈T,G^2/(X*Real.exp (-M)) := by
      apply Finset.sum_le_sum
      intro S hS
      apply (normalized_second_coefficient_sq_le p hg Ψ hΨ m c d g G X hG S).trans
      have hlo := columnLog_norm_lower p hp X M hX S (abs_le.mp (hM _ (Finset.mem_filter.mp hS).2)).1
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hlo
    _ = (T.card:ℝ)*(G^2/(X*Real.exp (-M))) := by simp
    _ ≤ ((diagonalControl sieveCutoff)*(X*Real.exp M))*(G^2/(X*Real.exp (-M))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (diagonalControl sieveCutoff)*Real.exp (2*M)*G^2 := by
      rw [show 2*M=M+M by ring,Real.exp_add,Real.exp_neg]
      field_simp [hX.ne',Real.exp_ne_zero]

end

theorem full_uniform_normalized_second_mass (g : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O) (X : ℝ),0<X →
      (∑S∈F.powerset,‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d
        (normalizedColumn p (fun A => g (columnLog p X A))) S‖^2)≤C := by
  have hcontrol := diagonalControl_nonneg sieveCutoff
  refine ⟨(diagonalControl sieveCutoff)*Real.exp (2*M)*(SchwartzMap.seminorm ℝ 0 0 g)^2+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj F Ψ hΨ m c d X hX
  exact (normalized_second_mass_fixed_bound p hp hg hinj F Ψ hΨ m c d g _ M X hX
    (fun t => g.norm_le_seminorm ℝ t) hM).trans (by linarith)


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels JointLogSeparation
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondInputCoefficient_fixedColumn_norm_le
    (Ψ : O →* ℂ) (m c d : O) (side : Bool) (r : QuadraticRayRing)
    (H : Finset ι → ℂ) (S : Finset ι) :
    ‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
      Ψ m c d (firstFixedColumn p hg side r H) S‖ ≤
    ‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
      Ψ m c d H S‖ := by
  simp only [secondInputCoefficient, norm_mul, norm_pow]
  gcongr
  exact firstFixedColumn_norm_le p hg side r H S

include hp in
/-- The first common divisor supplies reciprocal norm; frequency and residue masks are contractions. -/
theorem firstCoreInput_coefficient_sq_le
    (Ψ : O →* ℂ) (m c d : O) (g V : 𝓢(ℝ, ℂ)) (side : Bool)
    (r : QuadraticRayRing) (t : ℝ) (D S : Finset ι) (hDS : Disjoint D S)
    (X : ℝ) (hX : 0 < X) :
    ‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d
      (firstFixedColumn p hg side r (firstCoreTest
        (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) side t D)) S‖ ^ 2 ≤
    (primeProductNorm p D)⁻¹ *
      ‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d
        (normalizedColumn p (fun A => firstCoreBaseProfile g V side
          (columnLog p (X / primeProductNorm p D) A))) S‖ ^ 2 := by
  apply (pow_le_pow_left₀ (norm_nonneg _)
    (secondInputCoefficient_fixedColumn_norm_le p hg Ψ m c d side r _ S) 2).trans_eq
  have he := firstCoreTest_eq_normalized_mode p hp g V side t D S hDS X hX
  simp only [secondInputCoefficient, norm_mul, norm_pow, he, norm_inv,
    Complex.norm_of_nonneg (norm_nonneg _), normalizedColumn, norm_div,
    firstCoreModeProfile, frequencyTwist_norm, primeProductNorm, inv_pow]
  ring

def globalFirstColumnMass (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g : 𝓢(ℝ, ℂ)) (ell : ℝ) (side : Bool) : ℝ :=
  ∑ S ∈ (globalFirstRawPool pool b).powerset,
    ‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ
      (m * globalFirstBadLabel p b) (globalFirstRetainedLabel p b) (∏ i ∈ b.firstDivisor, p i)
      (normalizedColumn p (fun A => g (columnLog p
        (globalFirstBlockColumnScale p ell side b / primeProductNorm p b.firstCommon) A))) S‖ ^ 2

theorem globalFirstColumnMass_nonneg (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g : 𝓢(ℝ, ℂ)) (ell : ℝ) (side : Bool) :
    0 ≤ globalFirstColumnMass p hg pool b Ψ m g ell side :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

include hp in
theorem globalFirstInput_mass_le (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ, ℂ)) (ell : ℝ) (hell : 0 < ell)
    (side : Bool) (r : QuadraticRayRing) (t : ℝ) :
    (∑ S ∈ (globalFirstRawPool pool b).powerset,
      ‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ
        (m * globalFirstBadLabel p b) (globalFirstRetainedLabel p b) (∏ i ∈ b.firstDivisor, p i)
        (globalFirstInputTest p hg g V ell side r t b) S‖ ^ 2) ≤
      (primeProductNorm p b.firstCommon)⁻¹ *
        globalFirstColumnMass p hg pool b Ψ m (firstCoreBaseProfile g V side) ell side := by
  unfold globalFirstColumnMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  exact firstCoreInput_coefficient_sq_le p hp hg Ψ _ _ _ g V side r t b.firstCommon S
    (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hS) disjoint_sdiff_self_right) _
    (div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _)))

include hp in
theorem globalFirstColumnMass_support (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g : 𝓢(ℝ, ℂ)) (ell M : ℝ) (hell : 0 < ell)
    (hM : ∀ t, g t ≠ 0 → |t| ≤ M) (side : Bool)
    (hmass : globalFirstColumnMass p hg pool b Ψ m g ell side ≠ 0) :
    primeProductNorm p b.common ≤ ell * Real.exp M ∧
      primeProductNorm p b.firstCommon ≤ ell * Real.exp M := by
  let a := primeProductNorm p (b.cube.sideDivisor side)
  let c := primeProductNorm p b.common
  let v := primeProductNorm p b.firstCommon
  have ha : 1 ≤ a := primeProductNorm_ge_one p hp _
  have hc : 1 ≤ c := primeProductNorm_ge_one p hp _
  have hv : 1 ≤ v := primeProductNorm_ge_one p hp _
  have hden : 0 < a * c * v := by positivity
  have hX : 0 < globalFirstBlockColumnScale p ell side b / primeProductNorm p b.firstCommon := by
    change 0 < ell / (a * c) / v
    positivity
  have hlow : 1 ≤ (globalFirstBlockColumnScale p ell side b / primeProductNorm p b.firstCommon) * Real.exp M := by
    by_contra hh
    apply hmass
    exact normalized_second_mass_zero p hp hg (globalFirstRawPool pool b) Ψ
      (m * globalFirstBadLabel p b) (globalFirstRetainedLabel p b) (∏ i ∈ b.firstDivisor, p i)
      g M _ hX hM (lt_of_not_ge hh)
  have he : (globalFirstBlockColumnScale p ell side b / primeProductNorm p b.firstCommon) * Real.exp M =
      ell * Real.exp M / (a * c * v) := by change (ell / (a*c) / v) * Real.exp M = _; ring
  rw [he] at hlow
  have hb : a * c * v ≤ ell * Real.exp M := by simpa only [one_mul] using (le_div_iff₀ hden).mp hlow
  constructor
  · change c ≤ _
    calc
      c = 1 * c * 1 := by ring
      _ ≤ a * c * v := by gcongr
      _ ≤ _ := hb
  · change v ≤ _
    calc
      v = 1 * 1 * v := by ring
      _ ≤ a * c * v := by gcongr
      _ ≤ _ := hb

include hp in
theorem globalFirstColumnMass_zero_off_support (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g : 𝓢(ℝ, ℂ)) (ell M U : ℝ) (hell : 0 < ell)
    (hM : ∀ t, g t ≠ 0 → |t| ≤ M) (hU : ell * Real.exp M ≤ U) (side : Bool)
    (hoff : ¬(primeProductNorm p b.common ≤ U ∧ primeProductNorm p b.firstCommon ≤ U)) :
    globalFirstColumnMass p hg pool b Ψ m g ell side = 0 := by
  by_contra hm
  have h := globalFirstColumnMass_support p hp hg pool b Ψ m g ell M hell hM side hm
  exact hoff ⟨h.1.trans hU, h.2.trans hU⟩

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

def globalFirstZeroSource (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ, ℂ))
    (ell : ℝ) (side : Bool) (r : QuadraticRayRing) (t : ℝ) (Y : GlobalFirstData ι → ℝ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) : ℂ :=
  ∑ b ∈ s, w b * truncatedSecondZero p hg (globalFirstRawPool pool b) Ψ
    (m * globalFirstBadLabel p b) (globalFirstRetainedLabel p b) (∏ i ∈ b.firstDivisor, p i)
    (globalFirstInputTest p hg g V ell side r t b) W (Y b) (cutoff b)

def globalFirstDiagonalCost (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ, ℂ))
    (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℝ :=
  ∑ b ∈ s, ‖w b‖ * (primeProductNorm p b.firstCommon)⁻¹ *
    (|Y b| * ‖paperRadialFourier W 0‖ * globalFirstColumnMass p hg pool b Ψ m g ell side)

include hp in
theorem globalFirstDiagonalCost_nonneg (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ, ℂ))
    (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    0 ≤ globalFirstDiagonalCost p hg pool s w Ψ m g W ell side Y := by
  apply Finset.sum_nonneg
  intro b hb
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (primeProductNorm_pos p hp _).le))
    (mul_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (globalFirstColumnMass_nonneg p hg _ _ _ _ _ _ _))

theorem globalFirstTruncatedSource_eq_nonzero_add_zero
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ, ℂ)) (ell : ℝ) (side : Bool)
    (r : QuadraticRayRing) (t : ℝ) (Y : GlobalFirstData ι → ℝ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) :
    globalFirstTruncatedSource p hp hg pool s w Ψ m g V W ell side r t Y cutoff =
      globalFirstTruncatedSource p hp hg pool s w Ψ m g V W ell side r t Y
        (fun b G E => (cutoff b G E).erase 0) +
      globalFirstZeroSource p hg pool s w Ψ m g V W ell side r t Y cutoff := by
  unfold globalFirstTruncatedSource globalFirstZeroSource
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [truncatedSecondSource_eq_nonzero_add_zero p hg hp]
  exact mul_add _ _ _

include hp in
theorem globalFirstZeroSource_bound
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ, ℂ)) (ell : ℝ) (hell : 0 < ell)
    (side : Bool) (r : QuadraticRayRing) (t : ℝ) (Y : GlobalFirstData ι → ℝ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (hzero : ∀ b ∈ s, ∀ G ∈ (globalFirstRawPool pool b).powerset,
      ∀ E ∈ G.powerset, (0 : O) ∈ cutoff b G E) :
    ‖globalFirstZeroSource p hg pool s w Ψ m g V W ell side r t Y cutoff‖ ≤
      globalFirstDiagonalCost p hg pool s w Ψ m (firstCoreBaseProfile g V side) W ell side Y := by
  unfold globalFirstZeroSource globalFirstDiagonalCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  rw [norm_mul]
  have hz := truncatedSecondZero_norm_le p hg hinj (globalFirstRawPool pool b) Ψ
    (m * globalFirstBadLabel p b) (globalFirstRetainedLabel p b) (∏ i ∈ b.firstDivisor, p i)
    (globalFirstInputTest p hg g V ell side r t b) W (Y b) (cutoff b) (hzero b hb)
  have hm := globalFirstInput_mass_le p hp hg pool b Ψ m g V ell hell side r t
  have h := hz.trans (mul_le_mul_of_nonneg_left hm (mul_nonneg (abs_nonneg _) (norm_nonneg _)))
  exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (by ring)

include hp in
theorem globalFirstDiagonalCost_eq_supported (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ, ℂ))
    (ell M U : ℝ) (hell : 0 < ell) (hM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (hU : ell * Real.exp M ≤ U) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstDiagonalCost p hg pool s w Ψ m g W ell side Y =
      globalFirstDiagonalCost p hg pool
        (s.filter (fun b => primeProductNorm p b.common ≤ U ∧ primeProductNorm p b.firstCommon ≤ U))
        w Ψ m g W ell side Y := by
  unfold globalFirstDiagonalCost
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro b hb hn
  have hoff : ¬(primeProductNorm p b.common ≤ U ∧ primeProductNorm p b.firstCommon ≤ U) :=
    fun h => hn (Finset.mem_filter.mpr ⟨hb,h⟩)
  rw [globalFirstColumnMass_zero_off_support p hp hg pool b Ψ m g ell M U hell hM hU side hoff,
    mul_zero, mul_zero]

theorem globalFirstFiniteEnergy_le_nonzero_diagonal_tail
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
    (hw : ∀ b ∈ s, 0 ≤ w b) (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ, ℂ))
    (ell : ℝ) (hell : 0 < ell) (side : Bool) (r : QuadraticRayRing) (t : ℝ)
    (Y : GlobalFirstData ι → ℝ) (hY : ∀ b ∈ s, 0 < Y b) (T : GlobalFirstData ι → Finset O)
    (hT : ∀ b ∈ s, ∀ z ∈ T b, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y b)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (hzero : ∀ b ∈ s, ∀ G ∈ (globalFirstRawPool pool b).powerset,
      ∀ E ∈ G.powerset, (0 : O) ∈ cutoff b G E) :
    (∑ b ∈ s, w b * ∑ z ∈ T b, ‖globalFirstCoreRow p hg pool Ψ m g V ell side r t b z‖ ^ 2) ≤
      ‖globalFirstTruncatedSource p hp hg pool s (fun b => (w b : ℂ)) Ψ m g V rowMajorant ell side r t Y
        (fun b G E => (cutoff b G E).erase 0)‖ +
      globalFirstDiagonalCost p hg pool s (fun b => (w b : ℂ)) Ψ m
        (firstCoreBaseProfile g V side) rowMajorant ell side Y +
      ‖globalFirstSourceTail p hp hg pool s (fun b => (w b : ℂ)) Ψ m g V rowMajorant ell side r t Y cutoff‖ := by
  apply (globalFirstFiniteEnergy_le_sources p hp hg hinj pool s w hw Ψ m g V ell side r t Y hY T hT cutoff).trans
  rw [globalFirstTruncatedSource_eq_nonzero_add_zero]
  exact add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl
    (globalFirstZeroSource_bound p hp hg hinj pool s _ Ψ m g V rowMajorant ell hell side r t Y cutoff hzero))) le_rfl

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

def globalBinFirstCoefficient (K ell B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  K / (globalLogRep j 5 * ell * B^2 * F * Real.sqrt (globalLogRep j 9))

theorem globalBinFirstCoefficient_nonneg (K ell B F : ℝ) (hK : 0 ≤ K)
    (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) :
    0 ≤ globalBinFirstCoefficient K ell B F j := by
  have h5 := globalLogRep_pos j 5
  have h9 := Real.sqrt_pos.mpr (globalLogRep_pos j 9)
  unfold globalBinFirstCoefficient
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def globalFirstCoefficient (K ell B F : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  globalBinFirstCoefficient K ell B F (globalFirstIndex p side b)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalPooledRowScale_first (K ell B F : ℝ) (side : Bool) (x : GlobalSecondData ι) :
    globalPooledRowScale K ell B F (globalScaleIndex p side x)=
      globalFirstPooledRow p K ell B F side x.first := by
  have hc (i : Fin 10) (hi : i=1 ∨ i=4 ∨ i=5 ∨ i=9) :
      globalLogRep (globalScaleIndex p side x) i=globalLogRep (globalFirstIndex p side x.first) i := by
    rcases hi with rfl|rfl|rfl|rfl <;>
      simp [globalLogRep,globalFirstIndex,globalScaleIndex,globalScaleVector,GlobalFirstData.append,GlobalSecondData.first,globalCubeJNorm,globalCubeActiveRoot]
  unfold globalFirstPooledRow globalPooledRowScale
  rw [hc 1 (by simp),hc 4 (by simp),hc 5 (by simp)]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalBinFirstCoefficient_first (K ell B F : ℝ) (side : Bool) (x : GlobalSecondData ι) :
    globalBinFirstCoefficient K ell B F (globalScaleIndex p side x)=
      globalFirstCoefficient p K ell B F side x.first := by
  have hc (i : Fin 10) (hi : i=5 ∨ i=9) :
      globalLogRep (globalScaleIndex p side x) i=globalLogRep (globalFirstIndex p side x.first) i := by
    rcases hi with rfl|rfl <;>
      simp [globalLogRep,globalFirstIndex,globalScaleIndex,globalScaleVector,GlobalFirstData.append,GlobalSecondData.first,globalCubeJNorm,globalCubeActiveRoot]
  unfold globalFirstCoefficient globalBinFirstCoefficient
  rw [hc 5 (by simp),hc 9 (by simp)]


include hp in
theorem globalFirst_diagonal_scalar (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (side : Bool) (b : GlobalFirstData ι) :
    globalFirstCoefficient p K ell B F side b*
        globalFirstPooledRow p K ell B F side b*(primeProductNorm p b.firstCommon)⁻¹ ≤
      (Real.exp 1)^3*ell*B^2*F*(1/primeProductNorm p b.common)*
        (1/primeProductNorm p b.firstCommon)*
        (1/‖ringComplex (∏ i∈cubeActiveSupport b.cube.support
          (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖) := by
  let x := b.append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p side x
  let A := globalCubeActiveRoot p x
  have hbds := globalScaleIndex_bounds p hp side x (by exact one_ne_zero)
  have hc := (hbds 1).2
  have ha := (hbds 9).2
  change primeProductNorm p b.common≤globalLogRep j 1*Real.exp 1 at hc
  change A^2≤globalLogRep j 9*Real.exp 1 at ha
  have hcp := primeProductNorm_pos p hp b.common
  have htp := primeProductNorm_pos p hp b.firstCommon
  have hA := globalCubeActiveRoot_pos p hp x
  change 0<A at hA
  have h1 := globalLogRep_ge_one j 1
  have h4 := globalLogRep_ge_one j 4
  have h1p := globalLogRep_pos j 1
  have h4p := globalLogRep_pos j 4
  have h5p := globalLogRep_pos j 5
  have h9p := globalLogRep_pos j 9
  have h9s := Real.sqrt_pos.mpr h9p
  have he : 1≤Real.exp 1 := Real.one_le_exp (by norm_num)
  have has : A≤Real.sqrt (globalLogRep j 9)*Real.exp 1 := by
    apply (sq_le_sq₀ hA.le (mul_nonneg h9s.le (Real.exp_pos _).le)).mp
    rw [mul_pow,Real.sq_sqrt h9p.le]
    exact ha.trans (mul_le_mul_of_nonneg_left (by nlinarith : Real.exp 1≤(Real.exp 1)^2) h9p.le)
  have hcA : primeProductNorm p b.common*A ≤
      (Real.exp 1)^2*((globalLogRep j 1)^2*globalLogRep j 4*Real.sqrt (globalLogRep j 9)) := by
    calc
      _ ≤ (globalLogRep j 1*Real.exp 1)*(Real.sqrt (globalLogRep j 9)*Real.exp 1) :=
        mul_le_mul hc has hA.le (by positivity)
      _ = (Real.exp 1)^2*(globalLogRep j 1*1*1*Real.sqrt (globalLogRep j 9)) := by ring
      _ ≤ (Real.exp 1)^2*(globalLogRep j 1*globalLogRep j 1*globalLogRep j 4*Real.sqrt (globalLogRep j 9)) := by gcongr
      _ = _ := by ring
  have hr : 1/((globalLogRep j 1)^2*globalLogRep j 4*Real.sqrt (globalLogRep j 9))≤
      (Real.exp 1)^2/(primeProductNorm p b.common*A) := by
    apply (div_le_div_iff₀ (by positivity) (mul_pos hcp hA)).mpr
    simpa only [one_mul] using hcA
  change (K/(globalLogRep j 5*ell*B^2*F*Real.sqrt (globalLogRep j 9)))*
      (Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4))*
      (primeProductNorm p b.firstCommon)⁻¹≤_
  calc
    _ = (Real.exp 1*ell*B^2*F)*(1/((globalLogRep j 1)^2*globalLogRep j 4*Real.sqrt (globalLogRep j 9)))*
        (primeProductNorm p b.firstCommon)⁻¹ := by field_simp
    _ ≤ (Real.exp 1*ell*B^2*F)*((Real.exp 1)^2/(primeProductNorm p b.common*A))*
        (primeProductNorm p b.firstCommon)⁻¹ := by gcongr
    _ = _ := by change _ = (Real.exp 1)^3*ell*B^2*F*(1/primeProductNorm p b.common)*(1/primeProductNorm p b.firstCommon)*(1/A); ring


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

/-- A positive lattice-count constant, uniform in all prime families. -/
def descentLatticeConstant : ℝ := 1 + diagonalControl sieveCutoff

theorem descentLatticeConstant_pos : 0 < descentLatticeConstant := by
  have h := diagonalControl_nonneg sieveCutoff
  unfold descentLatticeConstant
  positivity

theorem descent_ideal_count (S : Finset (Ideal O)) (H : ℝ) (hH : 1 ≤ H)
    (_hS : ∀ I ∈ S, I ≠ 0) (hn : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (S.card : ℝ) ≤ descentLatticeConstant * H := by
  apply (finite_ideal_card_bound S H hH hn).trans
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (zero_le_one.trans hH)

theorem descent_ideal_inverse_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I∈S,I≠0) (hH : ∀ I∈S,(Ideal.absNorm I : ℝ)≤H) :
    (∑ I∈S,1/(Ideal.absNorm I : ℝ))≤descentLatticeConstant*Real.exp 1*(normLogBin H+1 : ℝ) := by
  have hconst := descentLatticeConstant_pos.le
  have hpos (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  let T := Finset.range (normLogBin H+1)
  let bin (j : ℕ) := S.filter (fun I => normLogBin (Ideal.absNorm I)=j)
  have hmap : ∀ I∈S,normLogBin (Ideal.absNorm I : ℝ)∈T := by
    intro I hI
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (normLogBin_mono (by linarith [hpos I hI]) (hH I hI)))
  have hbin (j : ℕ) : (∑ I∈bin j,1/(Ideal.absNorm I : ℝ))≤descentLatticeConstant*Real.exp 1 := by
    have hp := normLogScale_pos j
    have hone := normLogScale_ge_one j
    have he := Real.one_le_exp (show (0 : ℝ)≤1 by norm_num)
    have hc : ((bin j).card : ℝ)≤descentLatticeConstant*(normLogScale j*Real.exp 1) := by
      apply descent_ideal_count _ _ (by nlinarith)
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        simpa only [hj] using (normLogBin_scale_bounds (Ideal.absNorm I : ℝ) (hpos I hIS)).2
    have ht (I : Ideal O) (hI : I∈bin j) : 1/(Ideal.absNorm I : ℝ)≤1/normLogScale j := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (normLogBin_scale_bounds (Ideal.absNorm I : ℝ) (hpos I hIS)).1
      rw [hj] at hb
      exact one_div_le_one_div_of_le hp hb
    calc
      _ ≤ ∑ _I∈bin j,1/normLogScale j := Finset.sum_le_sum ht
      _ = ((bin j).card : ℝ)/normLogScale j := by simp [div_eq_mul_inv]
      _ ≤ (descentLatticeConstant*(normLogScale j*Real.exp 1))/normLogScale j := div_le_div_of_nonneg_right hc hp.le
      _ = _ := by field_simp
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑ _j∈T,descentLatticeConstant*Real.exp 1 := Finset.sum_le_sum (fun j _ => hbin j)
    _ = _ := by simp [T]; ring

theorem descent_normLogBin_small_power (ε : ℝ) (hε : 0<ε) (H : ℝ) (hH : 1≤H) :
    (normLogBin H+1 : ℝ)≤(1+1/ε)*H^ε := by
  have hH0 : 0<H := by linarith
  have hb : (normLogBin H : ℝ)≤Real.log H := Nat.floor_le (Real.log_nonneg hH)
  have hl := Real.log_le_rpow_div hH0.le hε
  have hp := Real.one_le_rpow hH hε.le
  calc
    _ ≤ H^ε/ε+1 := by linarith
    _ ≤ H^ε/ε+H^ε := add_le_add le_rfl hp
    _ = _ := by ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]

def cubeProductIdeal (x : CubeCoordinates ι) : Ideal O :=
  Ideal.span {primeProduct p x.support x.leftExponent}*
    Ideal.span {primeProduct p x.support x.rightExponent}

def cubeParityKey (x : CubeCoordinates ι) : Ideal O × Ideal O :=
  (Ideal.span {squarefreeLabel p x.support (fun i => x.leftExponent i+x.rightExponent i)},
   Ideal.span {b0Label p x.support (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit*
     j2Label p x.support (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit})

def cubeDivisorKey (x : CubeCoordinates ι) : Fin 3 → Ideal O :=
  ![Ideal.span {primeProduct p x.support x.leftExponent},
    Ideal.span {aLabel p x.support x.leftBit},Ideal.span {aLabel p x.support x.rightBit}]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem cubeParityKey_product (x : CubeCoordinates ι) :
    cubeProductIdeal p x=(cubeParityKey p x).2^2*(cubeParityKey p x).1 := by
  have h := FirstPassCubeLabels.cube_pair_product_decomposition p x.support
    x.leftExponent x.rightExponent x.leftBit x.rightBit x.support_pos
  have h' := congrArg (fun z : O => (Ideal.span {z} : Ideal O)) h
  simp only [cubeProductIdeal,cubeParityKey,pow_two,←Ideal.span_singleton_mul_span_singleton] at h' ⊢
  convert h' using 1 ; congr 1 ; ring

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem cubeDivisorKey_dvd (x : CubeCoordinates ι) (i : Fin 3) :
    cubeDivisorKey p x i ∣ cubeProductIdeal p x := by
  have hA1 := span_dvd_of_element_dvd
    (aLabel_dvd_primeProduct p x.support (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.support_pos)
  have hA2 := span_dvd_of_element_dvd
    (aLabel_dvd_primeProduct p x.support (fun i => x.leftExponent i+x.rightExponent i) x.rightBit x.support_pos)
  rw [primeProduct_add,←Ideal.span_singleton_mul_span_singleton] at hA1 hA2
  fin_cases i
  · exact dvd_mul_right _ _
  · exact hA1
  · exact hA2

variable (hp : ∀ i,p i≠0)
include hp

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem cubeParityKey_ne_zero (x : CubeCoordinates ι) :
    (cubeParityKey p x).1≠0 ∧ (cubeParityKey p x).2≠0 := by
  constructor
  · exact (Ideal.span_singleton_eq_bot.not).mpr (primeProduct_ne_zero p hp _ _)
  · exact (Ideal.span_singleton_eq_bot.not).mpr
      (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem cubeProductIdeal_ne_zero (x : CubeCoordinates ι) : cubeProductIdeal p x≠0 := by
  rw [cubeParityKey_product]
  exact mul_ne_zero (pow_ne_zero _ (cubeParityKey_ne_zero p hp x).2) (cubeParityKey_ne_zero p hp x).1

variable (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem cubeDivisorKey_injective_on_product {x y : CubeCoordinates ι}
    (hx : x.Admissible) (hy : y.Admissible)
    (hprod : cubeProductIdeal p x=cubeProductIdeal p y)
    (hk : cubeDivisorKey p x=cubeDivisorKey p y) : x=y := by
  have h1 := congrFun hk 0
  have hA1 := congrFun hk 1
  have hA2 := congrFun hk 2
  change Ideal.span {primeProduct p x.support x.leftExponent}=
    Ideal.span {primeProduct p y.support y.leftExponent} at h1
  have h2 : Ideal.span {primeProduct p x.support x.rightExponent}=
    Ideal.span {primeProduct p y.support y.rightExponent} := by
    apply mul_left_cancel₀ ((Ideal.span_singleton_eq_bot.not).mpr (primeProduct_ne_zero p hp x.support x.leftExponent))
    simpa only [cubeProductIdeal,h1] using hprod
  have hv1 := primeProduct_span_exponents_eq p hinj x.support y.support
    x.leftExponent y.leftExponent x.left_off y.left_off h1
  have hv2 := primeProduct_span_exponents_eq p hinj x.support y.support
    x.rightExponent y.rightExponent x.right_off y.right_off h2
  change Ideal.span {aLabel p x.support x.leftBit}=Ideal.span {aLabel p y.support y.leftBit} at hA1
  change Ideal.span {aLabel p x.support x.rightBit}=Ideal.span {aLabel p y.support y.rightBit} at hA2
  rw [CubeCoordinates.aLabel_left p x hx,CubeCoordinates.aLabel_left p y hy,
    span_finset_prime_product,span_finset_prime_product] at hA1
  rw [CubeCoordinates.aLabel_right p x hx,CubeCoordinates.aLabel_right p y hy,
    span_finset_prime_product,span_finset_prime_product] at hA2
  exact CubeCoordinates.ext (Finsupp.ext (congrFun hv1)) (Finsupp.ext (congrFun hv2))
    (primeIdealFamily_product_injective _ hinj hA1)
    (primeIdealFamily_product_injective _ hinj hA2)

theorem cubeParityKey_fiber_card (s : Finset (CubeCoordinates ι)) (q : Ideal O × Ideal O)
    (hq1 : q.1≠0) (hq2 : q.2≠0) (hs : ∀ x∈s,x.Admissible)
    (hk : ∀ x∈s,cubeParityKey p x=q) :
    s.card≤(idealDivisors (q.2^2*q.1)).card^3 := by
  let D := idealDivisors (q.2^2*q.1)
  have hprod0 : q.2^2*q.1≠0 := mul_ne_zero (pow_ne_zero _ hq2) hq1
  let encode (x : s) : Fin 3 → D := fun i => ⟨cubeDivisorKey p x.val i,by
    apply (mem_idealDivisors hprod0).mpr
    have h := cubeDivisorKey_dvd p x.val i
    simpa only [cubeParityKey_product,hk x.val x.property] using h⟩
  have hi : Function.Injective encode := by
    intro x y he
    apply Subtype.ext
    apply cubeDivisorKey_injective_on_product p hp hinj (hs _ x.property) (hs _ y.property)
    · simp only [cubeParityKey_product,hk _ x.property,hk _ y.property]
    · funext i
      exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin,D] using Fintype.card_le_of_injective encode hi

end SecondPassArithmetic

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
