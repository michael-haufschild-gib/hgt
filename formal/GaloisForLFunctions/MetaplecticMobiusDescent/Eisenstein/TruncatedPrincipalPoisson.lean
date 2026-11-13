/-
Truncated principal Poisson summation adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.DivisorBlocksAndKernelTransfer

/-!
# Truncated principal Poisson summation

Inclusion–exclusion over prime-subset generators leaves exact dilations. Poisson summation
without the zero frequency keeps both principal corrections and the signed coprimality
divisors; the truncated dual sum runs over a finite nonzero lattice disk.
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

namespace TruncatedPrincipalPoisson
open Eisenstein SchwartzPlanePoisson MeasureTheory UniqueFactorizationMonoid
open scoped SchwartzMap FourierTransform

def primeSubsetGenerator {ι : Type*} (P : ι → Ideal O) (E : Finset ι) : O :=
  ∏ i ∈ E, cubicIdealGenerator (P i)

lemma primeSubsetGenerator_span {ι : Type*} (P : ι → Ideal O) (E : Finset ι) :
    Ideal.span {primeSubsetGenerator P E} = ∏ i ∈ E, P i := by
  simp only [primeSubsetGenerator, span_finset_prime_product, span_cubicIdealGenerator]

lemma primeSubsetGenerator_norm_sq {ι : Type*} (P : ι → Ideal O) (E : Finset ι) :
    ‖ringComplex (primeSubsetGenerator P E)‖ ^ 2 = (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
  rw [ringComplex_norm_sq_eq_absNorm_span, primeSubsetGenerator_span]

lemma primeSubsetGenerator_ne_zero {ι : Type*} (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (E : Finset ι) : primeSubsetGenerator P E ≠ 0 := by
  have hp : (∏ i ∈ E, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i))
  intro hz
  have h := primeSubsetGenerator_span P E
  rw [hz, Ideal.span_singleton_zero] at h
  exact hp h.symm

def rowCoprimeMask {ι : Type*} (P : ι → Ideal O) (S : Finset ι) (z : O) : ℂ :=
  primeCoprimeMask (fun i => cubicIdealGenerator (P i)) S z

lemma prime_product_moebius {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (_hprime : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) :
    (moebius (∏ i ∈ S, P i) : ℂ) = (-1 : ℂ) ^ S.card := by
  have hi : Function.Injective (fun i : S => P i.val) := fun i j h => Subtype.ext (hinj h)
  simpa only [Fintype.card_coe, Finset.prod_coe_sort] using
    Eisenstein.primeProduct_moebius (fun i : S => P i.val) hi

lemma primeSubset_moebius_norm_sum {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P) (S : Finset ι) :
    (∑ E ∈ S.powerset, (moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) =
      ∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i)) := by
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro E hE
  rw [prime_product_moebius P hprime hinj E]
  simp only [Finset.prod_const_one, mul_one, map_prod, Nat.cast_prod,
    Finset.prod_inv_distrib, div_eq_mul_inv, one_mul]

lemma generator_pairwise_coprime {ι : Type*} (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hinj : Function.Injective P) :
    Pairwise (Function.onFun IsCoprime (fun i => cubicIdealGenerator (P i))) := by
  intro i j hij
  have h := Ideal.isCoprime_of_isMaximal (hinj.ne hij)
  rw [← span_cubicIdealGenerator (P i), ← span_cubicIdealGenerator (P j)] at h
  exact (Ideal.isCoprime_span_singleton_iff _ _).mp h

/-- Inclusion–exclusion leaves exact dilations by the selected prime generators. -/
theorem tsum_rowCoprimeMask_dilations {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (f : O → ℂ) (hf : Summable f) :
    (∑' z : O, rowCoprimeMask P S z * f z) =
      ∑ E ∈ S.powerset, (moebius (∏ i ∈ E, P i) : ℂ) *
        ∑' z : O, f (primeSubsetGenerator P E * z) := by
  have hprime (i : ι) : Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  have ht (z : O) : rowCoprimeMask P S z * f z =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        (if primeSubsetGenerator P E ∣ z then f z else 0) := by
    rw [rowCoprimeMask, primeCoprimeMask_divisor_expansion _ (generator_pairwise_coprime P hinj),
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro E hE
    by_cases h : primeSubsetGenerator P E ∣ z <;>
      simp only [primeSubsetGenerator] at h ⊢ <;> simp [h]
  have hs (E : Finset ι) : Summable (fun z : O => (-1 : ℂ) ^ E.card *
      (if primeSubsetGenerator P E ∣ z then f z else 0)) :=
    (hf.indicator {z | primeSubsetGenerator P E ∣ z}).mul_left _
  simp_rw [ht]
  rw [Summable.tsum_finsetSum (fun E _ => hs E)]
  apply Finset.sum_congr rfl
  intro E hE
  rw [tsum_mul_left, prime_product_moebius P hprime hinj E,
    tsum_divisibility_dilation _ (primeSubsetGenerator_ne_zero P E)]

lemma radial_full_poisson (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' z : O, W (‖ringComplex z‖ ^ 2 / X)) =
      (X : ℂ) * ∑' z : O, paperRadialFourier W (X * ‖ringComplex z‖ ^ 2) := by
  let p : Empty → O := Empty.elim
  letI : ∀ i, (Ideal.span {p i}).IsMaximal := fun i => nomatch i
  have hp := prime_quadratic_radial_poisson p (fun i => nomatch i)
    (by intro i; cases i) (fun i => nomatch i) W X hX
  simpa only [primeCuspRowCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    Finset.univ_eq_empty, Finset.prod_empty,
    QuadraticPhase.Eisenstein.fixedDualAverage_one, map_one, norm_one, one_pow, Complex.ofReal_one,
    one_mul, mul_one, div_one] using hp

/-- The finite nonzero lattice disk used by the truncated dual sum. -/
def rowNormDisk (N : ℕ) : Finset O :=
  ((Eisenstein.finite_norm_sublevel (Real.sqrt (N : ℝ))).subset
    (show {z : O | z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℕ) ≤ N} ⊆
      {z : O | ‖ringComplex z‖ ≤ Real.sqrt (N : ℝ)} from by
      intro z hz
      calc
        _ = Real.sqrt (‖ringComplex z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by
          rw [ringComplex_norm_sq_eq_absNorm_span]
          exact_mod_cast hz.2))).toFinset

lemma mem_rowNormDisk (N : ℕ) (z : O) :
    z ∈ rowNormDisk N ↔ 0 < Ideal.absNorm (Ideal.span {z}) ∧ Ideal.absNorm (Ideal.span {z}) ≤ N := by
  have hz : 0 < Ideal.absNorm (Ideal.span {z}) ↔ z ≠ 0 := by
    rw [Nat.pos_iff_ne_zero, ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  simp only [rowNormDisk, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hz]

end TruncatedPrincipalPoisson

open scoped BigOperators Classical SchwartzMap

namespace TruncatedPrincipalPoisson

section
local notation "O" => Eisenstein.O
open Eisenstein SchwartzPlanePoisson MeasureTheory UniqueFactorizationMonoid

def radialSource (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' z : O, if z = 0 then 0 else W (‖ringComplex z‖ ^ 2 / X)

def radialDual (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' h : O, if h = 0 then 0 else paperRadialFourier W (X * ‖ringComplex h‖ ^ 2)

theorem radialSource_summable (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    Summable (fun z : O => if z = 0 then 0 else W (‖ringComplex z‖ ^ 2 / X)) := by
  have hs : Summable (fun z : O => W (‖ringComplex z‖ ^ 2 / X)) := by
    simpa only [scaledRadialTest_apply] using
      (actual_eisenstein_summable_norm (scaledRadialTest W X hX)).of_norm
  have hi := hs.indicator {z : O | z ≠ 0}
  apply hi.congr
  intro z
  by_cases hz : z = 0 <;> simp [Set.indicator, hz]

/-- Removing zero from Poisson summation retains both principal corrections. -/
theorem radialSource_poisson (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    radialSource W X = (X : ℂ) * paperRadialFourier W 0 - W 0 +
      (X : ℂ) * radialDual W X := by
  have hp := radial_full_poisson W X hX
  have hs : Summable (fun z : O => W (‖ringComplex z‖ ^ 2 / X)) := by
    simpa only [scaledRadialTest_apply] using
      (actual_eisenstein_summable_norm (scaledRadialTest W X hX)).of_norm
  have hd := (paperRadialFourier_lattice_summable_norm W X hX).of_norm
  have hz := hs.tsum_eq_add_tsum_ite 0
  have hdz := hd.tsum_eq_add_tsum_ite 0
  simp only [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div, mul_zero] at hz hdz
  change (∑' z : O, W (‖ringComplex z‖ ^ 2 / X)) = W 0 + radialSource W X at hz
  change (∑' z : O, paperRadialFourier W (X * ‖ringComplex z‖ ^ 2)) =
    paperRadialFourier W 0 + radialDual W X at hdz
  rw [hz, hdz] at hp
  linear_combination hp

def subsetNorm {ι : Type*} (P : ι → Ideal O) (E : Finset ι) : ℝ :=
  Ideal.absNorm (∏ i ∈ E, P i)

def subsetMobius {ι : Type*} (P : ι → Ideal O) (E : Finset ι) : ℂ :=
  UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i)

def smallDivisors {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (Z : ℝ) :=
  S.powerset.filter (fun E => subsetNorm P E ≤ Z)

def largeDivisors {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (Z : ℝ) :=
  S.powerset.filter (fun E => Z < subsetNorm P E)

theorem subsetNorm_pos {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset ι) :
    0 < subsetNorm P E := by
  rw [subsetNorm, ← primeSubsetGenerator_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero (primeSubsetGenerator_ne_zero P E)))

theorem sum_small_add_large {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    (S : Finset ι) (Z : ℝ) (f : Finset ι → ℂ) :
    (∑ E ∈ smallDivisors P S Z, f E) + (∑ E ∈ largeDivisors P S Z, f E) =
      ∑ E ∈ S.powerset, f E := by
  simpa only [smallDivisors, largeDivisors, not_le] using
    Finset.sum_filter_add_sum_filter_not S.powerset (fun E => subsetNorm P E ≤ Z) f

theorem masked_radialSource_dilations {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' z : O, rowCoprimeMask P S z *
      (if z = 0 then 0 else W (‖ringComplex z‖ ^ 2 / X))) =
      ∑ E ∈ S.powerset, subsetMobius P E * radialSource W (X / subsetNorm P E) := by
  rw [tsum_rowCoprimeMask_dilations P hinj S _ (radialSource_summable W X hX)]
  apply Finset.sum_congr rfl
  intro E hE
  change subsetMobius P E * _ = _
  congr 1
  apply tsum_congr
  intro z
  rw [mul_eq_zero, or_iff_right (primeSubsetGenerator_ne_zero P E)]
  by_cases hz : z = 0
  · simp [hz]
  · rw [if_neg hz, if_neg hz, map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_sq]
    congr 1
    simp only [subsetNorm, div_div_eq_mul_div]
    ring

theorem masked_radialSource_truncated {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Z : ℝ) (hX : 0 < X) :
    (∑' z : O, rowCoprimeMask P S z *
      (if z = 0 then 0 else W (‖ringComplex z‖ ^ 2 / X))) =
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ E ∈ smallDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
      W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E) +
      (X : ℂ) * (∑ E ∈ smallDivisors P S Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  rw [masked_radialSource_dilations P hinj S W X hX,
    ← sum_small_add_large P S Z]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  rw [radialSource_poisson W _ (div_pos hX (subsetNorm_pos P E))]
  push_cast
  ring

theorem masked_radialSource_truncated_euler {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Z : ℝ) (hX : 0 < X) :
    (∑' z : O, rowCoprimeMask P S z *
      (if z = 0 then 0 else W (‖ringComplex z‖ ^ 2 / X))) =
      (X : ℂ) * paperRadialFourier W 0 *
        (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) -
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ E ∈ largeDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
      W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E) +
      (X : ℂ) * (∑ E ∈ smallDivisors P S Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  rw [masked_radialSource_truncated P hinj S W X Z hX]
  have hs := sum_small_add_large P S Z (fun E => subsetMobius P E / (subsetNorm P E : ℂ))
  have hprime : ∀ i, Prime (P i) := fun i => Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  have he := primeSubset_moebius_norm_sum P hprime hinj S
  change (∑ E ∈ S.powerset, subsetMobius P E / (subsetNorm P E : ℂ)) = _ at he
  rw [he] at hs
  linear_combination (X : ℂ) * paperRadialFourier W 0 * hs

end

local notation "O" => Eisenstein.O
open Eisenstein SchwartzPlanePoisson MeasureTheory UniqueFactorizationMonoid

def middleDivisors {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (Y Z : ℝ) :=
  (smallDivisors P S Z).filter (fun E => Y < subsetNorm P E)

def dualNear (W : ℝ → ℂ) (X lengthScale : ℝ) : ℂ :=
  ∑' h : O, if ‖ringComplex h‖ ^ 2 ≤ lengthScale then
    (if h = 0 then 0 else paperRadialFourier W (X * ‖ringComplex h‖ ^ 2)) else 0

def dualFar (W : ℝ → ℂ) (X lengthScale : ℝ) : ℂ :=
  ∑' h : O, if lengthScale < ‖ringComplex h‖ ^ 2 then
    (if h = 0 then 0 else paperRadialFourier W (X * ‖ringComplex h‖ ^ 2)) else 0

theorem radialDual_summable (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    Summable (fun h : O => if h = 0 then 0 else paperRadialFourier W (X * ‖ringComplex h‖ ^ 2)) := by
  have hs := (paperRadialFourier_lattice_summable_norm W X hX).of_norm
  have hi := hs.indicator {z : O | z ≠ 0}
  apply hi.congr
  intro z
  by_cases hz : z = 0 <;> simp [Set.indicator, hz]

theorem radialDual_near_add_far (W : 𝓢(ℝ, ℂ)) (X lengthScale : ℝ) (hX : 0 < X) :
    radialDual W X = dualNear W X lengthScale + dualFar W X lengthScale := by
  have hs := radialDual_summable W X hX
  have hn : Summable (fun h : O => if ‖ringComplex h‖ ^ 2 ≤ lengthScale then
      (if h = 0 then 0 else paperRadialFourier W (X * ‖ringComplex h‖ ^ 2)) else 0) := by
    exact hs.indicator {h : O | ‖ringComplex h‖ ^ 2 ≤ lengthScale}
  have hf : Summable (fun h : O => if lengthScale < ‖ringComplex h‖ ^ 2 then
      (if h = 0 then 0 else paperRadialFourier W (X * ‖ringComplex h‖ ^ 2)) else 0) := by
    exact hs.indicator {h : O | lengthScale < ‖ringComplex h‖ ^ 2}
  unfold radialDual dualNear dualFar
  rw [← hn.tsum_add hf]
  apply tsum_congr
  intro h
  by_cases hL : ‖ringComplex h‖ ^ 2 ≤ lengthScale <;> simp [hL, not_lt_of_ge, lt_of_not_ge]

theorem sum_small_add_middle {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    (S : Finset ι) (Y Z : ℝ) (hYZ : Y ≤ Z) (f : Finset ι → ℂ) :
    (∑ E ∈ smallDivisors P S Y, f E) + (∑ E ∈ middleDivisors P S Y Z, f E) =
      ∑ E ∈ smallDivisors P S Z, f E := by
  have hsmall : (smallDivisors P S Z).filter (fun E => subsetNorm P E ≤ Y) =
      smallDivisors P S Y := by
    ext E
    simp only [Finset.mem_filter, smallDivisors]
    constructor
    · rintro ⟨⟨hE, hEZ⟩, hEY⟩
      exact ⟨hE, hEY⟩
    · rintro ⟨hE, hEY⟩
      exact ⟨⟨hE, hEY.trans hYZ⟩, hEY⟩
  have hs := Finset.sum_filter_add_sum_filter_not (smallDivisors P S Z)
    (fun E => subsetNorm P E ≤ Y) f
  rw [hsmall] at hs
  simpa only [middleDivisors, not_le] using hs

theorem masked_radialSource_five_pieces {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ) (hX : 0 < X) (hYZ : Y ≤ Z) :
    (∑' z : O, rowCoprimeMask P S z *
      (if z = 0 then 0 else W (‖ringComplex z‖ ^ 2 / X))) =
      (X : ℂ) * paperRadialFourier W 0 *
        (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) -
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ E ∈ largeDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
      W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E) +
      (X : ℂ) * (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualNear W (X / subsetNorm P E) lengthScale) +
      (X : ℂ) * (∑ E ∈ smallDivisors P S Y,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (X : ℂ) * (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  rw [masked_radialSource_truncated_euler P hinj S W X Z hX]
  have hs := sum_small_add_middle P S Y Z hYZ (fun E =>
    (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E))
  rw [← hs]
  have hm : (∑ E ∈ middleDivisors P S Y Z,
      (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) =
      (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualNear W (X / subsetNorm P E) lengthScale) +
      (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro E hE
    rw [radialDual_near_add_far W _ lengthScale (div_pos hX (subsetNorm_pos P E)), mul_add]
  rw [hm]
  ring

end TruncatedPrincipalPoisson

open scoped BigOperators Classical SchwartzMap

namespace TruncatedPrincipalPoisson
local notation "O" => Eisenstein.O
open Eisenstein SchwartzPlanePoisson MeasureTheory UniqueFactorizationMonoid

private theorem zero_removed_tsum (f : O → ℂ) :
    (∑' h : O, if h = 0 then 0 else f h) = ∑' h : {h : O // h ≠ 0}, f h.val := by
  rw [← tsum_subtype_eq_of_support_subset (s := {h : O | h ≠ 0}) (by
    intro h hh hz
    subst h
    exact hh (by simp))]
  apply tsum_congr
  intro h
  simp only [if_neg h.property]

theorem radialSource_inverse_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        ‖radialSource W K⁻¹‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := radial_source_nonzero_lattice_decay A
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hs : Summable (fun h : O => W (K * ‖ringComplex h‖ ^ 2)) := by
    simpa only [scaledRadialTest_apply, div_inv_eq_mul, mul_comm] using
      (actual_eisenstein_summable_norm (scaledRadialTest W K⁻¹ (inv_pos.mpr hK0))).of_norm
  unfold radialSource
  rw [zero_removed_tsum]
  simp only [div_inv_eq_mul, mul_comm (‖ringComplex _‖ ^ 2) K]
  exact (norm_tsum_le_tsum_norm (hs.norm.subtype _)).trans (hb W K hK)

theorem radialDual_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        ‖radialDual W K‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hs := paperRadialFourier_lattice_summable_norm W K hK0
  let f : {h : O // h ≠ 0} → {h : O // K ≤ K * ‖ringComplex h‖ ^ 2} :=
    fun h => ⟨h.val, by nlinarith [one_le_eisenstein_norm_sq h.val h.property]⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : {h : O // K ≤ K * ‖ringComplex h‖ ^ 2} => z.val) hab)
  have hi : (∑' h : {h : O // h ≠ 0}, ‖paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖) ≤
      ∑' h : {h : O // K ≤ K * ‖ringComplex h‖ ^ 2}, ‖paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ :=
    (hs.subtype _).tsum_le_tsum_of_inj f hf (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hs.subtype _)
  have ht := hb W K K hK0 hK0.le
  simp only [min_eq_left hK, one_pow, one_mul] at ht
  unfold radialDual
  rw [zero_removed_tsum]
  exact (norm_tsum_le_tsum_norm (hs.subtype _)).trans (hi.trans ht)

theorem subsetMobius_norm_le_one {ι : Type*} (P : ι → Ideal O) (E : Finset ι) :
    ‖subsetMobius P E‖ ≤ 1 := norm_ideal_moebius_le_one _

private theorem scale_tail_bound (A : ℕ) (B x Y X : ℝ)
    (hB : 0 ≤ B) (hx : 0 < x) (hxY : x ≤ Y) (hX : 0 < X) :
    (X / x) * (B / (1 + X / x) ^ (A + 1)) ≤ B * (Y / X) ^ A := by
  have hu : 0 < X / x := div_pos hX hx
  calc
    _ ≤ (X / x) * (B / (X / x) ^ (A + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hu.le
      exact div_le_div_of_nonneg_left hB (pow_pos hu _) (pow_le_pow_left₀ hu.le (by linarith) _)
    _ = B * (x / X) ^ A := by
      simp only [div_pow, pow_succ]
      field_simp

    _ ≤ B * (Y / X) ^ A := by gcongr

private theorem norm_sum_subsets_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (T : Finset (Finset ι)) (hT : T ⊆ S.powerset) (f : Finset ι → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ E ∈ T, ‖f E‖ ≤ B) :
    ‖∑ E ∈ T, f E‖ ≤ (2 : ℝ) ^ S.card * B := by
  calc
    _ ≤ ∑ E ∈ T, ‖f E‖ := norm_sum_le _ _
    _ ≤ ∑ E ∈ T, B := Finset.sum_le_sum hf
    _ = (T.card : ℝ) * B := by simp
    _ ≤ (2 : ℝ) ^ S.card * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      have hc := Finset.card_le_card hT
      rw [Finset.card_powerset] at hc
      exact_mod_cast hc

theorem small_divisor_dual_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y : ℝ), 0 < X → 0 ≤ Y → Y ≤ X →
        ‖(X : ℂ) * ∑ E ∈ smallDivisors P S Y,
          (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * (Y / X) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := radialDual_decay (A + 1)
  refine ⟨s, C, hC, ?_⟩
  intro ι _ P _ S W X Y hX hY hYX
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  rw [Finset.mul_sum]
  have hf (E : Finset ι) (hE : E ∈ smallDivisors P S Y) :
      ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) *
        radialDual W (X / subsetNorm P E))‖ ≤ B * (Y / X) ^ A := by
    have hn := subsetNorm_pos P E
    have hEY : subsetNorm P E ≤ Y := (Finset.mem_filter.mp hE).2
    have hscale : 1 ≤ X / subsetNorm P E := (le_div_iff₀ hn).mpr (by simpa using hEY.trans hYX)
    calc
      _ = (X / subsetNorm P E) * ‖subsetMobius P E‖ * ‖radialDual W (X / subsetNorm P E)‖ := by
        simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hX, abs_of_pos hn]
        ring
      _ ≤ (X / subsetNorm P E) * 1 * (B / (1 + X / subsetNorm P E) ^ (A + 1)) := by
        gcongr
        · exact subsetMobius_norm_le_one P E
        · exact hb W _ hscale
      _ ≤ B * (Y / X) ^ A := by
        simpa only [mul_one] using scale_tail_bound A B (subsetNorm P E) Y X hB hn hEY hX
  exact (norm_sum_subsets_le S _ (Finset.filter_subset _ _) _ _ (by positivity) hf).trans_eq (by ring)

theorem large_divisor_source_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Z : ℝ), 0 < X → X ≤ Z →
        ‖∑ E ∈ largeDivisors P S Z,
          subsetMobius P E * radialSource W (X / subsetNorm P E)‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            (1 + Z / X) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := radialSource_inverse_decay A
  refine ⟨s, C, hC, ?_⟩
  intro ι _ P _ S W X Z hX hXZ
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ : 0 < Z := hX.trans_le hXZ
  have hf (E : Finset ι) (hE : E ∈ largeDivisors P S Z) :
      ‖subsetMobius P E * radialSource W (X / subsetNorm P E)‖ ≤ B / (1 + Z / X) ^ A := by
    have hn := subsetNorm_pos P E
    have hEZ : Z < subsetNorm P E := (Finset.mem_filter.mp hE).2
    have hscale : 1 ≤ subsetNorm P E / X := (le_div_iff₀ hX).mpr (by simpa using hXZ.trans hEZ.le)
    have hh := hb W (subsetNorm P E / X) hscale
    rw [inv_div] at hh
    calc
      _ = ‖subsetMobius P E‖ * ‖radialSource W (X / subsetNorm P E)‖ := norm_mul _ _
      _ ≤ 1 * (B / (1 + subsetNorm P E / X) ^ A) :=
        mul_le_mul (subsetMobius_norm_le_one P E) hh (norm_nonneg _) (by norm_num)
      _ ≤ B / (1 + Z / X) ^ A := by
        simp only [one_mul]
        apply div_le_div_of_nonneg_left hB (by positivity)
        exact pow_le_pow_left₀ (by positivity) (by gcongr) A
  exact (norm_sum_subsets_le S _ (Finset.filter_subset _ _) _ _ (by positivity) hf).trans_eq (by ring)

end TruncatedPrincipalPoisson

namespace TruncatedPrincipalPoisson

section
local notation "O" => Eisenstein.O
open Eisenstein SchwartzPlanePoisson MeasureTheory

theorem mem_rowNormDisk_floor {lengthScale : ℝ} (hL : 0 ≤ lengthScale) (z : O) :
    z ∈ rowNormDisk ⌊lengthScale⌋₊ ↔ z ≠ 0 ∧ ‖ringComplex z‖ ^ 2 ≤ lengthScale := by
  rw [mem_rowNormDisk]
  constructor
  · rintro ⟨hp, hN⟩
    refine ⟨?_, ?_⟩
    · intro hz
      subst z
      simp at hp
    · rw [ringComplex_norm_sq_eq_absNorm_span]
      exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hL)
  · rintro ⟨hz, hN⟩
    have hp := sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hz))
    rw [ringComplex_norm_sq_eq_absNorm_span] at hp hN
    exact ⟨by exact_mod_cast hp, Nat.le_floor hN⟩

theorem dualNear_eq_finite (W : ℝ → ℂ) (X lengthScale : ℝ) (hL : 0 ≤ lengthScale) :
    dualNear W X lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, paperRadialFourier W (X * ‖ringComplex h‖ ^ 2) := by
  unfold dualNear
  rw [tsum_eq_sum (s := rowNormDisk ⌊lengthScale⌋₊) (fun h hh => ?_)]
  · apply Finset.sum_congr rfl
    intro h hh
    have hd := (mem_rowNormDisk_floor hL h).mp hh
    simp only [if_pos hd.2, if_neg hd.1]
  · by_cases hz : h = 0
    · simp [hz]
    · have hn : ¬ ‖ringComplex h‖ ^ 2 ≤ lengthScale := fun hn => hh ((mem_rowNormDisk_floor hL h).mpr ⟨hz, hn⟩)
      simp only [if_neg hn]

theorem dualFar_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K lengthScale : ℝ), 0 < K → 0 ≤ lengthScale →
        ‖dualFar W K lengthScale‖ ≤ (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + K * lengthScale) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K lengthScale hK hL
  have he : dualFar W K lengthScale =
      ∑' h : {h : O // lengthScale < ‖ringComplex h‖ ^ 2}, paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2) := by
    calc
      _ = ∑' h : {h : O // lengthScale < ‖ringComplex h‖ ^ 2},
          if h.val = 0 then 0 else paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2) :=
        (tsum_subtype {h : O | lengthScale < ‖ringComplex h‖ ^ 2}
          (fun h => if h = 0 then 0 else paperRadialFourier W (K * ‖ringComplex h‖ ^ 2))).symm
      _ = _ := by
        apply tsum_congr
        intro h
        apply if_neg
        intro hz
        have hp := h.property
        simp only [hz, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hp
        exact (not_lt_of_ge hL) hp
  rw [he]
  have hs := paperRadialFourier_lattice_summable_norm W K hK
  let f : {h : O // lengthScale < ‖ringComplex h‖ ^ 2} →
      {h : O // K * lengthScale ≤ K * ‖ringComplex h‖ ^ 2} :=
    fun h => ⟨h.val, mul_le_mul_of_nonneg_left h.property.le hK.le⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : {h : O // K * lengthScale ≤ K * ‖ringComplex h‖ ^ 2} => z.val) hab)
  have hi : (∑' h : {h : O // lengthScale < ‖ringComplex h‖ ^ 2},
      ‖paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖) ≤
      ∑' h : {h : O // K * lengthScale ≤ K * ‖ringComplex h‖ ^ 2},
        ‖paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖ :=
    (hs.subtype _).tsum_le_tsum_of_inj f hf (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hs.subtype _)
  exact (norm_tsum_le_tsum_norm (hs.subtype _)).trans (hi.trans (hb W K (K * lengthScale) hK (mul_nonneg hK.le hL)))

end

section
local notation "O" => Eisenstein.O
open Eisenstein SchwartzPlanePoisson MeasureTheory

theorem middle_divisor_frequency_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ),
        0 < X → 0 < Y → Y ≤ Z → 0 ≤ lengthScale →
        ‖(X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
          (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale‖ ≤
          (2 : ℝ) ^ S.card * (X / Y) * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := dualFar_decay A
  refine ⟨s, C, hC, ?_⟩
  intro ι _ P _ S W X Y Z lengthScale hX hY hYZ hL
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let Q := (min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ : 0 < Z := hY.trans_le hYZ
  have hQ : 0 < Q := by dsimp [Q]; positivity
  rw [Finset.mul_sum]
  have hf (E : Finset ι) (hE : E ∈ middleDivisors P S Y Z) :
      ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) *
        dualFar W (X / subsetNorm P E) lengthScale)‖ ≤ (X / Y) * (B / Q) := by
    have hn := subsetNorm_pos P E
    have hEY : Y < subsetNorm P E := (Finset.mem_filter.mp hE).2
    have hEZ : subsetNorm P E ≤ Z := (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).2
    have hk : X / Z ≤ X / subsetNorm P E := div_le_div_of_nonneg_left hX.le hn hEZ
    have hden : Q ≤ (min 1 (X / subsetNorm P E)) ^ 2 *
        (1 + (X / subsetNorm P E) * lengthScale) ^ A := by
      dsimp [Q]
      have hmul : X * lengthScale / Z ≤ (X / subsetNorm P E) * lengthScale := by
        calc
          _ = (X / Z) * lengthScale := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hk hL
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity) (min_le_min_left _ hk) 2
      · exact pow_le_pow_left₀ (by positivity) (by linarith) A
      · positivity
      · positivity
    have hh : ‖dualFar W (X / subsetNorm P E) lengthScale‖ ≤ B / Q :=
      (hb W _ lengthScale (div_pos hX hn) hL).trans (div_le_div_of_nonneg_left hB hQ hden)
    calc
      _ = (X / subsetNorm P E) * ‖subsetMobius P E‖ * ‖dualFar W (X / subsetNorm P E) lengthScale‖ := by
        simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hX, abs_of_pos hn]
        ring
      _ ≤ (X / Y) * 1 * (B / Q) := by
        apply mul_le_mul
        · exact mul_le_mul (div_le_div_of_nonneg_left hX.le hY hEY.le)
            (subsetMobius_norm_le_one P E) (norm_nonneg _) (by positivity)
        · exact hh
        · exact norm_nonneg _
        · positivity
      _ = _ := by ring
  calc
    _ ≤ ∑ E ∈ middleDivisors P S Y Z,
        ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale)‖ := norm_sum_le _ _
    _ ≤ ∑ E ∈ middleDivisors P S Y Z, (X / Y) * (B / Q) := Finset.sum_le_sum hf
    _ = ((middleDivisors P S Y Z).card : ℝ) * ((X / Y) * (B / Q)) := by simp
    _ ≤ (2 : ℝ) ^ S.card * ((X / Y) * (B / Q)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hsub : middleDivisors P S Y Z ⊆ S.powerset :=
        (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_powerset] at hc
      exact_mod_cast hc
    _ = _ := by dsimp [B, Q]; ring

end

local notation "O" => Eisenstein.O
open Eisenstein SchwartzPlanePoisson MeasureTheory

def principalTruncation {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (W : ℝ → ℂ) (X Z : ℝ) : ℂ :=
  (X : ℂ) * paperRadialFourier W 0 * (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) -
  (X : ℂ) * paperRadialFourier W 0 *
    (∑ E ∈ largeDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
  W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E)

def middleTruncation {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) : ℂ :=
  (X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
    (subsetMobius P E / (subsetNorm P E : ℂ)) *
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, paperRadialFourier W ((X / subsetNorm P E) * ‖ringComplex h‖ ^ 2)

def truncationError {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) : ℂ :=
  (∑' z : O, rowCoprimeMask P S z * (if z = 0 then 0 else W (‖ringComplex z‖ ^ 2 / X))) -
    (principalTruncation P S W X Z + middleTruncation P S W X Y Z lengthScale)

theorem truncationError_eq {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ) (hX : 0 < X) (hYZ : Y ≤ Z) (hL : 0 ≤ lengthScale) :
    truncationError P S W X Y Z lengthScale =
      (X : ℂ) * (∑ E ∈ smallDivisors P S Y,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (X : ℂ) * (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  unfold truncationError principalTruncation middleTruncation
  rw [masked_radialSource_five_pieces P hinj S W X Y Z lengthScale hX hYZ]
  simp_rw [dualNear_eq_finite W _ lengthScale hL]
  ring

theorem truncationError_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ),
        0 < X → 0 < Y → Y ≤ X → X ≤ Z → 0 ≤ lengthScale →
        ‖truncationError P S W X Y Z lengthScale‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            ((Y / X) ^ A + (1 / (1 + Z / X) ^ A) +
              (X / Y) / ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A)) := by
  obtain ⟨s₀, C₀, hC₀, h₀⟩ := small_divisor_dual_tail A
  obtain ⟨s₁, C₁, hC₁, h₁⟩ := large_divisor_source_tail A
  obtain ⟨s₂, C₂, hC₂, h₂⟩ := middle_divisor_frequency_tail A
  refine ⟨(s₀ ∪ s₁) ∪ s₂, C₀ + C₁ + C₂, by positivity, ?_⟩
  intro ι _ P _ hinj S W X Y Z lengthScale hX hY hYX hXZ hL
  let Q := ((s₀ ∪ s₁) ∪ s₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let C := C₀ + C₁ + C₂
  have hQ : 0 ≤ Q := apply_nonneg _ _
  have hc₀ : C₀ ≤ C := by dsimp [C]; linarith
  have hc₁ : C₁ ≤ C := by dsimp [C]; linarith
  have hc₂ : C₂ ≤ C := by dsimp [C]; linarith
  have hq₀ : s₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left.trans Finset.subset_union_left)) W
  have hq₁ : s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right.trans Finset.subset_union_left)) W
  have hq₂ : s₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W
  have hz : 0 < Z := hX.trans_le hXZ
  let lo : ℂ := (X : ℂ) * ∑ E ∈ smallDivisors P S Y,
    (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)
  let mid : ℂ := (X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
    (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale
  let hi : ℂ := ∑ E ∈ largeDivisors P S Z,
    subsetMobius P E * radialSource W (X / subsetNorm P E)
  have hlo : ‖lo‖ ≤ (2 : ℝ) ^ S.card * (C * Q) * (Y / X) ^ A := by
    apply (h₀ P S W X Y hX hY.le hYX).trans
    gcongr
  have hhi : ‖hi‖ ≤ (2 : ℝ) ^ S.card * (C * Q) / (1 + Z / X) ^ A := by
    apply (h₁ P S W X Z hX hXZ).trans
    gcongr
  have hmid : ‖mid‖ ≤ (2 : ℝ) ^ S.card * (X / Y) * (C * Q) /
      ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) := by
    apply (h₂ P S W X Y Z lengthScale hX hY (hYX.trans hXZ) hL).trans
    gcongr
  rw [truncationError_eq P hinj S W X Y Z lengthScale hX (hYX.trans hXZ) hL]
  change ‖lo + mid + hi‖ ≤ _
  calc
    _ ≤ ‖lo‖ + ‖mid‖ + ‖hi‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le lo mid) le_rfl)
    _ ≤ (2 : ℝ) ^ S.card * (C * Q) * (Y / X) ^ A +
        (2 : ℝ) ^ S.card * (X / Y) * (C * Q) / ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) +
        (2 : ℝ) ^ S.card * (C * Q) / (1 + Z / X) ^ A := add_le_add (add_le_add hlo hmid) hhi
    _ = _ := by change _ = (2 : ℝ) ^ S.card * (C * Q) * _; ring

end TruncatedPrincipalPoisson

namespace TruncatedPrincipalPoisson
open Eisenstein SchwartzPlanePoisson MeasureTheory UniqueFactorizationMonoid
open scoped SchwartzMap

/-- Principal Poisson summation keeps the signed coprimality divisors. -/
theorem masked_principal_radial_poisson {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (V : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask P S z * V (‖ringComplex z‖ ^ 2 / M)) =
      (M : ℂ) * ∑ E ∈ S.powerset,
        ((moebius (∏ i ∈ E, P i) : ℂ) / (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
        ∑' h : O, paperRadialFourier V
          (M * ‖ringComplex h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) := by
  have hs : Summable (fun z : O => V (‖ringComplex z‖ ^ 2 / M)) := by
    simpa only [scaledRadialTest_apply] using
      (actual_eisenstein_summable_norm (scaledRadialTest V M hM)).of_norm
  rw [tsum_rowCoprimeMask_dilations P hinj S _ hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  have hn := subsetNorm_pos P E
  have ht : (∑' z : O, V (‖ringComplex (primeSubsetGenerator P E * z)‖ ^ 2 / M)) =
      ((M / subsetNorm P E : ℝ) : ℂ) *
        ∑' h : O, paperRadialFourier V (M * ‖ringComplex h‖ ^ 2 / subsetNorm P E) := by
    have harg (z : O) : subsetNorm P E * ‖ringComplex z‖ ^ 2 / M =
        ‖ringComplex z‖ ^ 2 / (M / subsetNorm P E) := by
      simp only [div_div_eq_mul_div]
      ring
    simp only [map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_sq]
    change (∑' z : O, V (subsetNorm P E * ‖ringComplex z‖ ^ 2 / M)) = _
    simp_rw [harg]
    rw [radial_full_poisson V _ (div_pos hM hn)]
    simp only [div_mul_eq_mul_div]
  rw [ht]
  simp only [subsetNorm, Complex.ofReal_div, Complex.ofReal_natCast]
  ring

def maskedPrincipalRemainder {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (V : ℝ → ℂ) (M : ℝ) : ℂ :=
  (M : ℂ) * ∑ E ∈ S.powerset,
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
    ∑' h : O, if h = 0 then 0 else paperRadialFourier V
      (M * ‖ringComplex h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ))

theorem masked_principal_radial_poisson_zero_split {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (V : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask P S z * V (‖ringComplex z‖ ^ 2 / M)) =
      (M : ℂ) * paperRadialFourier V 0 *
        (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) +
        maskedPrincipalRemainder P S V M := by
  have hp (E : Finset ι) : 0 < (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero (primeSubsetGenerator_ne_zero P E)))
  have hs (E : Finset ι) :
      (∑' h : O, paperRadialFourier V
        (M * ‖ringComplex h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ))) =
      paperRadialFourier V 0 +
        ∑' h : O, if h = 0 then 0 else paperRadialFourier V
          (M * ‖ringComplex h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) := by
    have hsum := (paperRadialFourier_lattice_summable_norm V
      (M / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) (div_pos hM (hp E))).of_norm
    have heq (h : O) : M / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) * ‖ringComplex h‖ ^ 2 =
        M * ‖ringComplex h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by ring
    simp_rw [heq] at hsum
    simpa only [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div]
      using hsum.tsum_eq_add_tsum_ite 0
  have hprime : ∀ i, Prime (P i) := fun i => Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  rw [masked_principal_radial_poisson P hinj S V M hM]
  simp_rw [hs, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, mul_add]
  rw [primeSubset_moebius_norm_sum P hprime hinj S]
  unfold maskedPrincipalRemainder
  ring

theorem quadratic_square_poisson_main_cancel {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask P S z *
      paperRadialFourier W ((‖ringComplex z‖ ^ 2 / M) ^ 2)) -
    (∑' z : O, rowCoprimeMask P S z * W ((‖ringComplex z‖ ^ 2 / M) ^ 2)) =
      maskedPrincipalRemainder P S (quadraticTransformedSquareProfile W) M -
      maskedPrincipalRemainder P S (quadraticSquareProfile W) M := by
  have h1 := masked_principal_radial_poisson_zero_split P hinj S
    (quadraticTransformedSquareProfile W) M hM
  have h2 := masked_principal_radial_poisson_zero_split P hinj S (quadraticSquareProfile W) M hM
  simp only [quadraticTransformedSquareProfile_apply] at h1
  simp only [quadraticSquareProfile_apply] at h2
  rw [h1, h2, quadraticSquareProfile_principal_equal]
  ring


end TruncatedPrincipalPoisson

namespace TruncatedPrincipalPoisson
open Eisenstein SchwartzPlanePoisson MeasureTheory UniqueFactorizationMonoid
open scoped SchwartzMap

/-- Principal truncation for the actual quadratic pair, including the finite frequency middle. -/
theorem quadraticDualPrincipalIdeal_truncated (I J : QuadraticIdeal)
    (hnt : I.val ≠ 1 ∨ J.val ≠ 1) (W : 𝓢(ℝ, ℂ))
    (X Y Z L : ℝ) (hX : 0 < X) :
    (Nat.card Oˣ : ℂ) * quadraticDualPrincipalIdeal I J W X =
      principalTruncation (fun P : primeSupport (I.val * J.val) => P.val) Finset.univ W X Z +
      middleTruncation (fun P : primeSupport (I.val * J.val) => P.val) Finset.univ W X Y Z L +
      truncationError (fun P : primeSupport (I.val * J.val) => P.val) Finset.univ W X Y Z L := by
  rw [← quadraticDualPrincipalIdeal_lattice I J hnt W X hX]
  unfold truncationError
  have he (z : O) : rowCoprimeMask (fun P : primeSupport (I.val * J.val) => P.val) Finset.univ z =
      primeCoprimeMask cubicIdealGenerator (primeSupport (I.val * J.val)) z := by
    simp only [rowCoprimeMask, primeCoprimeMask]
    exact Finset.prod_coe_sort (s := primeSupport (I.val * J.val))
      (f := fun P : Ideal O => (1 : ℂ) - if cubicIdealGenerator P ∣ z then 1 else 0)
  simp_rw [he]
  have hz : ∀ z : O,
      primeCoprimeMask cubicIdealGenerator (primeSupport (I.val * J.val)) z *
        (if z = 0 then 0 else W (‖ringComplex z‖ ^ 2 / X)) =
      primeCoprimeMask cubicIdealGenerator (primeSupport (I.val * J.val)) z *
        W (‖ringComplex z‖ ^ 2 / X) := by
    intro z
    by_cases h : z = 0
    · subst z
      rw [quadraticPair_prime_mask, ← canonicalQuadraticRow_square, ← canonicalQuadraticRow_square,
        zero_pow (by decide : 2 ≠ 0), canonicalQuadraticPair_zero I J hnt]
      simp only [zero_mul]
    · rw [if_neg h]
  simp_rw [hz]
  ring

/-- The actual reflected pair splits into finite principal and middle terms plus its squarefree tail. -/
theorem canonicalQuadraticPair_dual_finite_truncated (I J : QuadraticIdeal)
    (hray : quadraticColumnRay I = quadraticColumnRay J) (hnt : I.val ≠ 1 ∨ J.val ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (t K : ℝ) (ht : 0 < t) (Y Z L : Ideal O → ℝ) :
    (∑' z : O, (canonicalQuadraticRow I z * canonicalQuadraticRow J z) *
      paperRadialFourier W (t * ‖ringComplex z‖ ^ 2)) =
      (∑ B : squarefreeIdealBall K,
        let X := Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))
        let P := fun P : primeSupport (I.val * J.val) => P.val
        let V := quadraticTransformedSquareProfile W
        canonicalQuadraticPairIdeal I J B.val *
          (principalTruncation P Finset.univ V X (Z B.val) +
           middleTruncation P Finset.univ V X (Y B.val) (Z B.val) (L B.val) +
           truncationError P Finset.univ V X (Y B.val) (Z B.val) (L B.val))) +
      (Nat.card Oˣ : ℂ) * quadraticDualSquarefreeTail I J W t K := by
  rw [canonicalQuadraticPair_fourier_ideal_reindex I J hray hnt W t ht,
    quadraticDual_low_add_tail I J W t K ht, mul_add,
    quadraticDualSquarefreeLow_principal_finite I J hray W t K ht, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro B _
  have hB : 0 < (Ideal.absNorm B.val : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (mem_squarefreeIdealBall.mp B.property).1.ne_zero)
  have hX : 0 < Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ))) :=
    Real.sqrt_pos.mpr (one_div_pos.mpr (mul_pos ht hB))
  dsimp only
  calc
    _ = canonicalQuadraticPairIdeal I J B.val *
        ((Nat.card Oˣ : ℂ) * quadraticDualPrincipalIdeal I J (quadraticTransformedSquareProfile W)
          (Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ))))) := by ring
    _ = _ := by rw [quadraticDualPrincipalIdeal_truncated I J hnt _ _ _ _ _ hX]

end TruncatedPrincipalPoisson

namespace TruncatedPrincipalPoisson
open Eisenstein SchwartzPlanePoisson MeasureTheory UniqueFactorizationMonoid
open scoped SchwartzMap

theorem sum_subtype_powerset_products (S : Finset (Ideal O)) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset S).powerset, f (∏ P ∈ E, P.val)) =
      ∑ E ∈ S.powerset, f (∏ P ∈ E, P) := by
  classical
  have hS : (Finset.univ : Finset S).image Subtype.val = S := by
    ext P
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists, exists_prop,
      exists_eq_right]
  conv_rhs => rw [← hS, Finset.powerset_image]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro E hE
    congr 1
    rw [Finset.prod_image]
    exact fun _ _ _ _ h => Subtype.val_injective h
  · exact fun _ _ _ _ h => Finset.image_injective Subtype.val_injective h

theorem primeSupport_subset_sum_eq_divisors (G : Ideal O) (hG : Squarefree G) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset (primeSupport G)).powerset,
      f (∏ P ∈ E, P.val)) = ∑ d ∈ idealDivisors G, f d := by
  rw [sum_subtype_powerset_products]
  exact (squarefree_ideal_divisor_sum G hG f).symm

theorem middleTruncation_eq_ideal_divisors (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) :
    middleTruncation (fun P : primeSupport G => P.val) Finset.univ W X Y Z lengthScale =
      (X : ℂ) * ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) *
            ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊,
              paperRadialFourier W ((X / (Ideal.absNorm d : ℝ)) * ‖ringComplex h‖ ^ 2)
        else 0 := by
  classical
  let f : Ideal O → ℂ := fun d =>
    if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
      (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) *
        ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊,
          paperRadialFourier W ((X / (Ideal.absNorm d : ℝ)) * ‖ringComplex h‖ ^ 2)
    else 0
  change middleTruncation _ _ W X Y Z lengthScale = (X : ℂ) * ∑ d ∈ idealDivisors G, f d
  rw [← primeSupport_subset_sum_eq_divisors G hG f]
  unfold middleTruncation middleDivisors smallDivisors
  simp only [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only [f, subsetNorm, subsetMobius]
  push_cast
  by_cases hY : Y < (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) <;>
    by_cases hZ : (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) ≤ Z <;> simp only [hY, hZ, and_self,
      false_and, and_false, ite_true, ite_false]

theorem middleTruncation_eq_ideal_frequencies (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) :
    middleTruncation (fun P : primeSupport G => P.val) Finset.univ W X Y Z lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) *
            (((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
              paperRadialFourier W (X * ‖ringComplex h‖ ^ 2 / (Ideal.absNorm d : ℝ)))
        else 0 := by
  classical
  rw [middleTruncation_eq_ideal_divisors G hG, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hc : Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z
  · simp only [hc, and_self, ite_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    have harg : (X / (Ideal.absNorm d : ℝ)) * ‖ringComplex h‖ ^ 2 =
        X * ‖ringComplex h‖ ^ 2 / (Ideal.absNorm d : ℝ) := by ring
    rw [harg]
    push_cast
    ring
  · simp only [hc, ite_false, mul_zero, Finset.sum_const_zero]

theorem principalTruncation_eq_ideal_divisors (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (X Z : ℝ) :
    principalTruncation (fun P : primeSupport G => P.val) Finset.univ W X Z =
      (X : ℂ) * paperRadialFourier W 0 *
        (∏ P : primeSupport G, (1 - (1 : ℂ) / Ideal.absNorm P.val)) -
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d : ℝ) then
          (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) else 0) -
      W 0 * (∑ d ∈ idealDivisors G, if (Ideal.absNorm d : ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d : ℂ) else 0) := by
  classical
  rw [← primeSupport_subset_sum_eq_divisors G hG
    (fun d => if Z < (Ideal.absNorm d : ℝ) then
      (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) else 0),
    ← primeSupport_subset_sum_eq_divisors G hG
    (fun d => if (Ideal.absNorm d : ℝ) ≤ Z then (UniqueFactorizationMonoid.moebius d : ℂ) else 0)]
  unfold principalTruncation largeDivisors smallDivisors
  simp only [Finset.sum_filter, subsetNorm, subsetMobius, Complex.ofReal_natCast]


def primeSupportDensity (G : Ideal O) : ℂ :=
  ∏ P : primeSupport G, (1-(1:ℂ)/(Ideal.absNorm P.val:ℂ))

theorem principalTruncation_scaled (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (c X Z : ℝ) :
    (c:ℂ)*principalTruncation (fun P : primeSupport G => P.val) Finset.univ W X Z =
      ((c*X:ℝ):ℂ)*paperRadialFourier W 0*primeSupportDensity G -
      paperRadialFourier W 0 * (∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(((c*X)/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) -
      W 0 * (∑ d ∈ idealDivisors G, if (Ideal.absNorm d:ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(c:ℂ) else 0) := by
  classical
  have hl : (∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(((c*X)/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) =
      ((c*X:ℝ):ℂ)*(∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)/(Ideal.absNorm d:ℂ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : Z < (Ideal.absNorm d:ℝ)
    · simp only [hd,ite_true,Complex.ofReal_div,Complex.ofReal_natCast]
      ring
    · simp only [hd,ite_false,mul_zero]
  have hs : (∑ d ∈ idealDivisors G, if (Ideal.absNorm d:ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(c:ℂ) else 0) =
      (c:ℂ)*(∑ d ∈ idealDivisors G, if (Ideal.absNorm d:ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d:ℂ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : (Ideal.absNorm d:ℝ) ≤ Z <;> simp only [hd,ite_true,ite_false,mul_zero] ; ring
  rw [principalTruncation_eq_ideal_divisors G hG,hl,hs]
  unfold primeSupportDensity
  push_cast
  ring

end TruncatedPrincipalPoisson

namespace TruncatedPrincipalPoisson
open Eisenstein SchwartzPlanePoisson MeasureTheory
open scoped SchwartzMap

/-- Removing the zero lattice point gives principal truncation for every conductor pair. -/
theorem quadraticDualPrincipalIdeal_truncated_all_conductors (I J : QuadraticIdeal)
    (W : 𝓢(ℝ, ℂ)) (X Y Z L : ℝ) (hX : 0 < X) :
    (Nat.card Oˣ : ℂ) * quadraticDualPrincipalIdeal I J W X =
      principalTruncation (fun P : primeSupport (I.val * J.val) => P.val) Finset.univ W X Z +
      middleTruncation (fun P : primeSupport (I.val * J.val) => P.val) Finset.univ W X Y Z L +
      truncationError (fun P : primeSupport (I.val * J.val) => P.val) Finset.univ W X Y Z L := by
  let P := fun P : primeSupport (I.val * J.val) => P.val
  let f : O → ℂ := fun z => rowCoprimeMask P Finset.univ z *
    (if z = 0 then 0 else W (‖ringComplex z‖ ^ 2 / X))
  have hm (z : O) : rowCoprimeMask P Finset.univ z =
      primeCoprimeMask cubicIdealGenerator (primeSupport (I.val * J.val)) z := by
    simp only [rowCoprimeMask, primeCoprimeMask, P]
    exact Finset.prod_coe_sort (s := primeSupport (I.val * J.val))
      (f := fun Q : Ideal O => (1 : ℂ) - if cubicIdealGenerator Q ∣ z then 1 else 0)
  have hf : Summable f := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_)
      (actual_eisenstein_summable_norm (scaledRadialTest W X hX))
    rw [scaledRadialTest_apply]
    dsimp only [f]
    by_cases hz : z = 0
    · simp only [hz, ite_true, mul_zero, norm_zero]
      exact norm_nonneg _
    · rw [if_neg hz, norm_mul, hm]
      exact mul_le_of_le_one_left (norm_nonneg _) (primeCoprimeMask_norm_le_one _ _ _)
  have h0 : f 0 = 0 := by simp only [f, ite_true, mul_zero]
  have hu (u : Oˣ) (z : O) : f ((u : O) * z) = f z := by
    dsimp only [f]
    rw [hm, hm, primeCoprimeMask_unit_mul, map_mul, norm_mul, norm_ringComplex_unit, one_mul]
    simp only [mul_eq_zero, u.ne_zero, false_or]
  have he := tsum_unit_invariant_ideals f hf h0 hu
  have hd : (∑' A : NonzeroIdeal, f (cubicIdealGenerator A.val)) = quadraticDualPrincipalIdeal I J W X := by
    unfold quadraticDualPrincipalIdeal
    apply tsum_congr
    intro A
    simp only [f, hm, quadraticPair_prime_mask,
      if_neg (cubicIdealGenerator_ne_zero A.val A.property),
      ringComplex_norm_sq_eq_absNorm_span, span_cubicIdealGenerator]
  rw [hd] at he
  have hs : principalTruncation P Finset.univ W X Z +
      middleTruncation P Finset.univ W X Y Z L +
      truncationError P Finset.univ W X Y Z L = ∑' z : O, f z := by
    unfold truncationError
    dsimp only [f]
    ring
  exact he.symm.trans hs.symm

end TruncatedPrincipalPoisson

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
