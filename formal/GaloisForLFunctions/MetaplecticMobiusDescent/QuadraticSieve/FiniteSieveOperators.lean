/-
Finite sieve operators adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.EisensteinLatticePoisson

/-!
# Finite sieve operators

Coprimality masks `primeCoprimeMask` become exact radial dilations by inclusion–exclusion, and
finite exclusions cost at most their divisor count in Pólya–Vinogradov. Diagonal control,
squarefree prime-subset rows, divisor bounds and the sector decomposition of the sieve energy.
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

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap

/-- The finite coprimality mask keeps precisely the rows avoiding the selected primes. -/
def primeCoprimeMask {ι : Type*} (p : ι → O) (s : Finset ι) (z : O) : ℂ :=
  ∏ i ∈ s, (1 - if p i ∣ z then (1 : ℂ) else 0)

lemma primeCoprimeMask_divisor_expansion {ι : Type*} (p : ι → O)
    (hcop : Pairwise (Function.onFun IsCoprime p)) (s : Finset ι) (z : O) :
    primeCoprimeMask p s z = ∑ E ∈ s.powerset,
      (-1 : ℂ) ^ E.card * (if (∏ i ∈ E, p i) ∣ z then 1 else 0) := by
  classical
  rw [primeCoprimeMask, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro E hE
  simp only [Finset.prod_const_one, mul_one]
  have hd : (∏ i ∈ E, p i) ∣ z ↔ ∀ i ∈ E, p i ∣ z := by
    constructor
    · intro h i hi
      exact (Finset.dvd_prod_of_mem p hi).trans h
    · exact Finset.prod_dvd_of_isRelPrime (fun i _ j _ hij => (hcop hij).isRelPrime)
  have he : (∏ i ∈ E, if p i ∣ z then (1 : ℂ) else 0) =
      if ∀ i ∈ E, p i ∣ z then 1 else 0 := by
    by_cases h : ∀ i ∈ E, p i ∣ z
    · simp only [if_pos h]
      calc
        _ = ∏ _i ∈ E, (1 : ℂ) := Finset.prod_congr rfl (fun i hi => if_pos (h i hi))
        _ = 1 := Finset.prod_const_one
    · rw [if_neg h]
      push_neg at h
      obtain ⟨i, hi, hn⟩ := h
      exact Finset.prod_eq_zero hi (if_neg hn)
  rw [he, hd]
  split_ifs <;> rfl

/-- Multiples of a nonzero Eisenstein integer are parametrized without multiplicity. -/
lemma tsum_divisibility_dilation (d : O) (hd : d ≠ 0) (f : O → ℂ) :
    (∑' z : O, if d ∣ z then f z else 0) = ∑' z : O, f (d * z) := by
  classical
  let e : O ≃ {z : O // d ∣ z} := Equiv.ofBijective
    (fun z => ⟨d * z, ⟨z, rfl⟩⟩)
    ⟨fun x y h => mul_left_cancel₀ hd (congrArg Subtype.val h), by
      rintro ⟨z, w, hw⟩
      exact ⟨w, Subtype.ext hw.symm⟩⟩
  calc
    _ = ∑' z : {z : O // d ∣ z}, if d ∣ z.val then f z.val else 0 := by
      symm
      apply tsum_subtype_eq_of_support_subset
        (f := fun z : O => if d ∣ z then f z else 0) (s := {z : O | d ∣ z})
      intro z hz
      by_contra hn
      exact hz (if_neg hn)
    _ = ∑' z : {z : O // d ∣ z}, f z.val := tsum_congr (fun z => if_pos z.property)
    _ = ∑' z : O, f (d * z) := (e.tsum_eq (fun z => f z.val)).symm

/-- Inclusion–exclusion converts a coprimality mask into exact radial dilations. -/
theorem prime_row_masked_dilations {ι κ : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)
    (q : κ → O) (hq : ∀ i, q i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime q)) (S : Finset κ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, primeCoprimeMask q S z * primeCuspRowCharacter p χ z *
      W (‖ringComplex z‖ ^ 2 / Y)) =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card * primeCuspRowCharacter p χ (∏ i ∈ E, q i) *
        ∑' z : O, primeCuspRowCharacter p χ z *
          W (‖ringComplex z‖ ^ 2 / (Y / ‖ringComplex (∏ i ∈ E, q i)‖ ^ 2)) := by
  classical
  let F : O → ℂ := fun z => primeCuspRowCharacter p χ z * W (‖ringComplex z‖ ^ 2 / Y)
  have hsW : Summable (fun z : O => ‖W (‖ringComplex z‖ ^ 2 / Y)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest W Y hY)
  have hsF : Summable (fun z => ‖F z‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_) hsW
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (primeCuspRowCharacter_norm_le_one p χ z)
  have hsE (E : Finset κ) : Summable (fun z : O =>
      (-1 : ℂ) ^ E.card * (if (∏ i ∈ E, q i) ∣ z then F z else 0)) := by
    apply Summable.mul_left
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_) hsF
    split_ifs <;> simp only [norm_zero, le_refl, norm_nonneg]
  have he (z : O) : primeCoprimeMask q S z * primeCuspRowCharacter p χ z *
      W (‖ringComplex z‖ ^ 2 / Y) = ∑ E ∈ S.powerset,
        (-1 : ℂ) ^ E.card * (if (∏ i ∈ E, q i) ∣ z then F z else 0) := by
    rw [primeCoprimeMask_divisor_expansion q hcop, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro E hE
    split_ifs <;> simp only [F, mul_one, mul_zero, zero_mul, mul_assoc]
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun E _ => hsE E)]
  apply Finset.sum_congr rfl
  intro E hE
  let d := ∏ i ∈ E, q i
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hq i)
  rw [tsum_mul_left, tsum_divisibility_dilation d hd, mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro z
  dsimp only [F]
  rw [map_mul, map_mul, norm_mul, mul_pow]
  have harg : ‖ringComplex d‖ ^ 2 * ‖ringComplex z‖ ^ 2 / Y =
      ‖ringComplex z‖ ^ 2 / (Y / ‖ringComplex d‖ ^ 2) := by
    field_simp
  rw [harg]
  ring

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap

/-- Masks preserve the same Gauss phase; selected divisors only rescale the dual radial variable. -/
theorem prime_row_masked_radial_poisson {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hχ : ∀ i, χ i ≠ 1) :
    ∃ β : ℂ, ‖β‖ = 1 ∧ ∀ {κ : Type*} (q : κ → O) (hq : ∀ i, q i ≠ 0)
      (hcop : Pairwise (Function.onFun IsCoprime q)) (S : Finset κ)
      (W : 𝓢(ℝ, ℂ)) (Y : ℝ), 0 < Y →
      (∑' z : O, primeCoprimeMask q S z * primeCuspRowCharacter p χ z *
        W (‖ringComplex z‖ ^ 2 / Y)) =
        ((Y : ℂ) * β / (‖ringComplex (∏ i, p i)‖ : ℂ)) *
          ∑ E ∈ S.powerset,
            ((-1 : ℂ) ^ E.card * primeCuspRowCharacter p χ (∏ i ∈ E, q i) /
              (‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 : ℝ)) *
              ∑' h : O, primeCuspRowCharacter p (fun i => (χ i)⁻¹) h *
                paperRadialFourier W
                  (Y * ‖ringComplex h‖ ^ 2 /
                    (‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 * ‖ringComplex (∏ i, p i)‖ ^ 2)) := by
  classical
  obtain ⟨β, hβ, hP⟩ := prime_row_radial_poisson p hp hinj χ hχ
  refine ⟨β, hβ, ?_⟩
  intro κ q hq hcop S W Y hY
  rw [prime_row_masked_dilations p χ q hq hcop S W Y hY, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  have hd : (∏ i ∈ E, q i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hq i)
  have hn : 0 < ‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hd))
  rw [hP W _ (div_pos hY hn)]
  have harg (h : O) :
      Y / ‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 * ‖ringComplex h‖ ^ 2 /
          ‖ringComplex (∏ i, p i)‖ ^ 2 =
        Y * ‖ringComplex h‖ ^ 2 /
          (‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 * ‖ringComplex (∏ i, p i)‖ ^ 2) := by ring
  simp_rw [harg]
  push_cast
  ring

/-- Finite coprimality exclusions cost at most the number of their divisors in Pólya–Vinogradov. -/
theorem prime_row_masked_polya_vinogradov :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
        (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hχ : ∀ i, χ i ≠ 1)
        (q : κ → O) (hq : ∀ i, q i ≠ 0)
        (hcop : Pairwise (Function.onFun IsCoprime q)) (S : Finset κ)
        (W : 𝓢(ℝ, ℂ)) (Y : ℝ), 0 < Y →
        ‖∑' z : O, primeCoprimeMask q S z * primeCuspRowCharacter p χ z *
          W (‖ringComplex z‖ ^ 2 / Y)‖ ≤
          (2 : ℝ) ^ S.card *
            ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * ‖ringComplex (∏ i, p i)‖) := by
  obtain ⟨s, C, hC, hPV⟩ := prime_row_polya_vinogradov
  refine ⟨s, C, hC, ?_⟩
  intro ι κ _ _ _ p hp _ hinj χ hχ q hq hcop S W Y hY
  classical
  rw [prime_row_masked_dilations p χ q hq hcop S W Y hY]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _E ∈ S.powerset,
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * ‖ringComplex (∏ i, p i)‖ := by
      apply Finset.sum_le_sum
      intro E hE
      have hd : (∏ i ∈ E, q i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hq i)
      have hn : 0 < ‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 :=
        sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hd))
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (primeCuspRowCharacter_norm_le_one p χ _)).trans
          (hPV p hp hinj χ hχ W _ (div_pos hY hn))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein

/-- A squarefree row indexed by its selected prime coordinates. -/
def primeSubsetRow {ι : Type*} (p : ι → O)
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S : Finset ι) (z : O) : ℂ :=
  ∏ i ∈ S, χ i (Ideal.Quotient.mk (Ideal.span {p i}) z)

lemma primeSubsetRow_union {ι : Type*} [DecidableEq ι] (p : ι → O)
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S T : Finset ι)
    (hST : Disjoint S T) (z : O) :
    primeSubsetRow p χ (S ∪ T) z = primeSubsetRow p χ S z * primeSubsetRow p χ T z :=
  Finset.prod_union hST

lemma primeSubsetRow_diagonal {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S : Finset ι) (z : O) :
    star (primeSubsetRow p χ S z) * primeSubsetRow p χ S z = primeCoprimeMask p S z := by
  classical
  simp only [primeSubsetRow, star_prod, ← Finset.prod_mul_distrib, primeCoprimeMask]
  apply Finset.prod_congr rfl
  intro i hi
  rw [MulChar.star_apply', ← MulChar.mul_apply, inv_mul_cancel]
  by_cases h : p i ∣ z
  · rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h),
      MulChar.map_zero, if_pos h]
    ring
  · have hn : Ideal.Quotient.mk (Ideal.span {p i}) z ≠ 0 := by
      intro he
      exact h (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he))
    rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hn), if_neg h]
    ring

lemma primeSubsetRow_pair_kernel {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S T : Finset ι) (z : O) :
    star (primeSubsetRow p χ S z) * primeSubsetRow p χ T z =
      primeCoprimeMask p (S ∩ T) z *
        (star (primeSubsetRow p χ (S \ T) z) * primeSubsetRow p χ (T \ S) z) := by
  have hS : S = (S \ T) ∪ (S ∩ T) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hT : T = (T \ S) ∪ (S ∩ T) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdS : Disjoint (S \ T) (S ∩ T) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hj).2
  have hdT : Disjoint (T \ S) (S ∩ T) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hj).1
  have hs := congrArg (fun A => primeSubsetRow p χ A z) hS
  have ht := congrArg (fun A => primeSubsetRow p χ A z) hT
  rw [primeSubsetRow_union p χ _ _ hdS] at hs
  rw [primeSubsetRow_union p χ _ _ hdT] at ht
  rw [hs, ht, star_mul, ← primeSubsetRow_diagonal p χ (S ∩ T) z]
  ring

def activePrimeRowCharacter {ι : Type*} [DecidableEq ι] (p : ι → O)
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S T : Finset ι)
    (i : ↥((S \ T) ∪ (T \ S))) : MulChar (O ⧸ Ideal.span {p i.val}) ℂ :=
  if i.val ∈ S then (χ i.val)⁻¹ else χ i.val

lemma activePrimeRowCharacter_ne_one {ι : Type*} [DecidableEq ι] (p : ι → O)
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hχ : ∀ i, χ i ≠ 1)
    (S T : Finset ι) (i : ↥((S \ T) ∪ (T \ S))) :
    activePrimeRowCharacter p χ S T i ≠ 1 := by
  dsimp only [activePrimeRowCharacter]
  split_ifs
  · intro h
    apply hχ i.val
    simpa only [inv_inv, inv_one] using congrArg Inv.inv h
  · exact hχ i.val

/-- Common primes become density masks; differing primes form one primitive character row. -/
lemma primeSubsetRow_pair_active {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S T : Finset ι) (z : O) :
    star (primeSubsetRow p χ S z) * primeSubsetRow p χ T z =
      primeCoprimeMask p (S ∩ T) z *
        primeCuspRowCharacter (fun i : ↥((S \ T) ∪ (T \ S)) => p i.val)
          (activePrimeRowCharacter p χ S T) z := by
  classical
  rw [primeSubsetRow_pair_kernel]
  congr 1
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  change _ = ∏ i : ↥((S \ T) ∪ (T \ S)),
    (if i.val ∈ S then (χ i.val)⁻¹ else χ i.val)
      (Ideal.Quotient.mk (Ideal.span {p i.val}) z)
  have he (i : ↥((S \ T) ∪ (T \ S))) :
      (if i.val ∈ S then (χ i.val)⁻¹ else χ i.val)
        (Ideal.Quotient.mk (Ideal.span {p i.val}) z) =
      if i.val ∈ S then star (χ i.val (Ideal.Quotient.mk (Ideal.span {p i.val}) z))
        else χ i.val (Ideal.Quotient.mk (Ideal.span {p i.val}) z) := by
    split_ifs <;> simp only [MulChar.star_apply']
  rw [Finset.prod_congr rfl (fun i _ => he i)]
  have hc := Finset.prod_coe_sort (s := (S \ T) ∪ (T \ S))
    (f := fun i : ι => if i ∈ S then star (χ i (Ideal.Quotient.mk (Ideal.span {p i}) z))
      else χ i (Ideal.Quotient.mk (Ideal.span {p i}) z))
  rw [hc, Finset.prod_union hd]
  simp only [primeSubsetRow, star_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [if_pos (Finset.mem_sdiff.mp hi).1]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [if_neg (Finset.mem_sdiff.mp hi).2]

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein

/-- Norm of the squarefree conductor selected by a finite support. -/
def primeSubsetNorm {ι : Type*} (p : ι → O) (S : Finset ι) : ℝ :=
  ‖ringComplex (∏ i ∈ S, p i)‖ ^ 2

lemma primeSubsetNorm_nonneg {ι : Type*} (p : ι → O) (S : Finset ι) :
    0 ≤ primeSubsetNorm p S := sq_nonneg _

lemma primeSubsetNorm_prod {ι : Type*} (p : ι → O) (S : Finset ι) :
    primeSubsetNorm p S = ∏ i ∈ S, ‖ringComplex (p i)‖ ^ 2 := by
  rw [primeSubsetNorm, map_prod, norm_prod, Finset.prod_pow]

lemma primeSubsetNorm_union {ι : Type*} [DecidableEq ι] (p : ι → O)
    (S T : Finset ι) (hST : Disjoint S T) :
    primeSubsetNorm p (S ∪ T) = primeSubsetNorm p S * primeSubsetNorm p T := by
  simp only [primeSubsetNorm_prod, Finset.prod_union hST]

lemma primeSubsetNorm_pair {ι : Type*} [DecidableEq ι] (p : ι → O) (S T : Finset ι) :
    primeSubsetNorm p ((S \ T) ∪ (T \ S)) * primeSubsetNorm p (S ∩ T) ^ 2 =
      primeSubsetNorm p S * primeSubsetNorm p T := by
  have hS : S = (S \ T) ∪ (S ∩ T) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hT : T = (T \ S) ∪ (S ∩ T) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdS : Disjoint (S \ T) (S ∩ T) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hj).2
  have hdT : Disjoint (T \ S) (S ∩ T) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hj).1
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have hs := congrArg (primeSubsetNorm p) hS
  have ht := congrArg (primeSubsetNorm p) hT
  rw [primeSubsetNorm_union p _ _ hdS] at hs
  rw [primeSubsetNorm_union p _ _ hdT] at ht
  rw [primeSubsetNorm_union p _ _ hd, hs, ht]
  ring

lemma two_pow_card_le_primeSubsetNorm {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (S : Finset ι) :
    (2 : ℝ) ^ S.card ≤ primeSubsetNorm p S := by
  have hn (i : ι) : (2 : ℝ) ≤ ‖ringComplex (p i)‖ ^ 2 := by
    rw [ringComplex_norm_sq_eq_absNorm_span]
    have h0 : Ideal.absNorm (Ideal.span {p i}) ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact NeZero.ne _
    have h1 : Ideal.absNorm (Ideal.span {p i}) ≠ 1 := by
      rw [ne_eq, Ideal.absNorm_eq_one_iff]
      exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top
    exact_mod_cast (show 2 ≤ Ideal.absNorm (Ideal.span {p i}) by omega)
  rw [primeSubsetNorm_prod]
  calc
    _ = ∏ _i ∈ S, (2 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num) (fun i _ => hn i)

/-- Common-prime divisor cost is absorbed by the two original conductor norms. -/
lemma prime_gram_divisor_conductor_bound {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (S T : Finset ι)
    (N : ℝ) (hN : 0 ≤ N) (hS : primeSubsetNorm p S ≤ N) (hT : primeSubsetNorm p T ≤ N) :
    (2 : ℝ) ^ (S ∩ T).card *
      ‖ringComplex (∏ i : ↥((S \ T) ∪ (T \ S)), p i.val)‖ ≤ N := by
  rw [Finset.prod_coe_sort]
  have hpair := primeSubsetNorm_pair p S T
  have hnorm : 0 ≤ ‖ringComplex (∏ i ∈ (S \ T) ∪ (T \ S), p i)‖ := norm_nonneg _
  have hcommon := primeSubsetNorm_nonneg p (S ∩ T)
  apply (mul_le_mul_of_nonneg_right (two_pow_card_le_primeSubsetNorm p (S ∩ T)) hnorm).trans
  apply (sq_le_sq₀ (mul_nonneg hcommon hnorm) hN).mp
  calc
    _ = primeSubsetNorm p S * primeSubsetNorm p T := by
      rw [mul_pow]
      change primeSubsetNorm p (S ∩ T) ^ 2 * primeSubsetNorm p ((S \ T) ∪ (T \ S)) = _
      rw [mul_comm, hpair]
    _ ≤ N * N := mul_le_mul hS hT (primeSubsetNorm_nonneg p T) hN
    _ = N ^ 2 := by ring

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein
open scoped SchwartzMap

/-- Distinct squarefree rows have scale-uniform off-diagonal Gram bounds. -/
theorem primeSubsetRow_gram_offdiagonal :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hχ : ∀ i, χ i ≠ 1)
        (S T : Finset ι), S ≠ T → ∀ (W : 𝓢(ℝ, ℂ)) (Y : ℝ), 0 < Y →
        ‖∑' z : O, (star (primeSubsetRow p χ S z) * primeSubsetRow p χ T z) *
          W (‖ringComplex z‖ ^ 2 / Y)‖ ≤
          (2 : ℝ) ^ (S ∩ T).card *
            ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
              ‖ringComplex (∏ i : ↥((S \ T) ∪ (T \ S)), p i.val)‖) := by
  obtain ⟨s, C, hC, hPV⟩ := prime_row_masked_polya_vinogradov
  refine ⟨s, C, hC, ?_⟩
  intro ι _ p hp _ hinj χ hχ S T hST W Y hY
  classical
  have hnonempty : ((S \ T) ∪ (T \ S)).Nonempty := by
    have hn : ¬ ∀ i, i ∈ S ↔ i ∈ T := fun h => hST (Finset.ext h)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    refine ⟨i, ?_⟩
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  letI : Nonempty ↥((S \ T) ∪ (T \ S)) := hnonempty.to_subtype
  have hcop : Pairwise (Function.onFun IsCoprime p) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp
      (Ideal.isCoprime_of_isMaximal (hinj.ne hij))
  simp_rw [primeSubsetRow_pair_active]
  exact hPV (fun i : ↥((S \ T) ∪ (T \ S)) => p i.val) (fun i => hp i.val)
    (hinj.comp Subtype.val_injective) (activePrimeRowCharacter p χ S T)
    (activePrimeRowCharacter_ne_one p χ hχ S T) p hp hcop (S ∩ T) W Y hY

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap

def diagonalControl (W : 𝓢(ℝ, ℂ)) : ℝ :=
  16 * (1 + Real.pi) ^ 2 *
    (Finset.Iic (2, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W

theorem diagonalControl_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ diagonalControl W := by
  unfold diagonalControl
  positivity

theorem radial_weight_lattice_bound (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    (∑' z : O, ‖W (‖ringComplex z‖ ^ 2 / M)‖) ≤ diagonalControl W * M := by
  have hMp : 0 < M := by linarith
  let t := M⁻¹
  have ht : 0 < t := inv_pos.mpr hMp
  have ht1 : t ≤ 1 := (inv_le_one₀ hMp).mpr hM
  let B := 4 * (Finset.Iic (2, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp (z : O) : ‖W (‖ringComplex z‖ ^ 2 / M)‖ ≤
      B * ((1 + t * ‖ringComplex z‖ ^ 2) ^ 2)⁻¹ := by
    have hq : 0 ≤ ‖ringComplex z‖ ^ 2 / M := div_nonneg (sq_nonneg _) hMp.le
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (2, 0)) (k := 2) (n := 0) le_rfl le_rfl W (‖ringComplex z‖ ^ 2 / M)
    simp only [norm_iteratedFDeriv_zero, Real.norm_of_nonneg hq] at hh
    have hsf : (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) =
        schwartzSeminormFamily ℝ ℝ ℂ := by
      funext m
      rcases m with ⟨k, n⟩
      rfl
    rw [hsf] at hh
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hh
    change (1 + ‖ringComplex z‖ ^ 2 / M) ^ 2 * ‖W (‖ringComplex z‖ ^ 2 / M)‖ ≤ B at hh
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [t, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
  have hs : Summable (fun z : O => ‖W (‖ringComplex z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hMp)
  have hb := hs.tsum_le_tsum hp ((scaled_eisenstein_cauchy_summable t ht).mul_left B)
  rw [tsum_mul_left] at hb
  have hsmall := scaled_eisenstein_cauchy_small t ht ht1
  have hmul := mul_le_mul_of_nonneg_left hb ht.le
  have hcontrol := mul_le_mul_of_nonneg_left hsmall hB
  have hfinal : t * (∑' z : O, ‖W (‖ringComplex z‖ ^ 2 / M)‖) ≤ diagonalControl W := by
    unfold diagonalControl
    dsimp [B] at hcontrol hmul
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hfinal hMp.le
  simpa only [t, ← mul_assoc, mul_inv_cancel₀ hMp.ne', one_mul, mul_comm] using hh

lemma primeSubsetRow_norm_le_one {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S : Finset ι) (z : O) :
    ‖primeSubsetRow p χ S z‖ ≤ 1 := by
  rw [primeSubsetRow, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
    (fun i _ => finiteMulChar_norm_le_one (χ i) _)

lemma primeSubsetRow_pair_summable {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S T : Finset ι)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => (star (primeSubsetRow p χ S z) * primeSubsetRow p χ T z) *
      W (‖ringComplex z‖ ^ 2 / M)) := by
  have hW : Summable (fun z : O => ‖W (‖ringComplex z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hW
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (primeSubsetRow_norm_le_one p χ S z) (primeSubsetRow_norm_le_one p χ T z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

lemma primeSubsetRow_gram_diagonal {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S : Finset ι)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, (star (primeSubsetRow p χ S z) * primeSubsetRow p χ S z) *
      W (‖ringComplex z‖ ^ 2 / M)‖ ≤ diagonalControl W * M := by
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hs := (primeSubsetRow_pair_summable p χ S S W M hMp).norm
  have hW : Summable (fun z : O => ‖W (‖ringComplex z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hMp)
  refine (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum ?_ hW).trans
    (radial_weight_lattice_bound W M hM))
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (primeSubsetRow_norm_le_one p χ S z) (primeSubsetRow_norm_le_one p χ S z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap

private theorem norm_sq_finite_sum {β : Type*} (C : Finset β) (a r : β → ℂ) :
    (↑(‖∑ n ∈ C, a n * r n‖ ^ 2) : ℂ) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) * (star (r n) * r m) := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, map_mul, starRingEnd_apply]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem primeSubsetRow_mean_summable {α β : Type*}
    (p : α → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (C : Finset β) (support : β → Finset α) (a : β → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => W (‖ringComplex z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * primeSubsetRow p χ (support n) z‖ ^ 2) : ℂ)) := by
  have hs := summable_sum (s := C) (fun n hn => summable_sum (s := C) (fun m hm =>
    (primeSubsetRow_pair_summable p χ (support n) (support m) W M hM).mul_left (star (a n) * a m)))
  apply hs.congr
  intro z
  rw [norm_sq_finite_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem primeSubsetRow_mean_expand {α β : Type*}
    (p : α → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (C : Finset β) (support : β → Finset α) (a : β → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, W (‖ringComplex z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * primeSubsetRow p χ (support n) z‖ ^ 2) : ℂ)) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) *
        ∑' z : O, (star (primeSubsetRow p χ (support n) z) * primeSubsetRow p χ (support m) z) *
          W (‖ringComplex z‖ ^ 2 / M) := by
  let f : β → β → O → ℂ := fun n m z => (star (a n) * a m) *
    ((star (primeSubsetRow p χ (support n) z) * primeSubsetRow p χ (support m) z) *
      W (‖ringComplex z‖ ^ 2 / M))
  have hf (n m : β) : Summable (f n m) :=
    (primeSubsetRow_pair_summable p χ (support n) (support m) W M hM).mul_left _
  have heq (z : O) : W (‖ringComplex z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * primeSubsetRow p χ (support n) z‖ ^ 2) : ℂ) =
        ∑ n ∈ C, ∑ m ∈ C, f n m z := by
    rw [norm_sq_finite_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [f]
    ring
  rw [tsum_congr heq, Summable.tsum_finsetSum (fun n hn => summable_sum (fun m hm => hf n m))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Summable.tsum_finsetSum (fun m hm => hf n m)]
  apply Finset.sum_congr rfl
  intro m hm
  exact tsum_mul_left

/-- Initial mean-square cancellation for actual prime characters, with uniform conductor control. -/
theorem primeSubsetRow_initial_mean_bound :
    ∃ (s : Finset (ℕ × ℕ)) (K₀ : ℝ), 0 < K₀ ∧
      ∀ {α β : Type*} [DecidableEq α] [DecidableEq β]
        (p : α → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hχ : ∀ i, χ i ≠ 1)
        (C : Finset β) (support : β → Finset α)
        (hsupp : Set.InjOn support (↑C : Set β))
        (N : ℝ), 0 ≤ N → (∀ n ∈ C, primeSubsetNorm p (support n) ≤ N) →
        ∀ (a : β → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ), 1 ≤ M →
        ‖∑' z : O, W (‖ringComplex z‖ ^ 2 / M) *
          (↑(‖∑ n ∈ C, a n * primeSubsetRow p χ (support n) z‖ ^ 2) : ℂ)‖ ≤
          (diagonalControl W * M +
            (K₀ * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * N * C.card) *
              ∑ n ∈ C, ‖a n‖ ^ 2 := by
  obtain ⟨s, K₀, hK₀, hOff⟩ := primeSubsetRow_gram_offdiagonal
  refine ⟨s, K₀, hK₀, ?_⟩
  intro α β _ _ p hp _ hinj χ hχ C support hsupp N hN hNorm a W M hM
  classical
  have hcoef : 0 ≤ K₀ * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by positivity
  have hMp : 0 < M := by linarith
  let D := diagonalControl W * M
  let B := (K₀ * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * N
  have hB : 0 ≤ B := mul_nonneg hcoef hN
  let K : β → β → ℂ := fun n m => ∑' z : O,
    (star (primeSubsetRow p χ (support n) z) * primeSubsetRow p χ (support m) z) *
      W (‖ringComplex z‖ ^ 2 / M)
  have hK (n : β) (hn : n ∈ C) (m : β) (hm : m ∈ C) :
      ‖K n m‖ ≤ (if n = m then D else 0) + B := by
    by_cases hnm : n = m
    · subst m
      simp only [ite_true]
      exact (primeSubsetRow_gram_diagonal p χ (support n) W M hM).trans (le_add_of_nonneg_right hB)
    · simp only [hnm, ite_false, zero_add]
      have hb := hOff p hp hinj χ hχ (support n) (support m)
        (fun h => hnm (hsupp hn hm h)) W M hMp
      have hc := prime_gram_divisor_conductor_bound p (support n) (support m)
        N hN (hNorm n hn) (hNorm m hm)
      apply hb.trans
      calc
        _ = (K₀ * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            ((2 : ℝ) ^ (support n ∩ support m).card *
              ‖ringComplex (∏ i : ↥((support n \ support m) ∪ (support m \ support n)), p i.val)‖) := by ring
        _ ≤ B := mul_le_mul_of_nonneg_left hc hcoef
  have heq (n : β) (hn : n ∈ C) :
      (∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
        D * ‖a n‖ ^ 2 + B * ‖a n‖ * ∑ m ∈ C, ‖a m‖ := by
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq,  hn, ite_true]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hcalc : (∑ n ∈ C, ∑ m ∈ C,
      ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
      D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := by
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [primeSubsetRow_mean_expand p χ C support a W M hMp]
  calc
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖(star (a n) * a m) * K n m‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (hK n hn m hm) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := hcalc
    _ ≤ D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * ((C.card : ℝ) * ∑ n ∈ C, ‖a n‖ ^ 2) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ hB
      simpa only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, mul_comm] using
        Finset.sum_mul_sq_le_sq_mul_sq C (fun n => ‖a n‖) (fun _ => (1 : ℝ))
    _ = _ := by dsimp [D, B]; ring

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap ContDiff

def sieveBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def sieveCutoff : 𝓢(ℝ, ℂ) := by
  have hc : HasCompactSupport (fun t : ℝ => (sieveBump t : ℂ)) :=
    sieveBump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ (fun t : ℝ => (sieveBump t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp sieveBump.contDiff
  exact hc.toSchwartzMap hs

@[simp] theorem sieveCutoff_apply (t : ℝ) : sieveCutoff t = (sieveBump t : ℂ) := rfl

theorem sieveBump_eq_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : sieveBump t = 1 := by
  apply sieveBump.one_of_mem_closedBall
  change dist t 0 ≤ 1
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht0] using ht1

/-- Finite-ball mean-square bound for distinct squarefree prime-character rows. -/
theorem primeSubsetRow_initial_finite_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ {α β : Type*} [DecidableEq α] [DecidableEq β]
        (p : α → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hχ : ∀ i, χ i ≠ 1)
        (C : Finset β) (support : β → Finset α)
        (hsupp : Set.InjOn support (↑C : Set β))
        (N : ℝ), 0 ≤ N → (∀ n ∈ C, primeSubsetNorm p (support n) ≤ N) →
        ∀ (a : β → ℂ) (M : ℝ), 1 ≤ M → ∀ R : Finset O,
        (∀ z ∈ R, ‖ringComplex z‖ ^ 2 ≤ M) →
        (∑ z ∈ R, ‖∑ n ∈ C, a n * primeSubsetRow p χ (support n) z‖ ^ 2) ≤
          K * (M + N * C.card) * ∑ n ∈ C, ‖a n‖ ^ 2 := by
  obtain ⟨s, K₀, hK₀, hb⟩ := primeSubsetRow_initial_mean_bound
  let A := diagonalControl sieveCutoff
  let B := K₀ * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) sieveCutoff
  have hA : 0 ≤ A := diagonalControl_nonneg sieveCutoff
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨A + B + 1, by positivity, ?_⟩
  intro α β _ _ p hp _ hinj χ hχ C support hsupp N hN hNorm a M hM R hR
  have hMp : 0 < M := by linarith
  let E : O → ℝ := fun z => ‖∑ n ∈ C, a n * primeSubsetRow p χ (support n) z‖ ^ 2
  let F : O → ℝ := fun z => sieveBump (‖ringComplex z‖ ^ 2 / M) * E z
  let H : O → ℂ := fun z => sieveCutoff (‖ringComplex z‖ ^ 2 / M) * (E z : ℂ)
  have hF (z : O) : 0 ≤ F z := mul_nonneg sieveBump.nonneg (sq_nonneg _)
  have hH (z : O) : H z = (F z : ℂ) := by
    simp only [H, F, sieveCutoff_apply, Complex.ofReal_mul]
  have hHs : Summable H := primeSubsetRow_mean_summable p χ C support a sieveCutoff M hMp
  have hFs : Summable F := hHs.norm.congr (fun z => by
    rw [hH, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF z)])
  have hsum : ‖∑' z : O, H z‖ = ∑' z : O, F z := by
    rw [tsum_congr hH, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg hF)]
  calc
    _ = ∑ z ∈ R, F z := by
      apply Finset.sum_congr rfl
      intro z hz
      have ht0 : 0 ≤ ‖ringComplex z‖ ^ 2 / M := div_nonneg (sq_nonneg _) hMp.le
      have ht1 : ‖ringComplex z‖ ^ 2 / M ≤ 1 := (div_le_one hMp).mpr (hR z hz)
      simp only [F, sieveBump_eq_one ht0 ht1, one_mul, E]
    _ ≤ ∑' z : O, F z := hFs.sum_le_tsum R (fun z _ => hF z)
    _ = ‖∑' z : O, H z‖ := hsum.symm
    _ ≤ (A * M + B * N * C.card) * ∑ n ∈ C, ‖a n‖ ^ 2 :=
      hb p hp hinj χ hχ C support hsupp N hN hNorm a sieveCutoff M hM
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      have hM0 : 0 ≤ M := le_trans zero_le_one hM
      have hNC : 0 ≤ N * C.card := mul_nonneg hN (Nat.cast_nonneg _)
      nlinarith only [mul_nonneg hA hNC, mul_nonneg hB hM0, hM0, hNC]


end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap

/-- Distinct prime ideals give distinct squarefree products of their chosen generators. -/
lemma primeSubset_product_injective {ι : Type*} (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i})) :
    Function.Injective (fun S : Finset ι => ∏ i ∈ S, p i) := by
  classical
  have hprime (i : ι) : Prime (p i) := (Ideal.span_singleton_prime (hp i)).mp inferInstance
  have hsub (S T : Finset ι) (h : (∏ i ∈ S, p i) = ∏ i ∈ T, p i) : S ⊆ T := by
    intro i hi
    have hd : p i ∣ ∏ j ∈ T, p j := h ▸ Finset.dvd_prod_of_mem p hi
    obtain ⟨j, hj, hij⟩ := ((hprime i).dvd_finsetProd_iff p).mp hd
    have he : i = j := hinj (Ideal.span_singleton_eq_span_singleton.mpr
      ((hprime i).associated_of_dvd (hprime j) hij))
    simpa only [he] using hj
  intro S T h
  exact Finset.Subset.antisymm (hsub S T h) (hsub T S h.symm)

/-- The same positive Schwartz majorant controls the number of lattice points in a norm ball. -/
lemma finite_norm_ball_card_bound (R : Finset O) (N : ℝ) (hN : 1 ≤ N)
    (hR : ∀ z ∈ R, ‖ringComplex z‖ ^ 2 ≤ N) :
    (R.card : ℝ) ≤ diagonalControl sieveCutoff * N := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hs : Summable (fun z : O => ‖sieveCutoff (‖ringComplex z‖ ^ 2 / N)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest sieveCutoff N hNp)
  calc
    (R.card : ℝ) = ∑ _z ∈ R, (1 : ℝ) := by simp
    _ = ∑ z ∈ R, ‖sieveCutoff (‖ringComplex z‖ ^ 2 / N)‖ := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [sieveCutoff_apply, sieveBump_eq_one (div_nonneg (sq_nonneg _) hNp.le)
        ((div_le_one hNp).mpr (hR z hz)), Complex.ofReal_one, norm_one]
    _ ≤ ∑' z : O, ‖sieveCutoff (‖ringComplex z‖ ^ 2 / N)‖ :=
      hs.sum_le_tsum R (fun _ _ => norm_nonneg _)
    _ ≤ _ := radial_weight_lattice_bound sieveCutoff N hN

lemma primeSubset_card_bound {α β : Type*} [DecidableEq β]
    (p : α → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (C : Finset β) (support : β → Finset α) (hsupp : Set.InjOn support (↑C : Set β))
    (N : ℝ) (hN : 1 ≤ N) (hNorm : ∀ n ∈ C, primeSubsetNorm p (support n) ≤ N) :
    (C.card : ℝ) ≤ diagonalControl sieveCutoff * N := by
  classical
  let g : β → O := fun n => ∏ i ∈ support n, p i
  have hg : Set.InjOn g (↑C : Set β) := fun n hn m hm h =>
    hsupp hn hm (primeSubset_product_injective p hp hinj h)
  have hc : (C.image g).card = C.card := Finset.card_image_iff.mpr hg
  rw [← hc]
  apply finite_norm_ball_card_bound _ N hN
  intro z hz
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
  exact hNorm n hn

/-- Uniform initial large-sieve bound, valid for arbitrary nontrivial prime characters. -/
theorem primeSubsetRow_initial_sieve :
    ∃ K : ℝ, 0 < K ∧
      ∀ {α β : Type*} [DecidableEq α] [DecidableEq β]
        (p : α → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hχ : ∀ i, χ i ≠ 1)
        (C : Finset β) (support : β → Finset α)
        (hsupp : Set.InjOn support (↑C : Set β))
        (N : ℝ), 1 ≤ N → (∀ n ∈ C, primeSubsetNorm p (support n) ≤ N) →
        ∀ (a : β → ℂ) (M : ℝ), 1 ≤ M → ∀ R : Finset O,
        (∀ z ∈ R, ‖ringComplex z‖ ^ 2 ≤ M) →
        (∑ z ∈ R, ‖∑ n ∈ C, a n * primeSubsetRow p χ (support n) z‖ ^ 2) ≤
          K * (M + N ^ 2) * ∑ n ∈ C, ‖a n‖ ^ 2 := by
  obtain ⟨K, hK, hb⟩ := primeSubsetRow_initial_finite_bound
  let D := diagonalControl sieveCutoff
  have hD : 0 ≤ D := diagonalControl_nonneg sieveCutoff
  refine ⟨K * (1 + D), mul_pos hK (by positivity), ?_⟩
  intro α β _ _ p hp _ hinj χ hχ C support hsupp N hN hNorm a M hM R hR
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hc := primeSubset_card_bound p hp hinj C support hsupp N hN hNorm
  apply (hb p hp hinj χ hχ C support hsupp N hN0 hNorm a M hM R hR).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  calc
    K * (M + N * C.card) ≤ K * ((1 + D) * (M + N ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hK.le
      have hnc := mul_le_mul_of_nonneg_left hc hN0
      nlinarith only [hnc, mul_nonneg hD hM0, sq_nonneg N]
    _ = _ := by ring

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap

/-- Exact second reflection of a Gram entry, retaining the signed common-prime divisor sum. -/
theorem primeSubsetRow_gram_poisson {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hχ : ∀ i, χ i ≠ 1)
    (S T : Finset ι) :
    let p' : ↥((S \ T) ∪ (T \ S)) → O := fun i => p i.val
    let χ' := activePrimeRowCharacter p χ S T
    ∃ β : ℂ, ‖β‖ = 1 ∧ ∀ (W : 𝓢(ℝ, ℂ)) (Y : ℝ), 0 < Y →
      (∑' z : O, (star (primeSubsetRow p χ S z) * primeSubsetRow p χ T z) *
        W (‖ringComplex z‖ ^ 2 / Y)) =
        ((Y : ℂ) * β / (‖ringComplex (∏ i, p' i)‖ : ℂ)) *
          ∑ E ∈ (S ∩ T).powerset,
            ((-1 : ℂ) ^ E.card * primeCuspRowCharacter p' χ' (∏ i ∈ E, p i) /
              (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ)) *
              ∑' h : O, primeCuspRowCharacter p' (fun i => (χ' i)⁻¹) h *
                paperRadialFourier W
                  (Y * ‖ringComplex h‖ ^ 2 /
                    (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 * ‖ringComplex (∏ i, p' i)‖ ^ 2)) := by
  classical
  dsimp only
  obtain ⟨β, hβ, hP⟩ := prime_row_masked_radial_poisson
    (fun i : ↥((S \ T) ∪ (T \ S)) => p i.val) (fun i => hp i.val)
    (hinj.comp Subtype.val_injective) (activePrimeRowCharacter p χ S T)
    (activePrimeRowCharacter_ne_one p χ hχ S T)
  refine ⟨β, hβ, ?_⟩
  intro W Y hY
  have hcop : Pairwise (Function.onFun IsCoprime p) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp
      (Ideal.isCoprime_of_isMaximal (hinj.ne hij))
  simp_rw [primeSubsetRow_pair_active]
  exact hP p hp hcop (S ∩ T) W Y hY

end SchwartzPlanePoisson

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

namespace FiniteSieveOperator

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def operator (A : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  A.toEuclideanLin.toContinuousLinearMap

omit [DecidableEq m] in
@[simp] theorem operator_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) (i : m) :
    operator A x i = ∑ j, A i j * x j := rfl

theorem operator_conjTranspose (A : Matrix m n ℂ) :
    operator A.conjTranspose = (operator A).adjoint := by
  unfold operator
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]

theorem operator_conjTranspose_norm (A : Matrix m n ℂ) :
    ‖operator A.conjTranspose‖ = ‖operator A‖ := by
  rw [operator_conjTranspose]
  exact ContinuousLinearMap.adjoint.norm_map _

omit [DecidableEq m] in
theorem operator_zero : operator (0 : Matrix m n ℂ) = 0 := by
  ext x i
  simp

omit [DecidableEq m] in
theorem operator_add (A B : Matrix m n ℂ) : operator (A + B) = operator A + operator B := by
  ext x i
  simp [add_mul, Finset.sum_add_distrib]

omit [DecidableEq m] in
theorem operator_smul (c : ℂ) (A : Matrix m n ℂ) : operator (c • A) = c • operator A := by
  ext x i
  simp [Finset.mul_sum, mul_assoc]

omit [DecidableEq m] in
theorem operator_sum {κ : Type*} (S : Finset κ) (A : κ → Matrix m n ℂ) :
    operator (∑ k ∈ S, A k) = ∑ k ∈ S, operator (A k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [operator_zero]
  | @insert a S ha ih => simp only [Finset.sum_insert ha, operator_add, ih]

omit [DecidableEq m] in
theorem diagonal_twist_norm_le (A : Matrix m n ℂ) (l : m → ℂ) (r : n → ℂ)
    (hl : ∀ i, ‖l i‖ ≤ 1) (hr : ∀ j, ‖r j‖ ≤ 1) :
    ‖operator (fun i j => l i * A i j * r j)‖ ≤ ‖operator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  let y : EuclideanSpace ℂ n := WithLp.toLp 2 (fun j => r j * x j)
  have hy : ‖y‖ ≤ ‖x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro j _
    change ‖r j * x j‖ ^ 2 ≤ ‖x j‖ ^ 2
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hr j)
  have heq (i : m) : operator (fun i j => l i * A i j * r j) x i = l i * operator A y i := by
    simp only [operator_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change l i * A i j * r j * x j = l i * (A i j * (r j * x j))
    ring
  have hz : ‖operator (fun i j => l i * A i j * r j) x‖ ≤ ‖operator A y‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    rw [heq, norm_mul]
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_of_le_one_left (norm_nonneg _) (hl i)
  exact hz.trans ((operator A).le_opNorm y |>.trans
    (mul_le_mul_of_nonneg_left hy (norm_nonneg _)))

omit [DecidableEq m] in
theorem separated_phase_norm_le {κ : Type*} [Fintype κ]
    (A B : Matrix m n ℂ) (c : κ → ℂ) (l : κ → m → ℂ) (r : κ → n → ℂ)
    (hl : ∀ k i, ‖l k i‖ ≤ 1) (hr : ∀ k j, ‖r k j‖ ≤ 1)
    (heq : ∀ i j, A i j = ∑ k, c k * (l k i * B i j * r k j)) :
    ‖operator A‖ ≤ (∑ k, ‖c k‖) * ‖operator B‖ := by
  let T : κ → Matrix m n ℂ := fun k i j => l k i * B i j * r k j
  have hA : A = ∑ k, c k • T k := by
    ext i j
    rw [Matrix.sum_apply]
    exact heq i j
  have hOp : operator A = ∑ k, c k • operator (T k) := by
    calc
      _ = operator (∑ k, c k • T k) := congrArg operator hA
      _ = ∑ k, operator (c k • T k) := operator_sum _ _
      _ = _ := Finset.sum_congr rfl (fun k _ => operator_smul (c k) (T k))
  rw [hOp]
  calc
    _ ≤ ∑ k, ‖c k • operator (T k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖c k‖ * ‖operator B‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (diagonal_twist_norm_le B (l k) (r k) (hl k) (hr k))
        (norm_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

omit [DecidableEq m] in
theorem energy_bound (A : Matrix m n ℂ) (u : n → ℂ) :
    (∑ i, ‖∑ j, A i j * u j‖ ^ 2) ≤ ‖operator A‖ ^ 2 * ∑ j, ‖u j‖ ^ 2 := by
  let x : EuclideanSpace ℂ n := WithLp.toLp 2 u
  have h := (operator A).le_opNorm x
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [mul_pow, EuclideanSpace.norm_sq_eq, operator_apply, x, PiLp.toLp_apply] using hs

theorem squared_norm_le_of_energy {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ a : n → ℂ, (∑ i, ‖∑ j, A i j * a j‖ ^ 2) ≤ C * ∑ j, ‖a j‖ ^ 2) :
    ‖operator A‖ ^ 2 ≤ C := by
  have hop : ‖operator A‖ ≤ Real.sqrt C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg C)
    intro a
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg a))).mp
    simpa only [mul_pow, Real.sq_sqrt hC, EuclideanSpace.norm_sq_eq, operator_apply] using h a
  simpa only [Real.sq_sqrt hC] using pow_le_pow_left₀ (norm_nonneg _) hop 2

end FiniteSieveOperator

namespace SchwartzPlanePoisson
open Eisenstein

/-- The uniform finite-ball bound is the squared operator-norm bound for every prime-row matrix. -/
theorem primeSubsetRow_initial_operator_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ {ι m n : Type*} [DecidableEq ι] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hχ : ∀ i, χ i ≠ 1)
        (rows : m → O) (hrows : Function.Injective rows)
        (cols : n → Finset ι) (hcols : Function.Injective cols)
        (M N : ℝ), 1 ≤ M → 1 ≤ N →
        (∀ i, ‖ringComplex (rows i)‖ ^ 2 ≤ M) →
        (∀ j, primeSubsetNorm p (cols j) ≤ N) →
        ‖FiniteSieveOperator.operator (fun i j => primeSubsetRow p χ (cols j) (rows i))‖ ^ 2 ≤
          K * (M + N ^ 2) := by
  obtain ⟨K, hK, hb⟩ := primeSubsetRow_initial_sieve
  refine ⟨K, hK, ?_⟩
  intro ι m n _ _ _ _ _ p hp _ hinj χ hχ rows hrows cols hcols M N hM hN hRM hCN
  classical
  apply FiniteSieveOperator.squared_norm_le_of_energy _ _ (by positivity)
  intro a
  let R := Finset.univ.image rows
  have hR (z : O) (hz : z ∈ R) : ‖ringComplex z‖ ^ 2 ≤ M := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact hRM i
  have h := hb p hp hinj χ hχ Finset.univ cols hcols.injOn N hN
    (fun j _ => hCN j) a M hM R hR
  have he : (∑ i, ‖∑ j, primeSubsetRow p χ (cols j) (rows i) * a j‖ ^ 2) =
      ∑ z ∈ R, ‖∑ j, a j * primeSubsetRow p χ (cols j) z‖ ^ 2 := by
    dsimp only [R]
    rw [Finset.sum_image]
    · simp only [mul_comm]
    · intro i _ j _ hij
      exact hrows hij
  rw [he]
  exact h

end SchwartzPlanePoisson

namespace FiniteSieveRestriction
open FiniteSieveOperator

variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

def extendByZero (S : Finset n) (f : n → p) (u : n → ℂ) (k : p) : ℂ :=
  ∑ j ∈ S, if f j = k then u j else 0

omit [Fintype n] [Fintype p] [DecidableEq n] in
theorem extendByZero_apply_image (S : Finset n) (f : n → p) (u : n → ℂ)
    (hf : Set.InjOn f S) (j : n) (hj : j ∈ S) : extendByZero S f u (f j) = u j := by
  unfold extendByZero
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    simp only [if_neg (fun h => hkj (hf hk hj h))]
  · exact fun h => (h hj).elim

omit [Fintype n] [Fintype p] [DecidableEq n] in
theorem extendByZero_zero (S : Finset n) (f : n → p) (u : n → ℂ)
    (k : p) (hk : k ∉ S.image f) : extendByZero S f u k = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  exact if_neg (fun h => hk (Finset.mem_image.mpr ⟨j, hj, h⟩))

omit [Fintype n] [DecidableEq n] in
theorem extendByZero_energy (S : Finset n) (f : n → p) (u : n → ℂ)
    (hf : Set.InjOn f S) :
    (∑ k, ‖extendByZero S f u k‖ ^ 2) = ∑ j ∈ S, ‖u j‖ ^ 2 := by
  calc
    _ = ∑ k ∈ S.image f, ‖extendByZero S f u k‖ ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      simp [extendByZero_zero S f u k hk]
    _ = ∑ j ∈ S, ‖extendByZero S f u (f j)‖ ^ 2 := by
      rw [Finset.sum_image]
      exact fun j hj k hk h => hf hj hk h
    _ = _ := Finset.sum_congr rfl (fun j hj => by rw [extendByZero_apply_image S f u hf j hj])

omit [Fintype n] [DecidableEq n] in
theorem extendByZero_matrix {m : Type*} (S : Finset n) (f : n → p)
    (u : n → ℂ) (A : Matrix m p ℂ) (i : m) :
    (∑ k, A i k * extendByZero S f u k) = ∑ j ∈ S, A i (f j) * u j := by
  simp only [extendByZero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (f j)]
  · simp
  · intro k _ hkj
    simp [Ne.symm hkj]
  · simp

theorem masked_column_restriction_norm_le {m : Type*} [Fintype m] [DecidableEq m]
    (S : Finset n) (f : n → p) (hf : Set.InjOn f S) (A : Matrix m p ℂ) :
    ‖operator (fun i j => if j ∈ S then A i (f j) else 0)‖ ≤ ‖operator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  let v : EuclideanSpace ℂ p := WithLp.toLp 2 (extendByZero S f u)
  have hv : ‖v‖ ≤ ‖u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change (∑ k, ‖extendByZero S f u k‖ ^ 2) ≤ ∑ j, ‖u j‖ ^ 2
    rw [extendByZero_energy S f u hf]
    exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖u j‖)
  have heq : operator (fun i j => if j ∈ S then A i (f j) else 0) u = operator A v := by
    ext i
    change (∑ j, (if j ∈ S then A i (f j) else 0) * u j) =
      ∑ k, A i k * extendByZero S f u k
    rw [extendByZero_matrix]
    simp only [ite_mul, zero_mul, ← Finset.sum_filter]
    simp
  rw [heq]
  exact ((operator A).le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))

theorem column_restriction_norm_le {m : Type*} [Fintype m] [DecidableEq m]
    (f : n → p) (hf : Function.Injective f) (A : Matrix m p ℂ) :
    ‖operator (fun i j => A i (f j))‖ ≤ ‖operator A‖ := by
  simpa only [Finset.mem_univ, ite_true] using
    masked_column_restriction_norm_le Finset.univ f hf.injOn A

theorem row_restriction_norm_le {m : Type*} [Fintype m] [DecidableEq m]
    (f : n → p) (hf : Function.Injective f) (A : Matrix p m ℂ) :
    ‖operator (fun i j => A (f i) j)‖ ≤ ‖operator A‖ := by
  let B : Matrix n m ℂ := fun i j => A (f i) j
  have h := column_restriction_norm_le f hf A.conjTranspose
  change ‖operator B.conjTranspose‖ ≤ ‖operator A.conjTranspose‖ at h
  rw [operator_conjTranspose_norm B, operator_conjTranspose_norm A] at h
  exact h

theorem submatrix_norm_le {m q : Type*} [Fintype m] [Fintype q]
    [DecidableEq m] [DecidableEq q]
    (r : m → q) (hr : Function.Injective r) (c : n → p) (hc : Function.Injective c)
    (A : Matrix q p ℂ) :
    ‖operator (fun i j => A (r i) (c j))‖ ≤ ‖operator A‖ :=
  (row_restriction_norm_le r hr (fun i j => A i (c j))).trans
    (column_restriction_norm_le c hc A)

end FiniteSieveRestriction

namespace IdealDivisorBound
open Eisenstein Filter UniqueFactorizationMonoid
open scoped BigOperators Classical

theorem divisor_ne_zero {I J : Ideal O} (hI : I ≠ ⊥) (hJ : J ∈ idealDivisors I) : J ≠ 0 := by
  intro hz
  have hd := (mem_idealDivisors hI).mp hJ
  rw [hz, zero_dvd_iff] at hd
  exact hI hd

theorem divisor_card_le_product (I : Ideal O) (hI : I ≠ ⊥) :
    (idealDivisors I).card ≤
      ∏ P ∈ primeSupport I, ((normalizedFactors I).count P + 1) := by
  change (idealDivisors I).card ≤
    ∏ P ∈ (normalizedFactors I).toFinset, ((normalizedFactors I).count P + 1)
  rw [← Multiset.card_Iic]
  apply Finset.card_le_card_of_injOn normalizedFactors
  · intro J hJ
    change normalizedFactors J ∈ Finset.Iic (normalizedFactors I)
    rw [Finset.mem_Iic]
    exact (dvd_iff_normalizedFactors_le_normalizedFactors
      (divisor_ne_zero hI hJ) hI).mp ((mem_idealDivisors hI).mp hJ)
  · intro J hJ K hK he
    calc
      J = (normalizedFactors J).prod := (Ideal.prod_normalizedFactors_eq_self (divisor_ne_zero hI hJ)).symm
      _ = (normalizedFactors K).prod := congrArg Multiset.prod he
      _ = K := Ideal.prod_normalizedFactors_eq_self (divisor_ne_zero hI hK)

theorem linear_le_geometric (b : ℝ) (hb : 1 < b) (n : ℕ) :
    (n : ℝ) + 1 ≤ (1 + (b - 1)⁻¹) * b ^ n := by
  have hδ : 0 < b - 1 := sub_pos.mpr hb
  have hn := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ b by linarith) n
  have hn' : (n : ℝ) ≤ b ^ n / (b - 1) := by
    apply (le_div_iff₀ hδ).mpr
    linarith
  have h1 : (1 : ℝ) ≤ b ^ n := one_le_pow₀ hb.le
  calc
    (n : ℝ) + 1 ≤ b ^ n / (b - 1) + b ^ n := add_le_add hn' h1
    _ = _ := by ring

theorem support_norm_two_le {I P : Ideal O} (hP : P ∈ primeSupport I) :
    2 ≤ Ideal.absNorm P := by
  have hp := support_prime hP
  have h0 : Ideal.absNorm P ≠ 0 := by
    intro h
    exact hp.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm P ≠ 1 := by
    intro h
    have ht := Ideal.absNorm_eq_one_iff.mp h
    apply hp.2.1
    rw [ht]
    simpa only [Ideal.one_eq_top] using (show IsUnit (1 : Ideal O) from isUnit_one)
  omega

theorem norm_factor_product (I : Ideal O) (hI : I ≠ ⊥) :
    (∏ P ∈ primeSupport I, (Ideal.absNorm P : ℝ) ^ (normalizedFactors I).count P) =
      Ideal.absNorm I := by
  have he := congrArg (fun J : Ideal O => (Ideal.absNorm J : ℝ))
    (Ideal.prod_normalizedFactors_eq_self hI)
  rw [Finset.prod_multiset_count] at he
  simpa only [primeSupport, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow] using he

theorem ideal_divisor_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal O, I ≠ ⊥ →
      ((idealDivisors I).card : ℝ) ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  let small : Finset (Ideal O) :=
    (Ideal.finite_setOf_absNorm_le (S := O) N).toFinset
  let b : ℝ := (2 : ℝ) ^ ε
  have hb : 1 < b := by
    dsimp [b]
    exact Real.one_lt_rpow (by norm_num) hε
  let c : ℝ := 1 + (b - 1)⁻¹
  have hc : 1 ≤ c := by
    dsimp [c]
    have hi : 0 ≤ (b - 1)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hb.le)
    linarith
  refine ⟨c ^ small.card, by positivity, ?_⟩
  intro I hI
  let S := primeSupport I
  let e := fun P : Ideal O => (normalizedFactors I).count P
  have hfac (P : Ideal O) (hP : P ∈ S) :
      ((e P + 1 : ℕ) : ℝ) ≤
        (if P ∈ small then c else 1) * ((Ideal.absNorm P : ℝ) ^ ε) ^ e P := by
    have hnorm : (2 : ℝ) ≤ Ideal.absNorm P := by exact_mod_cast support_norm_two_le hP
    have hbase : b ≤ (Ideal.absNorm P : ℝ) ^ ε :=
      Real.rpow_le_rpow (by norm_num) hnorm hε.le
    by_cases hp : P ∈ small
    · rw [if_pos hp]
      have hlin := linear_le_geometric b hb (e P)
      have hl : ((e P + 1 : ℕ) : ℝ) ≤ c * b ^ e P := by
        simpa only [Nat.cast_add, Nat.cast_one, c] using hlin
      apply hl.trans
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hbase _) (by positivity)
    · rw [if_neg hp, one_mul]
      have hn : N ≤ Ideal.absNorm P := by
        have : ¬ Ideal.absNorm P ≤ N := fun h => hp (by simpa [small] using h)
        omega
      have hp2 := hN _ hn
      calc
        _ ≤ (2 : ℝ) ^ e P := by
          have hh := one_add_mul_sub_le_pow (by norm_num : (-1 : ℝ) ≤ 2) (e P)
          norm_num at hh ⊢
          linarith
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) hp2 _
  have hprod := Finset.prod_le_prod
    (fun P (_ : P ∈ S) => (by positivity : (0 : ℝ) ≤ ((e P + 1 : ℕ) : ℝ))) hfac
  have hconst : (∏ P ∈ S, if P ∈ small then c else 1) ≤ c ^ small.card := by
    have he : (∏ P ∈ S, if P ∈ small then c else 1) = c ^ (S ∩ small).card := by
      simp []
    rw [he]
    exact pow_le_pow_right₀ hc (Finset.card_le_card Finset.inter_subset_right)
  have hpow : (∏ P ∈ S, ((Ideal.absNorm P : ℝ) ^ ε) ^ e P) =
      (Ideal.absNorm I : ℝ) ^ ε := by
    calc
      _ = ∏ P ∈ S, ((Ideal.absNorm P : ℝ) ^ e P) ^ ε := by
        apply Finset.prod_congr rfl
        intro P hP
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
          ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        rw [mul_comm]
      _ = (∏ P ∈ S, (Ideal.absNorm P : ℝ) ^ e P) ^ ε :=
        Real.finsetProd_rpow S _ (fun _ _ => by positivity) ε
      _ = _ := by rw [norm_factor_product I hI]
  have hcard : ((idealDivisors I).card : ℝ) ≤ ∏ P ∈ S, ((e P + 1 : ℕ) : ℝ) := by
    exact_mod_cast divisor_card_le_product I hI
  apply hcard.trans
  rw [Finset.prod_mul_distrib, hpow] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hconst (by positivity))

end IdealDivisorBound

namespace DivisorBlockCauchy
open Eisenstein
open scoped BigOperators Classical

theorem divisor_mask_energy {n : Type*} [Fintype n]
    (S : Finset (Ideal O)) (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (a : n → ℂ) :
    (∑ D ∈ S, ∑ j, ‖if D ∣ column j then a j else 0‖ ^ 2) ≤
      ∑ j, ((idealDivisors (column j)).card : ℝ) * ‖a j‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  have hsub : S.filter (fun D => D ∣ column j) ⊆ idealDivisors (column j) := by
    intro D hD
    exact (mem_idealDivisors (hcol j)).mpr (Finset.mem_filter.mp hD).2
  have hite (D : Ideal O) : ‖if D ∣ column j then a j else 0‖ ^ 2 =
      if D ∣ column j then ‖a j‖ ^ 2 else 0 := by split_ifs <;> simp
  simp_rw [hite]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (sq_nonneg _)

def divisorConstant (ε : ℝ) (hε : 0 < ε) : ℝ :=
  (IdealDivisorBound.ideal_divisor_small_power ε hε).choose

theorem divisorConstant_pos (ε : ℝ) (hε : 0 < ε) : 0 < divisorConstant ε hε :=
  (IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.1

theorem divisor_mask_energy_small_power {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (S : Finset (Ideal O))
    (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ D ∈ S, ∑ j, ‖if D ∣ column j then a j else 0‖ ^ 2) ≤
      (divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
  apply (divisor_mask_energy S column hcol a).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2
    (column j) (hcol j)).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm j) hε.le) (divisorConstant_pos ε hε).le

theorem rectangular_cauchy {α β : Type*} (S : Finset α) (T : Finset β)
    (H : α → β → ℝ) (E : α → ℝ) (F : β → ℝ) (C : ℝ)
    (_hC : 0 ≤ C) (hH : ∀ d ∈ S, ∀ e ∈ T, (H d e) ^ 2 ≤ C * E d * F e) :
    (∑ d ∈ S, ∑ e ∈ T, H d e) ^ 2 ≤
      (S.card : ℝ) * T.card * C * (∑ d ∈ S, E d) * (∑ e ∈ T, F e) := by
  classical
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (S ×ˢ T)
    (fun _ => (1 : ℝ)) (fun x => H x.1 x.2)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_product, Nat.cast_mul, Finset.sum_product] at hCS
  have hsum : (∑ d ∈ S, ∑ e ∈ T, (H d e) ^ 2) ≤
      C * (∑ d ∈ S, E d) * (∑ e ∈ T, F e) := by
    calc
      _ ≤ ∑ d ∈ S, ∑ e ∈ T, C * E d * F e := by
        apply Finset.sum_le_sum
        intro d hd
        exact Finset.sum_le_sum (fun e he => hH d hd e he)
      _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]
  apply hCS.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum
    (show (0 : ℝ) ≤ (S.card : ℝ) * T.card by positivity)

end DivisorBlockCauchy

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap FourierTransform

/-- Squaring the real argument preserves Schwartz decay. -/
def quadraticSquareCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℝ (Function.hasTemperateGrowth_norm_sq ℝ)
    ⟨1, 1, fun x => by
      simp only [pow_one, one_mul, norm_pow, Real.norm_of_nonneg (norm_nonneg x)]
      nlinarith only [sq_nonneg (‖x‖ - 1)]⟩

def quadraticSquareProfile (W : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) := quadraticSquareCLM W

@[simp] lemma quadraticSquareProfile_apply (W : 𝓢(ℝ, ℂ)) (t : ℝ) :
    quadraticSquareProfile W t = W (t ^ 2) := by
  change W (‖t‖ ^ 2) = _
  rw [Real.norm_eq_abs, sq_abs]

/-- Restricting the plane Fourier transform to its scaled imaginary axis. -/
def quadraticTransformedSquareCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (2 / Real.sqrt 3 : ℝ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
        (Units.mk0 ((ringComplex omega).im)⁻¹ (inv_ne_zero complex_omega_im_ne_zero)))).comp
      ((SchwartzMap.compCLMOfAntilipschitz ℝ (vertical_temperate 0)
        (vertical_isometry 0).antilipschitz).comp radialFourierCLM)

def quadraticTransformedSquareProfile (W : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  quadraticTransformedSquareCLM W

@[simp] lemma quadraticTransformedSquareProfile_apply (W : 𝓢(ℝ, ℂ)) (t : ℝ) :
    quadraticTransformedSquareProfile W t = paperRadialFourier W (t ^ 2) := by
  have ht : ‖(t : ℂ)‖ ^ 2 = t ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← ht, ← paperFourier_radial W (t : ℂ), paperFourier_eq_standard]
  change (2 / Real.sqrt 3 : ℝ) •
    radialFourierCLM W (complexPoint 0 (((ringComplex omega).im)⁻¹ * t)) =
      (2 / Real.sqrt 3 : ℝ) • (𝓕 (radialTest W)) (paperFrequency (t : ℂ))
  rw [radialFourierCLM_apply, paperFrequency_coordinates]
  simp only [Complex.ofReal_im, Complex.ofReal_re, zero_div, div_eq_mul_inv, zero_mul, mul_comm]

lemma quadraticSquareProfile_seminorm_control (S : Finset (ℕ × ℕ)) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(ℝ, ℂ),
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W) ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
  schwartzCLM_finite_seminorm_control quadraticSquareCLM S

lemma quadraticTransformedSquareProfile_seminorm_control (S : Finset (ℕ × ℕ)) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(ℝ, ℂ),
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W) ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
  schwartzCLM_finite_seminorm_control quadraticTransformedSquareCLM S

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein

/-- Chosen generators inject ideal norm balls into Eisenstein lattice norm balls. -/
lemma finite_ideal_card_bound (S : Finset (Ideal O)) (N : ℝ) (hN : 1 ≤ N)
    (hn : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ N) :
    (S.card : ℝ) ≤ diagonalControl sieveCutoff * N := by
  classical
  rw [← Finset.card_image_iff.mpr cubicIdealGenerator_injective.injOn]
  apply finite_norm_ball_card_bound _ N hN
  intro z hz
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hz
  rw [ringComplex_norm_sq_eq_absNorm_span, span_cubicIdealGenerator]
  exact hn I hI

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein

lemma norm_fullIdealWeight_two (I : Ideal O) :
    ‖fullIdealWeight 2 I‖ = 1 / (Ideal.absNorm I : ℝ) ^ 2 := by
  by_cases hI : I = 0
  · subst I
    simp [fullIdealWeight]
  · rw [fullIdealWeight, if_neg hI, Complex.cpow_neg, Complex.cpow_ofNat,
      norm_inv, norm_pow, Complex.norm_natCast, one_div]

/-- Absolute convergence at two uniformly bounds all finite inverse-norm-square sums. -/
lemma finite_inverse_norm_square_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Finset (Ideal O),
      (∑ I ∈ S, 1 / (Ideal.absNorm I : ℝ) ^ 2) ≤ C := by
  let C : ℝ := 1 + ∑' I : Ideal O, ‖fullIdealWeight 2 I‖
  have hc : 0 ≤ ∑' I : Ideal O, ‖fullIdealWeight 2 I‖ := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro S
  have hs := fullIdealWeight_summable_norm (2 : ℂ) (by norm_num)
  calc
    _ = ∑ I ∈ S, ‖fullIdealWeight 2 I‖ := Finset.sum_congr rfl (fun I _ => (norm_fullIdealWeight_two I).symm)
    _ ≤ ∑' I : Ideal O, ‖fullIdealWeight 2 I‖ := hs.sum_le_tsum S (fun _ _ => norm_nonneg _)
    _ ≤ C := by dsimp [C]; linarith

end SchwartzPlanePoisson

namespace FiniteSieveRestriction

/-- Restrict coefficients to one finite ray or size class. -/
def sectorCoefficient {n r : Type*} [DecidableEq r] (σ : n → r) (c : r) (a : n → ℂ) (j : n) : ℂ :=
  if σ j = c then a j else 0

lemma sectorCoefficient_energy {n r : Type*} [Fintype n] [Fintype r] [DecidableEq r]
    (σ : n → r) (a : n → ℂ) :
    (∑ c, ∑ j, ‖sectorCoefficient σ c a j‖ ^ 2) = ∑ j, ‖a j‖ ^ 2 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (σ j)]
  · simp [sectorCoefficient]
  · intro c _ hc
    simp only [sectorCoefficient, if_neg (Ne.symm hc), norm_zero, zero_pow (by decide : 2 ≠ 0)]
  · simp

lemma matrix_sector_decomposition {m n r : Type*} [Fintype n] [Fintype r] [DecidableEq r]
    (σ : n → r) (A : Matrix m n ℂ) (a : n → ℂ) (i : m) :
    (∑ j, A i j * a j) = ∑ c, ∑ j, A i j * sectorCoefficient σ c a j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum]
  simp [sectorCoefficient]

/-- Splitting columns into finitely many sectors costs only the number of sectors. -/
lemma weighted_energy_sector_bound {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    [DecidableEq r] (σ : n → r) (A : Matrix m n ℂ) (a : n → ℂ)
    (v : m → ℝ) (hv : ∀ i, 0 ≤ v i) :
    (∑ i, v i * ‖∑ j, A i j * a j‖ ^ 2) ≤
      (Fintype.card r : ℝ) * ∑ c, ∑ i, v i * ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
  have hb (i : m) : ‖∑ j, A i j * a j‖ ^ 2 ≤
      (Fintype.card r : ℝ) * ∑ c, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2 := by
    rw [matrix_sector_decomposition σ A a i]
    have hn := norm_sum_le (Finset.univ : Finset r) (fun c => ∑ j, A i j * sectorCoefficient σ c a j)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset r)
      (fun _ => (1 : ℝ)) (fun c => ‖∑ j, A i j * sectorCoefficient σ c a j‖)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ] at hcs
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs
  calc
    _ ≤ ∑ i, v i * ((Fintype.card r : ℝ) * ∑ c, ‖∑ j, A i j * sectorCoefficient σ c a j‖ ^ 2) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (hv i))
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_congr rfl (fun i _ => by ring)

end FiniteSieveRestriction

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
