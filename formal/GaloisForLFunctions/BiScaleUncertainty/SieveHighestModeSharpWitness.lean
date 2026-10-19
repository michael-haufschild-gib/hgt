import GaloisForLFunctions.BiScaleUncertainty.PrimeFamilyTranslatedMoments
import GaloisForLFunctions.BiScaleUncertainty.EvenPrimePairMomentCalculus

/-! A cutoff-three parity/ternary family with cubic fifth-array errors, identical sixth arrays, and linear separation under every translation. -/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.TopAnchor.Sharp
open GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The actual cutoff-three profile with parity coefficient one and ternary coefficient t. -/
def weights (t : ℝ) (d : ℕ) : ℝ :=
  if d = 1 then -1-t else if d = 2 then 2 else if d = 3 then 3*t else 0

theorem coordinate_two (t : ℝ) : selbergMultiplesCoord 3 (weights t) 2 = 1 := by
  norm_num [selbergMultiplesCoord, Finset.sum_filter,
    show Icc 1 3 = ({1,2,3} : Finset ℕ) by decide, weights]

theorem signal (t : ℝ) (n : ℕ) :
    sieveSeq 3 (weights t) n = parityFactor n+t*residueRow 3 (n : ZMod 3) := by
  simp only [sieveSeq, show Icc 1 3 = ({1,2,3} : Finset ℕ) by decide,
    Finset.sum_filter]
  by_cases h2 : 2 ∣ n <;> by_cases h3 : 3 ∣ n <;>
    simp [weights, parityFactor, residueRow, ZMod.natCast_eq_zero_iff, h2, h3] <;> ring

private theorem row_bound (x : ZMod 3) : |residueRow 3 x| ≤ 2 := by
  unfold residueRow
  split_ifs <;> norm_num

private theorem row_nat (n : ℕ) :
    residueRow 3 (n : ZMod 3) = if 3 ∣ n then 2 else -1 := by
  simp only [residueRow, ZMod.natCast_eq_zero_iff]
  norm_num

/-- Both perturbations lie uniformly within twice their amplitude of the nonzero parity source. -/
theorem near_parity (t : ℝ) (n : ℕ) :
    |sieveSeq 3 (weights t) n-sieveSeq 3 (weights 0) n| ≤ 2*|t| := by
  rw [signal, signal]
  simp only [zero_mul, add_zero, add_sub_cancel_left, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left (row_bound (n : ZMod 3)) (abs_nonneg t)]

/-- Every natural translation leaves a discrepancy of at least twice the weak-mode amplitude. -/
theorem translation_separation (t : ℝ) (h : ℕ) :
    ∃ n : ℕ, 2*t ≤ |sieveSeq 3 (weights (-t)) n-sieveSeq 3 (weights t) (n+h)| := by
  have hpar (n : ℕ) : parityFactor n ≤ 1 := by
    unfold parityFactor
    split_ifs <;> norm_num
  by_cases hh : h % 3 = 1
  · refine ⟨4, ?_⟩
    have hn : ¬3 ∣ 4+h := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    rw [signal, signal]
    have hr : residueRow 3 ((4+h : ℕ) : ZMod 3) = -1 := by
      rw [row_nat, if_neg hn]
    have hr4 : residueRow 3 ((4 : ℕ) : ZMod 3) = -1 := by
      simpa using row_nat 4
    have hp4 : parityFactor 4 = 1 := by norm_num [parityFactor]
    rw [hr, hr4, hp4]
    have he := le_abs_self (1+(-t)*(-1)-(parityFactor (4+h)+t*(-1)))
    have hp := hpar (4+h)
    linarith
  · refine ⟨2, ?_⟩
    have hn : ¬3 ∣ 2+h := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    rw [signal, signal]
    have hr : residueRow 3 ((2+h : ℕ) : ZMod 3) = -1 := by
      rw [row_nat, if_neg hn]
    have hr2 : residueRow 3 ((2 : ℕ) : ZMod 3) = -1 := by
      simpa using row_nat 2
    have hp2 : parityFactor 2 = 1 := by norm_num [parityFactor]
    rw [hr, hr2, hp2]
    have he := le_abs_self (1+(-t)*(-1)-(parityFactor (2+h)+t*(-1)))
    have hp := hpar (2+h)
    linarith

private def pairedProduct {m : ℕ} (A B : Fin m → ℝ) (t : ℝ) : ℝ :=
  (∏ i, (A i+t*B i))+(∏ i, (-A i+t*B i))

private theorem pairedProduct_neg {m : ℕ} (A B : Fin m → ℝ) (t : ℝ) :
    pairedProduct A B (-t) = (-1)^m * pairedProduct A B t := by
  have h₁ : (∏ i, (A i+(-t)*B i)) = (-1)^m * ∏ i, (-A i+t*B i) := by
    simp_rw [show ∀ i, A i+(-t)*B i = -(-A i+t*B i) by intro i; ring]
    rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  have h₂ : (∏ i, (-A i+(-t)*B i)) = (-1)^m * ∏ i, (A i+t*B i) := by
    simp_rw [show ∀ i, -A i+(-t)*B i = -(A i+t*B i) by intro i; ring]
    rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  unfold pairedProduct
  rw [h₁, h₂]
  ring

/-- Exact period-six average, paired over the two parity residues. -/
private theorem moment_paired (t : ℝ) {m : ℕ} (h : Fin m → ℕ) :
    translatedMoment 3 (weights t) h =
      (∑ x : ZMod 3, pairedProduct (fun i => parityFactor (h i))
        (fun i => residueRow 3 (x+(h i : ZMod 3))) t) / 6 := by
  have hu : (Finset.univ : Finset (ZMod 3)) = {0,1,2} := by decide
  have h30 : (3 : ZMod 3) = 0 := by decide
  have h41 : (4 : ZMod 3) = 1 := by decide
  have h52 : (5 : ZMod 3) = 2 := by decide
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  simp only [translatedMoment, show (3 : ℕ).factorial = 6 by decide, signal,
    parityFactor_add, Nat.cast_add, hu, pairedProduct]
  simp only [Finset.sum_range_succ, Finset.sum_insert, Finset.mem_insert,
    Finset.mem_singleton, Finset.sum_singleton, h01, h02, h12,
    not_false_eq_true, or_self]
  norm_num only [parityFactor, Nat.cast_ofNat, h30, h41, h52, zero_add, one_mul, neg_one_mul]
  simp only [ite_true, ite_false, h30, h41, h52, zero_add, one_mul, neg_one_mul]
  ring

private theorem moment_neg (t : ℝ) {m : ℕ} (h : Fin m → ℕ) :
    translatedMoment 3 (weights (-t)) h = (-1)^m * translatedMoment 3 (weights t) h := by
  rw [moment_paired, moment_paired]
  simp_rw [pairedProduct_neg]
  rw [← Finset.mul_sum]
  ring

/-- Every sixth raw array agrees despite the weak signed odd coordinate changing sign. -/
theorem sixth_equal (t : ℝ) (h : Fin 6 → ℕ) :
    translatedMoment 3 (weights (-t)) h = translatedMoment 3 (weights t) h := by
  rw [moment_neg]
  norm_num

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.TopAnchor.Sharp

namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.TopAnchor.Sharp

private def linearTerm (A B : Fin 5 → ℝ) : ℝ :=
  B 0*(A 1*A 2*A 3*A 4) + B 1*(A 0*A 2*A 3*A 4) +
  B 2*(A 0*A 1*A 3*A 4) + B 3*(A 0*A 1*A 2*A 4) +
  B 4*(A 0*A 1*A 2*A 3)

private def cubicTerms (A B : Fin 5 → ℝ) : Fin 10 → ℝ :=
  ![A 0*A 1*B 2*B 3*B 4, A 0*A 2*B 1*B 3*B 4,
    A 0*A 3*B 1*B 2*B 4, A 0*A 4*B 1*B 2*B 3,
    A 1*A 2*B 0*B 3*B 4, A 1*A 3*B 0*B 2*B 4,
    A 1*A 4*B 0*B 2*B 3, A 2*A 3*B 0*B 1*B 4,
    A 2*A 4*B 0*B 1*B 3, A 3*A 4*B 0*B 1*B 2]

private theorem paired_five (A B : Fin 5 → ℝ) (t : ℝ) :
    pairedProduct A B t = 2*t*linearTerm A B +
      2*t^3*(∑ j, cubicTerms A B j) + 2*t^5*(∏ i, B i) := by
  simp [pairedProduct, linearTerm, cubicTerms, Fin.prod_univ_succ,
    Fin.sum_univ_succ]
  ring

private theorem cubic_bound (A B : Fin 5 → ℝ)
    (hA : ∀ i, |A i| ≤ 1) (hB : ∀ i, |B i| ≤ 2) :
    |∑ j, cubicTerms A B j| ≤ 80 := by
  have hm (i j k l m : Fin 5) : |A i*A j*B k*B l*B m| ≤ 8 := by
    calc
      _ = |A i| * |A j| * |B k| * |B l| * |B m| := by simp only [abs_mul]
      _ ≤ 1*1*2*2*2 := by gcongr <;> first | exact hA _ | exact hB _
      _ = 8 := by norm_num
  calc
    _ ≤ ∑ j, |cubicTerms A B j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 10, (8 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      fin_cases j <;> dsimp [cubicTerms] <;> apply hm
    _ = 80 := by norm_num

private theorem product_bound (B : Fin 5 → ℝ) (hB : ∀ i, |B i| ≤ 2) :
    |∏ i, B i| ≤ 32 := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i : Fin 5, (2 : ℝ) :=
      Finset.prod_le_prod (fun i _ => abs_nonneg (B i)) (fun i _ => hB i)
    _ = 32 := by norm_num

private theorem linear_average_zero (A : Fin 5 → ℝ) (h : Fin 5 → ℕ) :
    (∑ x : ZMod 3, linearTerm A (fun i => residueRow 3 (x+(h i : ZMod 3)))) = 0 := by
  simp only [linearTerm, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_residueRow_shift, zero_mul, add_zero]

/-- Uniform all-lag fifth-moment cancellation is cubic at the parity source. -/
theorem fifth_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (h : Fin 5 → ℕ) :
    |translatedMoment 3 (weights t) h| ≤ 112*t^3 := by
  let A : Fin 5 → ℝ := fun i => parityFactor (h i)
  let B : ZMod 3 → Fin 5 → ℝ := fun x i => residueRow 3 (x+(h i : ZMod 3))
  have hA (i : Fin 5) : |A i| ≤ 1 := by
    dsimp [A]
    unfold parityFactor
    split_ifs <;> norm_num
  have hB (x : ZMod 3) (i : Fin 5) : |B x i| ≤ 2 := row_bound _
  have hc (x : ZMod 3) : |∑ j, cubicTerms A (B x) j| ≤ 80 := cubic_bound A (B x) hA (hB x)
  have hp (x : ZMod 3) : |∏ i, B x i| ≤ 32 := product_bound (B x) (hB x)
  have heq : translatedMoment 3 (weights t) h =
      (2*t^3*(∑ x : ZMod 3, ∑ j, cubicTerms A (B x) j) +
        2*t^5*(∑ x : ZMod 3, ∏ i, B x i))/6 := by
    rw [moment_paired]
    change (∑ x : ZMod 3, pairedProduct A (B x) t)/6 = _
    simp_rw [paired_five]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hz : (∑ x : ZMod 3, linearTerm A (B x)) = 0 := linear_average_zero A h
    rw [hz]
    ring
  have hcSum : |∑ x : ZMod 3, ∑ j, cubicTerms A (B x) j| ≤ 240 := by
    calc
      _ ≤ ∑ x : ZMod 3, |∑ j, cubicTerms A (B x) j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : ZMod 3, (80 : ℝ) := Finset.sum_le_sum (fun x _ => hc x)
      _ = 240 := by norm_num
  have hpSum : |∑ x : ZMod 3, ∏ i, B x i| ≤ 96 := by
    calc
      _ ≤ ∑ x : ZMod 3, |∏ i, B x i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : ZMod 3, (32 : ℝ) := Finset.sum_le_sum (fun x _ => hp x)
      _ = 96 := by norm_num
  have ht2 : t^2 ≤ 1 := by nlinarith
  have ht3 : 0 ≤ t^3 := by positivity
  have ht5 : t^5 ≤ t^3 := by nlinarith [mul_le_mul_of_nonneg_left ht2 ht3]
  rw [heq, abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 6)).2
  calc
    _ ≤ |2*t^3*(∑ x : ZMod 3, ∑ j, cubicTerms A (B x) j)| +
        |2*t^5*(∑ x : ZMod 3, ∏ i, B x i)| := abs_add_le _ _
    _ = |2*t^3| * |∑ x : ZMod 3, ∑ j, cubicTerms A (B x) j| +
        |2*t^5| * |∑ x : ZMod 3, ∏ i, B x i| := by simp only [abs_mul]
    _ ≤ (2*t^3)*240+(2*t^5)*96 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ 2*t^3),
        abs_of_nonneg (by positivity : 0 ≤ 2*t^5)]
      gcongr
    _ ≤ (112*t^3)*6 := by nlinarith

/-- The opposite weak signs differ by at most a cubic error in every fifth raw lag array. -/
theorem fifth_error {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (h : Fin 5 → ℕ) :
    |translatedMoment 3 (weights (-t)) h-translatedMoment 3 (weights t) h| ≤ 224*t^3 := by
  rw [moment_neg]
  rw [show (-1 : ℝ)^5 = -1 by norm_num]
  have he : (-1 : ℝ)*translatedMoment 3 (weights t) h-translatedMoment 3 (weights t) h =
      -2*translatedMoment 3 (weights t) h := by ring
  rw [he, abs_mul]
  norm_num
  nlinarith [fifth_bound ht ht1 h]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.TopAnchor.Sharp
