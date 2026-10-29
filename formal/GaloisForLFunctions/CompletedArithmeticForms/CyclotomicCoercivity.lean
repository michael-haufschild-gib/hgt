import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AllDivisorConductorsRecoverTheDiscreteBridge
import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticLargeSieveForSquarefreeModuli

/-!
# Coercivity of the completed cyclotomic Gram

Completing all nontrivial divisor conductors gives a quantitative norm on the interior
prefix coefficients. The exact positive remainder is the energy of `(1 + ζ) P(ζ)`;
the complementary multiplier `(1 - ζ)` recovers the coefficient square mass by Parseval.
-/

noncomputable section

open Finset Polynomial

namespace GaloisForLFunctions.CompletedArithmeticForms

open CriticalArithmeticCorrelationTheory ArithmeticEffectivityTheory BezoutValuationIncidence

/-- The cyclotomic prefix packet on the interior of one period. -/
def prefixPacket (Q : ℕ) (a : ℕ → ℝ) (ζ : ℂ) : ℂ :=
  ∑ i ∈ Ico 1 Q, (a i : ℂ) * primitivePrefixValue ζ i

/-- The complete nonconstant divisor-conductor energy. -/
def divisorGramEnergy (Q : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Q.divisors.erase 1, ∑ i ∈ Ico 1 Q, ∑ j ∈ Ico 1 Q,
    a i * a j * primitivePrefixGram m i j

/-- The exact positive remainder in the coefficient coercivity law. -/
def cyclotomicRemainder (Q : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Q.divisors.erase 1, ∑ ζ ∈ primitiveRoots m ℂ,
    ‖(1 + ζ) * prefixPacket Q a ζ‖ ^ 2

private theorem range_eq_insert_Ico {Q : ℕ} (hQ : 0 < Q) :
    range Q = insert 0 (Ico 1 Q) := by
  ext i
  simp only [mem_range, mem_insert, mem_Ico]
  omega

/-- Multiplication by the cyclic difference exposes the original coefficients. -/
theorem prefixPacket_difference (Q : ℕ) (a : ℕ → ℝ) (ζ : ℂ) :
    (1 - ζ) * prefixPacket Q a ζ =
      (∑ i ∈ Ico 1 Q, (a i : ℂ)) - ∑ i ∈ Ico 1 Q, (a i : ℂ) * ζ ^ i := by
  have hgeom (i : ℕ) : (1 - ζ) * primitivePrefixValue ζ i = 1 - ζ ^ i := by
    have h := geom_sum_mul ζ i
    change (∑ j ∈ range i, ζ ^ j) * (ζ - 1) = ζ ^ i - 1 at h
    change (1 - ζ) * (∑ j ∈ range i, ζ ^ j) = 1 - ζ ^ i
    linear_combination -h
  simp only [prefixPacket, mul_sum]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  calc
    (1 - ζ) * ((a i : ℂ) * primitivePrefixValue ζ i) =
        (a i : ℂ) * ((1 - ζ) * primitivePrefixValue ζ i) := by ring
    _ = (a i : ℂ) - (a i : ℂ) * ζ ^ i := by rw [hgeom]; ring

private theorem period_parseval {Q : ℕ} (hQ : 0 < Q) (b : ℕ → ℂ) :
    (∑ ζ ∈ nthRootsFinset Q (1 : ℂ), ‖∑ i ∈ range Q, b i * ζ ^ i‖ ^ 2) =
      (Q : ℝ) * ∑ i ∈ range Q, ‖b i‖ ^ 2 := by
  rw [sum_nthRootsFinset_norm_sq hQ]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have hfilter : (range Q).filter (fun j => j % Q = i) = {i} := by
    ext j
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨hj, hji⟩
      rwa [Nat.mod_eq_of_lt hj] at hji
    · rintro rfl
      exact ⟨mem_range.mp hi, Nat.mod_eq_of_lt (mem_range.mp hi)⟩
  rw [hfilter, sum_singleton]

private theorem sum_nontrivial_orders {Q : ℕ} (hQ : 0 < Q) (f : ℂ → ℝ)
    (hf : f 1 = 0) :
    (∑ m ∈ Q.divisors.erase 1, ∑ ζ ∈ primitiveRoots m ℂ, f ζ) =
      ∑ ζ ∈ nthRootsFinset Q (1 : ℂ), f ζ := by
  have h := congrArg Complex.re
    (sum_nthRoots_eq_sum_divisors Q (fun ζ => (f ζ : ℂ)))
  simp only [Complex.re_sum, Complex.ofReal_re] at h
  have hs := sum_erase_add Q.divisors (fun m => ∑ ζ ∈ primitiveRoots m ℂ, f ζ)
    (Nat.one_mem_divisors.mpr hQ.ne')
  simpa only [IsPrimitiveRoot.primitiveRoots_one, sum_singleton, hf, add_zero] using
    hs.trans h.symm

private def differenceCoefficient (Q : ℕ) (a : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then ∑ j ∈ Ico 1 Q, a j else -a i

private theorem differenceCoefficient_fourier {Q : ℕ} (hQ : 0 < Q)
    (a : ℕ → ℝ) (ζ : ℂ) :
    (∑ i ∈ range Q, (differenceCoefficient Q a i : ℂ) * ζ ^ i) =
      (1 - ζ) * prefixPacket Q a ζ := by
  rw [range_eq_insert_Ico hQ, sum_insert (by simp), prefixPacket_difference]
  simp only [differenceCoefficient, ite_true, pow_zero, mul_one, Complex.ofReal_sum]
  have hsum : (∑ i ∈ Ico 1 Q,
      ((if i = 0 then ∑ j ∈ Ico 1 Q, a j else -a i : ℝ) : ℂ) * ζ ^ i) =
      -(∑ i ∈ Ico 1 Q, (a i : ℂ) * ζ ^ i) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun i hi => ?_
    have hi0 : i ≠ 0 := by have := (mem_Ico.mp hi).1; omega
    simp only [if_neg hi0, Complex.ofReal_neg, neg_mul]
  rw [hsum, sub_eq_add_neg]

private theorem differenceCoefficient_mass {Q : ℕ} (hQ : 0 < Q) (a : ℕ → ℝ) :
    (∑ i ∈ range Q, ‖(differenceCoefficient Q a i : ℂ)‖ ^ 2) =
      (∑ i ∈ Ico 1 Q, a i) ^ 2 + ∑ i ∈ Ico 1 Q, a i ^ 2 := by
  rw [range_eq_insert_Ico hQ, sum_insert (by simp)]
  simp only [differenceCoefficient, ite_true, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have hi0 : i ≠ 0 := by have := (mem_Ico.mp hi).1; omega
  rw [if_neg hi0, neg_sq]

/-- The derivative channel is exactly the mass of the interior coefficient vector and its sum. -/
theorem prefixPacket_difference_energy {Q : ℕ} (hQ : 0 < Q) (a : ℕ → ℝ) :
    (∑ m ∈ Q.divisors.erase 1, ∑ ζ ∈ primitiveRoots m ℂ,
      ‖(1 - ζ) * prefixPacket Q a ζ‖ ^ 2) =
        (Q : ℝ) * ((∑ i ∈ Ico 1 Q, a i) ^ 2 + ∑ i ∈ Ico 1 Q, a i ^ 2) := by
  rw [sum_nontrivial_orders hQ _ (by simp)]
  simp_rw [← differenceCoefficient_fourier hQ a]
  rw [period_parseval hQ, differenceCoefficient_mass hQ]

/-- The complete Gram retains all mixed coefficient terms. -/
theorem divisorGramEnergy_eq_norms (Q : ℕ) (a : ℕ → ℝ) :
    divisorGramEnergy Q a =
      ∑ m ∈ Q.divisors.erase 1, ∑ ζ ∈ primitiveRoots m ℂ, ‖prefixPacket Q a ζ‖ ^ 2 := by
  unfold divisorGramEnergy
  refine sum_congr rfl fun m hm => ?_
  have hm0 := Nat.pos_of_mem_divisors (mem_erase.mp hm).2
  simpa only [prefixPacket, Complex.real_smul] using
    primitivePrefixGram_quadratic_eq (Ico 1 Q) hm0 a id

/-- The arithmetic energy is the full discrete bridge quadratic form. -/
theorem divisorGramEnergy_eq_bridge {Q : ℕ} (hQ : 0 < Q) (a : ℕ → ℝ) :
    divisorGramEnergy Q a = ∑ i ∈ Ico 1 Q, ∑ j ∈ Ico 1 Q,
      a i * a j * ((Q : ℝ) * min (i : ℝ) j - (i : ℝ) * j) := by
  unfold divisorGramEnergy
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [← mul_sum, sum_nontrivial_divisors_primitivePrefixGram hQ
    (mem_Ico.mp hi).2.le (mem_Ico.mp hj).2.le]

private theorem unit_root_channel_identity (ζ z : ℂ) (hζ : ‖ζ‖ = 1) :
    ‖(1 - ζ) * z‖ ^ 2 + ‖(1 + ζ) * z‖ ^ 2 = 4 * ‖z‖ ^ 2 := by
  have hsq : Complex.normSq ζ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hζ, one_pow]
  have hfour : ‖1 - ζ‖ ^ 2 + ‖1 + ζ‖ ^ 2 = 4 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    change ζ.re * ζ.re + ζ.im * ζ.im = 1 at hsq
    change (1 - ζ.re) * (1 - ζ.re) + (0 - ζ.im) * (0 - ζ.im) +
      ((1 + ζ.re) * (1 + ζ.re) + (0 + ζ.im) * (0 + ζ.im)) = 4
    nlinarith only [hsq]
  simp only [norm_mul, mul_pow]
  rw [← add_mul, hfour]

/-- The complete arithmetic Gram splits into a coefficient reserve and an exact positive remainder. -/
theorem divisorGramEnergy_completion {Q : ℕ} (hQ : 0 < Q) (a : ℕ → ℝ) :
    4 * divisorGramEnergy Q a =
      (Q : ℝ) * ((∑ i ∈ Ico 1 Q, a i) ^ 2 + ∑ i ∈ Ico 1 Q, a i ^ 2) +
        cyclotomicRemainder Q a := by
  rw [divisorGramEnergy_eq_norms]
  calc
    _ = ∑ m ∈ Q.divisors.erase 1, ∑ ζ ∈ primitiveRoots m ℂ,
        (‖(1 - ζ) * prefixPacket Q a ζ‖ ^ 2 +
          ‖(1 + ζ) * prefixPacket Q a ζ‖ ^ 2) := by
      simp only [mul_sum]
      refine sum_congr rfl fun m hm => sum_congr rfl fun ζ hζ => ?_
      have hm0 := Nat.pos_of_mem_divisors (mem_erase.mp hm).2
      have hroot := (mem_primitiveRoots hm0).mp hζ
      exact (unit_root_channel_identity ζ _
        (Complex.norm_eq_one_of_pow_eq_one hroot.pow_eq_one hm0.ne')).symm
    _ = _ := by
      simp only [sum_add_distrib]
      rw [prefixPacket_difference_energy hQ]
      rfl

theorem cyclotomicRemainder_nonneg (Q : ℕ) (a : ℕ → ℝ) :
    0 ≤ cyclotomicRemainder Q a :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

/-- The coefficient norm and the total coefficient mass are controlled simultaneously. -/
theorem divisorGramEnergy_coercive {Q : ℕ} (hQ : 0 < Q) (a : ℕ → ℝ) :
    (Q : ℝ) * ((∑ i ∈ Ico 1 Q, a i) ^ 2 + ∑ i ∈ Ico 1 Q, a i ^ 2) ≤
      4 * divisorGramEnergy Q a := by
  rw [divisorGramEnergy_completion hQ]
  exact le_add_of_nonneg_right (cyclotomicRemainder_nonneg Q a)

theorem divisorGramEnergy_nonneg (Q : ℕ) (a : ℕ → ℝ) :
    0 ≤ divisorGramEnergy Q a := by
  rw [divisorGramEnergy_eq_norms]
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

/-- Completing the conductor family removes every interior radical direction. -/
theorem divisorGramEnergy_eq_zero_iff {Q : ℕ} (hQ : 0 < Q) (a : ℕ → ℝ) :
    divisorGramEnergy Q a = 0 ↔ ∀ i ∈ Ico 1 Q, a i = 0 := by
  constructor
  · intro hzero i hi
    have h := divisorGramEnergy_coercive hQ a
    rw [hzero, mul_zero] at h
    have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hmass := (mul_nonpos_iff_of_pos_left hQr).mp h
    have hsum : (∑ j ∈ Ico 1 Q, a j ^ 2) ≤ 0 := by
      linarith only [hmass, sq_nonneg (∑ j ∈ Ico 1 Q, a j)]
    have hiSq := (single_le_sum (fun j _ => sq_nonneg (a j)) hi).trans hsum
    exact (sq_eq_zero_iff).mp (le_antisymm hiSq (sq_nonneg _))
  · intro ha
    unfold divisorGramEnergy
    refine sum_eq_zero fun m _ => sum_eq_zero fun i hi => ?_
    simp only [ha i hi, zero_mul, sum_const_zero]

/-- Every nonzero interior packet has strictly positive complete arithmetic energy. -/
theorem divisorGramEnergy_pos_iff {Q : ℕ} (hQ : 0 < Q) (a : ℕ → ℝ) :
    0 < divisorGramEnergy Q a ↔ ∃ i ∈ Ico 1 Q, a i ≠ 0 := by
  rw [lt_iff_le_and_ne]
  simp only [divisorGramEnergy_nonneg, true_and, ne_eq, eq_comm (a := (0 : ℝ)),
    divisorGramEnergy_eq_zero_iff hQ, not_forall, exists_prop]

#print axioms divisorGramEnergy_completion
#print axioms divisorGramEnergy_coercive
#print axioms divisorGramEnergy_eq_zero_iff

end GaloisForLFunctions.CompletedArithmeticForms
