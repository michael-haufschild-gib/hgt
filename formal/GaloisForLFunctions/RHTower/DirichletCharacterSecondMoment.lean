/-
# Finite residue-class Cauchy machinery for quadratic character moments

This module isolates the coefficient-side finite Cauchy step in the
Bondarenko--Heap Lemma 8 argument.  It is deliberately independent of any
asymptotic divisor estimate: every modulus, interval, and coefficient family
is finite and literal.

No RH, GRH, zero-density hypothesis, or undischarged analytic input is used.
-/
import GaloisForLFunctions.RHTower.QuadraticJacobiSum
import GaloisForLFunctions.RHTower.Sieve.ResiduePartitionCount
import Mathlib.Data.Int.NatAbs

open Finset

noncomputable section

namespace RHTower

/-- The `ℓ¹` mass of coefficients from `[1,M]` in one literal residue class modulo `e + 1`. -/
def residueClassL1Mass (e M r : ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 M).filter (fun k => k % (e + 1) = r), ‖b k‖

/-- The squared `ℓ²` mass of coefficients from `[1,M]` in one literal residue class modulo
`e + 1`. -/
def residueClassL2Mass (e M r : ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 M).filter (fun k => k % (e + 1) = r), ‖b k‖ ^ (2 : ℕ)

/-- Cauchy's inequality in one finite residue class, with its class occupancy bounded by the
elementary interval count. -/
theorem residueClassL1Mass_sq_le (e M r : ℕ) (b : ℕ → ℂ) :
    residueClassL1Mass e M r b ^ (2 : ℕ) ≤
      ((M : ℝ) / ((e + 1 : ℕ) : ℝ) + 1) * residueClassL2Mass e M r b := by
  rw [residueClassL1Mass, residueClassL2Mass]
  calc
    (∑ k ∈ (Finset.Icc 1 M).filter (fun k => k % (e + 1) = r), ‖b k‖) ^ (2 : ℕ)
        ≤ (((Finset.Icc 1 M).filter (fun k => k % (e + 1) = r)).card : ℝ) *
          ∑ k ∈ (Finset.Icc 1 M).filter (fun k => k % (e + 1) = r), ‖b k‖ ^ (2 : ℕ) :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ ((M : ℝ) / ((e + 1 : ℕ) : ℝ) + 1) *
          ∑ k ∈ (Finset.Icc 1 M).filter (fun k => k % (e + 1) = r), ‖b k‖ ^ (2 : ℕ) := by
      apply mul_le_mul_of_nonneg_right
      · exact RHTower.Sieve.card_residue_class_le (by omega) M r
      · exact Finset.sum_nonneg fun k hk => sq_nonneg ‖b k‖

/-- Summing the residue-class Cauchy inequalities gives an exact finite second-moment bound.
The only loss is the literal `M / (e + 1) + 1` occupancy of an interval residue class. -/
theorem sum_residueClassL1Mass_sq_le (e M : ℕ) (b : ℕ → ℂ) :
    ∑ r ∈ Finset.range (e + 1), residueClassL1Mass e M r b ^ (2 : ℕ) ≤
      ((M : ℝ) / ((e + 1 : ℕ) : ℝ) + 1) *
        ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ (2 : ℕ) := by
  have hclass : ∀ r ∈ Finset.range (e + 1),
      residueClassL1Mass e M r b ^ (2 : ℕ) ≤
        ((M : ℝ) / ((e + 1 : ℕ) : ℝ) + 1) * residueClassL2Mass e M r b := by
    intro r hr
    exact residueClassL1Mass_sq_le e M r b
  calc
    _ ≤ ∑ r ∈ Finset.range (e + 1),
        ((M : ℝ) / ((e + 1 : ℕ) : ℝ) + 1) * residueClassL2Mass e M r b :=
      Finset.sum_le_sum hclass
    _ = ((M : ℝ) / ((e + 1 : ℕ) : ℝ) + 1) *
          ∑ r ∈ Finset.range (e + 1), residueClassL2Mass e M r b := by
      rw [Finset.mul_sum]
    _ = ((M : ℝ) / ((e + 1 : ℕ) : ℝ) + 1) *
          ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ (2 : ℕ) := by
      congr 1
      simp only [residueClassL2Mass]
      simpa only [Finset.filter_filter] using
        (Finset.sum_fiberwise_of_maps_to
          (s := Finset.Icc 1 M) (t := Finset.range (e + 1))
          (g := fun k => k % (e + 1))
          (fun k hk => Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))
          (fun k => ‖b k‖ ^ (2 : ℕ)))

/-- Exact decomposition of a pair sum by equal residue classes. -/
theorem sum_same_residueClass_pair_mass (e M : ℕ) (b : ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M,
      if k % (e + 1) = l % (e + 1) then ‖b k‖ * ‖b l‖ else 0) =
      ∑ r ∈ Finset.range (e + 1), residueClassL1Mass e M r b ^ (2 : ℕ) := by
  classical
  simp only [residueClassL1Mass]
  simp_rw [pow_two, Finset.sum_mul_sum]
  symm
  calc
    _ = ∑ r ∈ Finset.range (e + 1),
        ∑ i ∈ Finset.Icc 1 M with i % (e + 1) = r,
          ∑ j ∈ Finset.Icc 1 M with j % (e + 1) = i % (e + 1), ‖b i‖ * ‖b j‖ := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i % (e + 1) = r := (Finset.mem_filter.mp hi).2
      simp [hir]
    _ = ∑ i ∈ Finset.Icc 1 M,
        ∑ j ∈ Finset.Icc 1 M with j % (e + 1) = i % (e + 1), ‖b i‖ * ‖b j‖ := by
      exact Finset.sum_fiberwise_of_maps_to
        (s := Finset.Icc 1 M) (t := Finset.range (e + 1))
        (g := fun i => i % (e + 1))
        (fun i hi => Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))
        (fun i => ∑ j ∈ Finset.Icc 1 M with j % (e + 1) = i % (e + 1), ‖b i‖ * ‖b j‖)
    _ = _ := by
      simp only [Finset.sum_filter, eq_comm]

/-- Divisibility of an unsigned difference is exactly equality of natural residue classes. -/
theorem dvd_natDist_iff_modEq (e k l : ℕ) :
    e ∣ Nat.dist k l ↔ k % e = l % e := by
  change e ∣ Nat.dist k l ↔ k ≡ l [MOD e]
  rcases le_total k l with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    exact (Nat.modEq_iff_dvd' h).symm
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]
    exact ((Nat.modEq_iff_dvd' h).symm).trans Nat.ModEq.comm

/-- The divisors of `gcd(q + 1,d)` are precisely the divisors of `q + 1` which divide `d`. -/
theorem gcd_succ_divisors_eq_filter (q d : ℕ) :
    (Nat.gcd (q + 1) d).divisors =
      (q + 1).divisors.filter (fun e => e ∣ d) := by
  classical
  ext e
  simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨heq, hed⟩, -⟩
    exact ⟨⟨heq, by omega⟩, hed⟩
  · rintro ⟨⟨heq, -⟩, hed⟩
    exact ⟨⟨heq, hed⟩, Nat.gcd_pos_of_pos_left _ (by omega) |>.ne'⟩

/-- Gauss's totient expansion of the literal gcd kernel, expressed directly in residue classes. -/
theorem gcd_succ_eq_sum_totient_residueClasses (q k l : ℕ) :
    ((Nat.gcd (q + 1) (Nat.dist k l) : ℕ) : ℝ) =
      ∑ e ∈ (q + 1).divisors,
        if k % e = l % e then (Nat.totient e : ℝ) else 0 := by
  classical
  have hsum : ∑ e ∈ (Nat.gcd (q + 1) (Nat.dist k l)).divisors, Nat.totient e =
      Nat.gcd (q + 1) (Nat.dist k l) := Nat.sum_totient _
  rw [gcd_succ_divisors_eq_filter] at hsum
  rw [Finset.sum_filter] at hsum
  have hreal : ((Nat.gcd (q + 1) (Nat.dist k l) : ℕ) : ℝ) =
      ∑ e ∈ (q + 1).divisors,
        if e ∣ Nat.dist k l then (Nat.totient e : ℝ) else 0 := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) hsum.symm
  simpa only [dvd_natDist_iff_modEq] using hreal

/-- The finite divisor-weighted residue-class moment occurring after the totient expansion of a
gcd kernel.  Modulus `q + 1` keeps positivity internal to the statement. -/
def divisorWeightedResidueClassL1Moment (q M : ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ e ∈ (q + 1).divisors, (Nat.totient e : ℝ) *
    ∑ r ∈ Finset.range e, residueClassL1Mass (e - 1) M r b ^ (2 : ℕ)

/-- The finite coefficient-side divisor/Cauchy estimate.  This is the exact bookkeeping layer
used after a totient expansion of a square-free quadratic correlation; the remaining task is to
identify the character second moment with this positive divisor majorant. -/
theorem divisorWeightedResidueClassL1Moment_le (q M : ℕ) (b : ℕ → ℂ) :
    divisorWeightedResidueClassL1Moment q M b ≤
      (∑ e ∈ (q + 1).divisors, (Nat.totient e : ℝ) *
        ((M : ℝ) / (e : ℝ) + 1)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ (2 : ℕ) := by
  have hstep : ∀ e ∈ (q + 1).divisors,
      ∑ r ∈ Finset.range e, residueClassL1Mass (e - 1) M r b ^ (2 : ℕ) ≤
        ((M : ℝ) / (e : ℝ) + 1) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ (2 : ℕ) := by
    intro e he
    have hepos : 0 < e := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp he).1 (by omega)
    have heone : 1 ≤ e := hepos
    have hsub : e - 1 + 1 = e := Nat.sub_add_cancel heone
    simpa only [hsub] using sum_residueClassL1Mass_sq_le (e - 1) M b
  rw [divisorWeightedResidueClassL1Moment]
  calc
    _ ≤ ∑ e ∈ (q + 1).divisors, (Nat.totient e : ℝ) *
        (((M : ℝ) / (e : ℝ) + 1) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ (2 : ℕ)) := by
      apply Finset.sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_left (hstep e he) (Nat.cast_nonneg _)
    _ = (∑ e ∈ (q + 1).divisors, (Nat.totient e : ℝ) *
          ((M : ℝ) / (e : ℝ) + 1)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ (2 : ℕ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      ring

/-- Exact total totient mass over the positive divisors of a concrete modulus. -/
theorem sum_totient_divisors_eq_succ (q : ℕ) :
    ∑ e ∈ (q + 1).divisors, (Nat.totient e : ℝ) = q + 1 := by
  exact_mod_cast Nat.sum_totient (q + 1)

/-- The explicit coefficient factor from the divisor/Cauchy calculation is at most the modulus
plus interval length times the literal divisor count. -/
theorem divisor_totient_coefficient_le (q M : ℕ) :
    ∑ e ∈ (q + 1).divisors, (Nat.totient e : ℝ) *
        ((M : ℝ) / (e : ℝ) + 1) ≤
      (M : ℝ) * ((q + 1).divisors.card : ℝ) + (q + 1 : ℝ) := by
  have hterm : ∀ e ∈ (q + 1).divisors, (Nat.totient e : ℝ) *
      ((M : ℝ) / (e : ℝ) + 1) ≤ (M : ℝ) + (Nat.totient e : ℝ) := by
    intro e he
    have hepos : 0 < e := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp he).1 (by omega)
    have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast hepos
    have hphi : (Nat.totient e : ℝ) ≤ (e : ℝ) := by
      exact_mod_cast Nat.totient_le e
    have hratio : (Nat.totient e : ℝ) / (e : ℝ) ≤ 1 := by
      rw [div_le_one heR]
      exact hphi
    have hrewrite : (Nat.totient e : ℝ) * ((M : ℝ) / (e : ℝ) + 1) =
        (M : ℝ) * ((Nat.totient e : ℝ) / (e : ℝ)) + (Nat.totient e : ℝ) := by
      field_simp
    rw [hrewrite]
    nlinarith [mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg M)]
  calc
    _ ≤ (∑ e ∈ (q + 1).divisors, ((M : ℝ) + (Nat.totient e : ℝ))) :=
      Finset.sum_le_sum hterm
    _ = (M : ℝ) * ((q + 1).divisors.card : ℝ) + (q + 1 : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        sum_totient_divisors_eq_succ]
      ring

/-- Positive gcd-kernel majorant for a finite coefficient family on `[1,M]`. -/
def gcdKernelMoment (q M : ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M,
    ‖b k‖ * ‖b l‖ * ((Nat.gcd (q + 1) (Nat.dist k l) : ℕ) : ℝ)

/-- Expand the finite gcd-kernel moment by totient weights and residue-class coincidences. -/
theorem gcdKernelMoment_expand (q M : ℕ) (b : ℕ → ℂ) :
    gcdKernelMoment q M b =
      ∑ e ∈ (q + 1).divisors, (Nat.totient e : ℝ) *
        ∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M,
          if k % e = l % e then ‖b k‖ * ‖b l‖ else 0 := by
  classical
  unfold gcdKernelMoment
  simp_rw [gcd_succ_eq_sum_totient_residueClasses]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k hk => Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  by_cases h : k % e = l % e
  · simp [h]
    ring
  · simp [h]

/-- The gcd-kernel moment is exactly the divisor-weighted residue-class moment. -/
theorem gcdKernelMoment_eq_divisorWeightedResidueClassL1Moment (q M : ℕ) (b : ℕ → ℂ) :
    gcdKernelMoment q M b = divisorWeightedResidueClassL1Moment q M b := by
  rw [gcdKernelMoment_expand, divisorWeightedResidueClassL1Moment]
  apply Finset.sum_congr rfl
  intro e he
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp he).1 (by omega)
  have heone : 1 ≤ e := hepos
  have hsub : e - 1 + 1 = e := Nat.sub_add_cancel heone
  rw [← (show (∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M,
      if k % e = l % e then ‖b k‖ * ‖b l‖ else 0) =
      ∑ r ∈ Finset.range e, residueClassL1Mass (e - 1) M r b ^ (2 : ℕ) by
    simpa only [hsub] using sum_same_residueClass_pair_mass (e - 1) M b)]

/-- Closed finite gcd-kernel estimate obtained from the literal divisor/Cauchy calculation. -/
theorem gcdKernelMoment_le (q M : ℕ) (b : ℕ → ℂ) :
    gcdKernelMoment q M b ≤
      (∑ e ∈ (q + 1).divisors, (Nat.totient e : ℝ) *
        ((M : ℝ) / (e : ℝ) + 1)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ (2 : ℕ) := by
  rw [gcdKernelMoment_eq_divisorWeightedResidueClassL1Moment]
  exact divisorWeightedResidueClassL1Moment_le q M b

namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- Incomplete finite quadratic-character shift sum on the literal coefficient interval `[1,M]`.
Integer casts make the connection to the CRT complete-correlation theorem explicit. -/
def quadraticIntervalShiftSum [DecidableEq I] (P : OddPrimeFamily I)
    (M : ℕ) (b : ℕ → ℂ) (x : ZMod P.modulus) : ℂ :=
  ∑ k ∈ Finset.Icc 1 M,
    b k * quadraticCharacter P (x + ((k : ℤ) : ZMod P.modulus))

/-- The natural absolute value of an integer difference of natural casts is the natural distance. -/
theorem natAbs_intCast_sub_eq_natDist (k l : ℕ) :
    ((l : ℤ) - (k : ℤ)).natAbs = Nat.dist k l := by
  rcases le_total k l with h | h
  · rw [Int.natAbs_natCast_sub_natCast_of_ge h, Nat.dist_eq_sub_of_le h]
  · rw [Int.natAbs_natCast_sub_natCast_of_le h, Nat.dist_comm,
      Nat.dist_eq_sub_of_le h]

/-- Exact expansion of the incomplete finite quadratic-character second moment into complete
CRT correlations. -/
theorem quadratic_intervalShiftSum_energy [DecidableEq I] (P : OddPrimeFamily I)
    (M : ℕ) (b : ℕ → ℂ) :
    (∑ x : ZMod P.modulus, (Complex.normSq (quadraticIntervalShiftSum P M b x) : ℂ)) =
      ∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M, b k * star (b l) *
        ∑ x : ZMod P.modulus,
          quadraticCharacter P (x + ((k : ℤ) : ZMod P.modulus)) *
            quadraticCharacter P (x + ((l : ℤ) : ZMod P.modulus)) := by
  have hnorm : ∀ x : ZMod P.modulus,
      (Complex.normSq (quadraticIntervalShiftSum P M b x) : ℂ) =
        quadraticIntervalShiftSum P M b x * star (quadraticIntervalShiftSum P M b x) := by
    intro x
    exact (Complex.mul_conj _).symm
  rw [Finset.sum_congr rfl fun x hx => hnorm x]
  simp only [quadraticIntervalShiftSum]
  simp_rw [star_sum, Finset.sum_mul_sum, star_mul, quadraticCharacter_star]
  have hreorder (x : ZMod P.modulus) (k l : ℕ) :
      b k * quadraticCharacter P (x + ((k : ℤ) : ZMod P.modulus)) *
          (quadraticCharacter P (x + ((l : ℤ) : ZMod P.modulus)) * star (b l)) =
        (b k * star (b l)) *
          (quadraticCharacter P (x + ((k : ℤ) : ZMod P.modulus)) *
            quadraticCharacter P (x + ((l : ℤ) : ZMod P.modulus))) := by
    ring
  simp_rw [hreorder]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, k]
    rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]

/-- The incomplete finite second moment is dominated by the literal positive gcd kernel.  This
joins the CRT complete-correlation theorem to the finite divisor/Cauchy machinery. -/
theorem quadratic_intervalShiftSum_normSq_le_gcdKernel [DecidableEq I] (P : OddPrimeFamily I)
    (M : ℕ) (b : ℕ → ℂ) :
    ∑ x : ZMod P.modulus, Complex.normSq (quadraticIntervalShiftSum P M b x) ≤
      gcdKernelMoment (P.modulus - 1) M b := by
  have henergy := quadratic_intervalShiftSum_energy P M b
  have hnonneg : 0 ≤ ∑ x : ZMod P.modulus,
      Complex.normSq (quadraticIntervalShiftSum P M b x) :=
    Finset.sum_nonneg fun x hx => Complex.normSq_nonneg _
  have hmodpos : 0 < P.modulus := Nat.pos_of_ne_zero P.modulus_neZero.out
  have hmod : P.modulus - 1 + 1 = P.modulus := Nat.sub_add_cancel hmodpos
  calc
    ∑ x : ZMod P.modulus, Complex.normSq (quadraticIntervalShiftSum P M b x)
        = ‖(↑(∑ x : ZMod P.modulus,
            Complex.normSq (quadraticIntervalShiftSum P M b x)) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M, b k * star (b l) *
        ∑ x : ZMod P.modulus,
          quadraticCharacter P (x + ((k : ℤ) : ZMod P.modulus)) *
            quadraticCharacter P (x + ((l : ℤ) : ZMod P.modulus))‖ := by
      have hcast : (↑(∑ x : ZMod P.modulus,
          Complex.normSq (quadraticIntervalShiftSum P M b x)) : ℂ) =
          ∑ x : ZMod P.modulus,
            (Complex.normSq (quadraticIntervalShiftSum P M b x) : ℂ) := by
        exact_mod_cast rfl
      rw [hcast, henergy]
    _ ≤ ∑ k ∈ Finset.Icc 1 M, ‖∑ l ∈ Finset.Icc 1 M, b k * star (b l) *
        ∑ x : ZMod P.modulus,
          quadraticCharacter P (x + ((k : ℤ) : ZMod P.modulus)) *
            quadraticCharacter P (x + ((l : ℤ) : ZMod P.modulus))‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M,
        ‖b k * star (b l) * ∑ x : ZMod P.modulus,
          quadraticCharacter P (x + ((k : ℤ) : ZMod P.modulus)) *
            quadraticCharacter P (x + ((l : ℤ) : ZMod P.modulus))‖ := by
      apply Finset.sum_le_sum
      intro k hk
      exact norm_sum_le _ _
    _ = ∑ k ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Icc 1 M,
        ‖b k‖ * ‖b l‖ * ‖∑ x : ZMod P.modulus,
          quadraticCharacter P (x + ((k : ℤ) : ZMod P.modulus)) *
            quadraticCharacter P (x + ((l : ℤ) : ZMod P.modulus))‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      simp only [norm_mul, norm_star]
    _ ≤ gcdKernelMoment (P.modulus - 1) M b := by
      rw [gcdKernelMoment]
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      rw [hmod]
      have hcorr : ‖∑ x : ZMod P.modulus,
          quadraticCharacter P (x + ((k : ℤ) : ZMod P.modulus)) *
            quadraticCharacter P (x + ((l : ℤ) : ZMod P.modulus))‖ ≤
          P.modulus.gcd (Nat.dist k l) := by
        simpa only [natAbs_intCast_sub_eq_natDist] using
          quadratic_shiftCorrelation_norm_le_gcd P (k : ℤ) (l : ℤ)
      exact mul_le_mul_of_nonneg_left hcorr
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Fully discharged finite interval quadratic-character second moment.  Its explicit divisor
factor is the unsimplified form of the coefficient estimate in Bondarenko--Heap Lemma 8; turning
it into their `q^ε(q+K)` form still requires the divisor-function estimate and dyadic interval
bookkeeping. -/
theorem quadratic_intervalShiftSum_normSq_le_divisor [DecidableEq I] (P : OddPrimeFamily I)
    (M : ℕ) (b : ℕ → ℂ) :
    ∑ x : ZMod P.modulus, Complex.normSq (quadraticIntervalShiftSum P M b x) ≤
      (∑ e ∈ P.modulus.divisors, (Nat.totient e : ℝ) *
        ((M : ℝ) / (e : ℝ) + 1)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ (2 : ℕ) := by
  have hmodpos : 0 < P.modulus := Nat.pos_of_ne_zero P.modulus_neZero.out
  have hmod : P.modulus - 1 + 1 = P.modulus := Nat.sub_add_cancel hmodpos
  have hmodR : ((P.modulus - 1 : ℕ) : ℝ) + 1 = (P.modulus : ℝ) := by
    exact_mod_cast hmod
  calc
    _ ≤ gcdKernelMoment (P.modulus - 1) M b :=
      quadratic_intervalShiftSum_normSq_le_gcdKernel P M b
    _ ≤ (∑ e ∈ (P.modulus - 1 + 1).divisors, (Nat.totient e : ℝ) *
        ((M : ℝ) / (e : ℝ) + 1)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ (2 : ℕ) :=
      gcdKernelMoment_le (P.modulus - 1) M b
    _ = _ := by rw [hmod]

/-- Explicit divisor-count form of the finite interval quadratic-character second moment.  The
only remaining quantitative reduction toward the source Lemma 8 is a divisor-function growth
estimate and the source's dyadic/even-modulus bookkeeping. -/
theorem quadratic_intervalShiftSum_normSq_le_divisorCount [DecidableEq I]
    (P : OddPrimeFamily I) (M : ℕ) (b : ℕ → ℂ) :
    ∑ x : ZMod P.modulus, Complex.normSq (quadraticIntervalShiftSum P M b x) ≤
      ((M : ℝ) * (P.modulus.divisors.card : ℝ) + (P.modulus : ℝ)) *
        ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ (2 : ℕ) := by
  have hmodpos : 0 < P.modulus := Nat.pos_of_ne_zero P.modulus_neZero.out
  have hmod : P.modulus - 1 + 1 = P.modulus := Nat.sub_add_cancel hmodpos
  have hmodR : ((P.modulus - 1 : ℕ) : ℝ) + 1 = (P.modulus : ℝ) := by
    exact_mod_cast hmod
  have henergy_nonneg : 0 ≤ ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun k hk => sq_nonneg ‖b k‖
  calc
    _ ≤ (∑ e ∈ P.modulus.divisors, (Nat.totient e : ℝ) *
        ((M : ℝ) / (e : ℝ) + 1)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ (2 : ℕ) :=
      quadratic_intervalShiftSum_normSq_le_divisor P M b
    _ ≤ ((M : ℝ) * (P.modulus.divisors.card : ℝ) + (P.modulus : ℝ)) *
        ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ (2 : ℕ) := by
      apply mul_le_mul_of_nonneg_right
      simpa only [hmod, hmodR] using divisor_totient_coefficient_le (P.modulus - 1) M
      exact henergy_nonneg

end OddPrimeFamily

end RHTower
