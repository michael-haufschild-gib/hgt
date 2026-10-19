import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeLimit
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# Harmonic divisor diagonal of the complete critical prime limit

The actual factorial prime-channel limit admits an absolutely convergent regrouping
by harmonic. Its divisor charge is negative exactly at harmonic two, zero at one
and multiples of four, and positive at every other harmonic. The regrouping uses
mathlib's fiberwise summation theorem and the existing complete native prime limit.
-/

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GaloisForLFunctions.ArithmeticPositivityTheory
noncomputable section
set_option autoImplicit false

private def diagonalPrimeTerm (r l : ℕ) : ℝ :=
  if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
    dyadicHarmonicWeight (r*l) * dyadicHarmonicWeight l *
      factorialCriticalHarmonicDefect (r*l) else 0

private theorem diagonal_prime_term_bound (r l : ℕ) :
    ‖diagonalPrimeTerm r l‖ ≤
      (2 * envelopePrimeMajorant (3 / 2) r) * |dyadicHarmonicWeight l| := by
  by_cases hr : 2 ≤ r
  · by_cases hl : l = 0
    · simp [diagonalPrimeTerm, hl, dyadicHarmonicWeight_zero]
    have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
    have hrl : (r : ℝ) ≤ ((r*l : ℕ) : ℝ) ^ 2 := by
      rw [Nat.cast_mul]
      have hprod : (r : ℝ) ≤ (r : ℝ) * l := by nlinarith
      nlinarith [sq_nonneg ((r : ℝ) * l - 1)]
    have hw : |dyadicHarmonicWeight (r*l)| ≤ 1 / (r : ℝ) :=
      (abs_dyadicHarmonicWeight_le _).trans (one_div_le_one_div_of_le hrp hrl)
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt r : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hJ := factorialCriticalHarmonicDefect_bounds (r*l)
    simp only [diagonalPrimeTerm, if_pos hr, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hΛ hrp.le), abs_of_nonneg hJ.1,
      envelopePrimeMajorant, show (3 / 2 : ℝ) + 1 / 2 = 2 by norm_num,
      Real.rpow_two]
    calc (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
          |dyadicHarmonicWeight (r*l)| * |dyadicHarmonicWeight l| *
          factorialCriticalHarmonicDefect (r*l)
        ≤ ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
          (1 / (r : ℝ)) * |dyadicHarmonicWeight l|) * 2 :=
          mul_le_mul
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hw (div_nonneg hΛ hrp.le)) (abs_nonneg _))
            hJ.2 hJ.1 (by positivity)
      _ = _ := by ring
  · simp [diagonalPrimeTerm, envelopePrimeMajorant, hr]

private theorem diagonal_prime_joint_summable :
    Summable (fun p : ℕ × ℕ => diagonalPrimeTerm p.1 p.2) := by
  have h := (summable_canonicalPrimeMajorant.mul_left 2).mul_of_nonneg
    summable_abs_dyadicHarmonicWeight
    (fun r => mul_nonneg (by norm_num) (envelopePrimeMajorant_nonneg _ _))
    (fun l => abs_nonneg (dyadicHarmonicWeight l))
  exact h.of_norm_bounded (fun p => diagonal_prime_term_bound p.1 p.2)

/-- The signed divisor charge of one harmonic in the complete critical prime limit. -/
def factorialCriticalPrimeHarmonicCharge (m : ℕ) : ℝ :=
  dyadicHarmonicChi m * ∑ r ∈ m.divisors,
    (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * dyadicHarmonicChi (m/r)

private theorem diagonal_prime_finite_fiber (m : ℕ) :
    (∑ p ∈ m.divisorsAntidiagonal, diagonalPrimeTerm p.1 p.2) =
      factorialCriticalPrimeHarmonicCharge m * factorialCriticalHarmonicDefect m /
        (m : ℝ) ^ 4 := by
  rw [Nat.sum_divisorsAntidiagonal]
  have hterm (r : ℕ) (hr : r ∈ m.divisors) :
      diagonalPrimeTerm r (m/r) =
        (dyadicHarmonicChi m * ((r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) *
          dyadicHarmonicChi (m/r))) * factorialCriticalHarmonicDefect m / (m : ℝ) ^ 4 := by
    obtain ⟨hdvd, hm⟩ := Nat.mem_divisors.mp hr
    have hrp : 0 < r := Nat.pos_of_mem_divisors hr
    by_cases hr2 : 2 ≤ r
    · have hlp : 0 < m/r := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd) hrp
      have hmul : (r : ℝ) * ((m/r : ℕ) : ℝ) = (m : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hrp)
      have hl0 : ((m/r : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hlp)
      simp only [diagonalPrimeTerm, if_pos hr2, Nat.mul_div_cancel' hdvd,
        dyadicHarmonicWeight]
      rw [← hmul]
      field_simp
    · have hr1 : r = 1 := by omega
      subst r
      simp [diagonalPrimeTerm, ArithmeticFunction.vonMangoldt_apply_one]
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_div, ← Finset.sum_mul, ← Finset.mul_sum]
  rfl

private theorem diagonal_prime_fiber (m : ℕ) :
    (∑' p : {p : ℕ × ℕ // p.1 * p.2 = m}, diagonalPrimeTerm p.1.1 p.1.2) =
      factorialCriticalPrimeHarmonicCharge m * factorialCriticalHarmonicDefect m /
        (m : ℝ) ^ 4 := by
  by_cases hm : m = 0
  · subst m
    have hz (p : {p : ℕ × ℕ // p.1 * p.2 = 0}) : diagonalPrimeTerm p.1.1 p.1.2 = 0 := by
      rcases Nat.mul_eq_zero.mp p.2 with h | h
      · simp [diagonalPrimeTerm, h]
      · simp [diagonalPrimeTerm, h, dyadicHarmonicWeight_zero]
    simp only [hz, tsum_zero, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, div_zero]
  let e : {p : ℕ × ℕ // p.1 * p.2 = m} ≃ {p // p ∈ m.divisorsAntidiagonal} :=
    Equiv.subtypeEquiv (Equiv.refl (ℕ × ℕ)) (by simp [Nat.mem_divisorsAntidiagonal, hm])
  have he : (∑' p : {p // p ∈ m.divisorsAntidiagonal}, diagonalPrimeTerm p.1.1 p.1.2) =
      (∑' p : {p : ℕ × ℕ // p.1 * p.2 = m}, diagonalPrimeTerm p.1.1 p.1.2) :=
    e.symm.tsum_eq (fun p => diagonalPrimeTerm p.1.1 p.1.2)
  rw [← he, tsum_fintype]
  exact (Finset.sum_coe_sort m.divisorsAntidiagonal
    (fun p => diagonalPrimeTerm p.1 p.2)).trans (diagonal_prime_finite_fiber m)

private theorem diagonal_prime_hasSum :
    HasSum (fun m : ℕ => factorialCriticalPrimeHarmonicCharge m *
      factorialCriticalHarmonicDefect m / (m : ℝ) ^ 4)
      (∑' p : ℕ × ℕ, diagonalPrimeTerm p.1 p.2) := by
  have h := diagonal_prime_joint_summable.hasSum.tsum_fiberwise
    (fun p : ℕ × ℕ => p.1 * p.2)
  exact h.congr_fun (fun m => (diagonal_prime_fiber m).symm)

/-- Absolute convergence of the complete prime limit after regrouping by harmonic. -/
theorem summable_factorialCriticalPrimeHarmonicCharge :
    Summable (fun m : ℕ => |factorialCriticalPrimeHarmonicCharge m *
      factorialCriticalHarmonicDefect m / (m : ℝ) ^ 4|) :=
  diagonal_prime_hasSum.summable.abs

/-- Every prime power and harmonic is retained in the exact native divisor diagonal. -/
theorem factorialCriticalPrimeLimit_eq_harmonic_diagonal :
    factorialCriticalPrimeLimit = (4 / Real.pi ^ 4) *
      ∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m *
        factorialCriticalHarmonicDefect m / (m : ℝ) ^ 4 := by
  have hrow (r : ℕ) :
      (if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
        factorialCriticalCorrelationLimit r else 0) =
      (4 / Real.pi ^ 4) * ∑' l : ℕ, diagonalPrimeTerm r l := by
    by_cases hr : 2 ≤ r
    · have heq : (fun l => diagonalPrimeTerm r l) =
          (fun l => ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ)) *
            (dyadicHarmonicWeight (r*l) * dyadicHarmonicWeight l *
              factorialCriticalHarmonicDefect (r*l))) := by
        funext l
        simp only [diagonalPrimeTerm, if_pos hr]
        ring
      rw [if_pos hr, heq, tsum_mul_left]
      unfold factorialCriticalCorrelationLimit
      ring
    · simp [hr, diagonalPrimeTerm]
  unfold factorialCriticalPrimeLimit
  simp_rw [hrow]
  rw [tsum_mul_left, ← diagonal_prime_joint_summable.tsum_prod,
    diagonal_prime_hasSum.tsum_eq]

private theorem diagonal_chi_divisor (m r : ℕ) (hr : r ∈ m.divisors)
    (hm : m % 4 ≠ 0) :
    dyadicHarmonicChi m * dyadicHarmonicChi (m/r) = dyadicHarmonicChi r := by
  let q := m/r
  have hmul : r*q = m := Nat.mul_div_cancel' (Nat.mem_divisors.mp hr).1
  have hχ : dyadicHarmonicChi m = dyadicHarmonicChi (r*q) := congrArg _ hmul.symm
  have hmod : (r*q) % 4 ≠ 0 := by simpa only [hmul] using hm
  change dyadicHarmonicChi m * dyadicHarmonicChi q = dyadicHarmonicChi r
  rw [hχ]
  have hr2 : r % 2 = (r % 4) % 2 := by omega
  have hq2 : q % 2 = (q % 4) % 2 := by omega
  have hr4 := Nat.mod_lt r (by norm_num : 0 < 4)
  have hq4 := Nat.mod_lt q (by norm_num : 0 < 4)
  interval_cases hR : r % 4 <;> interval_cases hQ : q % 4 <;>
    norm_num [Nat.mul_mod, hR, hQ] at hmod <;>
    norm_num [dyadicHarmonicChi, Nat.mul_mod, hr2, hq2, hR, hQ]

private def diagonalSignedCharge (r : ℕ) : ℝ :=
  (r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * dyadicHarmonicChi r

private theorem diagonal_charge_eq_signed_sum (m : ℕ) (hm : m % 4 ≠ 0) :
    factorialCriticalPrimeHarmonicCharge m = ∑ r ∈ m.divisors, diagonalSignedCharge r := by
  unfold factorialCriticalPrimeHarmonicCharge
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  calc dyadicHarmonicChi m *
        ((r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) * dyadicHarmonicChi (m/r)) =
      ((r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ)) *
        (dyadicHarmonicChi m * dyadicHarmonicChi (m/r)) := by ring
    _ = diagonalSignedCharge r := by rw [diagonal_chi_divisor m r hr hm]; rfl

private theorem diagonal_even_vonMangoldt_zero (r : ℕ) (hr : r ≠ 2)
    (hodd : ¬ r % 2 = 1) (hfour : r % 4 ≠ 0) :
    (ArithmeticFunction.vonMangoldt r : ℝ) = 0 := by
  apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
  intro hpow
  have hr2 : 2 < r := by have h := hpow.two_le; omega
  have h4 : ¬ 4 ∣ r := by
    intro h
    exact hfour (Nat.mod_eq_zero_of_dvd h)
  obtain ⟨p, hp, hpd, hpodd⟩ :=
    (Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hr2).resolve_left h4
  obtain ⟨q, _, hq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
  have h2dvd : 2 ∣ r := Nat.dvd_of_mod_eq_zero (by omega)
  have hpq := hq p ⟨hp, hpd⟩
  have h2q := hq 2 ⟨Nat.prime_two, h2dvd⟩
  have hp3 := hp.odd_iff.mp hpodd
  omega

private theorem diagonal_signed_nonneg (r : ℕ) (hr : r ≠ 2) :
    0 ≤ diagonalSignedCharge r := by
  by_cases hodd : r % 2 = 1
  · simp only [diagonalSignedCharge, dyadicHarmonicChi, if_pos hodd, mul_one]
    exact mul_nonneg (Nat.cast_nonneg r) ArithmeticFunction.vonMangoldt_nonneg
  · by_cases hfour : r % 4 = 0
    · have htwo : ¬r % 4 = 2 := by omega
      simp [diagonalSignedCharge, dyadicHarmonicChi, hodd, htwo]
    · simp [diagonalSignedCharge, diagonal_even_vonMangoldt_zero r hr hodd hfour]

private theorem diagonal_signed_two : diagonalSignedCharge 2 = -2 * Real.log 2 := by
  norm_num [diagonalSignedCharge, dyadicHarmonicChi,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

private theorem diagonal_charge_four_zero (m : ℕ) (hm : m % 4 = 0) :
    factorialCriticalPrimeHarmonicCharge m = 0 := by
  have hodd : ¬m % 2 = 1 := by omega
  simp [factorialCriticalPrimeHarmonicCharge, dyadicHarmonicChi, hodd, hm]

private theorem diagonal_charge_one : factorialCriticalPrimeHarmonicCharge 1 = 0 := by
  simp [factorialCriticalPrimeHarmonicCharge]

/-- Harmonic two is the sole negative coefficient; its exact charge is `-2 log 2`. -/
theorem factorialCriticalPrimeHarmonicCharge_two :
    factorialCriticalPrimeHarmonicCharge 2 = -2 * Real.log 2 := by
  have hdiv : (2 : ℕ).divisors = {1,2} := by decide
  norm_num [factorialCriticalPrimeHarmonicCharge, hdiv, dyadicHarmonicChi,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

private theorem diagonal_charge_positive (m : ℕ) (hm : 2 < m) (hfour : m % 4 ≠ 0) :
    0 < factorialCriticalPrimeHarmonicCharge m := by
  have h4 : ¬4 ∣ m := by intro h; exact hfour (Nat.mod_eq_zero_of_dvd h)
  obtain ⟨p, hp, hpd, hpodd⟩ :=
    (Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hm).resolve_left h4
  have hp3 := hp.odd_iff.mp hpodd
  have hp2 : p ≠ 2 := by omega
  have hpmod : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have hpterm : diagonalSignedCharge p = (p : ℝ) * Real.log (p : ℝ) := by
    simp [diagonalSignedCharge, ArithmeticFunction.vonMangoldt_apply_prime hp,
      dyadicHarmonicChi, hpmod]
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogp : Real.log (2 : ℝ) < Real.log (p : ℝ) :=
    Real.log_lt_log (by norm_num) (by exact_mod_cast (show 2 < p by omega))
  have hpos : 2 * Real.log 2 < diagonalSignedCharge p := by
    rw [hpterm]
    exact (mul_lt_mul_of_pos_left hlogp (by norm_num : (0 : ℝ) < 2)).trans_le
      (mul_le_mul_of_nonneg_right (by exact_mod_cast (show 2 ≤ p by omega))
        (le_of_lt (hlog2.trans hlogp)))
  have hpmem : p ∈ m.divisors := Nat.mem_divisors.mpr ⟨hpd, by omega⟩
  rw [diagonal_charge_eq_signed_sum m hfour]
  by_cases htwo : 2 ∈ m.divisors
  · have hsum : diagonalSignedCharge p ≤
        ∑ r ∈ m.divisors.erase 2, diagonalSignedCharge r :=
      Finset.single_le_sum
        (fun r hr => diagonal_signed_nonneg r (Finset.mem_erase.mp hr).1)
        (Finset.mem_erase.mpr ⟨hp2, hpmem⟩)
    have he := Finset.sum_erase_add m.divisors diagonalSignedCharge htwo
    rw [diagonal_signed_two] at he
    linarith
  · have hsum : diagonalSignedCharge p ≤ ∑ r ∈ m.divisors, diagonalSignedCharge r :=
      Finset.single_le_sum (fun r hr => diagonal_signed_nonneg r (by
        intro h; subst r; exact htwo hr)) hpmem
    exact (lt_trans (by positivity : 0 < 2 * Real.log (2 : ℝ)) hpos).trans_le hsum

/-- Complete sign classification of the arithmetic diagonal of the actual critical prime limit. -/
theorem factorialCriticalPrimeHarmonicCharge_sign (m : ℕ) :
    (factorialCriticalPrimeHarmonicCharge m < 0 ↔ m = 2) ∧
    (factorialCriticalPrimeHarmonicCharge m = 0 ↔ m = 1 ∨ m % 4 = 0) ∧
    (0 < factorialCriticalPrimeHarmonicCharge m ↔ 2 < m ∧ m % 4 ≠ 0) := by
  have hzero : factorialCriticalPrimeHarmonicCharge 0 = 0 := diagonal_charge_four_zero 0 rfl
  have htwo : factorialCriticalPrimeHarmonicCharge 2 < 0 := by
    rw [factorialCriticalPrimeHarmonicCharge_two]
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    nlinarith
  have hneg : factorialCriticalPrimeHarmonicCharge m < 0 ↔ m = 2 := by
    constructor
    · intro h
      by_contra hne
      by_cases h4 : m % 4 = 0
      · rw [diagonal_charge_four_zero m h4] at h; linarith
      by_cases hm : 2 < m
      · have hp := diagonal_charge_positive m hm h4; linarith
      have hm1 : m = 1 := by omega
      subst m
      rw [diagonal_charge_one] at h
      linarith
    · rintro rfl
      exact htwo
  have hpos : 0 < factorialCriticalPrimeHarmonicCharge m ↔ 2 < m ∧ m % 4 ≠ 0 := by
    constructor
    · intro h
      have hm0 : m ≠ 0 := by intro hm; subst m; linarith
      have hm1 : m ≠ 1 := by intro hm; subst m; rw [diagonal_charge_one] at h; linarith
      have hm2 : m ≠ 2 := by intro hm; subst m; linarith
      refine ⟨by omega, ?_⟩
      intro h4
      rw [diagonal_charge_four_zero m h4] at h
      linarith
    · rintro ⟨hm, h4⟩
      exact diagonal_charge_positive m hm h4
  refine ⟨hneg, ?_, hpos⟩
  constructor
  · intro h
    by_cases h4 : m % 4 = 0
    · exact Or.inr h4
    have hm2 : ¬2 < m := by intro hm; have hp := hpos.mpr ⟨hm,h4⟩; linarith
    have hne2 : m ≠ 2 := by intro hm; subst m; linarith
    exact Or.inl (by omega)
  · rintro (rfl | h4)
    · exact diagonal_charge_one
    · exact diagonal_charge_four_zero m h4

end
end GaloisForLFunctions.ArithmeticPositivityTheory
