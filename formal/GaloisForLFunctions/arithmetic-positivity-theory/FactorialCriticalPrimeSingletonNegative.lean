import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeCumulativeCharge
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalHarmonicFiniteBounds
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalHarmonicTaylorBounds
import GaloisForLFunctions.RHTower.XiRadialJensenMassCentralCurvature
import GaloisForLFunctions.HTGeometry.LogLinearTailIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SumIntegralComparisons

/-!
# A negative singleton for the complete critical prime form

The unique negative harmonic is compared with every positive harmonic and the
whole infinite remainder. Exact composite charges retain their subtractions.
The resulting native prime limit is strictly negative; the full Weil form
subtracts this prime channel, so its sign is a separate question.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false


private theorem prime_log_bounds :
    Real.log 3 ≤ (8/5) * Real.log 2 ∧
    Real.log 5 ≤ (7/3) * Real.log 2 ∧
    Real.log 7 ≤ (17/6) * Real.log 2 ∧
    Real.log 11 ≤ (7/2) * Real.log 2 ∧
    Real.log 13 ≤ (15/4) * Real.log 2 ∧
    Real.log 17 ≤ (25/6) * Real.log 2 ∧
    Real.log 19 ≤ (13/3) * Real.log 2 ∧
    (2/3 : ℝ) ≤ Real.log 2 := by
  have h3 := Real.log_le_log (by norm_num : 0 < (3 : ℝ)^5)
    (by norm_num : (3 : ℝ)^5 ≤ 2^8)
  have h5 := Real.log_le_log (by norm_num : 0 < (5 : ℝ)^3)
    (by norm_num : (5 : ℝ)^3 ≤ 2^7)
  have h7 := Real.log_le_log (by norm_num : 0 < (7 : ℝ)^6)
    (by norm_num : (7 : ℝ)^6 ≤ 2^17)
  have h11 := Real.log_le_log (by norm_num : 0 < (11 : ℝ)^2)
    (by norm_num : (11 : ℝ)^2 ≤ 2^7)
  have h13 := Real.log_le_log (by norm_num : 0 < (13 : ℝ)^4)
    (by norm_num : (13 : ℝ)^4 ≤ 2^15)
  have h17 := Real.log_le_log (by norm_num : 0 < (17 : ℝ)^6)
    (by norm_num : (17 : ℝ)^6 ≤ 2^25)
  have h19 := Real.log_le_log (by norm_num : 0 < (19 : ℝ)^3)
    (by norm_num : (19 : ℝ)^3 ≤ 2^13)
  simp only [Real.log_pow, Nat.cast_ofNat] at h3 h5 h7 h11 h13 h17 h19
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith [Real.log_two_gt_d9]

private theorem inverse_cube_integrable :
    IntegrableOn (fun x : ℝ => 1 / x^3) (Ioi (19 : ℝ)) := by
  apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 19)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := le_trans (by norm_num : (0 : ℝ) ≤ 19) hx.le
  rw [Real.rpow_neg hx0]
  simpa only [Nat.cast_ofNat, one_div] using
    congrArg (fun t : ℝ => t⁻¹) (Real.rpow_natCast x 3)

private theorem inverse_cube_integral :
    (∫ x : ℝ in Ioi (19 : ℝ), 1 / x^3) = 1/722 := by
  calc
    _ = ∫ x : ℝ in Ioi (19 : ℝ), x^(-3 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := le_trans (by norm_num : (0 : ℝ) ≤ 19) hx.le
      rw [Real.rpow_neg hx0]
      simpa only [Nat.cast_ofNat, one_div] using
        (congrArg (fun t : ℝ => t⁻¹) (Real.rpow_natCast x 3)).symm
    _ = 1/722 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num : (0 : ℝ) < 19)]
      norm_num

private theorem log_cube_integrable :
    IntegrableOn (fun x : ℝ => Real.log x / x^3) (Ioi (19 : ℝ)) := by
  have hsub := RHTower.integrableOn_log_sub_div_cube (by norm_num : (0 : ℝ) < 19)
  have hc := inverse_cube_integrable.const_mul (Real.log 19)
  have heq : (fun x : ℝ => Real.log x / x^3) =
      (fun x : ℝ => (Real.log x - Real.log 19) / x^3 + Real.log 19 * (1 / x^3)) := by
    funext x
    ring
  rw [heq]
  exact hsub.add hc

private theorem log_cube_integral :
    (∫ x : ℝ in Ioi (19 : ℝ), Real.log x / x^3) = (Real.log 19 + 1/2) / 722 := by
  have hsub := RHTower.integrableOn_log_sub_div_cube (by norm_num : (0 : ℝ) < 19)
  have hc := inverse_cube_integrable.const_mul (Real.log 19)
  have hsplit : (∫ x : ℝ in Ioi (19 : ℝ), Real.log x / x^3) =
      (∫ x : ℝ in Ioi (19 : ℝ), (Real.log x - Real.log 19) / x^3) +
      Real.log 19 * (1/722) := by
    rw [← inverse_cube_integral, ← integral_const_mul, ← integral_add hsub hc]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  have hlogdiv : (∫ x : ℝ in Ioi (19 : ℝ), (Real.log x - Real.log 19) / x^3) =
      ∫ x : ℝ in Ioi (19 : ℝ), Real.log (x/19) / x^3 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := lt_trans (by norm_num : (0 : ℝ) < 19) hx
    rw [Real.log_div hxpos.ne' (by norm_num)]
  rw [hsplit, hlogdiv, RHTower.integral_Ioi_log_div_cube (by norm_num : (0 : ℝ) < 19)]
  ring

private theorem log_cube_antitone :
    AntitoneOn (fun x : ℝ => Real.log x / x^3) (Ici (19 : ℝ)) := by
  intro a ha b hb hab
  have hapos : 0 < a := by change 19 ≤ a at ha; linarith
  have hbpos : 0 < b := hapos.trans_le hab
  have he19 : Real.exp 1 ≤ (19 : ℝ) := le_trans Real.exp_one_lt_three.le (by norm_num)
  have hdiv := HTGeometry.antitoneOn_logLin_div_sq (he19.trans ha) (he19.trans hb) hab
  have hinv := one_div_le_one_div_of_le hapos hab
  have hp := mul_le_mul hdiv hinv (one_div_nonneg.mpr hbpos.le)
    (div_nonneg (Real.log_nonneg (by change 19 ≤ a at ha; linarith)) (sq_nonneg a))
  convert hp using 1 <;> field_simp

private theorem log_cube_nonneg :
    ∀ x ∈ Ioi (19 : ℝ), 0 ≤ Real.log x / x^3 := by
  intro x hx
  exact div_nonneg (Real.log_nonneg (by change 19 < x at hx; linarith))
    (by change 19 < x at hx; positivity)

private theorem criticalPrimeLogTail_twenty_le :
    (∑' m : ℕ, Real.log ((m+20 : ℕ) : ℝ) / ((m+20 : ℕ) : ℝ)^3) ≤
      (61/8664) * Real.log 2 := by
  have h := AntitoneOn.tsum_comp_add_le_integral
    (f := fun x : ℝ => Real.log x / x^3) 19 log_cube_antitone
    log_cube_integrable log_cube_nonneg
  norm_num only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_ofNat] at h
  rw [log_cube_integral] at h
  rcases prime_log_bounds with ⟨_, _, _, _, _, _, h19, h2⟩
  linarith

private theorem summable_criticalPrimeLogCube :
    Summable (fun m : ℕ => Real.log (m : ℝ) / (m : ℝ)^3) :=
  AntitoneOn.summable_of_integrableOn_Ioi
    (f := fun x : ℝ => Real.log x / x^3) (N := 19) log_cube_antitone
    log_cube_integrable log_cube_nonneg

private theorem composite_charges :
    factorialCriticalPrimeHarmonicCharge 6 = 3 * Real.log 3 - 2 * Real.log 2 ∧
    factorialCriticalPrimeHarmonicCharge 9 = 12 * Real.log 3 ∧
    factorialCriticalPrimeHarmonicCharge 10 = 5 * Real.log 5 - 2 * Real.log 2 ∧
    factorialCriticalPrimeHarmonicCharge 14 = 7 * Real.log 7 - 2 * Real.log 2 ∧
    factorialCriticalPrimeHarmonicCharge 15 = 3 * Real.log 3 + 5 * Real.log 5 ∧
    factorialCriticalPrimeHarmonicCharge 18 = 12 * Real.log 3 - 2 * Real.log 2 := by
  have d6 : (6 : ℕ).divisors = {1,2,3,6} := by decide
  have d9 : (9 : ℕ).divisors = {1,3,9} := by decide
  have d10 : (10 : ℕ).divisors = {1,2,5,10} := by decide
  have d14 : (14 : ℕ).divisors = {1,2,7,14} := by decide
  have d15 : (15 : ℕ).divisors = {1,3,5,15} := by decide
  have d18 : (18 : ℕ).divisors = {1,2,3,6,9,18} := by decide
  have v2 := ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)
  have v3 := ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 3)
  have v5 := ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 5)
  have v7 := ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 7)
  norm_num only [Nat.cast_ofNat] at v2 v3 v5 v7
  have v9 : (ArithmeticFunction.vonMangoldt 9 : ℝ) = Real.log 3 := by
    rw [show (9 : ℕ) = 3^2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), v3]
  have v6 : (ArithmeticFunction.vonMangoldt 6 : ℝ) = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (by decide)
  have v10 : (ArithmeticFunction.vonMangoldt 10 : ℝ) = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (by decide)
  have v14 : (ArithmeticFunction.vonMangoldt 14 : ℝ) = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (by decide)
  have v15 : (ArithmeticFunction.vonMangoldt 15 : ℝ) = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro h
    obtain ⟨p, _, hu⟩ := isPrimePow_iff_unique_prime_dvd.mp h
    have h3 := hu 3 ⟨by norm_num, by norm_num⟩
    have h5 := hu 5 ⟨by norm_num, by norm_num⟩
    omega
  have v18 : (ArithmeticFunction.vonMangoldt 18 : ℝ) = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [factorialCriticalPrimeHarmonicCharge, d6, d9, d10, d14, d15, d18,
      dyadicHarmonicChi, v2, v3, v5, v7, v9, v6, v10, v14, v15, v18] <;> ring

private def primeAtom (m : ℕ) : ℝ :=
  factorialCriticalPrimeHarmonicCharge m * factorialCriticalHarmonicDefect m / (m : ℝ)^4

private theorem prime_atom_le (m : ℕ) (c d : ℝ) (hm : m ≠ 2)
    (hc : factorialCriticalPrimeHarmonicCharge m ≤ c * Real.log 2)
    (hd : factorialCriticalHarmonicDefect m ≤ d) (hd0 : 0 ≤ d) :
    primeAtom m ≤ (c * d / (m : ℝ)^4) * Real.log 2 := by
  have hA : 0 ≤ factorialCriticalPrimeHarmonicCharge m :=
    le_of_not_gt (fun h => hm ((factorialCriticalPrimeHarmonicCharge_sign m).1.mp h))
  have h := (mul_le_mul_of_nonneg_left hd hA).trans
    (mul_le_mul_of_nonneg_right hc hd0)
  have hh := div_le_div_of_nonneg_right h (show 0 ≤ (m : ℝ)^4 by positivity)
  unfold primeAtom
  calc
    _ ≤ (c * Real.log 2 * d) / (m : ℝ)^4 := hh
    _ = (c * d / (m : ℝ)^4) * Real.log 2 := by ring

private theorem prime_atom_prime_le (p : ℕ) (c d : ℝ) (hp : p.Prime)
    (hodd : p % 2 = 1) (hc : Real.log p ≤ c * Real.log 2)
    (hd : factorialCriticalHarmonicDefect p ≤ d) (hd0 : 0 ≤ d) :
    primeAtom p ≤ (c * d / (p : ℝ)^3) * Real.log 2 := by
  have h := prime_atom_le p ((p : ℝ)*c) d
    (by intro heq; subst p; norm_num at hodd) ?_ hd hd0
  · have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    calc
      _ ≤ ((p : ℝ) * c * d / (p : ℝ)^4) * Real.log 2 := h
      _ = (c * d / (p : ℝ)^3) * Real.log 2 := by field_simp [hp0]
  · rw [factorialCriticalPrimeHarmonicCharge_odd_prime hp hodd]
    nlinarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg p)]

private theorem prime_atom_two_le : primeAtom 2 ≤ -(5/36) * Real.log 2 := by
  unfold primeAtom
  rw [factorialCriticalPrimeHarmonicCharge_two]
  have h := mul_le_mul_of_nonpos_left factorialCriticalHarmonicDefect_two_ge
    (show -2 * Real.log 2 ≤ 0 by nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])
  norm_num only [Nat.cast_ofNat] at *
  nlinarith only [h]

private theorem finite_prime_budget :
    (∑ m ∈ Finset.range 20, primeAtom m) ≤
      (-61/7220 - 1/390) * Real.log 2 := by
  rcases prime_log_bounds with ⟨l3, l5, l7, l11, l13, l17, l19, l2⟩
  rcases composite_charges with ⟨a6, a9, a10, a14, a15, a18⟩
  have h2 := prime_atom_two_le
  have h3 := prime_atom_prime_le 3 (8/5) (4/3) (by norm_num) (by norm_num)
    l3 factorialCriticalHarmonicDefect_three_le (by norm_num)
  have h5 := prime_atom_prime_le 5 (7/3) (4/3) (by norm_num) (by norm_num)
    l5 factorialCriticalHarmonicDefect_five_le (by norm_num)
  have h6 := prime_atom_le 6 (14/5) (7/6) (by norm_num)
    (by rw [a6]; linarith) factorialCriticalHarmonicDefect_six_le (by norm_num)
  have h7 := prime_atom_prime_le 7 (17/6) (7/6) (by norm_num) (by norm_num)
    l7 factorialCriticalHarmonicDefect_seven_le (by norm_num)
  have h9 := prime_atom_le 9 (96/5) 1 (by norm_num)
    (by rw [a9]; linarith) factorialCriticalHarmonicDefect_nine_le (by norm_num)
  have h10 := prime_atom_le 10 (29/3) 1 (by norm_num)
    (by rw [a10]; linarith) factorialCriticalHarmonicDefect_ten_le (by norm_num)
  have h11 := prime_atom_prime_le 11 (7/2) 1 (by norm_num) (by norm_num)
    l11 factorialCriticalHarmonicDefect_eleven_le (by norm_num)
  have h13 := prime_atom_prime_le 13 (15/4) (7/6) (by norm_num) (by norm_num)
    l13 factorialCriticalHarmonicDefect_thirteen_le (by norm_num)
  have h14 := prime_atom_le 14 (107/6) (7/6) (by norm_num)
    (by rw [a14]; linarith) factorialCriticalHarmonicDefect_fourteen_le (by norm_num)
  have h15 := prime_atom_le 15 (247/15) (7/6) (by norm_num)
    (by rw [a15]; linarith) factorialCriticalHarmonicDefect_fifteen_le (by norm_num)
  have h17 := prime_atom_prime_le 17 (25/6) (7/6) (by norm_num) (by norm_num)
    l17 factorialCriticalHarmonicDefect_seventeen_le (by norm_num)
  have h18 := prime_atom_le 18 (86/5) (7/6) (by norm_num)
    (by rw [a18]; linarith) factorialCriticalHarmonicDefect_eighteen_le (by norm_num)
  have h19 := prime_atom_prime_le 19 (13/3) (7/6) (by norm_num) (by norm_num)
    l19 (factorialCriticalHarmonicDefect_add_nineteen_le 0) (by norm_num)
  have hz (m : ℕ) (hm : m = 1 ∨ m % 4 = 0) : primeAtom m = 0 := by
    simp [primeAtom, (factorialCriticalPrimeHarmonicCharge_sign m).2.1.mpr hm]
  have hz0 := hz 0 (Or.inr (by norm_num))
  have hz1 := hz 1 (Or.inl rfl)
  have hz4 := hz 4 (Or.inr (by norm_num))
  have hz8 := hz 8 (Or.inr (by norm_num))
  have hz12 := hz 12 (Or.inr (by norm_num))
  have hz16 := hz 16 (Or.inr (by norm_num))
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, hz0, hz1, hz4, hz8,
    hz12, hz16, zero_add, add_zero]
  norm_num only [Nat.cast_ofNat] at h3 h5 h6 h7 h9 h10 h11 h13 h14 h15 h17 h18 h19
  linarith only [h2, h3, h5, h6, h7, h9, h10, h11, h13, h14, h15, h17, h18, h19, l2]

private theorem prime_atom_tail_bound (m : ℕ) :
    primeAtom (m+20) ≤ (6/5) *
      (Real.log ((m+20 : ℕ) : ℝ) / ((m+20 : ℕ) : ℝ)^3) := by
  let q := m+20
  have hq : (1 : ℝ) ≤ (q : ℝ) := by dsimp [q]; exact_mod_cast (show 1 ≤ m+20 by omega)
  have hq0 : (q : ℝ) ≠ 0 := by linarith
  have hJ := (factorialCriticalHarmonicDefect_bounds q).1
  have hA := (le_abs_self (factorialCriticalPrimeHarmonicCharge q)).trans
    (abs_factorialCriticalPrimeHarmonicCharge_le q)
  have hfirst := mul_le_mul_of_nonneg_right hA hJ
  have hsecond := mul_le_mul_of_nonneg_left (factorialCriticalHarmonicDefect_add_twenty_le m)
    (mul_nonneg (Nat.cast_nonneg q) (Real.log_nonneg hq))
  have hmul := hfirst.trans hsecond
  have hdiv := div_le_div_of_nonneg_right hmul (show 0 ≤ (q : ℝ)^4 by positivity)
  change primeAtom q ≤ (6/5) * (Real.log (q : ℝ) / (q : ℝ)^3)
  calc
    _ = factorialCriticalPrimeHarmonicCharge q * factorialCriticalHarmonicDefect q /
        (q : ℝ)^4 := rfl
    _ ≤ ((q : ℝ) * Real.log q * (6/5)) / (q : ℝ)^4 := hdiv
    _ = (6/5) * (Real.log (q : ℝ) / (q : ℝ)^3) := by field_simp [hq0]

private theorem summable_prime_atom : Summable primeAtom :=
  summable_abs_iff.mp summable_factorialCriticalPrimeHarmonicCharge

private theorem infinite_prime_budget :
    (∑' m : ℕ, primeAtom (m+20)) ≤ (61/7220) * Real.log 2 := by
  have hs : Summable (fun m : ℕ => primeAtom (m+20)) :=
    (summable_nat_add_iff 20).mpr summable_prime_atom
  have hl : Summable (fun m : ℕ => Real.log ((m+20 : ℕ) : ℝ) / ((m+20 : ℕ) : ℝ)^3) :=
    (summable_nat_add_iff 20).mpr summable_criticalPrimeLogCube
  have h := hs.tsum_le_tsum prime_atom_tail_bound (hl.mul_left (6/5))
  rw [tsum_mul_left] at h
  linarith [criticalPrimeLogTail_twenty_le]

/-- The full infinite harmonic sum has a strictly negative arithmetic margin. -/
theorem factorialCriticalPrimeHarmonicSum_negative_bound :
    (∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m *
      factorialCriticalHarmonicDefect m / (m : ℝ)^4) ≤ -(1/390) * Real.log 2 := by
  change (∑' m : ℕ, primeAtom m) ≤ -(1/390) * Real.log 2
  rw [← summable_prime_atom.sum_add_tsum_nat_add 20]
  linarith only [finite_prime_budget, infinite_prime_budget]

/-- The native complete prime limit is negative, with every harmonic retained. -/
theorem factorialCriticalPrimeLimit_negative_bound :
    factorialCriticalPrimeLimit ≤ (4 / Real.pi^4) * (-(1/390) * Real.log 2) := by
  rw [factorialCriticalPrimeLimit_eq_harmonic_diagonal]
  exact mul_le_mul_of_nonneg_left factorialCriticalPrimeHarmonicSum_negative_bound (by positivity)

/-- An unconditional sign for the complete singleton prime channel. -/
theorem factorialCriticalPrimeLimit_neg : factorialCriticalPrimeLimit < 0 := by
  apply lt_of_le_of_lt factorialCriticalPrimeLimit_negative_bound
  apply mul_neg_of_pos_of_neg (by positivity)
  exact mul_neg_of_neg_of_pos (by norm_num) (Real.log_pos (by norm_num))

/-- A singleton pattern scales the complete native prime limit by its coefficient square. -/
theorem factorialCriticalTranslatedPrimeLimit_singleton (j : ℕ) (b : ℕ → ℝ) :
    factorialCriticalTranslatedPrimeLimit {j} b = b j ^ 2 * factorialCriticalPrimeLimit := by
  rw [factorialCriticalTranslatedPrimeLimit_eq_harmonic_diagonal,
    factorialCriticalPrimeLimit_eq_harmonic_diagonal]
  simp_rw [factorialCriticalPatternHarmonicMass_singleton]
  have hsum : (∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m *
      (b j ^ 2 * factorialCriticalHarmonicDefect m) / (m : ℝ)^4) =
      b j ^ 2 * ∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m *
        factorialCriticalHarmonicDefect m / (m : ℝ)^4 := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    ring
  rw [hsum]
  ring

/-- An actual finite negative vector for the complete limiting critical prime form. -/
theorem factorialCriticalTranslatedPrimeLimit_singleton_negative (j : ℕ) :
    factorialCriticalTranslatedPrimeLimit {j} (fun _ => 1) < 0 := by
  simpa only [factorialCriticalTranslatedPrimeLimit_singleton, one_pow, one_mul] using
    factorialCriticalPrimeLimit_neg

end GaloisForLFunctions.ArithmeticPositivityTheory
