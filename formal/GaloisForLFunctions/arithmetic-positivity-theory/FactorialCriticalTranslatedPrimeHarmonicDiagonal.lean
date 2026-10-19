import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalTranslatedPrimeLimit
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeHarmonicDiagonal

/-! The complete critical prime form of a translated finite factorial pattern.
Absolute regrouping retains the existing native divisor charge and the exact
physical pattern mass. The limit is bounded in coefficient `ℓ²`; its individual
harmonic signs are rigid, while the sign of their total sum is left open. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

private def translatedDiagonalTerm (S : Finset ℕ) (b : ℕ → ℝ) (r l : ℕ) : ℝ :=
  if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
    dyadicHarmonicWeight (r*l) * dyadicHarmonicWeight l *
      factorialCriticalPatternHarmonicMass S b (r*l) else 0

private theorem translated_diagonal_term_bound (S : Finset ℕ) (b : ℕ → ℝ) (r l : ℕ) :
    ‖translatedDiagonalTerm S b r l‖ ≤
      ((4 * (∑ j ∈ S, b j ^ 2)) * envelopePrimeMajorant (3 / 2) r) * |dyadicHarmonicWeight l| := by
  by_cases hr : 2 ≤ r
  · by_cases hl : l = 0
    · simp [translatedDiagonalTerm, hl, dyadicHarmonicWeight_zero]
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
    have hJ : 0 ≤ factorialCriticalPatternHarmonicMass S b (r*l) ∧
        factorialCriticalPatternHarmonicMass S b (r*l) ≤ 4 * (∑ j ∈ S, b j ^ 2) :=
      ⟨factorialCriticalPatternHarmonicMass_nonneg S b _,
        factorialCriticalPatternHarmonicMass_le S b (Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hl))⟩
    simp only [translatedDiagonalTerm, if_pos hr, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hΛ hrp.le), abs_of_nonneg hJ.1,
      envelopePrimeMajorant, show (3 / 2 : ℝ) + 1 / 2 = 2 by norm_num,
      Real.rpow_two]
    calc (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
          |dyadicHarmonicWeight (r*l)| * |dyadicHarmonicWeight l| *
          factorialCriticalPatternHarmonicMass S b (r*l)
        ≤ ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
          (1 / (r : ℝ)) * |dyadicHarmonicWeight l|) * (4 * (∑ j ∈ S, b j ^ 2)) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hw (div_nonneg hΛ hrp.le)) (abs_nonneg _))
            hJ.2 hJ.1 (by positivity)
      _ = _ := by ring
  · simp [translatedDiagonalTerm, envelopePrimeMajorant, hr]

private theorem translated_diagonal_majorant_summable (S : Finset ℕ) (b : ℕ → ℝ) :
    Summable (fun p : ℕ × ℕ =>
      ((4 * (∑ j ∈ S, b j ^ 2)) * envelopePrimeMajorant (3 / 2) p.1) *
        |dyadicHarmonicWeight p.2|) := by
  have hE : 0 ≤ (4 : ℝ) * (∑ j ∈ S, b j ^ 2) := by positivity
  have hs : Summable (fun r : ℕ =>
      (4 * (∑ j ∈ S, b j ^ 2)) * envelopePrimeMajorant (3 / 2) r) :=
    summable_canonicalPrimeMajorant.mul_left _
  exact hs.mul_of_nonneg summable_abs_dyadicHarmonicWeight
    (fun r => mul_nonneg hE (envelopePrimeMajorant_nonneg (3 / 2) r))
    (fun l => abs_nonneg (dyadicHarmonicWeight l))

private theorem translated_diagonal_joint_summable (S : Finset ℕ) (b : ℕ → ℝ) :
    Summable (fun p : ℕ × ℕ => translatedDiagonalTerm S b p.1 p.2) :=
  (translated_diagonal_majorant_summable S b).of_norm_bounded
    (fun p => translated_diagonal_term_bound S b p.1 p.2)

private theorem translated_diagonal_finite_fiber (S : Finset ℕ) (b : ℕ → ℝ) (m : ℕ) :
    (∑ p ∈ m.divisorsAntidiagonal, translatedDiagonalTerm S b p.1 p.2) =
      factorialCriticalPrimeHarmonicCharge m * factorialCriticalPatternHarmonicMass S b m /
        (m : ℝ) ^ 4 := by
  rw [Nat.sum_divisorsAntidiagonal]
  have hterm (r : ℕ) (hr : r ∈ m.divisors) :
      translatedDiagonalTerm S b r (m/r) =
        (dyadicHarmonicChi m * ((r : ℝ) * (ArithmeticFunction.vonMangoldt r : ℝ) *
          dyadicHarmonicChi (m/r))) * factorialCriticalPatternHarmonicMass S b m / (m : ℝ) ^ 4 := by
    obtain ⟨hdvd, hm⟩ := Nat.mem_divisors.mp hr
    have hrp : 0 < r := Nat.pos_of_mem_divisors hr
    by_cases hr2 : 2 ≤ r
    · have hlp : 0 < m/r := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd) hrp
      have hmul : (r : ℝ) * ((m/r : ℕ) : ℝ) = (m : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hrp)
      have hl0 : ((m/r : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hlp)
      simp only [translatedDiagonalTerm, if_pos hr2, Nat.mul_div_cancel' hdvd,
        dyadicHarmonicWeight]
      rw [← hmul]
      field_simp
    · have hr1 : r = 1 := by omega
      subst r
      simp [translatedDiagonalTerm, ArithmeticFunction.vonMangoldt_apply_one]
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_div, ← Finset.sum_mul, ← Finset.mul_sum]
  rfl

private theorem translated_diagonal_fiber (S : Finset ℕ) (b : ℕ → ℝ) (m : ℕ) :
    (∑' p : {p : ℕ × ℕ // p.1 * p.2 = m}, translatedDiagonalTerm S b p.1.1 p.1.2) =
      factorialCriticalPrimeHarmonicCharge m * factorialCriticalPatternHarmonicMass S b m /
        (m : ℝ) ^ 4 := by
  by_cases hm : m = 0
  · subst m
    have hz (p : {p : ℕ × ℕ // p.1 * p.2 = 0}) : translatedDiagonalTerm S b p.1.1 p.1.2 = 0 := by
      rcases Nat.mul_eq_zero.mp p.2 with h | h
      · simp [translatedDiagonalTerm, h]
      · simp [translatedDiagonalTerm, h, dyadicHarmonicWeight_zero]
    simp only [hz, tsum_zero, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, div_zero]
  let e : {p : ℕ × ℕ // p.1 * p.2 = m} ≃ {p // p ∈ m.divisorsAntidiagonal} :=
    Equiv.subtypeEquiv (Equiv.refl (ℕ × ℕ)) (by simp [Nat.mem_divisorsAntidiagonal, hm])
  have he : (∑' p : {p // p ∈ m.divisorsAntidiagonal}, translatedDiagonalTerm S b p.1.1 p.1.2) =
      (∑' p : {p : ℕ × ℕ // p.1 * p.2 = m}, translatedDiagonalTerm S b p.1.1 p.1.2) :=
    e.symm.tsum_eq (fun p => translatedDiagonalTerm S b p.1.1 p.1.2)
  rw [← he, tsum_fintype]
  exact (Finset.sum_coe_sort m.divisorsAntidiagonal
    (fun p => translatedDiagonalTerm S b p.1 p.2)).trans (translated_diagonal_finite_fiber S b m)

private theorem translated_diagonal_hasSum (S : Finset ℕ) (b : ℕ → ℝ) :
    HasSum (fun m : ℕ => factorialCriticalPrimeHarmonicCharge m *
      factorialCriticalPatternHarmonicMass S b m / (m : ℝ) ^ 4)
      (∑' p : ℕ × ℕ, translatedDiagonalTerm S b p.1 p.2) := by
  have h := (translated_diagonal_joint_summable S b).hasSum.tsum_fiberwise
    (fun p : ℕ × ℕ => p.1 * p.2)
  exact h.congr_fun (fun m => (translated_diagonal_fiber S b m).symm)

/-- Absolute convergence of the complete prime limit after regrouping by harmonic. -/
theorem summable_factorialCriticalTranslatedPrimeHarmonicDiagonal (S : Finset ℕ) (b : ℕ → ℝ) :
    Summable (fun m : ℕ => |factorialCriticalPrimeHarmonicCharge m *
      factorialCriticalPatternHarmonicMass S b m / (m : ℝ) ^ 4|) :=
  (translated_diagonal_hasSum S b).summable.abs

/-- Every prime power and harmonic is retained in the exact native divisor diagonal. -/
theorem factorialCriticalTranslatedPrimeLimit_eq_harmonic_diagonal (S : Finset ℕ) (b : ℕ → ℝ) :
    factorialCriticalTranslatedPrimeLimit S b = (4 / Real.pi ^ 4) *
      ∑' m : ℕ, factorialCriticalPrimeHarmonicCharge m *
        factorialCriticalPatternHarmonicMass S b m / (m : ℝ) ^ 4 := by
  have hrow (r : ℕ) :
      (if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
        factorialCriticalTranslatedCorrelationLimit S b r else 0) =
      (4 / Real.pi ^ 4) * ∑' l : ℕ, translatedDiagonalTerm S b r l := by
    by_cases hr : 2 ≤ r
    · have heq : (fun l => translatedDiagonalTerm S b r l) =
          (fun l => ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ)) *
            (dyadicHarmonicWeight (r*l) * dyadicHarmonicWeight l *
              factorialCriticalPatternHarmonicMass S b (r*l))) := by
        funext l
        simp only [translatedDiagonalTerm, if_pos hr]
        ring
      rw [if_pos hr, heq, tsum_mul_left]
      unfold factorialCriticalTranslatedCorrelationLimit
      ring
    · simp [hr, translatedDiagonalTerm]
  unfold factorialCriticalTranslatedPrimeLimit
  simp_rw [hrow]
  rw [tsum_mul_left, ← (translated_diagonal_joint_summable S b).tsum_prod,
    (translated_diagonal_hasSum S b).tsum_eq]


/-- The complete limiting prime form is bounded in coefficient `ℓ²`, independently of support. -/
theorem abs_factorialCriticalTranslatedPrimeLimit_le_l2 (S : Finset ℕ) (b : ℕ → ℝ) :
    |factorialCriticalTranslatedPrimeLimit S b| ≤
      (16 / Real.pi ^ 4) * canonicalPrimeMajorantConstant *
        (∑' l : ℕ, |dyadicHarmonicWeight l|) * (∑ j ∈ S, b j ^ 2) := by
  have hB := translated_diagonal_majorant_summable S b
  have hj := translated_diagonal_joint_summable S b
  have hbound := (norm_tsum_le_tsum_norm hj.norm).trans
    (hj.norm.tsum_le_tsum (fun p => translated_diagonal_term_bound S b p.1 p.2) hB)
  have hsum :
      (∑' p : ℕ × ℕ, ((4 * (∑ j ∈ S, b j ^ 2)) * envelopePrimeMajorant (3 / 2) p.1) *
        |dyadicHarmonicWeight p.2|) =
      4 * (∑ j ∈ S, b j ^ 2) * canonicalPrimeMajorantConstant *
        (∑' l : ℕ, |dyadicHarmonicWeight l|) := by
    rw [hB.tsum_prod]
    simp only [tsum_mul_left, tsum_mul_right, canonicalPrimeMajorantConstant]
  rw [hsum, Real.norm_eq_abs] at hbound
  rw [factorialCriticalTranslatedPrimeLimit_eq_harmonic_diagonal,
    (translated_diagonal_hasSum S b).tsum_eq, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (4 : ℝ) / Real.pi ^ 4)]
  calc (4 / Real.pi ^ 4) * |∑' p : ℕ × ℕ, translatedDiagonalTerm S b p.1 p.2|
      ≤ (4 / Real.pi ^ 4) * (4 * (∑ j ∈ S, b j ^ 2) * canonicalPrimeMajorantConstant *
          (∑' l : ℕ, |dyadicHarmonicWeight l|)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

/-- Every nonzero pattern has the same arithmetic harmonic sign boundary. -/
theorem factorialCriticalTranslatedPrimeHarmonic_sign
    (S : Finset ℕ) (b : ℕ → ℝ) (m : ℕ) :
    (factorialCriticalPrimeHarmonicCharge m * factorialCriticalPatternHarmonicMass S b m /
        (m : ℝ)^4 < 0 ↔ m = 2 ∧ ∃ j ∈ S, b j ≠ 0) ∧
    (factorialCriticalPrimeHarmonicCharge m * factorialCriticalPatternHarmonicMass S b m /
        (m : ℝ)^4 = 0 ↔ (∀ j ∈ S, b j = 0) ∨ m = 1 ∨ m % 4 = 0) ∧
    (0 < factorialCriticalPrimeHarmonicCharge m * factorialCriticalPatternHarmonicMass S b m /
        (m : ℝ)^4 ↔ (∃ j ∈ S, b j ≠ 0) ∧ 2 < m ∧ m % 4 ≠ 0) := by
  by_cases hm : m = 0
  · subst m
    norm_num
  have hmp : 0 < m := Nat.pos_of_ne_zero hm
  by_cases hz : ∀ j ∈ S, b j = 0
  · have hJ := (factorialCriticalPatternHarmonicMass_eq_zero_iff S b hmp).mpr hz
    have hn : ¬ (∃ j ∈ S, b j ≠ 0) := by
      rintro ⟨j, hj, hbj⟩
      exact hbj (hz j hj)
    simp [hJ, hn]
    exact Or.inl hz
  have hb : ∃ j ∈ S, b j ≠ 0 := by
    push Not at hz
    exact hz
  have hJ : 0 < factorialCriticalPatternHarmonicMass S b m :=
    (factorialCriticalPatternHarmonicMass_pos_iff S b hmp).mpr hb
  have hs : 0 < factorialCriticalPatternHarmonicMass S b m / (m : ℝ)^4 :=
    div_pos hJ (by positivity)
  have hneg : factorialCriticalPrimeHarmonicCharge m * factorialCriticalPatternHarmonicMass S b m /
      (m : ℝ)^4 < 0 ↔ factorialCriticalPrimeHarmonicCharge m < 0 := by
    rw [mul_div_assoc]
    simpa only [zero_mul] using
      (mul_lt_mul_iff_left₀ (b := factorialCriticalPrimeHarmonicCharge m) (c := (0 : ℝ)) hs)
  have hpos : 0 < factorialCriticalPrimeHarmonicCharge m * factorialCriticalPatternHarmonicMass S b m /
      (m : ℝ)^4 ↔ 0 < factorialCriticalPrimeHarmonicCharge m := by
    rw [mul_div_assoc]
    simpa only [zero_mul] using
      (mul_lt_mul_iff_left₀ (b := (0 : ℝ)) (c := factorialCriticalPrimeHarmonicCharge m) hs)
  have heq : factorialCriticalPrimeHarmonicCharge m * factorialCriticalPatternHarmonicMass S b m /
      (m : ℝ)^4 = 0 ↔ factorialCriticalPrimeHarmonicCharge m = 0 := by
    rw [mul_div_assoc, mul_eq_zero]
    simp only [ne_of_gt hs, or_false]
  rcases factorialCriticalPrimeHarmonicCharge_sign m with ⟨hAneg, hAzero, hApos⟩
  constructor
  · rw [hneg, hAneg]
    simp only [hb, and_true]
  constructor
  · rw [heq, hAzero]
    simp only [hz, false_or]
  · rw [hpos, hApos]
    simp only [hb, true_and]

end GaloisForLFunctions.ArithmeticPositivityTheory
