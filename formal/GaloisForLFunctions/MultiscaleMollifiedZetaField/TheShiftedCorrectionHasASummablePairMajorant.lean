import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShiftedSelbergCorrectionIsMultiplicative
import GaloisForLFunctions.RHTower.Sieve.SelbergEulerCorrectionCoefficientMass

/-!
# A summable pair majorant for shifted Euler corrections

Push the absolute triple-fibre masses onto coefficient pairs before taking
any signed sums. This gives a summable majorant for every retained shifted
coefficient, with a constant depending only on its normalized shift.
-/

open ArithmeticFunction Filter Set Topology
open RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private def correctionPairFiberEquiv {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    {x : ℕ × (ℕ × ℕ) // selbergCorrectionIndex x = (m, n)} ≃
      {r // r ∈ (Nat.gcd m n).divisors} where
  toFun x := by
    have hmEq : x.1.1 * x.1.2.1 = m := congrArg Prod.fst x.2
    have hnEq : x.1.1 * x.1.2.2 = n := congrArg Prod.snd x.2
    refine ⟨x.1.1, Nat.mem_divisors.mpr ⟨Nat.dvd_gcd ⟨x.1.2.1, hmEq.symm⟩
      ⟨x.1.2.2, hnEq.symm⟩, (Nat.gcd_pos_of_pos_left n hm).ne'⟩⟩
  invFun r := by
    have hrm : r.1 ∣ m := dvd_trans (Nat.dvd_of_mem_divisors r.2)
      (Nat.gcd_dvd_left m n)
    have hrn : r.1 ∣ n := dvd_trans (Nat.dvd_of_mem_divisors r.2)
      (Nat.gcd_dvd_right m n)
    refine ⟨(r.1, (m / r.1, n / r.1)), ?_⟩
    apply Prod.ext
    · exact Nat.mul_div_cancel' hrm
    · exact Nat.mul_div_cancel' hrn
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · have hmEq : x.1.1 * x.1.2.1 = m := congrArg Prod.fst x.2
        have hrpos : 0 < x.1.1 := by
          by_contra hr
          have : x.1.1 = 0 := by omega
          rw [this, zero_mul] at hmEq
          omega
        change m / x.1.1 = x.1.2.1
        apply Nat.div_eq_of_eq_mul_left hrpos
        calc
          m = x.1.1 * x.1.2.1 := hmEq.symm
          _ = x.1.2.1 * x.1.1 := Nat.mul_comm _ _
      · have hnEq : x.1.1 * x.1.2.2 = n := congrArg Prod.snd x.2
        have hrpos : 0 < x.1.1 := by
          by_contra hr
          have : x.1.1 = 0 := by omega
          rw [this, zero_mul] at hnEq
          omega
        change n / x.1.1 = x.1.2.2
        apply Nat.div_eq_of_eq_mul_left hrpos
        calc
          n = x.1.1 * x.1.2.2 := hnEq.symm
          _ = x.1.2.2 * x.1.1 := Nat.mul_comm _ _
  right_inv r := by
    apply Subtype.ext
    rfl

/-- Absolute fibre mass over a fixed coefficient pair. -/
def absoluteSelbergCorrectionCoeff (m n : ℕ) : ℝ :=
  if m = 0 ∨ n = 0 then 0 else
    ∑ r : {r // r ∈ (Nat.gcd m n).divisors},
      |selbergCorrectionWeight r.1 (m / r.1) (n / r.1)|

/-- The pair majorant is exactly the pushforward of the absolute fibre mass. -/
theorem absoluteSelbergCorrectionCoeff_eq_fibre (m n : ℕ) :
    absoluteSelbergCorrectionCoeff m n =
      summableFiberPushforward selbergCorrectionIndex
        (fun x => |selbergCorrectionTerm x|) (m, n) := by
  by_cases hm : m = 0
  · subst m
    simp only [absoluteSelbergCorrectionCoeff, true_or, if_true, summableFiberPushforward]
    symm
    calc
      _ = ∑' _ : {x : ℕ × (ℕ × ℕ) // selbergCorrectionIndex x = (0, n)}, (0 : ℝ) := by
        apply tsum_congr
        intro x
        rw [selbergCorrectionTerm_eq_zero_of_index_fst_zero
          (by simpa using congrArg Prod.fst x.2), abs_zero]
      _ = 0 := tsum_zero
  by_cases hn : n = 0
  · subst n
    simp only [absoluteSelbergCorrectionCoeff, or_true, if_true, summableFiberPushforward]
    symm
    calc
      _ = ∑' _ : {x : ℕ × (ℕ × ℕ) // selbergCorrectionIndex x = (m, 0)}, (0 : ℝ) := by
        apply tsum_congr
        intro x
        rw [selbergCorrectionTerm_eq_zero_of_index_snd_zero
          (by simpa using congrArg Prod.snd x.2), abs_zero]
      _ = 0 := tsum_zero
  · let e := correctionPairFiberEquiv (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)
    rw [absoluteSelbergCorrectionCoeff, if_neg (not_or_intro hm hn)]
    have he := e.symm.tsum_eq (fun x => |selbergCorrectionTerm x.1|)
    rw [tsum_fintype] at he
    exact he

/-- Absolute correction masses remain summable after the many-to-one pushforward. -/
theorem summable_absoluteSelbergCorrectionCoeff :
    Summable (fun mn : ℕ × ℕ => absoluteSelbergCorrectionCoeff mn.1 mn.2) := by
  have hw : Summable (fun x => |selbergCorrectionTerm x|) := by
    simpa only [selbergCorrectionTerm, Real.norm_eq_abs] using summable_selbergCorrectionWeight.norm
  exact (summable_summableFiberPushforward selbergCorrectionIndex _ hw).congr
    (fun mn => (absoluteSelbergCorrectionCoeff_eq_fibre mn.1 mn.2).symm)

theorem absoluteSelbergCorrectionCoeff_nonneg (m n : ℕ) :
    0 ≤ absoluteSelbergCorrectionCoeff m n := by
  unfold absoluteSelbergCorrectionCoeff
  split_ifs
  · exact le_rfl
  · exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Retained shifted coefficients are dominated by the absolute unshifted fibres. -/
theorem abs_shiftedSelbergCorrectionCoeff_le {N m n : ℕ} (hN : 1 < N)
    (C : ℝ) (hm : m ≤ N) (hn : n ≤ N) :
    |shiftedSelbergCorrectionCoeff (C / Real.log N) m n| ≤
      Real.exp (4 * |C|) * absoluteSelbergCorrectionCoeff m n := by
  classical
  by_cases hzero : m = 0 ∨ n = 0
  · simp only [shiftedSelbergCorrectionCoeff, absoluteSelbergCorrectionCoeff, if_pos hzero,
      abs_zero, mul_zero, le_refl]
  · simp only [shiftedSelbergCorrectionCoeff, absoluteSelbergCorrectionCoeff, if_neg hzero]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    exact abs_shiftedSelbergCorrectionWeight_le hN C r.1
      ((Nat.div_le_self _ _).trans hm) ((Nat.div_le_self _ _).trans hn)

/-- Each shifted coefficient depends continuously on its displacement. -/
theorem continuous_shiftedSelbergCorrectionCoeff (m n : ℕ) :
    Continuous (fun s : ℝ => shiftedSelbergCorrectionCoeff s m n) := by
  classical
  unfold shiftedSelbergCorrectionCoeff
  split_ifs
  · exact continuous_const
  · exact continuous_finset_sum _ (fun r _ =>
      continuous_shiftedSelbergCorrectionWeight r.1 (m / r.1) (n / r.1))

/-- Zero shift recovers the original correction coefficients. -/
theorem shiftedSelbergCorrectionCoeff_zero (m n : ℕ) :
    shiftedSelbergCorrectionCoeff 0 m n = selbergEulerCorrectionCoeff m n := by
  classical
  simp only [shiftedSelbergCorrectionCoeff, selbergEulerCorrectionCoeff,
    shiftedSelbergCorrectionWeight_zero]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
