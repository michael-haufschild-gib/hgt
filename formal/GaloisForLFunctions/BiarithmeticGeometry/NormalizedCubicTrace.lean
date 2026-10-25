import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The arithmetic cost of fixed-determinant cubic amplification

Cubing two roots and dividing each by their prime determinant preserves the
determinant. The transformed trace is integral only if the original trace is
divisible by that prime. Nonnegative degree-two point counts on both sides
then leave four nonzero small-prime cases and the zero trace.
-/

namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Integral normalized-cube traces with nonnegative degree-two point counts on both sides. -/
def NormalizedCubicTraceCondition (p : ℕ) (T U : ℤ) : Prop :=
  (p : ℤ) * U = T ^ 3 - 3 * p * T ∧
    T ^ 2 ≤ ((p : ℤ) + 1) ^ 2 ∧ U ^ 2 ≤ ((p : ℤ) + 1) ^ 2

/-- Integrality of the fixed-determinant normalized cube forces prime divisibility of the trace. -/
theorem prime_dvd_of_integral_normalizedCube {p : ℕ} (hp : p.Prime) {T U : ℤ}
    (h : (p : ℤ) * U = T ^ 3 - 3 * p * T) : (p : ℤ) ∣ T := by
  apply Int.Prime.dvd_pow' hp (k := 3)
  refine ⟨U + 3 * T, ?_⟩
  calc
    T ^ 3 = (T ^ 3 - 3 * p * T) + 3 * p * T := by ring
    _ = (p : ℤ) * U + 3 * p * T := by rw [h]
    _ = _ := by ring

private theorem trace_three_values {p : ℕ} (hp : p.Prime) {T U : ℤ}
    (h : NormalizedCubicTraceCondition p T U) :
    T = 0 ∨ T = (p : ℤ) ∨ T = -(p : ℤ) := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℤ) ≤ p := by omega
  obtain ⟨k, hk⟩ := prime_dvd_of_integral_normalizedCube hp h.1
  have hb := abs_le_of_sq_le_sq' h.2.1 (by omega : 0 ≤ (p : ℤ) + 1)
  rw [hk] at hb
  have hlo : -1 ≤ k := by
    by_contra hn
    have hk2 : k ≤ -2 := by omega
    have hm := mul_le_mul_of_nonneg_left hk2 hp0
    omega
  have hhi : k ≤ 1 := by
    by_contra hn
    have hk2 : 2 ≤ k := by omega
    have hm := mul_le_mul_of_nonneg_left hk2 hp0
    omega
  have hc : k = 0 ∨ k = 1 ∨ k = -1 := by omega
  rcases hc with rfl | rfl | rfl
  · exact Or.inl (by simpa using hk)
  · exact Or.inr (Or.inl (by simpa using hk))
  · exact Or.inr (Or.inr (by simpa using hk))

/-- At every prime at least five, integral positive-count normalized cubing leaves only zero trace. -/
theorem normalizedCubicTrace_eq_zero_of_five_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {T U : ℤ} (h : NormalizedCubicTraceCondition p T U) : T = 0 := by
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp5Z : (5 : ℤ) ≤ p := by exact_mod_cast hp5
  have hU := abs_le_of_sq_le_sq' h.2.2 (by omega : 0 ≤ (p : ℤ) + 1)
  have hlarge : 2 * (p : ℤ) ≤ (p : ℤ) * ((p : ℤ) - 3) := by
    simpa only [mul_comm 2 (p : ℤ)] using
      mul_le_mul_of_nonneg_left (by omega : (2 : ℤ) ≤ (p : ℤ) - 3)
        (by omega : (0 : ℤ) ≤ p)
  rcases trace_three_values hp h with hz | ht | ht
  · exact hz
  · have he : U = (p : ℤ) * ((p : ℤ) - 3) := by
      apply mul_left_cancel₀ hpZ
      calc
        (p : ℤ) * U = T ^ 3 - 3 * p * T := h.1
        _ = (p : ℤ) * ((p : ℤ) * ((p : ℤ) - 3)) := by rw [ht]; ring
    rw [he] at hU
    omega
  · have he : U = -((p : ℤ) * ((p : ℤ) - 3)) := by
      apply mul_left_cancel₀ hpZ
      calc
        (p : ℤ) * U = T ^ 3 - 3 * p * T := h.1
        _ = (p : ℤ) * (-((p : ℤ) * ((p : ℤ) - 3))) := by rw [ht]; ring
    rw [he] at hU
    omega

/-- The complete prime-by-prime classification of surviving integral traces. -/
theorem exists_normalizedCubicTrace_iff {p : ℕ} (hp : p.Prime) (T : ℤ) :
    (∃ U : ℤ, NormalizedCubicTraceCondition p T U) ↔
      T = 0 ∨ (p = 2 ∨ p = 3) ∧ (T = (p : ℤ) ∨ T = -(p : ℤ)) := by
  constructor
  · rintro ⟨U, h⟩
    by_cases hz : T = 0
    · exact Or.inl hz
    · have hp5 : p < 5 := by
        by_contra hn
        exact hz (normalizedCubicTrace_eq_zero_of_five_le hp (by omega) h)
      have hp4 : p ≠ 4 := by
        intro he
        rw [he] at hp
        have hd := hp.eq_one_or_self_of_dvd 2 (show 2 ∣ 4 from ⟨2, rfl⟩)
        omega
      have hp23 : p = 2 ∨ p = 3 := by have := hp.two_le; omega
      exact Or.inr ⟨hp23, (trace_three_values hp h).resolve_left hz⟩
  · rintro (rfl | ⟨hp23, ht⟩)
    · refine ⟨0, ?_, ?_, ?_⟩
      · ring
      · simpa only [zero_pow (by omega : 2 ≠ 0)] using sq_nonneg ((p : ℤ) + 1)
      · simpa only [zero_pow (by omega : 2 ≠ 0)] using sq_nonneg ((p : ℤ) + 1)
    · rcases hp23 with rfl | rfl
      · rcases ht with rfl | rfl
        · exact ⟨-2, by norm_num [NormalizedCubicTraceCondition]⟩
        · exact ⟨2, by norm_num [NormalizedCubicTraceCondition]⟩
      · rcases ht with rfl | rfl
        · exact ⟨0, by norm_num [NormalizedCubicTraceCondition]⟩
        · exact ⟨0, by norm_num [NormalizedCubicTraceCondition]⟩

/-- Every surviving trace lies in the genus-one square-root interval. -/
theorem normalizedCubicTrace_pure_bound {p : ℕ} (hp : p.Prime) {T U : ℤ}
    (h : NormalizedCubicTraceCondition p T U) : T ^ 2 ≤ 4 * (p : ℤ) := by
  rcases (exists_normalizedCubicTrace_iff hp T).mp ⟨U, h⟩ with rfl | ⟨hp23, ht⟩
  · positivity
  · rcases hp23 with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num

/-- The integral normalized-cube trace, when it exists, is unique. -/
theorem normalizedCubicTrace_unique {p : ℕ} (hp : p.Prime) {T U V : ℤ}
    (hU : NormalizedCubicTraceCondition p T U) (hV : NormalizedCubicTraceCondition p T V) :
    U = V :=
  mul_left_cancel₀ (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0) (hU.1.trans hV.1.symm)

end GaloisForLFunctions.BiarithmeticGeometry
