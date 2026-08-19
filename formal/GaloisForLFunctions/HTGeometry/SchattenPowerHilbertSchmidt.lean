/-
# Powers of a Schatten operator split into Hilbert–Schmidt factors

The trace of an operator is defined in the corpus through a Hilbert–Schmidt factorisation, so a
regularized determinant of order `p` needs each power at or above `p` to be written as a product of
two Hilbert–Schmidt operators.  Splitting a power in half and moving each half down the Schatten
scale does it: each half is Schatten `p/a`, which is Schatten 2 as soon as `2a ≥ p`.

Main results:
* `memSchattenClass_two_pow` — a power lands in Schatten 2 once twice its exponent dominates `p`.
* `exists_hilbertSchmidt_factorization_pow` — **a balanced split is a Hilbert–Schmidt
  factorisation**.
* `exists_hilbertSchmidt_factorization_pow_of_le` — every power above `p` splits.
-/
import GaloisForLFunctions.HTGeometry.SchattenHolder
import GaloisForLFunctions.RHTower.SchattenTwoIdentity

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A power lands in Schatten 2 once twice its exponent dominates the Schatten exponent. -/
theorem memSchattenClass_two_pow {p : ℝ} (hp : 0 < p) {T : H →L[ℂ] H}
    (hT : MemSchattenClass p T) {a : ℕ} (ha : 0 < a) (hpa : p ≤ 2 * (a : ℝ)) :
    MemSchattenClass 2 (T ^ a) := by
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hdivpos : 0 < p / (a : ℝ) := div_pos hp hapos
  have hdivle : p / (a : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hapos]
    linarith
  exact (memSchattenClass_pow hp hT ha).mono hdivpos hdivle

/-- **A balanced split is a Hilbert–Schmidt factorisation.** -/
theorem exists_hilbertSchmidt_factorization_pow {p : ℝ} (hp : 0 < p) {T : H →L[ℂ] H}
    (hT : MemSchattenClass p T) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hpa : p ≤ 2 * (a : ℝ)) (hpb : p ≤ 2 * (b : ℝ)) :
    ∃ A B : H →L[ℂ] H, A.IsHilbertSchmidt ∧ B.IsHilbertSchmidt ∧ T ^ (a + b) = A ∘L B := by
  refine ⟨T ^ a, T ^ b, ?_, ?_, ?_⟩
  · exact (memSchattenClass_two_iff_isHilbertSchmidt _).mp (memSchattenClass_two_pow hp hT ha hpa)
  · exact (memSchattenClass_two_iff_isHilbertSchmidt _).mp (memSchattenClass_two_pow hp hT hb hpb)
  · rw [pow_add]
    rfl

/-- **Every power strictly above the Schatten exponent splits into Hilbert–Schmidt factors.** -/
theorem exists_hilbertSchmidt_factorization_pow_of_le {p : ℝ} (hp : 0 < p) {T : H →L[ℂ] H}
    (hT : MemSchattenClass p T) {m : ℕ} (hm : p + 1 ≤ (m : ℝ)) :
    ∃ A B : H →L[ℂ] H, A.IsHilbertSchmidt ∧ B.IsHilbertSchmidt ∧ T ^ m = A ∘L B := by
  have hm2 : 2 ≤ m := by
    by_contra hcon
    have hmlt : m ≤ 1 := by omega
    have : (m : ℝ) ≤ 1 := by exact_mod_cast hmlt
    linarith
  set b : ℕ := m / 2 with hbdef
  set a : ℕ := m - b with hadef
  have hbpos : 0 < b := by omega
  have hab : a + b = m := by omega
  have hbge : (m : ℝ) - 1 ≤ 2 * (b : ℝ) := by
    have hnat : m ≤ 2 * b + 1 := by omega
    have : (m : ℝ) ≤ 2 * (b : ℝ) + 1 := by exact_mod_cast hnat
    linarith
  have hage : (m : ℝ) ≤ 2 * (a : ℝ) := by
    have hnat : m ≤ 2 * a := by omega
    exact_mod_cast hnat
  have hapos : 0 < a := by omega
  have hpa : p ≤ 2 * (a : ℝ) := le_trans (by linarith) hage
  have hpb : p ≤ 2 * (b : ℝ) := by linarith
  obtain ⟨A, B, hA, hB, hfac⟩ :=
    exists_hilbertSchmidt_factorization_pow hp hT hapos hbpos hpa hpb
  rw [hab] at hfac
  exact ⟨A, B, hA, hB, hfac⟩

end

end GaloisForLFunctions.HTGeometry
