import GaloisForLFunctions.HTGeometry.AiryTowerFactorization

/-!
# Separated loopless Airy cores

This module formalizes the arithmetic content of the separated-core theorem.  A vertex remembers
the first divisor drop `R = aE`.  Its pair edge is `RS/min(a,b)`, and the rescaled matrix
`1/min(a,b)` satisfies the acute-isosceles law for every finite family.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

/-- First divisor drop of an Airy tower, with quotient `a ≥ 2`. -/
structure AiryHead (R : ℕ) where
  nextRamification : ℕ
  firstFactor : ℕ
  next_pos : 0 < nextRamification
  factor_ge_two : 2 ≤ firstFactor
  ramification_eq : R = firstFactor * nextRamification

/-- Extract the first divisor drop from a strict divisor chain. -/
def StrictDivisorChain.toAiryHead {R : ℕ} (d : StrictDivisorChain R) : AiryHead R := by
  cases d with
  | terminal hR =>
      exact {
        nextRamification := 1
        firstFactor := R
        next_pos := by omega
        factor_ge_two := by omega
        ramification_eq := by simp }
  | @step R E hER hE hdvd tail =>
      have hfactor : 2 ≤ R / E := by
        apply (Nat.le_div_iff_mul_le (by omega)).2
        obtain ⟨q, rfl⟩ := hdvd
        have hq : 1 < q := by nlinarith
        nlinarith
      exact {
        nextRamification := E
        firstFactor := R / E
        next_pos := by omega
        factor_ge_two := hfactor
        ramification_eq := (Nat.div_mul_cancel hdvd).symm }

/-- Edge multiplicity of two leading-separated Airy towers. -/
def separatedEdge {R S : ℕ} (x : AiryHead R) (y : AiryHead S) : ℕ :=
  R * S / min x.firstFactor y.firstFactor

/-- Branch formula when the left first quotient is smaller. -/
theorem separatedEdge_eq_right_mul_next_of_le {R S : ℕ} (x : AiryHead R) (y : AiryHead S)
    (hxy : x.firstFactor ≤ y.firstFactor) :
    separatedEdge x y = S * x.nextRamification := by
  rw [separatedEdge, min_eq_left hxy]
  have hfactor : 0 < x.firstFactor :=
    lt_of_lt_of_le Nat.zero_lt_two x.factor_ge_two
  calc
    R * S / x.firstFactor =
        (x.firstFactor * x.nextRamification) * S / x.firstFactor :=
      congrArg (fun n => n * S / x.firstFactor) x.ramification_eq
    _ = S * x.nextRamification := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        Nat.mul_div_left (S * x.nextRamification) hfactor

/-- Symmetric branch formula when the right first quotient is smaller. -/
theorem separatedEdge_eq_left_mul_next_of_le {R S : ℕ} (x : AiryHead R) (y : AiryHead S)
    (hyx : y.firstFactor ≤ x.firstFactor) :
    separatedEdge x y = R * y.nextRamification := by
  rw [separatedEdge, min_eq_right hyx]
  have hfactor : 0 < y.firstFactor :=
    lt_of_lt_of_le Nat.zero_lt_two y.factor_ge_two
  calc
    R * S / y.firstFactor =
        R * (y.firstFactor * y.nextRamification) / y.firstFactor :=
      congrArg (fun n => R * n / y.firstFactor) y.ramification_eq
    _ = R * y.nextRamification := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        Nat.mul_div_left (R * y.nextRamification) hfactor

/-- Rescaled separated-core weight; it depends only on first factors. -/
def separatedRescaledWeight (a b : ℕ) : ℚ := 1 / ((min a b : ℕ) : ℚ)

theorem separatedRescaledWeight_symm (a b : ℕ) :
    separatedRescaledWeight a b = separatedRescaledWeight b a := by
  simp [separatedRescaledWeight, min_comm]

/-- One ultrametric inequality for reciprocal-min weights. -/
theorem separatedRescaledWeight_le_max {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    separatedRescaledWeight a b ≤
      max (separatedRescaledWeight a c) (separatedRescaledWeight b c) := by
  simp only [separatedRescaledWeight]
  by_cases hab : a ≤ b
  · rw [min_eq_left hab]
    by_cases hac : a ≤ c
    · rw [min_eq_left hac]
      exact le_max_left _ _
    · have hca : c ≤ a := le_of_not_ge hac
      have hcb : c ≤ b := hca.trans hab
      rw [min_eq_right hca, min_eq_right hcb]
      apply le_trans _ (le_max_right _ _)
      exact one_div_le_one_div_of_le (by exact_mod_cast hc) (by exact_mod_cast hca)
  · have hba : b ≤ a := le_of_not_ge hab
    rw [min_eq_right hba]
    by_cases hbc : b ≤ c
    · rw [min_eq_left hbc]
      exact le_max_right _ _
    · have hcb : c ≤ b := le_of_not_ge hbc
      have hca : c ≤ a := hcb.trans hba
      rw [min_eq_right hca, min_eq_right hcb]
      apply le_trans _ (le_max_left _ _)
      exact one_div_le_one_div_of_le (by exact_mod_cast hc) (by exact_mod_cast hcb)

/-- Full acute-isosceles law for every triple of first factors. -/
theorem separatedRescaledWeight_acuteIsosceles {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    separatedRescaledWeight a b ≤
        max (separatedRescaledWeight a c) (separatedRescaledWeight b c) ∧
    separatedRescaledWeight a c ≤
        max (separatedRescaledWeight a b) (separatedRescaledWeight b c) ∧
    separatedRescaledWeight b c ≤
        max (separatedRescaledWeight a b) (separatedRescaledWeight a c) := by
  refine ⟨separatedRescaledWeight_le_max ha hb hc, ?_, ?_⟩
  · simpa [separatedRescaledWeight_symm b c] using
      (separatedRescaledWeight_le_max ha hc hb)
  · simpa [separatedRescaledWeight_symm b a, separatedRescaledWeight_symm c a] using
      (separatedRescaledWeight_le_max hb hc ha)

end IrregularStokes
end GaloisForLFunctions
