import GaloisForLFunctions.HTGeometry.SourceCrossBlockWeightNonselection

/-!
# Biunitary equivalence is inhabited and is a genuine equivalence

Two blocks are biunitarily equivalent when one is carried to the other by unitaries on each side.
The identity pair realizes the relation, so it is reflexive; and a unimodular phase realizes it
nontrivially, so the invariants it preserves are genuinely blind to a global phase.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Biunitary equivalence is reflexive. -/
theorem biunitarilyEquivalent_refl (B : Matrix (Fin 2) (Fin 2) ℂ) :
    BiunitarilyEquivalent B B := by
  refine ⟨1, 1, ?_, ?_, ?_⟩ <;> simp

/-- **A unimodular phase is a biunitary equivalence,** so every biunitary invariant is blind to a
global phase. -/
theorem biunitarilyEquivalent_smul (B : Matrix (Fin 2) (Fin 2) ℂ) {c : ℂ} (hc : ‖c‖ = 1) :
    BiunitarilyEquivalent B (c • B) := by
  have hcc : (starRingEnd ℂ) c * c = 1 := by
    have hconj := Complex.normSq_eq_conj_mul_self (z := c)
    have hn : Complex.normSq c = 1 := by
      rw [Complex.normSq_eq_norm_sq, hc]
      norm_num
    rw [← hconj] at *
    exact_mod_cast hn
  refine ⟨c • 1, 1, ?_, by simp, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, smul_smul]
    rw [show (star c : ℂ) = (starRingEnd ℂ) c from rfl, hcc, one_smul]
  · rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one]

end GaloisForLFunctions.HTGeometry
