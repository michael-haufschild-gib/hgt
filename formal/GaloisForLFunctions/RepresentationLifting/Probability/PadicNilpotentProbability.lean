import GaloisForLFunctions.RepresentationLifting.Probability.PadicMatrixHaar
import GaloisForLFunctions.RepresentationLifting.Probability.PrimePowerNilpotentMatrices
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Topological and algebraic nilpotence have different Haar probabilities

Topological nilpotence of an integral p-adic matrix has probability
`p^(-n)`, since it is detected modulo `p`. Algebraic nilpotence has
probability zero in positive dimension: nilpotent matrices have zero
trace, and every trace fiber has zero Haar measure.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

open MeasureTheory OperatorKernels

variable (p : ℕ) [Fact p.Prime]

/-- Probability that the powers of a p-adic Haar matrix converge to zero. -/
theorem padicMatrixHaar_topNil (n : ℕ) :
    (padicMatrixHaar p n).real {A | IsTopologicallyNilpotent A} = 1 / (p : ℝ) ^ n := by
  simp_rw [padicMatrix_topNil_iff_residue_nil]
  rw [padicMatrixHaar_residue_probability]
  exact_mod_cast primePower_nilpotent_matrix_density p 0 n

/-- Finite residue of the trace, as an additive quotient. -/
def padicMatrixTraceResidue (k n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ_[p] →+ ZMod (p ^ k) where
  toFun A := PadicInt.toZModPow k (Matrix.trace A)
  map_zero' := by simp
  map_add' A B := by rw [Matrix.trace_add, map_add]

/-- Trace residue is continuous, being a finite sum followed by residue reduction. -/
theorem padicMatrixTraceResidue_continuous (k n : ℕ) :
    Continuous (padicMatrixTraceResidue p k n) :=
  (RHTower.fieldOnePadicInt_toZModPow_continuous p k).comp continuous_id.matrix_trace

/-- A single diagonal entry realizes any prescribed trace residue. -/
theorem padicMatrixTraceResidue_surjective (k n : ℕ) :
    Function.Surjective (padicMatrixTraceResidue p k n) := by
  intro r
  refine ⟨Matrix.single 0 0 (RHTower.fieldOnePadicIntResidueRep p k r), ?_⟩
  change PadicInt.toZModPow k (Matrix.trace _) = r
  simpa using RHTower.fieldOnePadicIntResidueRep_spec p k r

/-- Every residue class of the trace has probability `p^(-k)`. -/
theorem padicMatrixHaar_trace_residue (k n : ℕ) (r : ZMod (p ^ k)) :
    (padicMatrixHaar p (n + 1)).real {A | padicMatrixTraceResidue p k n A = r} =
      1 / (p : ℝ) ^ k := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k (Fact.out : p.Prime).ne_zero⟩
  have h := haar_finite_quotient_probability (padicMatrixHaar p (n + 1))
    (padicMatrixTraceResidue p k n) (padicMatrixTraceResidue_surjective p k n)
    (padicMatrixTraceResidue_continuous p k n) (fun x => x = r)
  simpa only [Nat.card_unique, Nat.cast_one, Nat.card_zmod, Nat.cast_pow] using h

/-- Every exact trace fiber has zero Haar measure in positive matrix dimension. -/
theorem padicMatrixHaar_trace_fiber (n : ℕ) (t : ℤ_[p]) :
    padicMatrixHaar p (n + 1) {A | Matrix.trace A = t} = 0 := by
  apply measureReal_eq_zero_iff.mp
  apply le_antisymm ?_ measureReal_nonneg
  by_contra! hpos
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hpos
  have hle : (padicMatrixHaar p (n + 1)).real {A | Matrix.trace A = t} ≤
      (padicMatrixHaar p (n + 1)).real
        {A | padicMatrixTraceResidue p k n A = PadicInt.toZModPow k t} := by
    apply measureReal_mono
    intro A hA
    change PadicInt.toZModPow k (Matrix.trace A) = PadicInt.toZModPow k t
    rw [hA]
  rw [padicMatrixHaar_trace_residue] at hle
  have hlt : 1 / (p : ℝ) ^ k <
      (padicMatrixHaar p (n + 1)).real {A | Matrix.trace A = t} := by
    simpa only [zpow_neg, zpow_natCast, one_div] using hk
  exact (not_lt_of_ge hle) hlt

/-- Algebraically nilpotent p-adic matrices form a Haar null set in positive dimension. -/
theorem padicMatrixHaar_nilpotent (n : ℕ) :
    padicMatrixHaar p (n + 1) {A | IsNilpotent A} = 0 := by
  apply measure_mono_null (s := {A | IsNilpotent A})
    (t := {A | Matrix.trace A = 0}) ?_ (padicMatrixHaar_trace_fiber p n 0)
  intro A hA
  exact (Matrix.isNilpotent_trace_of_isNilpotent hA).eq_zero

#print axioms padicMatrixHaar_topNil
#print axioms padicMatrixHaar_trace_residue
#print axioms padicMatrixHaar_trace_fiber
#print axioms padicMatrixHaar_nilpotent

end GaloisForLFunctions.RepresentationLifting
