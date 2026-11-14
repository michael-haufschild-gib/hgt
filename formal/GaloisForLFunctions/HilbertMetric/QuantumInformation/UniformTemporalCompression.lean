import GaloisForLFunctions.HilbertMetric.QuantumInformation.FermionSpectralEntropy
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FieldSimp

/-!
# An unresolved temporal cell is an actual rank-one compression

Uniform observation of `n+1` aliased modes gives the projector with every entry
`1/(n+1)`. Compressing a pure occupation projector onto this line has the single
nonzero occupation `k/(n+1)`, where `k` is the number of occupied modes.
The rectangular Gram entropy identity proves the binary-entropy formula
without assuming a spectral decomposition or a sampling-rank premise.
-/

noncomputable section
open scoped Matrix BigOperators
namespace GaloisForLFunctions.HilbertMetric

/-- Orthogonal projector for a uniformly observed unresolved cell. -/
def uniformTemporalProjection (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun _ _ => 1 / (n + 1 : ℕ)

/-- Compression of the physical occupied-mode projector. -/
def uniformTemporalCorrelation (n : ℕ) (occupied : Finset (Fin (n + 1))) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  uniformTemporalProjection n * Matrix.diagonal (fun i => if i ∈ occupied then 1 else 0) *
    uniformTemporalProjection n

/-- A one-column Gram factor for the compressed correlation. -/
def uniformTemporalAmplitude (n : ℕ) (occupied : Finset (Fin (n + 1))) :
    Matrix (Fin (n + 1)) (Fin 1) ℂ :=
  fun _ _ => ((Real.sqrt occupied.card / (n + 1 : ℕ) : ℝ) : ℂ)

/-- Uniform observation really is idempotent, for every cell size. -/
theorem uniformTemporalProjection_idempotent (n : ℕ) :
    uniformTemporalProjection n * uniformTemporalProjection n = uniformTemporalProjection n := by
  ext i j
  simp only [Matrix.mul_apply, uniformTemporalProjection, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

/-- The observation projector is self-adjoint. -/
theorem uniformTemporalProjection_isHermitian (n : ℕ) :
    (uniformTemporalProjection n).IsHermitian := by
  ext i j
  simp [uniformTemporalProjection, Matrix.conjTranspose_apply]

/-- Every entry of the compressed occupation counts occupied modes uniformly. -/
theorem uniformTemporalCorrelation_entry (n : ℕ) (occupied : Finset (Fin (n + 1)))
    (i j : Fin (n + 1)) :
    uniformTemporalCorrelation n occupied i j = (occupied.card : ℂ) / (n + 1 : ℕ) ^ 2 := by
  rw [uniformTemporalCorrelation, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, uniformTemporalProjection]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem]
  simp only [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The full compressed matrix is a one-column Gram matrix. -/
theorem uniformTemporalCorrelation_gram (n : ℕ) (occupied : Finset (Fin (n + 1))) :
    uniformTemporalCorrelation n occupied =
      uniformTemporalAmplitude n occupied * (uniformTemporalAmplitude n occupied)ᴴ := by
  ext i j
  rw [uniformTemporalCorrelation_entry]
  simp only [Matrix.mul_apply, uniformTemporalAmplitude, Matrix.conjTranspose_apply,
    Complex.conj_ofReal, Fin.sum_univ_one]
  have hs : (Real.sqrt (occupied.card : ℝ) : ℂ) ^ 2 = (occupied.card : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg occupied.card)
  push_cast
  rw [div_mul_div_comm, ← pow_two, hs]
  rfl

/-- The dual Gram matrix has exactly one occupation, the occupied fraction. -/
theorem uniformTemporalAmplitude_dualGram (n : ℕ) (occupied : Finset (Fin (n + 1))) :
    (uniformTemporalAmplitude n occupied)ᴴ * uniformTemporalAmplitude n occupied =
      Matrix.diagonal (fun _ : Fin 1 => (((occupied.card : ℝ) / (n + 1 : ℕ) : ℝ) : ℂ)) := by
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  subst j
  simp only [Matrix.mul_apply, uniformTemporalAmplitude, Matrix.conjTranspose_apply,
    Complex.conj_ofReal, Matrix.diagonal_apply_eq, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs : (Real.sqrt (occupied.card : ℝ) : ℂ) ^ 2 = (occupied.card : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg occupied.card)
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  rw [div_mul_div_comm, ← pow_two, hs]
  field_simp

/-- Exact entropy of the actual unresolved-cell compression. -/
theorem uniformTemporalCorrelation_entropy (n : ℕ) (occupied : Finset (Fin (n + 1))) :
    fermionSpectralEntropy (uniformTemporalCorrelation n occupied) =
      Real.binEntropy ((occupied.card : ℝ) / (n + 1 : ℕ)) := by
  rw [uniformTemporalCorrelation_gram, fermionSpectralEntropy_gram,
    uniformTemporalAmplitude_dualGram, fermionSpectralEntropy_diagonal]
  simp

/-- The compressed correlation is positive, certified by its explicit Gram factor. -/
theorem uniformTemporalCorrelation_posSemidef (n : ℕ) (occupied : Finset (Fin (n + 1))) :
    (uniformTemporalCorrelation n occupied).PosSemidef := by
  rw [uniformTemporalCorrelation_gram]
  simpa only [Matrix.conjTranspose_conjTranspose] using
    Matrix.posSemidef_conjTranspose_mul_self (uniformTemporalAmplitude n occupied)ᴴ

/-- An unresolved cell is pure exactly when all its modes have the same occupation. -/
theorem uniformTemporalCorrelation_entropy_zero_iff
    (n : ℕ) (occupied : Finset (Fin (n + 1))) :
    fermionSpectralEntropy (uniformTemporalCorrelation n occupied) = 0 ↔
      occupied.card = 0 ∨ occupied.card = n + 1 := by
  rw [uniformTemporalCorrelation_entropy, Real.binEntropy_eq_zero]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [div_eq_zero_iff, div_eq_one_iff_eq hn]
  simp only [hn, or_false, Nat.cast_eq_zero, Nat.cast_inj]

end GaloisForLFunctions.HilbertMetric

-- BEGIN PAPER AXIOM AUDIT
#print axioms GaloisForLFunctions.HilbertMetric.uniformTemporalProjection_idempotent
#print axioms GaloisForLFunctions.HilbertMetric.uniformTemporalProjection_isHermitian
#print axioms GaloisForLFunctions.HilbertMetric.uniformTemporalCorrelation_entry
#print axioms GaloisForLFunctions.HilbertMetric.uniformTemporalCorrelation_gram
#print axioms GaloisForLFunctions.HilbertMetric.uniformTemporalAmplitude_dualGram
#print axioms GaloisForLFunctions.HilbertMetric.uniformTemporalCorrelation_entropy
#print axioms GaloisForLFunctions.HilbertMetric.uniformTemporalCorrelation_posSemidef
#print axioms GaloisForLFunctions.HilbertMetric.uniformTemporalCorrelation_entropy_zero_iff
-- END PAPER AXIOM AUDIT
