import GaloisForLFunctions.HTGeometry.FiniteKMSPurityNormalization
import GaloisForLFunctions.HTGeometry.PureBipartiteEntanglementEntropy

/-!
# Finite thermofield purification and opposite-copy observables

The diagonal amplitude with entries `sqrt (exp (-β Eₐ) / Z)` is the coefficient
matrix of the thermofield double. Both reductions are the Gibbs density matrix.
Its two-copy expectation contracts against the existing KMS half-density, and
operators on the two copies commute even when their expectations do not factor.

These are the finite-spectrum identities underlying equations (2.3)--(2.4) of
Maldacena, *Eternal black holes in Anti-de-Sitter*, arXiv:hep-th/0106112.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry.Thermofield

open _root_.HTGeometry

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Coefficient matrix of the canonical entangled purification. -/
def amplitude (β : ℝ) (E : α → ℝ) : Matrix α α ℂ :=
  Matrix.diagonal fun a => (Real.sqrt (finiteGibbsStateWeight β E a) : ℂ)

/-- Gibbs density matrix in the energy eigenbasis. -/
def density (β : ℝ) (E : α → ℝ) : Matrix α α ℂ :=
  Matrix.diagonal fun a => (finiteGibbsStateWeight β E a : ℂ)

/-- A left observable acts on the first coefficient index. -/
def left (A Ψ : Matrix α α ℂ) : Matrix α α ℂ := A * Ψ

/-- A right observable acts on the second coefficient index; hence the transpose. -/
def right (B Ψ : Matrix α α ℂ) : Matrix α α ℂ := Ψ * Bᵀ

/-- Pure-state expectation of a product of opposite-copy observables. -/
def pairExpectation (Ψ A B : Matrix α α ℂ) : ℂ :=
  Matrix.trace (Ψᴴ * A * Ψ * Bᵀ)

omit [Nonempty α] in
theorem amplitude_adjoint (β : ℝ) (E : α → ℝ) :
    (amplitude β E)ᴴ = amplitude β E := by
  rw [amplitude, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  exact Complex.conj_ofReal _

/-- Squaring the half-density recovers the actual Gibbs density. -/
theorem amplitude_sq (β : ℝ) (E : α → ℝ) :
    amplitude β E * amplitude β E = density β E := by
  rw [amplitude, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  rw [← Complex.ofReal_mul,
    Real.mul_self_sqrt (finiteGibbsStateWeight_pos β E a).le]

theorem density_trace (β : ℝ) (E : α → ℝ) :
    Matrix.trace (density β E) = 1 := by
  simpa [density, Matrix.trace_diagonal] using
    congrArg (fun x : ℝ => (x : ℂ)) (sum_finiteGibbsStateWeight_eq_one β E)

theorem amplitude_normSq (β : ℝ) (E : α → ℝ) :
    Matrix.trace ((amplitude β E)ᴴ * amplitude β E) = 1 := by
  rw [amplitude_adjoint, amplitude_sq, density_trace]

/-- Tracing out either copy yields the same thermal state. -/
theorem reduced_left (β : ℝ) (E : α → ℝ) :
    pureStateReducedLeft (fun p => amplitude β E p.1 p.2) = density β E := by
  change amplitude β E * (amplitude β E)ᴴ = density β E
  rw [amplitude_adjoint, amplitude_sq]

theorem reduced_right (β : ℝ) (E : α → ℝ) :
    pureStateReducedRight (fun p => amplitude β E p.1 p.2) = density β E := by
  change (amplitude β E)ᴴ * amplitude β E = density β E
  rw [amplitude_adjoint, amplitude_sq]

omit [DecidableEq α] [Nonempty α] in
/-- Independence of the two operator algebras is independent of the state. -/
theorem left_right_commute (A B Ψ : Matrix α α ℂ) :
    left A (right B Ψ) = right B (left A Ψ) := by
  exact (Matrix.mul_assoc A Ψ Bᵀ).symm

/-- The one-boundary expectation is exactly the thermal trace. -/
theorem expectation_left (β : ℝ) (E : α → ℝ) (A : Matrix α α ℂ) :
    pairExpectation (amplitude β E) A 1 = Matrix.trace (density β E * A) := by
  rw [pairExpectation, amplitude_adjoint, Matrix.transpose_one, Matrix.mul_one,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, amplitude_sq]

theorem expectation_right (β : ℝ) (E : α → ℝ) (B : Matrix α α ℂ) :
    pairExpectation (amplitude β E) 1 B = Matrix.trace (density β E * B) := by
  rw [pairExpectation, amplitude_adjoint, Matrix.mul_one, amplitude_sq]
  simp [density, Matrix.trace, Matrix.diagonal_mul, Matrix.transpose_apply]

theorem expectation_one (β : ℝ) (E : α → ℝ) :
    pairExpectation (amplitude β E) 1 1 = 1 := by
  rw [expectation_left, Matrix.mul_one, density_trace]

omit [DecidableEq α] in
/-- The existing KMS transition weight is the product of thermofield amplitudes. -/
theorem sqrt_weight_mul (β : ℝ) (E : α → ℝ) (a b : α) :
    Real.sqrt (finiteGibbsStateWeight β E a) *
        Real.sqrt (finiteGibbsStateWeight β E b) = finiteKMSWightmanWeight β E a b := by
  rw [← Real.sqrt_mul (finiteGibbsStateWeight_pos β E a).le,
    ← finiteKMSWightmanWeight_sq, Real.sqrt_sq (finiteKMSWightmanWeight_pos β E a b).le]

/-- Opposite-copy correlations are exactly the KMS half-density pairing. -/
theorem expectation_eq_kms (β : ℝ) (E : α → ℝ) (A B : Matrix α α ℂ) :
    pairExpectation (amplitude β E) A B =
      ∑ a, ∑ b, (finiteKMSWightmanWeight β E a b : ℂ) * A a b * B a b := by
  rw [pairExpectation, amplitude_adjoint]
  change (∑ a, ∑ b, ((amplitude β E * A) * amplitude β E) a b * B a b) = _
  simp only [amplitude, Matrix.mul_diagonal, Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [← sqrt_weight_mul β E a b, Complex.ofReal_mul]
  ring

/-- A conjugate observable on the opposite copy reads the existing nonnegative
Wightman transition intensity, including all off-diagonal transitions. -/
theorem expectation_conjugate (β : ℝ) (E : α → ℝ) (A : Matrix α α ℂ) :
    pairExpectation (amplitude β E) A (fun a b => star (A a b)) =
      ((∑ a, ∑ b, finiteKMSWightmanTransitionIntensity β E A a b : ℝ) : ℂ) := by
  rw [expectation_eq_kms]
  push_cast
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [finiteKMSWightmanTransitionIntensity, wightmanTransitionIntensity,
    Complex.ofReal_mul, Complex.star_def]
  rw [mul_assoc, Complex.mul_conj]

omit [Nonempty α] in
/-- Every diagonal conserved quantity agrees on the two copies. -/
theorem diagonal_difference (β : ℝ) (E Q : α → ℝ) :
    left (Matrix.diagonal fun a => (Q a : ℂ)) (amplitude β E) -
      right (Matrix.diagonal fun a => (Q a : ℂ)) (amplitude β E) = 0 := by
  simp only [left, right, amplitude, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  apply sub_eq_zero.mpr
  congr 1
  funext a
  exact mul_comm _ _

omit [Nonempty α] in
/-- The difference of the two Hamiltonians kills the thermofield state. -/
theorem hamiltonian_difference (β : ℝ) (E : α → ℝ) :
    left (Matrix.diagonal fun a => (E a : ℂ)) (amplitude β E) -
      right (Matrix.diagonal fun a => (E a : ℂ)) (amplitude β E) = 0 :=
  diagonal_difference β E E

omit [Nonempty α] in
/-- The grand-canonical purification satisfies the energy and charge constraints
separately, even though the Boltzmann exponent couples them. -/
theorem charged_constraints (β μ : ℝ) (E Q : α → ℝ) :
    left (Matrix.diagonal fun a => (E a : ℂ)) (amplitude β (fun a => E a + μ * Q a)) -
        right (Matrix.diagonal fun a => (E a : ℂ))
          (amplitude β (fun a => E a + μ * Q a)) = 0 ∧
      left (Matrix.diagonal fun a => (Q a : ℂ)) (amplitude β (fun a => E a + μ * Q a)) -
        right (Matrix.diagonal fun a => (Q a : ℂ))
          (amplitude β (fun a => E a + μ * Q a)) = 0 :=
  ⟨diagonal_difference _ _ _, diagonal_difference _ _ _⟩

/-- The canonical finite thermofield state factors exactly in dimension one.
Positive Schmidt amplitudes make every two-level diagonal minor nonzero. -/
theorem amplitude_product_iff (β : ℝ) (E : α → ℝ) :
    (∃ f g : α → ℂ, ∀ a b, amplitude β E a b = f a * g b) ↔ Subsingleton α := by
  constructor
  · rintro ⟨f, g, h⟩
    refine ⟨fun a b => ?_⟩
    by_contra hab
    have hm : amplitude β E a a * amplitude β E b b =
        amplitude β E a b * amplitude β E b a := by
      rw [h, h, h, h]
      ring
    have ha : (Real.sqrt (finiteGibbsStateWeight β E a) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (finiteGibbsStateWeight_pos β E a)).ne'
    have hb : (Real.sqrt (finiteGibbsStateWeight β E b) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (finiteGibbsStateWeight_pos β E b)).ne'
    simp only [amplitude, Matrix.diagonal_apply, if_true, if_neg hab,
      zero_mul] at hm
    exact mul_ne_zero ha hb hm
  · intro h
    letI := h
    refine ⟨fun a => (Real.sqrt (finiteGibbsStateWeight β E a) : ℂ), fun _ => 1, ?_⟩
    intro a b
    simp only [amplitude, Matrix.diagonal_apply, Subsingleton.elim a b, if_true, mul_one]

/-- Purity of the reduced state is the thermal replica ratio. -/
theorem reduced_purity (β : ℝ) (E : α → ℝ) :
    Matrix.trace (density β E * density β E) =
      ((finiteGibbsPartition (2 * β) E / finiteGibbsPartition β E ^ 2 : ℝ) : ℂ) := by
  rw [← finiteGibbsPurity_eq_partitionRatio]
  simp [density, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
    finiteGibbsPurity, pow_two]

end

end GaloisForLFunctions.HTGeometry.Thermofield
