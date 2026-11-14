import GaloisForLFunctions.HTGeometry.Thermofield.FinitePurification
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Two-copy time evolution, thermal continuation, and no signalling

In the thermofield state, two Heisenberg times enter through their sum.
Opposite evolution therefore fixes every two-copy expectation. The same
expectation is the ordinary thermal correlator continued by half the imaginary
thermal period. An arbitrary unitary on the unobserved copy preserves the
observed reduced density matrix.

These exact finite-dimensional identities implement the operator mechanisms
around equations (2.3)--(2.6) of Maldacena, arXiv:hep-th/0106112.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry.Thermofield

open _root_.HTGeometry

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Entire complex-time Heisenberg evolution in an energy eigenbasis. -/
def evolve (E : α → ℝ) (z : ℂ) (A : Matrix α α ℂ) : Matrix α α ℂ :=
  fun a b => Complex.exp (Complex.I * z * ((E a - E b : ℝ) : ℂ)) * A a b

omit [Fintype α] [DecidableEq α] [Nonempty α] in
theorem evolve_zero (E : α → ℝ) (A : Matrix α α ℂ) : evolve E 0 A = A := by
  ext a b
  simp [evolve]

/-- The two independent boundary times add in the entangled expectation. -/
theorem expectation_two_times (β : ℝ) (E : α → ℝ)
    (A B : Matrix α α ℂ) (z w : ℂ) :
    pairExpectation (amplitude β E) (evolve E z A) (evolve E w B) =
      pairExpectation (amplitude β E) (evolve E (z + w) A) B := by
  rw [expectation_eq_kms, expectation_eq_kms]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [evolve]
  rw [show Complex.I * (z + w) * ((E a - E b : ℝ) : ℂ) =
    Complex.I * z * ((E a - E b : ℝ) : ℂ) +
      Complex.I * w * ((E a - E b : ℝ) : ℂ) by ring, Complex.exp_add]
  ring

/-- The difference generator is an exact symmetry, for arbitrary observables. -/
theorem expectation_opposite_times (β : ℝ) (E : α → ℝ)
    (A B : Matrix α α ℂ) (z : ℂ) :
    pairExpectation (amplitude β E) (evolve E z A) (evolve E (-z) B) =
      pairExpectation (amplitude β E) A B := by
  rw [expectation_two_times, add_neg_cancel, evolve_zero]

/-- Concrete opposite-copy correlators reproduce the finite Wightman spectrum. -/
theorem expectation_evolved_conjugate (β : ℝ) (E : α → ℝ)
    (A : Matrix α α ℂ) (z w : ℂ) :
    pairExpectation (amplitude β E) (evolve E z A)
        (evolve E w (fun a b => star (A a b))) =
      ∑ a, ∑ b, (finiteKMSWightmanTransitionIntensity β E A a b : ℂ) *
        Complex.exp (Complex.I * (z + w) * ((E a - E b : ℝ) : ℂ)) := by
  rw [expectation_two_times, expectation_eq_kms]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [evolve, finiteKMSWightmanTransitionIntensity, wightmanTransitionIntensity,
    Complex.ofReal_mul, Complex.star_def, ← Complex.mul_conj]
  ring

omit [DecidableEq α] [Nonempty α] in
/-- Half an imaginary thermal period turns a Gibbs weight into a Wightman weight. -/
theorem half_thermal_weight (β : ℝ) (E : α → ℝ) (a b : α) :
    (finiteGibbsStateWeight β E a : ℂ) *
        Complex.exp ((β : ℂ) * ((E a - E b : ℝ) : ℂ) / 2) =
      (finiteKMSWightmanWeight β E a b : ℂ) := by
  have h : finiteGibbsStateWeight β E a * Real.exp (β * (E a - E b) / 2) =
      finiteKMSWightmanWeight β E a b := by
    rw [finiteGibbsStateWeight, finiteKMSWightmanWeight, div_mul_eq_mul_div,
      ← Real.exp_add]
    congr 2
    ring
  exact_mod_cast h

/-- Opposite-copy expectation is the ordinary thermal correlator continued by
minus half the imaginary period, for the chosen `exp (i t H)` convention. -/
theorem expectation_eq_half_thermal_time (β : ℝ) (E : α → ℝ)
    (A B : Matrix α α ℂ) (z : ℂ) :
    pairExpectation (amplitude β E) (evolve E z A) B =
      Matrix.trace (density β E * evolve E (z - Complex.I * (β : ℂ) / 2) A * Bᵀ) := by
  rw [expectation_eq_kms]
  change _ = ∑ a, ∑ b, (density β E *
    evolve E (z - Complex.I * (β : ℂ) / 2) A) a b * B a b
  simp only [density, Matrix.diagonal_mul, evolve]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have harg :
      Complex.I * (z - Complex.I * (β : ℂ) / 2) * ((E a - E b : ℝ) : ℂ) =
        (β : ℂ) * ((E a - E b : ℝ) : ℂ) / 2 +
          Complex.I * z * ((E a - E b : ℝ) : ℂ) := by
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [harg, Complex.exp_add]
  rw [show (finiteGibbsStateWeight β E a : ℂ) *
      (Complex.exp ((β : ℂ) * ((E a - E b : ℝ) : ℂ) / 2) *
        Complex.exp (Complex.I * z * ((E a - E b : ℝ) : ℂ)) * A a b) * B a b =
      ((finiteGibbsStateWeight β E a : ℂ) *
        Complex.exp ((β : ℂ) * ((E a - E b : ℝ) : ℂ) / 2)) *
          (Complex.exp (Complex.I * z * ((E a - E b : ℝ) : ℂ)) * A a b) * B a b by ring]
  rw [half_thermal_weight]

omit [Nonempty α] in
/-- A unitary on the unobserved copy leaves the observed density matrix unchanged. -/
theorem reduced_left_right_unitary (Ψ : Matrix α α ℂ)
    (U : Matrix.unitaryGroup α ℂ) :
    pureStateReducedLeft (fun p => right (U : Matrix α α ℂ) Ψ p.1 p.2) =
      pureStateReducedLeft (fun p => Ψ p.1 p.2) := by
  have hU : (U : Matrix α α ℂ)ᵀ * ((U : Matrix α α ℂ)ᵀ)ᴴ = 1 :=
    (Matrix.mem_unitaryGroup_iff.mp
      (Matrix.transpose_mem_unitaryGroup_iff.mpr U.property))
  change (Ψ * (U : Matrix α α ℂ)ᵀ) * (Ψ * (U : Matrix α α ℂ)ᵀ)ᴴ = Ψ * Ψᴴ
  rw [Matrix.conjTranspose_mul]
  calc
    _ = Ψ * ((U : Matrix α α ℂ)ᵀ * ((U : Matrix α α ℂ)ᵀ)ᴴ) * Ψᴴ := by
      simp only [Matrix.mul_assoc]
    _ = Ψ * Ψᴴ := by rw [hU, Matrix.mul_one]

/-- In particular, a remote unitary leaves the canonical Gibbs marginal intact. -/
theorem thermal_no_signalling (β : ℝ) (E : α → ℝ)
    (U : Matrix.unitaryGroup α ℂ) :
    pureStateReducedLeft
        (fun p => right (U : Matrix α α ℂ) (amplitude β E) p.1 p.2) = density β E := by
  rw [reduced_left_right_unitary, reduced_left]

end

end GaloisForLFunctions.HTGeometry.Thermofield
