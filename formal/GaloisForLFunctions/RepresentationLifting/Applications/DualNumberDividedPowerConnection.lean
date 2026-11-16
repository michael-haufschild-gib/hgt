import GaloisForLFunctions.RepresentationLifting.Differential.NilpotentDividedPowerConnection
import GaloisForLFunctions.RepresentationLifting.ModularTrace
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Integral horizontal sections for the dual-number shift

The square-zero matrix acting on a free dual-number module defines an
integral connection on divided-power coefficient lists. Its horizontal
sections have only two nonzero coefficients, and every inhomogeneous
initial-value problem has a unique finite divided-power solution.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

variable (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The existing dual-number shift, regarded as an endomorphism of its coordinate module. -/
def dualNumberMonodromy : Module.End R ((ι ⊕ ι) → R) :=
  (LinearMap.toMatrixAlgEquiv' (R := R) (n := ι ⊕ ι)).symm dualNumberShift

theorem dualNumberMonodromy_sq : dualNumberMonodromy R ι ^ 2 = 0 := by
  have h := congrArg (LinearMap.toMatrixAlgEquiv' (R := R) (n := ι ⊕ ι)).symm
    (dualNumberShift_sq (ι := ι) (R := R))
  simpa only [dualNumberMonodromy, map_pow, map_zero] using h

/-- Initial value and connection image give exact coordinates for every divided-power section. -/
def dualNumberConnectionEquiv :
    (ℕ →₀ ((ι ⊕ ι) → R)) ≃ₗ[R] (((ι ⊕ ι) → R) × (ℕ →₀ ((ι ⊕ ι) → R))) :=
  DividedPower.normalFormEquiv (dualNumberMonodromy R ι) ⟨2, dualNumberMonodromy_sq R ι⟩

/-- No characteristic restriction or rational denominators are needed for the initial-value problem. -/
theorem dualNumber_existsUnique_connection_solution
    (v : (ι ⊕ ι) → R) (f : ℕ →₀ ((ι ⊕ ι) → R)) :
    ∃! p : ℕ →₀ ((ι ⊕ ι) → R),
      p 0 = v ∧ DividedPower.connection (dualNumberMonodromy R ι) p = f :=
  DividedPower.existsUnique_connection_solution (dualNumberMonodromy R ι)
    ⟨2, dualNumberMonodromy_sq R ι⟩ v f

/-- The horizontal exponential truncates after its linear divided-power term. -/
theorem dualNumber_horizontal_eq (v : (ι ⊕ ι) → R) :
    DividedPower.horizontal (dualNumberMonodromy R ι) ⟨2, dualNumberMonodromy_sq R ι⟩ v =
      Finsupp.single 0 v + Finsupp.single 1 (dualNumberMonodromy R ι v) := by
  apply Finsupp.ext
  intro n
  rw [DividedPower.horizontal_coeff]
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp
    | succ n =>
      rw [show n + 1 + 1 = 2 + n by omega, pow_add, dualNumberMonodromy_sq, zero_mul]
      simp [show (1 : ℕ) ≠ 2 + n by omega]

#print axioms dualNumberConnectionEquiv
#print axioms dualNumber_existsUnique_connection_solution
#print axioms dualNumber_horizontal_eq

end GaloisForLFunctions.RepresentationLifting
