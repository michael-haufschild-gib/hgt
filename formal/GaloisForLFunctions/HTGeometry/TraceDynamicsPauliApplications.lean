import GaloisForLFunctions.HTGeometry.TraceDynamicsMatrixCharge
import GaloisForLFunctions.HTGeometry.TraceDynamicsPauliEvolution

/-!
# Trace-dynamics interactions on the Pauli corpus

Pauli involutions make quartic forces radial and preserve individual sector charges.
Yang--Mills forces retain exactly the erased Pauli component. Discrete total-charge
readouts remain constant for arbitrary registers and iteration counts.

Source: Singh, arXiv:2609.10571, sections 6.2, 6.4 and 13.2.
-/

set_option autoImplicit false

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.TraceDynamics
noncomputable section
variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
local notation "M" => Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ

/-- Squared Pauli coordinates make the mixed quartic force purely radial. -/
theorem quarticPairForce_pauli (P Q : σ → Option (Fin 3)) :
    quarticPairForce (finitePauliMatrix P) (finitePauliMatrix Q) =
      (2 : ℂ) • finitePauliMatrix P := by
  unfold quarticPairForce
  rw [mul_assoc, finitePauliMatrix_mul_self, mul_one, one_mul]
  module

/-- Every finite Pauli family loses all tangential quartic sector forces. -/
theorem quarticForce_pauli_radial (O : ι → σ → Option (Fin 3))
    (a b : ι → ℂ) (c : ι → ι → ℂ) (i : ι) :
    quarticForce (fun j => finitePauliMatrix (O j)) a b c i =
      (a i+b i+∑ j, 2*(c i j+c j i)) • finitePauliMatrix (O i) := by
  simp only [quarticForce, quarticPairForce_pauli, finitePauliMatrix_mul_self, one_mul,
    smul_smul]
  rw [← Finset.sum_smul]
  simp_rw [mul_comm (c i _ + c _ i) 2]
  module

/-- Quartic Pauli kicks preserve every individual sector charge, not only their sum. -/
theorem quarticPauli_subsystemCharge (O : ι → σ → Option (Fin 3))
    (p : ι → M) (a b : ι → ℂ) (c : ι → ι → ℂ) (h : ℂ) (i : ι) :
    finitePauliMatrix (O i) *
        (p i - h • quarticForce (fun j => finitePauliMatrix (O j)) a b c i) -
      (p i - h • quarticForce (fun j => finitePauliMatrix (O j)) a b c i) *
        finitePauliMatrix (O i) =
      finitePauliMatrix (O i)*p i-p i*finitePauliMatrix (O i) := by
  rw [quarticForce_pauli_radial]
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm]
  abel

/-- The Yang--Mills interaction retains exactly the Pauli-erased component. -/
theorem yangMillsPairForce_pauli_dissipation (P : σ → Option (Fin 3)) (X : M) :
    yangMillsPairForce X (finitePauliMatrix P) =
      -(4 : ℂ) • (X-pauliStaticPart P X) := by
  have h := pauli_doubleCommutator P X
  calc
    yangMillsPairForce X (finitePauliMatrix P) =
        -(finitePauliMatrix P * (finitePauliMatrix P * X-X*finitePauliMatrix P) -
          (finitePauliMatrix P * X-X*finitePauliMatrix P)*finitePauliMatrix P) := by
      unfold yangMillsPairForce
      noncomm_ring
    _ = _ := by rw [h, neg_smul]

/-- The exact quartic leapfrog conservation law applies to every finite Pauli register. -/
theorem pauliRegister_leapfrog_charge (O : ι → σ → Option (Fin 3))
    (p : ι → M) (a b : ι → ℂ) (c : ι → ι → ℂ) (h : ℂ) (n : ℕ) :
    charge ((leapfrog a b c h)^[n] (fun j => finitePauliMatrix (O j), p)).1
        ((leapfrog a b c h)^[n] (fun j => finitePauliMatrix (O j), p)).2 =
      ∑ j, (finitePauliMatrix (O j)*p j-p j*finitePauliMatrix (O j)) :=
  leapfrog_iterate_conserves_charge a b c h _ n

/-- No centered scalar readout of the conserved total charge varies along the discrete flow. -/
theorem leapfrog_totalCharge_centered_readout (a b : ι → ℂ) (c : ι → ι → ℂ) (h : ℂ)
    (z : (ι → M) × (ι → M)) (T : M) (n : ℕ) :
    Matrix.trace (T * charge ((leapfrog a b c h)^[n] z).1 ((leapfrog a b c h)^[n] z).2) -
      Matrix.trace (T * charge z.1 z.2) = 0 := by
  rw [leapfrog_iterate_conserves_charge, sub_self]

end
end GaloisForLFunctions.HTGeometry.TraceDynamics
