import GaloisForLFunctions.HTGeometry.OneStepKrylovCarrierLaw
import GaloisForLFunctions.RHTower.ScalarRecurrenceKrylovReplicaDichotomyLaw

/-!
# First scalar-removed static-Choi Krylov innovation

For a traceless finite Hamiltonian, the first scalar-removed replicated
Krylov load is exactly the replicated directional correlation with its energy
vector.  This removes the inverse Gram matrix at the first nonconstant layer
and is the deterministic input to coefficient-sphere anti-concentration.
-/

open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Removing the identity-Choi component makes the unnormalized spectral
diagonal sum to zero. -/
theorem sum_staticChoiTracelessDiagonal_eq_zero
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    ∑ i, staticChoiTracelessDiagonal energy target i = 0 := by
  have h := sum_staticChoiTracelessSpectralCoefficient_eq_zero hd energy target
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hd))
  rw [show (∑ i, staticChoiTracelessSpectralCoefficient energy target i) =
      ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
        ∑ i, staticChoiTracelessDiagonal energy target i by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rfl] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast inv_ne_zero hsqrt)

/-- For a traceless spectrum, first scalar-removed carrier mass is exactly
one normalized spectral directional correlation. -/
theorem norm_sq_scalarRemovedStaticChoiKrylovCarrier_one_eq
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (henergyZero : ∑ i, energy i = 0) :
    ‖spectralKrylovCarrier (fun i => -energy i) 1
        (staticChoiTracelessDiagonal energy target)‖ ^ 2 =
      ‖inner ℂ (spectralPowerVector (fun i => -energy i) 1)
        (staticChoiTracelessDiagonal energy target)‖ ^ 2 /
      ‖spectralPowerVector (fun i => -energy i) 1‖ ^ 2 := by
  apply norm_sq_spectralKrylovCarrier_one_eq_of_sum_zero
  · exact sum_staticChoiTracelessDiagonal_eq_zero hd energy target
  · simpa [Finset.sum_neg_distrib] using congrArg Neg.neg henergyZero

/-- Exact family identity: the order-one replicated carrier load is the sum
of powers of normalized directional correlations. -/
theorem scalarRemovedStaticChoiKrylovReplicaLoad_one_eq
    {d : ℕ} (hd : 0 < d) {W : Type*} [Fintype W]
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (energy : Fin d → ℝ) (r : ℕ)
    (henergyZero : ∑ i, energy i = 0) :
    scalarRemovedStaticChoiKrylovReplicaLoad target energy 1 r =
      ∑ w, (‖inner ℂ (spectralPowerVector (fun i => -energy i) 1)
          (staticChoiTracelessDiagonal energy (target w))‖ ^ 2 /
        ‖spectralPowerVector (fun i => -energy i) 1‖ ^ 2) ^ r := by
  unfold scalarRemovedStaticChoiKrylovReplicaLoad
    finiteKrylovCarrierReplicaLoad
  apply Finset.sum_congr rfl
  intro w hw
  rw [pow_mul,
    norm_sq_scalarRemovedStaticChoiKrylovCarrier_one_eq hd energy (target w) henergyZero]

end RHTower
