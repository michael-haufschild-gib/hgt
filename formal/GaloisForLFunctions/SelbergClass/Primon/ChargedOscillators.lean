import GaloisForLFunctions.HTGeometry.CPVTwoModeFock

/-!
# Charged primon oscillators on polynomial Fock space

The Hamiltonian and charge in Hartnoll–Yang, arXiv:2502.02661v2, (79), act on
the existing two-mode polynomial Fock domain. Removing the Cartan vacuum
shift gives energy `log p` per particle. Pair creation raises energy by
`2 log p` while preserving charge. All identities are operator identities
on the concrete polynomial domain.
-/

namespace GaloisForLFunctions.SelbergClass.Primon
open HTGeometry.CPV
noncomputable section

/-- Prime-frequency two-mode Hamiltonian with zero vacuum energy. -/
def primonHamiltonian (p : Nat.Primes) : FockEnd :=
  (Real.log (p : ℝ) : ℂ) • (pairCartan - 1)

/-- Charge is conserved by the primon Hamiltonian on the full Fock domain. -/
theorem primonHamiltonian_comm_charge (p : Nat.Primes) :
    primonHamiltonian p * pairCharge = pairCharge * primonHamiltonian p := by
  simp only [primonHamiltonian, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub,
    one_mul, mul_one, pairCharge_cartan]

/-- Exact energy of a state with `n` pairs and `d` unpaired particles. -/
theorem primonHamiltonian_state (p : Nat.Primes) (d n : ℕ) :
    primonHamiltonian p (pairState d n) =
      ((Real.log (p : ℝ) : ℂ) * (2 * (n : ℂ) + d)) • pairState d n := by
  simp only [primonHamiltonian, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.one_apply, pairCartan_state]
  simp [MvPolynomial.smul_eq_C_mul]
  ring

/-- The oscillator vacuum has zero energy at every prime. -/
theorem primonHamiltonian_vacuum (p : Nat.Primes) :
    primonHamiltonian p (pairState 0 0) = 0 := by
  rw [primonHamiltonian_state]
  simp

/-- Pair creation adds exactly twice the prime frequency. -/
theorem primonHamiltonian_create (p : Nat.Primes) :
    primonHamiltonian p * pairCreate - pairCreate * primonHamiltonian p =
      (2 * (Real.log (p : ℝ) : ℂ)) • pairCreate := by
  unfold primonHamiltonian
  generalize (Real.log (p : ℝ) : ℂ) = c
  simp only [smul_mul_assoc, mul_smul_comm,
    sub_mul, mul_sub, one_mul, mul_one]
  have h : (pairCartan * pairCreate - pairCreate) -
      (pairCreate * pairCartan - pairCreate) =
      pairCartan * pairCreate - pairCreate * pairCartan := by abel
  rw [← smul_sub, h, pairCartan_create, smul_smul, mul_comm]

/-- Chemical-potential weighting remains diagonal in the concrete charge basis. -/
theorem primon_grandCanonical_state (p : Nat.Primes) (β θ : ℝ) (d n : ℕ) :
    ((-(β : ℂ)) • primonHamiltonian p +
      ((θ : ℂ) * Complex.I) • pairCharge) (pairState d n) =
    (-((β : ℂ) * (Real.log (p : ℝ) : ℂ) * (2 * (n : ℂ) + d)) +
      (θ : ℂ) * Complex.I * d) • pairState d n := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply,
    primonHamiltonian_state, pairCharge_state, smul_smul, ← add_smul]
  congr 1
  ring

end
end GaloisForLFunctions.SelbergClass.Primon
