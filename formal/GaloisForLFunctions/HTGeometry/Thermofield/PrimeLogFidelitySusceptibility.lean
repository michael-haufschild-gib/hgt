import GaloisForLFunctions.HTGeometry.Thermofield.PrimeLogApplications
import GaloisForLFunctions.HTGeometry.PureStateReplicaProjectiveGramLaw

/-!
# Inverse-gap fidelity susceptibility of the prime-log Hamiltonian

The spectral response formula in Telles de Miranda--Micklitz,
arXiv:2608.16847, weights perturbations by inverse squared energy gaps.
Every vacuum and prime level of the corpus's multiplicative Hamiltonian is
simple, so its horizontal response and projective susceptibility are defined
without a nondegeneracy premise. Positive energy dilation gives an exact
inverse-square susceptibility law.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.Thermofield

/-- The first-order eigenvector response, orthogonal to the selected energy level. -/
def primeLogSpectralResponse (P : Finset Nat.Primes) (s : ℝ)
    (a : Option P) (forcing : Option P → ℂ) (i : Option P) : ℂ :=
  if i = a then 0 else forcing i /
    ((Real.exp s * (primeLogKMSFiniteEnergy P a-primeLogKMSFiniteEnergy P i) : ℝ) : ℂ)

/-- The response solves the linearized eigenvector equation on every spectral coordinate. -/
theorem primeLogSpectralResponse_equation (P : Finset Nat.Primes) (s : ℝ)
    (a : Option P) (forcing : Option P → ℂ) (i : Option P) :
    ((Real.exp s * (primeLogKMSFiniteEnergy P a-primeLogKMSFiniteEnergy P i) : ℝ) : ℂ) *
        primeLogSpectralResponse P s a forcing i =
      forcing i - if i = a then forcing a else 0 := by
  classical
  by_cases hi : i = a
  · simp [primeLogSpectralResponse, hi]
  · have hg : primeLogKMSFiniteEnergy P a-primeLogKMSFiniteEnergy P i ≠ 0 :=
      sub_ne_zero.mpr (fun h => hi ((primeLog_energy_injective P) h).symm)
    have hd : ((Real.exp s *
        (primeLogKMSFiniteEnergy P a-primeLogKMSFiniteEnergy P i) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (mul_ne_zero (Real.exp_pos s).ne' hg)
    simp only [primeLogSpectralResponse, if_neg hi, sub_zero]
    field_simp

/-- Squared norm of the horizontal spectral response. -/
def primeLogFidelitySusceptibility (P : Finset Nat.Primes) (s : ℝ)
    (a : Option P) (forcing : Option P → ℂ) : ℝ :=
  ∑ i, ‖primeLogSpectralResponse P s a forcing i‖^2

/-- Exact inverse-square gap formula for every vacuum or prime eigenstate. -/
theorem primeLogFidelitySusceptibility_sum (P : Finset Nat.Primes) (s : ℝ)
    (a : Option P) (forcing : Option P → ℂ) :
    primeLogFidelitySusceptibility P s a forcing =
      ∑ i, if i = a then 0 else ‖forcing i‖^2 /
        ((Real.exp s)^2 * (primeLogKMSFiniteEnergy P a-primeLogKMSFiniteEnergy P i)^2) := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = a
  · simp [primeLogSpectralResponse, hi]
  · simp only [primeLogSpectralResponse, if_neg hi, norm_div, div_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]

/-- Spectral susceptibility is nonnegative for every forcing. -/
theorem primeLogFidelitySusceptibility_nonneg (P : Finset Nat.Primes) (s : ℝ)
    (a : Option P) (forcing : Option P → ℂ) :
    0 ≤ primeLogFidelitySusceptibility P s a forcing :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Exactly the forcing supported on the chosen level is invisible to the projective response. -/
theorem primeLogFidelitySusceptibility_eq_zero_iff (P : Finset Nat.Primes) (s : ℝ)
    (a : Option P) (forcing : Option P → ℂ) :
    primeLogFidelitySusceptibility P s a forcing = 0 ↔
      ∀ i, i ≠ a → forcing i = 0 := by
  classical
  rw [primeLogFidelitySusceptibility,
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  constructor
  · intro h i hi
    have hz := norm_eq_zero.mp (sq_eq_zero_iff.mp (h i (Finset.mem_univ i)))
    have he := primeLogSpectralResponse_equation P s a forcing i
    rw [hz, mul_zero, if_neg hi, sub_zero] at he
    exact he.symm
  · intro h i _
    by_cases hi : i = a
    · simp [primeLogSpectralResponse, hi]
    · simp [primeLogSpectralResponse, hi, h i hi]

/-- The selected basis state has unit norm in the corpus's pure-state inner product. -/
theorem primeLogBasis_normalized (P : Finset Nat.Primes) (a : Option P) :
    finiteComplexInner (Pi.single a 1) (Pi.single a 1) = 1 := by
  classical
  simp [finiteComplexInner, Pi.single_apply]

/-- The inverse-gap response is already horizontal at its selected eigenstate. -/
theorem primeLogSpectralResponse_horizontal (P : Finset Nat.Primes) (s : ℝ)
    (a : Option P) (forcing : Option P → ℂ) :
    finitePureStateHorizontalTangent (Pi.single a 1)
      (primeLogSpectralResponse P s a forcing) = primeLogSpectralResponse P s a forcing := by
  classical
  have h : finiteComplexInner (Pi.single a 1) (primeLogSpectralResponse P s a forcing) = 0 := by
    simp [finiteComplexInner, Pi.single_apply, primeLogSpectralResponse]
  funext i
  simp only [finitePureStateHorizontalTangent, h, mul_zero, sub_zero]

/-- The corpus's projective information metric is exactly the spectral-gap susceptibility. -/
theorem primeLogSpectralResponse_projectiveGram (P : Finset Nat.Primes) (s : ℝ)
    (a : Option P) (forcing : Option P → ℂ) :
    finitePureStateProjectiveGram (Pi.single a 1)
      (fun _ : Fin 1 => primeLogSpectralResponse P s a forcing) 0 0 =
      primeLogFidelitySusceptibility P s a forcing := by
  simp only [finitePureStateProjectiveGram, primeLogSpectralResponse_horizontal,
    finiteComplexInner, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    primeLogFidelitySusceptibility, ← Complex.ofReal_sum, Complex.ofReal_re]

/-- Replicas amplify this inverse-gap metric linearly, with no change of spectral weights. -/
theorem primeLogSpectralResponse_replicaGram (P : Finset Nat.Primes) (r : ℕ) (s : ℝ)
    (a : Option P) (forcing : Option P → ℂ) :
    finitePureStateReplicaProjectiveGram r (Pi.single a 1)
      (fun _ : Fin 1 => primeLogSpectralResponse P s a forcing) 0 0 =
      (r : ℝ) * primeLogFidelitySusceptibility P s a forcing := by
  rw [finitePureStateReplicaProjectiveGram_eq_smul _ _ _ (primeLogBasis_normalized P a)]
  change (r : ℝ) * finitePureStateProjectiveGram (Pi.single a 1)
    (fun _ : Fin 1 => primeLogSpectralResponse P s a forcing) 0 0 = _
  rw [primeLogSpectralResponse_projectiveGram]

/-- Energy dilation suppresses susceptibility by its exact inverse square. -/
theorem primeLogFidelitySusceptibility_energy_scaling (P : Finset Nat.Primes) (s : ℝ)
    (a : Option P) (forcing : Option P → ℂ) :
    primeLogFidelitySusceptibility P s a forcing =
      (Real.exp s)^(-2 : ℤ) * primeLogFidelitySusceptibility P 0 a forcing := by
  classical
  rw [primeLogFidelitySusceptibility_sum, primeLogFidelitySusceptibility_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = a
  · simp [hi]
  · simp only [if_neg hi, Real.exp_zero, one_pow, one_mul]
    rw [zpow_neg, zpow_natCast]
    ring

end GaloisForLFunctions.HTGeometry.Thermofield
