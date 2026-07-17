import GaloisForLFunctions.RHTower.PrimeHarmonicLogLower
import GaloisForLFunctions.RHTower.PrimeBarycentricCoefficientDivergence

/-!
# Critical prime Poisson--GCD Möbius vacuum

The two-state critical prime block has weight `q_p = p⁻¹`.  Its source feature

`z ↦ (1, 1-z)`

is equipped with the positive diagonal form with weights `(1-q_p, q_p)`.  The resulting kernel is

`1 - q_p w - q_p conj(z) + q_p conj(z)w`.

The pointed phase has local energy `1-p⁻¹`, whereas the antipodal phase has local energy
`1+3p⁻¹`.  Over the primes below a cutoff, the ratio of these energies grows at least like
`4 log log(X+1)-3`.  Thus no scalar completion can keep the pointed Möbius vacuum and the full
prime-phase fibre uniformly comparable at the critical boundary.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The squared critical Euler amplitude at a finite prime. -/
def criticalPrimePoissonWeight (p : ℕ) : ℝ := ((p : ℝ))⁻¹

/-- The source feature before the positive prime weights are applied. -/
def criticalPrimePoissonLocalFeature (z : ℂ) : ℂ × ℂ := (1, 1 - z)

/-- The positive two-channel local prime form, with weights `1-p⁻¹` and `p⁻¹`. -/
def criticalPrimePoissonLocalGram (p : ℕ) (x y : ℂ × ℂ) : ℂ :=
  ((1 - criticalPrimePoissonWeight p : ℝ) : ℂ) * starRingEnd ℂ x.1 * y.1 +
    (criticalPrimePoissonWeight p : ℂ) * starRingEnd ℂ x.2 * y.2

/-- The critical local prime kernel is definitionally a weighted Gram kernel. -/
def criticalPrimePoissonLocalKernel (p : ℕ) (z w : ℂ) : ℂ :=
  criticalPrimePoissonLocalGram p
    (criticalPrimePoissonLocalFeature z) (criticalPrimePoissonLocalFeature w)

theorem criticalPrimePoissonWeight_pos {p : ℕ} (hp : p.Prime) :
    0 < criticalPrimePoissonWeight p := by
  rw [criticalPrimePoissonWeight]
  exact inv_pos.mpr (by exact_mod_cast hp.pos)

theorem criticalPrimePoissonWeight_lt_one {p : ℕ} (hp : p.Prime) :
    criticalPrimePoissonWeight p < 1 := by
  rw [criticalPrimePoissonWeight]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

theorem criticalPrimePoissonLocalKernel_eq
    (p : ℕ) (z w : ℂ) :
    criticalPrimePoissonLocalKernel p z w =
      1 - (criticalPrimePoissonWeight p : ℂ) * w -
        (criticalPrimePoissonWeight p : ℂ) * starRingEnd ℂ z +
          (criticalPrimePoissonWeight p : ℂ) * starRingEnd ℂ z * w := by
  simp only [criticalPrimePoissonLocalKernel, criticalPrimePoissonLocalGram,
    criticalPrimePoissonLocalFeature, map_one, map_sub]
  push_cast
  ring

/-- Every phase has the same pairing with the pointed Möbius vacuum. -/
theorem criticalPrimePoissonLocalKernel_pointed_right
    (p : ℕ) (z : ℂ) :
    criticalPrimePoissonLocalKernel p z 1 =
      ((1 - criticalPrimePoissonWeight p : ℝ) : ℂ) := by
  rw [criticalPrimePoissonLocalKernel_eq]
  push_cast
  ring

/-- The local pointed Möbius-vacuum energy. -/
theorem criticalPrimePoissonLocalKernel_pointed (p : ℕ) :
    criticalPrimePoissonLocalKernel p 1 1 =
      ((1 - criticalPrimePoissonWeight p : ℝ) : ℂ) := by
  exact criticalPrimePoissonLocalKernel_pointed_right p 1

/-- The local energy of the antipodal prime phase. -/
theorem criticalPrimePoissonLocalKernel_antipode (p : ℕ) :
    criticalPrimePoissonLocalKernel p (-1) (-1) =
      ((1 + 3 * criticalPrimePoissonWeight p : ℝ) : ℂ) := by
  rw [criticalPrimePoissonLocalKernel_eq]
  norm_num
  ring

/-- Tensor-product finite-prime kernel. -/
def finiteCriticalPrimePoissonKernel
    (S : Finset ℕ) (z w : ℕ → ℂ) : ℂ :=
  ∏ p ∈ S, criticalPrimePoissonLocalKernel p (z p) (w p)

/-- Squared norm of the finite pointed Möbius vacuum. -/
def finiteCriticalPrimeMobiusVacuumEnergy (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, (1 - criticalPrimePoissonWeight p)

/-- Squared norm of the finite antipodal prime phase. -/
def finiteCriticalPrimeMobiusAntipodeEnergy (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, (1 + 3 * criticalPrimePoissonWeight p)

/-- Relative antipodal-to-pointed energy. -/
def finiteCriticalPrimeMobiusPhaseDistortion (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S,
    (1 + 3 * criticalPrimePoissonWeight p) /
      (1 - criticalPrimePoissonWeight p)

theorem finiteCriticalPrimePoissonKernel_pointed (S : Finset ℕ) :
    finiteCriticalPrimePoissonKernel S (fun _ => 1) (fun _ => 1) =
      (finiteCriticalPrimeMobiusVacuumEnergy S : ℂ) := by
  rw [finiteCriticalPrimePoissonKernel, finiteCriticalPrimeMobiusVacuumEnergy]
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
    criticalPrimePoissonLocalKernel_pointed p

theorem finiteCriticalPrimePoissonKernel_antipode (S : Finset ℕ) :
    finiteCriticalPrimePoissonKernel S (fun _ => -1) (fun _ => -1) =
      (finiteCriticalPrimeMobiusAntipodeEnergy S : ℂ) := by
  rw [finiteCriticalPrimePoissonKernel, finiteCriticalPrimeMobiusAntipodeEnergy]
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one,
    Complex.ofReal_ofNat] using criticalPrimePoissonLocalKernel_antipode p

theorem finiteCriticalPrimeMobiusVacuumEnergy_pos
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    0 < finiteCriticalPrimeMobiusVacuumEnergy S := by
  rw [finiteCriticalPrimeMobiusVacuumEnergy]
  exact Finset.prod_pos fun p hp => sub_pos.mpr
    (criticalPrimePoissonWeight_lt_one (hS p hp))

theorem finiteCriticalPrimeMobiusPhaseDistortion_pos
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    0 < finiteCriticalPrimeMobiusPhaseDistortion S := by
  rw [finiteCriticalPrimeMobiusPhaseDistortion]
  apply Finset.prod_pos
  intro p hp
  exact div_pos (by
    nlinarith [criticalPrimePoissonWeight_pos (hS p hp)])
    (sub_pos.mpr (criticalPrimePoissonWeight_lt_one (hS p hp)))

/-- The antipodal energy is exactly the pointed energy times the phase distortion. -/
theorem finiteCriticalPrimeMobiusVacuumEnergy_mul_phaseDistortion
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    finiteCriticalPrimeMobiusVacuumEnergy S *
        finiteCriticalPrimeMobiusPhaseDistortion S =
      finiteCriticalPrimeMobiusAntipodeEnergy S := by
  rw [finiteCriticalPrimeMobiusVacuumEnergy,
    finiteCriticalPrimeMobiusPhaseDistortion,
    finiteCriticalPrimeMobiusAntipodeEnergy, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hden : 1 - criticalPrimePoissonWeight p ≠ 0 :=
    ne_of_gt (sub_pos.mpr (criticalPrimePoissonWeight_lt_one (hS p hp)))
  field_simp

/-- One local antipodal/vacuum ratio dominates its first reciprocal-prime term. -/
theorem one_add_four_mul_inv_le_criticalPrimeMobiusPhaseDistortionFactor
    {p : ℕ} (hp : p.Prime) :
    1 + 4 * criticalPrimePoissonWeight p ≤
      (1 + 3 * criticalPrimePoissonWeight p) /
        (1 - criticalPrimePoissonWeight p) := by
  have hq0 : 0 ≤ criticalPrimePoissonWeight p :=
    (criticalPrimePoissonWeight_pos hp).le
  have hden : 0 < 1 - criticalPrimePoissonWeight p :=
    sub_pos.mpr (criticalPrimePoissonWeight_lt_one hp)
  apply (le_div_iff₀ hden).2
  nlinarith [sq_nonneg (criticalPrimePoissonWeight p)]

/-- Finite prime distortion dominates the first-order prime-harmonic mass. -/
theorem one_add_four_mul_primeHarmonicSum_le_phaseDistortion
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    1 + 4 * (∑ p ∈ S, ((p : ℝ))⁻¹) ≤
      finiteCriticalPrimeMobiusPhaseDistortion S := by
  let u : ℕ → ℝ := fun p => 4 * criticalPrimePoissonWeight p
  have hu : ∀ p ∈ S, 0 ≤ u p := by
    intro p hp
    exact mul_nonneg (by norm_num) (criticalPrimePoissonWeight_pos (hS p hp)).le
  calc
    1 + 4 * (∑ p ∈ S, ((p : ℝ))⁻¹) =
        1 + ∑ p ∈ S, u p := by
          rw [Finset.mul_sum]
          rfl
    _ ≤ ∏ p ∈ S, (1 + u p) := one_add_sum_le_prod_one_add S u hu
    _ ≤ finiteCriticalPrimeMobiusPhaseDistortion S := by
      rw [finiteCriticalPrimeMobiusPhaseDistortion]
      apply Finset.prod_le_prod
      · intro p hp
        linarith [hu p hp]
      · intro p hp
        exact one_add_four_mul_inv_le_criticalPrimeMobiusPhaseDistortionFactor
          (hS p hp)

/-- Quantitative critical-boundary obstruction: the antipodal/vacuum ratio over all primes up to
`X` is at least `4 log log(X+1)-3`. -/
theorem four_mul_log_log_sub_three_le_primesBelow_phaseDistortion
    (X : ℕ) (hX : 1 ≤ X) :
    4 * Real.log (Real.log ((X : ℝ) + 1)) - 3 ≤
      finiteCriticalPrimeMobiusPhaseDistortion (Nat.primesBelow (X + 1)) := by
  have hprime : ∀ p ∈ Nat.primesBelow (X + 1), p.Prime :=
    fun p hp => Nat.prime_of_mem_primesBelow hp
  have hprod := one_add_four_mul_primeHarmonicSum_le_phaseDistortion hprime
  have hharm := log_log_sub_one_le_sum_primesBelow_inv X hX
  linarith

/-- Any nonnegative scalar normalization that retains the pointed vacuum forces the normalized
antipodal energy to inherit the same explicit `log log` distortion. -/
theorem scalarNormalized_vacuum_mul_logLower_le_antipode
    (X : ℕ) (hX : 1 ≤ X) (a : ℝ) (ha : 0 ≤ a) :
    (a * finiteCriticalPrimeMobiusVacuumEnergy (Nat.primesBelow (X + 1))) *
        (4 * Real.log (Real.log ((X : ℝ) + 1)) - 3) ≤
      a * finiteCriticalPrimeMobiusAntipodeEnergy (Nat.primesBelow (X + 1)) := by
  have hprime : ∀ p ∈ Nat.primesBelow (X + 1), p.Prime :=
    fun p hp => Nat.prime_of_mem_primesBelow hp
  have hvac : 0 ≤ finiteCriticalPrimeMobiusVacuumEnergy (Nat.primesBelow (X + 1)) :=
    (finiteCriticalPrimeMobiusVacuumEnergy_pos hprime).le
  have hdist := four_mul_log_log_sub_three_le_primesBelow_phaseDistortion X hX
  have hmul := mul_le_mul_of_nonneg_left hdist (mul_nonneg ha hvac)
  calc
    (a * finiteCriticalPrimeMobiusVacuumEnergy (Nat.primesBelow (X + 1))) *
        (4 * Real.log (Real.log ((X : ℝ) + 1)) - 3) =
      (a * finiteCriticalPrimeMobiusVacuumEnergy (Nat.primesBelow (X + 1))) *
        (4 * Real.log (Real.log ((X : ℝ) + 1)) - 3) := rfl
    _ ≤ (a * finiteCriticalPrimeMobiusVacuumEnergy (Nat.primesBelow (X + 1))) *
        finiteCriticalPrimeMobiusPhaseDistortion (Nat.primesBelow (X + 1)) := hmul
    _ = a * (finiteCriticalPrimeMobiusVacuumEnergy (Nat.primesBelow (X + 1)) *
        finiteCriticalPrimeMobiusPhaseDistortion (Nat.primesBelow (X + 1))) := by ring
    _ = a * finiteCriticalPrimeMobiusAntipodeEnergy (Nat.primesBelow (X + 1)) := by
      rw [finiteCriticalPrimeMobiusVacuumEnergy_mul_phaseDistortion hprime]

end RHTower
