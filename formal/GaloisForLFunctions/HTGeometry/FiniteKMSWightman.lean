import GaloisForLFunctions.HTGeometry.ThermalKrylovMoments

/-!
# Finite KMS/Wightman value relations

For a finite Hamiltonian spectrum, the Wightman half-density inner product weights a transition
`a → b` by

`exp (-β (E_a + E_b) / 2) / Z_β`.

This file records the exact finite-temperature value relations that matter to the moment corpus:

* the partition function and every Wightman weight are positive;
* the Wightman pair weight is symmetric and its square is the product of the endpoint Gibbs
  probabilities;
* a Hermitian observable therefore has a nonnegative symmetric transition intensity;
* ordinary and shifted Hankel positivity require no separately supplied weight hypothesis, and all
  odd Liouvillian moments vanish.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Canonical partition function of a finite Hamiltonian spectrum. -/
def finiteGibbsPartition {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) : ℝ :=
  ∑ a, Real.exp (-β * energy a)

/-- A nonempty finite Hamiltonian has strictly positive partition function. -/
theorem finiteGibbsPartition_pos {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) :
    0 < finiteGibbsPartition β energy := by
  rw [finiteGibbsPartition]
  exact Finset.sum_pos (fun a _ => Real.exp_pos _) Finset.univ_nonempty

/-- Normalized Gibbs probability of an energy eigenstate. -/
def finiteGibbsStateWeight {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (a : α) : ℝ :=
  Real.exp (-β * energy a) / finiteGibbsPartition β energy

/-- The finite Gibbs probabilities have total mass one. -/
theorem sum_finiteGibbsStateWeight_eq_one
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) :
    ∑ a, finiteGibbsStateWeight β energy a = 1 := by
  simp_rw [finiteGibbsStateWeight]
  rw [← Finset.sum_div]
  change finiteGibbsPartition β energy / finiteGibbsPartition β energy = 1
  exact div_self (ne_of_gt (finiteGibbsPartition_pos β energy))

/-- Gibbs probabilities are strictly positive. -/
theorem finiteGibbsStateWeight_pos
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (a : α) :
    0 < finiteGibbsStateWeight β energy a := by
  exact div_pos (Real.exp_pos _) (finiteGibbsPartition_pos β energy)

/-- The symmetric half-density weight occurring in the finite-temperature Wightman inner product. -/
def finiteKMSWightmanWeight {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (a b : α) : ℝ :=
  Real.exp (-β * ((energy a + energy b) / 2)) /
    finiteGibbsPartition β energy

/-- Canonical finite Wightman weights are strictly positive. -/
theorem finiteKMSWightmanWeight_pos {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (a b : α) :
    0 < finiteKMSWightmanWeight β energy a b := by
  exact div_pos (Real.exp_pos _) (finiteGibbsPartition_pos β energy)

/-- The half-density Wightman weight is symmetric under exchange of transitions. -/
theorem finiteKMSWightmanWeight_symm {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (a b : α) :
    finiteKMSWightmanWeight β energy a b =
      finiteKMSWightmanWeight β energy b a := by
  simp only [finiteKMSWightmanWeight]
  congr 2
  ring

/-- On the diagonal, the Wightman half-density equals the Gibbs probability. -/
theorem finiteKMSWightmanWeight_self {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (a : α) :
    finiteKMSWightmanWeight β energy a a =
      finiteGibbsStateWeight β energy a := by
  simp only [finiteKMSWightmanWeight, finiteGibbsStateWeight]
  congr 2
  ring

/-- The Wightman pair weight is exactly the geometric-mean coupling of the endpoint Gibbs
probabilities, expressed without square roots. -/
theorem finiteKMSWightmanWeight_sq {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (a b : α) :
    finiteKMSWightmanWeight β energy a b ^ 2 =
      finiteGibbsStateWeight β energy a *
        finiteGibbsStateWeight β energy b := by
  simp only [finiteKMSWightmanWeight, finiteGibbsStateWeight]
  have hexp : Real.exp (-β * ((energy a + energy b) / 2)) ^ 2 =
      Real.exp (-β * energy a) * Real.exp (-β * energy b) := by
    calc
      Real.exp (-β * ((energy a + energy b) / 2)) ^ 2 =
          Real.exp
            ((-β * ((energy a + energy b) / 2)) +
              (-β * ((energy a + energy b) / 2))) := by
            rw [pow_two, Real.exp_add]
      _ = Real.exp ((-β * energy a) + (-β * energy b)) := by
            congr 1
            ring
      _ = Real.exp (-β * energy a) * Real.exp (-β * energy b) :=
            Real.exp_add _ _
  rw [div_pow, hexp]
  ring

/-- Canonical finite-temperature Wightman transition intensity. -/
def finiteKMSWightmanTransitionIntensity {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (a b : α) : ℝ :=
  wightmanTransitionIntensity (finiteKMSWightmanWeight β energy) amplitude a b

/-- Positivity of canonical Wightman intensities requires no user-supplied weight hypothesis. -/
theorem finiteKMSWightmanTransitionIntensity_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (a b : α) :
    0 ≤ finiteKMSWightmanTransitionIntensity β energy amplitude a b := by
  apply wightmanTransitionIntensity_nonneg
  intro i j
  exact (finiteKMSWightmanWeight_pos β energy i j).le

/-- A Hermitian observable makes the canonical Wightman transition spectrum symmetric. -/
theorem finiteKMSWightmanTransitionIntensity_symm
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) (a b : α) :
    finiteKMSWightmanTransitionIntensity β energy amplitude a b =
      finiteKMSWightmanTransitionIntensity β energy amplitude b a := by
  apply wightmanTransitionIntensity_symm
  · exact finiteKMSWightmanWeight_symm β energy
  · exact hHermitian

/-- Canonical Wightman data automatically cancel every odd Liouvillian moment. -/
theorem finiteKMSWightman_thermalGapMoment_odd_eq_zero
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b))
    {k : ℕ} (hk : Odd k) :
    thermalGapMoment
      (finiteKMSWightmanTransitionIntensity β energy amplitude) energy k = 0 := by
  exact thermalGapMoment_odd_eq_zero _ energy
    (finiteKMSWightmanTransitionIntensity_symm β energy amplitude hHermitian) hk

/-- Canonical Wightman data automatically produce every ordinary Hankel-square inequality. -/
theorem momentFunctional_finiteKMSWightmanEvenGapMoment_sq_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (p : Polynomial ℝ) :
    0 ≤ momentFunctional
      (thermalEvenGapMoment
        (finiteKMSWightmanTransitionIntensity β energy amplitude) energy) (p ^ 2) := by
  exact momentFunctional_thermalEvenGapMoment_sq_nonneg _ energy
    (finiteKMSWightmanTransitionIntensity_nonneg β energy amplitude) p

/-- Canonical Wightman data automatically produce every shifted Stieltjes-Hankel inequality. -/
theorem momentFunctional_X_mul_sq_finiteKMSWightmanEvenGapMoment_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (p : Polynomial ℝ) :
    0 ≤ momentFunctional
      (thermalEvenGapMoment
        (finiteKMSWightmanTransitionIntensity β energy amplitude) energy)
        (Polynomial.X * p ^ 2) := by
  exact momentFunctional_X_mul_sq_thermalEvenGapMoment_nonneg _ energy
    (finiteKMSWightmanTransitionIntensity_nonneg β energy amplitude) p

end

end HTGeometry
