import GaloisForLFunctions.HTGeometry.FiniteKMSWightman

/-!
# Finite KMS detailed balance and fluctuation--dissipation values

The Gibbs transition intensity of a Hermitian observable is an unsymmetrized thermal spectral
value.  Its two orientations obey exact KMS detailed balance.  Relative to the symmetric
Wightman half-density, their difference and sum acquire the universal `sinh` and `cosh` factors;
their ratio is the finite spectral fluctuation--dissipation law.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Unsymmetrized Gibbs transition intensity, with `b` the source state. -/
def finiteGibbsTransitionIntensity {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (a b : α) : ℝ :=
  finiteGibbsStateWeight β energy b * Complex.normSq (amplitude a b)

theorem finiteGibbsTransitionIntensity_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (a b : α) :
    0 ≤ finiteGibbsTransitionIntensity β energy amplitude a b := by
  exact mul_nonneg (finiteGibbsStateWeight_pos β energy b).le
    (Complex.normSq_nonneg _)

/-- The Gibbs spectral intensity is the Wightman half-density intensity multiplied by half of
the detailed-balance exponential. -/
theorem finiteGibbsTransitionIntensity_eq_exp_half_mul_wightman
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (a b : α) :
    finiteGibbsTransitionIntensity β energy amplitude a b =
      Real.exp (β * (energy a - energy b) / 2) *
        finiteKMSWightmanTransitionIntensity β energy amplitude a b := by
  have hexp : Real.exp (-β * energy b) =
      Real.exp (β * (energy a - energy b) / 2) *
        Real.exp (-β * ((energy a + energy b) / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [finiteGibbsTransitionIntensity, finiteGibbsStateWeight,
    finiteKMSWightmanTransitionIntensity, wightmanTransitionIntensity,
    finiteKMSWightmanWeight]
  rw [hexp]
  ring

/-- Finite Gibbs transition values obey exact KMS detailed balance for a Hermitian observable. -/
theorem finiteGibbsTransitionIntensity_detailedBalance
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) (a b : α) :
    finiteGibbsTransitionIntensity β energy amplitude a b =
      Real.exp (β * (energy a - energy b)) *
        finiteGibbsTransitionIntensity β energy amplitude b a := by
  rw [finiteGibbsTransitionIntensity_eq_exp_half_mul_wightman,
    finiteGibbsTransitionIntensity_eq_exp_half_mul_wightman,
    finiteKMSWightmanTransitionIntensity_symm β energy amplitude hHermitian a b]
  have hexp : Real.exp (β * (energy a - energy b) / 2) =
      Real.exp (β * (energy a - energy b)) *
        Real.exp (β * (energy b - energy a) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- Spectral weight of the thermal commutator. -/
def finiteKMSCommutatorTransitionIntensity {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (a b : α) : ℝ :=
  finiteGibbsTransitionIntensity β energy amplitude a b -
    finiteGibbsTransitionIntensity β energy amplitude b a

/-- Spectral weight of the symmetrized thermal fluctuation. -/
def finiteKMSSymmetricTransitionIntensity {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (a b : α) : ℝ :=
  finiteGibbsTransitionIntensity β energy amplitude a b +
    finiteGibbsTransitionIntensity β energy amplitude b a

/-- Half-density form of the finite fluctuation--dissipation numerator. -/
theorem finiteKMSCommutatorTransitionIntensity_eq_sinh
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) (a b : α) :
    finiteKMSCommutatorTransitionIntensity β energy amplitude a b =
      2 * Real.sinh (β * (energy a - energy b) / 2) *
        finiteKMSWightmanTransitionIntensity β energy amplitude a b := by
  rw [finiteKMSCommutatorTransitionIntensity,
    finiteGibbsTransitionIntensity_eq_exp_half_mul_wightman,
    finiteGibbsTransitionIntensity_eq_exp_half_mul_wightman,
    finiteKMSWightmanTransitionIntensity_symm β energy amplitude hHermitian a b,
    Real.sinh_eq]
  have hneg : β * (energy b - energy a) / 2 =
      -(β * (energy a - energy b) / 2) := by ring
  rw [hneg]
  ring

/-- Half-density form of the finite symmetrized thermal fluctuation. -/
theorem finiteKMSSymmetricTransitionIntensity_eq_cosh
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) (a b : α) :
    finiteKMSSymmetricTransitionIntensity β energy amplitude a b =
      2 * Real.cosh (β * (energy a - energy b) / 2) *
        finiteKMSWightmanTransitionIntensity β energy amplitude a b := by
  rw [finiteKMSSymmetricTransitionIntensity,
    finiteGibbsTransitionIntensity_eq_exp_half_mul_wightman,
    finiteGibbsTransitionIntensity_eq_exp_half_mul_wightman,
    finiteKMSWightmanTransitionIntensity_symm β energy amplitude hHermitian a b,
    Real.cosh_eq]
  have hneg : β * (energy b - energy a) / 2 =
      -(β * (energy a - energy b) / 2) := by ring
  rw [hneg]
  ring

/-- Exact finite spectral fluctuation--dissipation relation. -/
theorem finiteKMSCommutatorTransitionIntensity_eq_tanh_mul_symmetric
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) (a b : α) :
    finiteKMSCommutatorTransitionIntensity β energy amplitude a b =
      Real.tanh (β * (energy a - energy b) / 2) *
        finiteKMSSymmetricTransitionIntensity β energy amplitude a b := by
  rw [finiteKMSCommutatorTransitionIntensity_eq_sinh β energy amplitude hHermitian,
    finiteKMSSymmetricTransitionIntensity_eq_cosh β energy amplitude hHermitian,
    Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos (β * (energy a - energy b) / 2)).ne']

end

end HTGeometry
