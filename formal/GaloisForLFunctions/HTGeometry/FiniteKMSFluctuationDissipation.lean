import GaloisForLFunctions.HTGeometry.FiniteKMSDetailedBalance
import GaloisForLFunctions.HTGeometry.FinitePassiveResponse

/-!
# Finite KMS fluctuation--dissipation value relations

For a finite Hamiltonian, the symmetric KMS half-density and, for Hermitian amplitudes, the signed
commutator spectrum are related pointwise by the exact fluctuation--dissipation identity

`2 sinh (β (E_a - E_b) / 2) Iᵂ_ab = (p_b - p_a) |A_ab|²`.

Multiplication by the energy gap removes the sign: at nonnegative inverse temperature,

`(E_a - E_b) 2 sinh (β (E_a - E_b) / 2) Iᵂ_ab ≥ 0`.

Thus the energy-dissipation spectrum supplies the nonnegative-intensity hypotheses of the finite
passive-response and Stieltjes--Hankel APIs directly.  For a Hermitian amplitude it is symmetric,
while the underlying commutator spectrum is antisymmetric.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Weight-level finite KMS fluctuation--dissipation identity.  The symmetric thermofield
half-density becomes the difference of the endpoint Gibbs populations after multiplication by the
thermal commutator factor. -/
theorem two_mul_sinh_mul_finiteKMSWightmanWeight_eq_stateWeight_sub
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (a b : α) :
    2 * Real.sinh (β * (energy a - energy b) / 2) *
        finiteKMSWightmanWeight β energy a b =
      finiteGibbsStateWeight β energy b -
        finiteGibbsStateWeight β energy a := by
  rw [finiteKMSWightmanWeight, finiteGibbsStateWeight,
    finiteGibbsStateWeight]
  have hforward :
      Real.exp (β * (energy a - energy b) / 2) *
          Real.exp (-β * ((energy a + energy b) / 2)) =
        Real.exp (-β * energy b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hbackward :
      Real.exp (-(β * (energy a - energy b) / 2)) *
          Real.exp (-β * ((energy a + energy b) / 2)) =
        Real.exp (-β * energy a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    2 * Real.sinh (β * (energy a - energy b) / 2) *
        (Real.exp (-β * ((energy a + energy b) / 2)) /
          finiteGibbsPartition β energy) =
      ((Real.exp (β * (energy a - energy b) / 2) -
          Real.exp (-(β * (energy a - energy b) / 2))) *
        Real.exp (-β * ((energy a + energy b) / 2))) /
          finiteGibbsPartition β energy := by
        rw [Real.sinh_eq]
        ring
    _ = (Real.exp (-β * energy b) - Real.exp (-β * energy a)) /
          finiteGibbsPartition β energy := by
        rw [sub_mul, hforward, hbackward]
    _ = Real.exp (-β * energy b) / finiteGibbsPartition β energy -
          Real.exp (-β * energy a) / finiteGibbsPartition β energy := by
        ring

/-- The commutator intensity is exactly the Gibbs population difference times the squared matrix
element for a Hermitian amplitude.  This eliminates the thermofield half-density from the signed
spectrum. -/
theorem finiteKMSCommutatorTransitionIntensity_eq_stateWeight_sub_mul_normSq
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) (a b : α) :
    finiteKMSCommutatorTransitionIntensity β energy amplitude a b =
      (finiteGibbsStateWeight β energy b -
        finiteGibbsStateWeight β energy a) * Complex.normSq (amplitude a b) := by
  rw [finiteKMSCommutatorTransitionIntensity_eq_sinh β energy amplitude hHermitian,
    finiteKMSWightmanTransitionIntensity, wightmanTransitionIntensity]
  calc
    2 * Real.sinh (β * (energy a - energy b) / 2) *
        (finiteKMSWightmanWeight β energy a b * Complex.normSq (amplitude a b)) =
      (2 * Real.sinh (β * (energy a - energy b) / 2) *
        finiteKMSWightmanWeight β energy a b) * Complex.normSq (amplitude a b) := by
        ring
    _ = (finiteGibbsStateWeight β energy b -
        finiteGibbsStateWeight β energy a) * Complex.normSq (amplitude a b) := by
      rw [two_mul_sinh_mul_finiteKMSWightmanWeight_eq_stateWeight_sub]

/-- The finite KMS commutator spectrum is antisymmetric under reversal by definition. -/
theorem finiteKMSCommutatorTransitionIntensity_antisymm
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (a b : α) :
    finiteKMSCommutatorTransitionIntensity β energy amplitude b a =
      -finiteKMSCommutatorTransitionIntensity β energy amplitude a b := by
  simp only [finiteKMSCommutatorTransitionIntensity]
  ring

/-- Energy-weighted fluctuation--dissipation transform of the symmetric KMS/Wightman intensity.
It is nonnegative even for a directed jump amplitude; for Hermitian amplitudes it is exactly the
energy gap times the thermal commutator intensity. -/
def finiteKMSDissipativeTransitionIntensity {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (a b : α) : ℝ :=
  (energy a - energy b) *
    (2 * Real.sinh (β * (energy a - energy b) / 2) *
      finiteKMSWightmanTransitionIntensity β energy amplitude a b)

/-- Population-difference form of the finite dissipative oscillator strength. -/
theorem finiteKMSDissipativeTransitionIntensity_eq_gap_mul_stateWeight_sub_mul_normSq
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (a b : α) :
    finiteKMSDissipativeTransitionIntensity β energy amplitude a b =
      (energy a - energy b) *
        (finiteGibbsStateWeight β energy b -
          finiteGibbsStateWeight β energy a) * Complex.normSq (amplitude a b) := by
  rw [finiteKMSDissipativeTransitionIntensity,
    finiteKMSWightmanTransitionIntensity, wightmanTransitionIntensity]
  calc
    (energy a - energy b) *
        (2 * Real.sinh (β * (energy a - energy b) / 2) *
          (finiteKMSWightmanWeight β energy a b * Complex.normSq (amplitude a b))) =
      (energy a - energy b) *
        (2 * Real.sinh (β * (energy a - energy b) / 2) *
          finiteKMSWightmanWeight β energy a b) * Complex.normSq (amplitude a b) := by
      ring
    _ = (energy a - energy b) *
        (finiteGibbsStateWeight β energy b -
          finiteGibbsStateWeight β energy a) * Complex.normSq (amplitude a b) := by
      rw [two_mul_sinh_mul_finiteKMSWightmanWeight_eq_stateWeight_sub]

/-- For a Hermitian amplitude, the nonnegative FDT transform is exactly the energy gap times the
signed thermal commutator spectrum already defined by detailed balance. -/
theorem finiteKMSDissipativeTransitionIntensity_eq_gap_mul_commutator
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) (a b : α) :
    finiteKMSDissipativeTransitionIntensity β energy amplitude a b =
      (energy a - energy b) *
        finiteKMSCommutatorTransitionIntensity β energy amplitude a b := by
  rw [finiteKMSDissipativeTransitionIntensity,
    finiteKMSCommutatorTransitionIntensity_eq_sinh β energy amplitude hHermitian]

/-- A real value times the hyperbolic sine of any nonnegative multiple of that value is
nonnegative. -/
theorem mul_sinh_nonneg_of_nonneg_scale {β x : ℝ} (hβ : 0 ≤ β) :
    0 ≤ x * Real.sinh (β * x / 2) := by
  rcases le_total 0 x with hx | hx
  · exact mul_nonneg hx
      (Real.sinh_nonneg_iff.mpr
        (div_nonneg (mul_nonneg hβ hx) (by norm_num)))
  · have hxneg : 0 ≤ -x := neg_nonneg.mpr hx
    have harg : 0 ≤ β * (-x) / 2 :=
      div_nonneg (mul_nonneg hβ hxneg) (by norm_num)
    calc
      0 ≤ (-x) * Real.sinh (β * (-x) / 2) :=
        mul_nonneg hxneg (Real.sinh_nonneg_iff.mpr harg)
      _ = x * Real.sinh (β * x / 2) := by
        rw [show β * x / 2 = -(β * (-x) / 2) by ring, Real.sinh_neg]
        ring

/-- At nonnegative inverse temperature, every finite KMS dissipative transition intensity is
nonnegative.  No independent passivity hypothesis is needed. -/
theorem finiteKMSDissipativeTransitionIntensity_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (hβ : 0 ≤ β)
    (a b : α) :
    0 ≤ finiteKMSDissipativeTransitionIntensity β energy amplitude a b := by
  rw [finiteKMSDissipativeTransitionIntensity]
  have hgap : 0 ≤ (energy a - energy b) *
      Real.sinh (β * (energy a - energy b) / 2) :=
    mul_sinh_nonneg_of_nonneg_scale hβ
  have hW : 0 ≤ finiteKMSWightmanTransitionIntensity β energy amplitude a b :=
    finiteKMSWightmanTransitionIntensity_nonneg β energy amplitude a b
  calc
    0 ≤ 2 * ((energy a - energy b) *
        Real.sinh (β * (energy a - energy b) / 2)) *
          finiteKMSWightmanTransitionIntensity β energy amplitude a b :=
      mul_nonneg (mul_nonneg (by norm_num) hgap) hW
    _ = (energy a - energy b) *
        (2 * Real.sinh (β * (energy a - energy b) / 2) *
          finiteKMSWightmanTransitionIntensity β energy amplitude a b) := by
      ring

/-- For a Hermitian amplitude, the nonnegative dissipative transition spectrum is symmetric. -/
theorem finiteKMSDissipativeTransitionIntensity_symm
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) (a b : α) :
    finiteKMSDissipativeTransitionIntensity β energy amplitude a b =
      finiteKMSDissipativeTransitionIntensity β energy amplitude b a := by
  simp only [finiteKMSDissipativeTransitionIntensity_eq_gap_mul_commutator β energy amplitude
    hHermitian]
  rw [show energy b - energy a = -(energy a - energy b) by ring,
    finiteKMSCommutatorTransitionIntensity_antisymm β energy amplitude a b]
  ring

/-- The finite response built from KMS dissipative oscillator strengths is passive in the upper
half-plane. -/
theorem finiteKMSDissipativeTransitionPassiveResponse_im_nonpos
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (hβ : 0 ≤ β)
    {z : ℂ} (hz : 0 < z.im) :
    (finiteTransitionPassiveResponse
      (finiteKMSDissipativeTransitionIntensity β energy amplitude) energy z).im ≤ 0 := by
  exact finiteTransitionPassiveResponse_im_nonpos _ energy
    (finiteKMSDissipativeTransitionIntensity_nonneg β energy amplitude hβ) hz

/-- Hermiticity makes the dissipative response exactly odd in the centered spectral coordinate. -/
theorem finiteKMSDissipativeTransitionPassiveResponse_neg
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) (z : ℂ) :
    finiteTransitionPassiveResponse
        (finiteKMSDissipativeTransitionIntensity β energy amplitude) energy (-z) =
      -finiteTransitionPassiveResponse
        (finiteKMSDissipativeTransitionIntensity β energy amplitude) energy z := by
  exact finiteTransitionPassiveResponse_neg _ energy
    (finiteKMSDissipativeTransitionIntensity_symm β energy amplitude hHermitian) z

/-- Odd commutator moments, reindexed as moments of the nonnegative dissipative spectrum. -/
def finiteKMSDissipativeMoment {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) (k : ℕ) : ℝ :=
  thermalGapMoment (finiteKMSCommutatorTransitionIntensity β energy amplitude)
    energy (2 * k + 1)

/-- Exact FDT moment reindexing: an odd commutator moment is the corresponding even moment of the
energy-weighted dissipative spectrum. -/
theorem finiteKMSDissipativeMoment_eq_thermalEvenGapMoment
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) (k : ℕ) :
    finiteKMSDissipativeMoment β energy amplitude k =
      thermalEvenGapMoment
        (finiteKMSDissipativeTransitionIntensity β energy amplitude) energy k := by
  rw [finiteKMSDissipativeMoment, thermalGapMoment, thermalEvenGapMoment_eq]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [finiteKMSCommutatorTransitionIntensity_eq_sinh β energy amplitude hHermitian,
    finiteKMSDissipativeTransitionIntensity, pow_succ, ← pow_mul]
  ring

/-- Nonnegative temperature supplies every ordinary Hankel-square inequality for the finite FDT
moment sequence. -/
theorem momentFunctional_finiteKMSDissipativeMoment_sq_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) (hβ : 0 ≤ β)
    (p : Polynomial ℝ) :
    0 ≤ momentFunctional (finiteKMSDissipativeMoment β energy amplitude) (p ^ 2) := by
  rw [show finiteKMSDissipativeMoment β energy amplitude =
      thermalEvenGapMoment
        (finiteKMSDissipativeTransitionIntensity β energy amplitude) energy by
    funext k
    exact finiteKMSDissipativeMoment_eq_thermalEvenGapMoment
      β energy amplitude hHermitian k]
  exact momentFunctional_thermalEvenGapMoment_sq_nonneg _ energy
    (finiteKMSDissipativeTransitionIntensity_nonneg β energy amplitude hβ) p

/-- Nonnegative temperature also supplies every once-shifted Stieltjes--Hankel inequality for the
finite FDT moment sequence. -/
theorem momentFunctional_X_mul_sq_finiteKMSDissipativeMoment_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b)) (hβ : 0 ≤ β)
    (p : Polynomial ℝ) :
    0 ≤ momentFunctional (finiteKMSDissipativeMoment β energy amplitude)
      (Polynomial.X * p ^ 2) := by
  rw [show finiteKMSDissipativeMoment β energy amplitude =
      thermalEvenGapMoment
        (finiteKMSDissipativeTransitionIntensity β energy amplitude) energy by
    funext k
    exact finiteKMSDissipativeMoment_eq_thermalEvenGapMoment
      β energy amplitude hHermitian k]
  exact momentFunctional_X_mul_sq_thermalEvenGapMoment_nonneg _ energy
    (finiteKMSDissipativeTransitionIntensity_nonneg β energy amplitude hβ) p

end

end HTGeometry
