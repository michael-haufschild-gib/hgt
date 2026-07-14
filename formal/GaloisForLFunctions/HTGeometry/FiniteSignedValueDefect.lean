import Mathlib

/-!
# Finite signed value defects

For a finite real coefficient packet, the total negative mass is the exact excess of total
variation over signed mass.  It therefore controls the associated generating polynomial on the
closed unit disk.  This elementary finite-volume law is the coefficient-level bridge between
positivity defects and partition-function or divisor-pencil value bounds.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Total negative mass of a finite real coefficient packet. -/
def finiteNegativeMass {n : ℕ} (b : Fin n → ℝ) : ℝ :=
  ∑ i, (b i)⁻

/-- Signed mass of a finite real coefficient packet. -/
def finiteSignedMass {n : ℕ} (b : Fin n → ℝ) : ℝ :=
  ∑ i, b i

/-- Total variation of a finite real coefficient packet. -/
def finiteL1Mass {n : ℕ} (b : Fin n → ℝ) : ℝ :=
  ∑ i, |b i|

/-- Generating polynomial of a finite real coefficient packet. -/
def finiteValuePolynomial {n : ℕ} (b : Fin n → ℝ) (w : ℂ) : ℂ :=
  ∑ i, (b i : ℂ) * w ^ (i : ℕ)

/-- **Exact signed-mass defect law.**  Total variation is signed mass plus twice the total
negative mass. -/
theorem finiteL1Mass_eq_signedMass_add_two_negativeMass
    {n : ℕ} (b : Fin n → ℝ) :
    finiteL1Mass b = finiteSignedMass b + 2 * finiteNegativeMass b := by
  rw [finiteL1Mass, finiteSignedMass, finiteNegativeMass, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have h := abs_sub_eq_two_nsmul_negPart (b i)
  simp only [nsmul_eq_mul] at h
  norm_num at h
  linarith

/-- The finite value polynomial is bounded on the closed unit disk by the packet total
variation. -/
theorem norm_finiteValuePolynomial_le_l1
    {n : ℕ} (b : Fin n → ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖finiteValuePolynomial b w‖ ≤ finiteL1Mass b := by
  rw [finiteValuePolynomial, finiteL1Mass]
  calc
    ‖∑ i, (b i : ℂ) * w ^ (i : ℕ)‖ ≤
        ∑ i, ‖(b i : ℂ) * w ^ (i : ℕ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, |b i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      calc
        |b i| * ‖w‖ ^ (i : ℕ) ≤ |b i| * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg w) hw) (abs_nonneg _)
        _ = |b i| := mul_one _

/-- The negative-mass defect vanishes exactly on the positive orthant. -/
theorem finiteNegativeMass_eq_zero_iff
    {n : ℕ} (b : Fin n → ℝ) :
    finiteNegativeMass b = 0 ↔ ∀ i, 0 ≤ b i := by
  constructor
  · intro h i
    have hterm : (b i)⁻ = 0 := by
      have hiff := Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => negPart_nonneg (b j))
      exact (hiff.mp (by simpa only [finiteNegativeMass] using h)) i (Finset.mem_univ i)
    exact negPart_eq_zero.mp hterm
  · intro h
    simp [finiteNegativeMass, h]

/-- Unit-disk values are controlled exactly by signed mass plus twice the positivity defect. -/
theorem norm_finiteValuePolynomial_le_signedMass_add_two_negativeMass
    {n : ℕ} (b : Fin n → ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖finiteValuePolynomial b w‖ ≤
      finiteSignedMass b + 2 * finiteNegativeMass b := by
  rw [← finiteL1Mass_eq_signedMass_add_two_negativeMass]
  exact norm_finiteValuePolynomial_le_l1 b hw

end

end HTGeometry
