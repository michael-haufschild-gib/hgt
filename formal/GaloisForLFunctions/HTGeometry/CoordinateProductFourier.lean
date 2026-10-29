import GaloisForLFunctions.HTGeometry.SchwartzPoissonSummation
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Fourier transforms of finite coordinate products

The Euclidean Fourier phase is the product of its scalar coordinate phases.
The volume-preserving Euclidean coordinate map and finite-product Fubini then
factor the Fourier transform, even with the Bochner integral's zero convention.
Scalar integrability also gives integrability of the full coordinate product.
-/

noncomputable section
open MeasureTheory
open scoped Classical FourierTransform

namespace GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
variable {ι : Type*} [Fintype ι]
local notation "X" => ι → ℝ
local notation "E" => EuclideanSpace ℝ ι

/-- Product of scalar functions on the Euclidean coordinate axes. -/
def coordinateProduct (f : ι → ℝ → ℂ) (x : E) : ℂ := ∏ i, f i (x i)

theorem euclidean_fourier_phase_eq_prod (x ξ : E) :
    Complex.exp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) =
      ∏ i, Complex.exp ((-2 * Real.pi * inner ℝ (x i) (ξ i) : ℝ) * Complex.I) := by
  rw [← Complex.exp_sum]
  congr 1
  rw [PiLp.inner_apply, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]

/-- Scalar integrability gives integrability of the Euclidean coordinate product. -/
theorem integrable_coordinateProduct {f : ι → ℝ → ℂ} (hf : ∀ i, Integrable (f i)) :
    Integrable (coordinateProduct f) := by
  have h : Integrable (fun x : X => ∏ i, f i (x i)) := Integrable.fintype_prod hf
  exact ((PiLp.volume_preserving_toLp ι).integrable_comp_emb
    (MeasurableEquiv.toLp 2 X).measurableEmbedding).mp h

/-- Euclidean Fourier transform factors into the scalar coordinate transforms. -/
theorem fourier_coordinateProduct (f : ι → ℝ → ℂ) (ξ : E) :
    (𝓕 (coordinateProduct f)) ξ = ∏ i, (𝓕 (f i)) (ξ i) := by
  rw [Real.fourier_eq']
  rw [← (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 X).measurableEmbedding]
  calc
    _ = ∫ x : X, ∏ i, (Complex.exp
        ((-2 * Real.pi * inner ℝ (x i) (ξ i) : ℝ) * Complex.I) * f i (x i)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [euclidean_fourier_phase_eq_prod, coordinateProduct, Finset.prod_mul_distrib]
      rfl
    _ = ∏ i, ∫ x : ℝ, Complex.exp
        ((-2 * Real.pi * inner ℝ x (ξ i) : ℝ) * Complex.I) * f i x :=
      integral_fintype_prod_volume_eq_prod (fun i (x : ℝ) =>
        Complex.exp ((-2 * Real.pi * inner ℝ x (ξ i) : ℝ) * Complex.I) * f i x)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Real.fourier_eq']
      rfl

end GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
