import GaloisForLFunctions.HilbertMetric.Spectral.ClippedThreshold
import GaloisForLFunctions.HTGeometry.FiniteMatrixSpectralHankel

/-!
# Clipped defects of signed matrix-valued spectral moments

Block-Hankel symmetry survives arbitrary signed spectral masses. Its first two
moments therefore give a clipped lower certificate even when positivity and
spectral identifiability fail. Subtracting an observation covariance has only
the linear trace cost of the clipped variational inequality.
-/

open Matrix HTGeometry
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.HilbertMetric.Observation
open Clipped
noncomputable section
variable {d m : ℕ}

theorem spectralHankel_complex_hermitian (mass node : Fin d → ℝ)
    (coupling : Fin d → Fin m → ℝ) (n : ℕ) :
    ((finiteMatrixSpectralBlockHankel mass node coupling n).map Complex.ofReal).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def,
    Complex.conj_ofReal]
  congr 1
  unfold finiteMatrixSpectralBlockHankel finiteMatrixSpectralMoment
  rw [Nat.add_comm (j.1 : ℕ) (i.1 : ℕ)]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Signed spectral moments retain an explicit centered second-moment surplus. -/
theorem spectralHankel_clippedDefect (mass node : Fin d → ℝ)
    (coupling : Fin d → Fin m → ℝ) (n : ℕ) (τ : ℝ≥0) :
    min ((∑ i : Fin n × Fin m, ∑ j : Fin n × Fin m,
        (finiteMatrixSpectralMoment mass node coupling ((i.1 : ℕ) + j.1) i.2 j.2) ^ 2) -
      2 * (∑ i : Fin n × Fin m,
        finiteMatrixSpectralMoment mass node coupling ((i.1 : ℕ) + i.1) i.2 i.2) +
      (n : ℝ) * m) ((τ : ℝ) ^ 2) ≤
        defectEnergy τ ((finiteMatrixSpectralBlockHankel mass node coupling n).map Complex.ofReal) := by
  have hH := spectralHankel_complex_hermitian mass node coupling n
  have h := defectEnergy_min_bound hH τ
  rw [trace_square hH] at h
  simpa only [trace, diag, Matrix.map_apply, finiteMatrixSpectralBlockHankel,
    Complex.normSq_ofReal, ← pow_two, Complex.re_sum, Complex.ofReal_re,
    Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using h

/-- Any removed covariance pays its trace cost, even for signed spectral input. -/
theorem spectralHankel_covariance_subtraction {κ : Type*} [Fintype κ]
    (mass node : Fin d → ℝ) (coupling : Fin d → Fin m → ℝ) (n : ℕ)
    (B : Matrix (Fin n × Fin m) κ ℂ) (c : ℝ) :
    let H := (finiteMatrixSpectralBlockHankel mass node coupling n).map Complex.ofReal
    energy c H ≤ (trace ((H - B * Bᴴ) * (H - B * Bᴴ))).re + 2 * c * (trace (B * Bᴴ)).re :=
  energy_le_sub_square (spectralHankel_complex_hermitian mass node coupling n)
    (Matrix.posSemidef_self_mul_conjTranspose B) c

#print axioms spectralHankel_clippedDefect
#print axioms spectralHankel_covariance_subtraction

end
end GaloisForLFunctions.HilbertMetric.Observation
