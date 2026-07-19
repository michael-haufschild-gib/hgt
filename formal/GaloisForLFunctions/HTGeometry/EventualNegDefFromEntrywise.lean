import GaloisForLFunctions.HTGeometry.DiagonalNegativeMargin

/-!
# Eventual negative definiteness from entrywise convergence

Assembling the abstract lower bound.  A family of matrices converging entrywise to a diagonal with
all entries at most `-δ` is eventually negative definite: the entrywise bound gives a quadratic
modulus, the diagonal supplies the margin, and the perturbation criterion does the rest.

This is the form the Krein index computation consumes, with the family being the height-scaled Pick
Gram matrix and the diagonal the atom coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Filter

noncomputable section

/-- **Entrywise smallness gives a quadratic-form perturbation bound.**  The deviation of the form
from the coefficient diagonal is controlled by the entrywise deviation summed over the `n²`
positions, so choosing the entrywise threshold below `δ/(2n²)` keeps the form within half the
margin.  The sign of the coefficients plays no role here. -/
theorem eventually_quadForm_sub_diagonal_le
    {n : ℕ} {ι : Type*} {l : Filter ι} (G : ι → Matrix (Fin n) (Fin n) ℂ)
    (c : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ j k,
      ‖G i j k - (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)) j k‖ ≤ ε) :
    ∀ᶠ i in l, ∀ x : Fin n → ℂ,
      |(star x ⬝ᵥ (G i).mulVec x).re
          - (star x ⬝ᵥ (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)).mulVec x).re|
        ≤ (δ / 2) * ‖x‖ ^ 2 := by
  classical
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun j => ((c j : ℝ) : ℂ) with hD
  set ε : ℝ := δ / (2 * ((n : ℝ) ^ 2 + 1)) with hε
  have hεpos : 0 < ε := by
    rw [hε]
    positivity
  have hεn : ε * (n : ℝ) ^ 2 ≤ δ / 2 := by
    rw [hε, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg ((n : ℝ)), hδ.le]
  filter_upwards [hconv ε hεpos] with i hi
  intro x
  -- The difference of the forms is the form of the difference.
  have hsub : (star x ⬝ᵥ (G i).mulVec x).re - (star x ⬝ᵥ D.mulVec x).re
      = (star x ⬝ᵥ (G i - D).mulVec x).re := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
  rw [hsub]
  have hentry : ∀ j k, ‖(G i - D) j k‖ ≤ ε := by
    intro j k
    simpa using hi j k
  have hquad := norm_quadForm_le_of_entries (G i - D) hεpos.le hentry x
  have hre : |(star x ⬝ᵥ (G i - D).mulVec x).re| ≤ ‖star x ⬝ᵥ (G i - D).mulVec x‖ :=
    Complex.abs_re_le_norm _
  have hnn : (0 : ℝ) ≤ ‖x‖ ^ 2 := by positivity
  calc |(star x ⬝ᵥ (G i - D).mulVec x).re|
      ≤ ‖star x ⬝ᵥ (G i - D).mulVec x‖ := hre
    _ ≤ ε * (n : ℝ) ^ 2 * ‖x‖ ^ 2 := hquad
    _ ≤ δ / 2 * ‖x‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hεn hnn

/-- **Entrywise convergence to a negative diagonal gives eventual negative definiteness.** -/
theorem eventually_negDef_of_entrywise_tendsto_diagonal
    {n : ℕ} {ι : Type*} {l : Filter ι} (G : ι → Matrix (Fin n) (Fin n) ℂ)
    (c : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ) (hc : ∀ j, c j ≤ -δ)
    (hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ j k,
      ‖G i j k - (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)) j k‖ ≤ ε) :
    ∀ᶠ i in l, ∀ x : Fin n → ℂ, x ≠ 0 → (star x ⬝ᵥ (G i).mulVec x).re < 0 :=
  eventually_neg_of_tendsto_negDef
    (fun i x => (star x ⬝ᵥ (G i).mulVec x).re)
    (fun x => (star x ⬝ᵥ (Matrix.diagonal fun j => ((c j : ℝ) : ℂ)).mulVec x).re)
    (fun x => re_quadForm_diagonal_le_margin c hδ.le hc x)
    (eventually_quadForm_sub_diagonal_le G c hδ hconv) hδ

end

end GaloisForLFunctions.HTGeometry
