import GaloisForLFunctions.HTGeometry.LatticeGaussianSummability

/-!
# Transversal decay of the periodized Gaussian

A translate transverse to the lattice moves **every** lattice copy of the Gaussian away from the
centre at once, so the whole periodization inherits the damping in the scale.  This is what makes an
invariant multiplier able to decay: the periodization is constant along the lattice and small
transverse to it.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The periodized Gaussian is damped on a transverse translate.**  Each lattice copy carries the
factor `exp(-rate·B)` because the transverse translate keeps it away from the centre, and the
residual Gaussians sum. -/
theorem norm_tsum_scaledGaussian_translate_le {d k : ℕ}
    (vec : (Fin k → ℤ) → Fin d → ℝ) (σ : Fin d → ℝ) (hσ : ∀ i, 0 < σ i)
    (center : Fin d → ℂ) {ρ σ₀ : ℝ}
    {K : Set (Fin d → ℂ)}
    (hKb : ∀ x ∈ K, ∀ i, |(x i).re - (center i).re| ≤ ρ ∧ |(x i).im - (center i).im| ≤ ρ)
    {B : ℝ} (hB : 1 ≤ B) (u : Fin d → ℝ)
    (hmass : ∀ n : Fin k → ℤ, σ₀ ≤ ∑ i, σ i * (u i + vec n i) ^ (2 : ℕ))
    (hsum : Summable fun n : Fin k → ℤ =>
      Real.exp (-∑ i, σ i / 4 * (u i + vec n i) ^ (2 : ℕ)))
    {x : Fin d → ℂ} (hx : x ∈ K) :
    ‖∑' n : Fin k → ℤ, (centeredComplexGaussian (fun i => B * σ i) center).1
        (x + fun i => (((u i + vec n i : ℝ)) : ℂ))‖
      ≤ Real.exp (-((σ₀ / 4 - (∑ i, σ i) * (2 * ρ ^ (2 : ℕ))) * B))
        * ∑' n : Fin k → ℤ, Real.exp (-∑ i, σ i / 4 * (u i + vec n i) ^ (2 : ℕ)) := by
  classical
  set rate : ℝ := σ₀ / 4 - (∑ i, σ i) * (2 * ρ ^ (2 : ℕ)) with hrate
  have hterm : ∀ n : Fin k → ℤ,
      ‖(centeredComplexGaussian (fun i => B * σ i) center).1
          (x + fun i => (((u i + vec n i : ℝ)) : ℂ))‖
        ≤ Real.exp (-(rate * B))
          * Real.exp (-∑ i, σ i / 4 * (u i + vec n i) ^ (2 : ℕ)) := fun n =>
    norm_scaledGaussian_realTranslate_damped σ hσ center hKb hB (hmass n) hx
  have hnormsum : Summable fun n : Fin k → ℤ =>
      ‖(centeredComplexGaussian (fun i => B * σ i) center).1
        (x + fun i => (((u i + vec n i : ℝ)) : ℂ))‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hsum.mul_left _)
  calc ‖∑' n : Fin k → ℤ, (centeredComplexGaussian (fun i => B * σ i) center).1
          (x + fun i => (((u i + vec n i : ℝ)) : ℂ))‖
      ≤ ∑' n : Fin k → ℤ, ‖(centeredComplexGaussian (fun i => B * σ i) center).1
          (x + fun i => (((u i + vec n i : ℝ)) : ℂ))‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : Fin k → ℤ, Real.exp (-(rate * B))
          * Real.exp (-∑ i, σ i / 4 * (u i + vec n i) ^ (2 : ℕ)) :=
        hnormsum.tsum_le_tsum hterm (hsum.mul_left _)
    _ = Real.exp (-(rate * B))
          * ∑' n : Fin k → ℤ, Real.exp (-∑ i, σ i / 4 * (u i + vec n i) ^ (2 : ℕ)) := by
        rw [tsum_mul_left]

end

end GaloisForLFunctions.HTGeometry
