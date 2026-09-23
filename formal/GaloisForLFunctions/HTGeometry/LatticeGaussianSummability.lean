import GaloisForLFunctions.HTGeometry.QuasiAbelianSeedCompactBound
import GaloisForLFunctions.HTGeometry.LatticePeriodization

/-!
# Summability of the periodized Gaussian

The periodization of a Gaussian along a **real** lattice converges: a lattice translate moves only
real parts, so the Gaussian decays along the lattice, and uniform discreteness of the lattice turns
that decay into a Gaussian in the index, which is summable.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The zero-degree polynomial-Gaussian weight is the plain Gaussian of the index. -/
theorem polynomialGaussianLatticeWeight_zero_deg {k : ℕ} (s : ℝ) (n : Fin k → ℤ) :
    polynomialGaussianLatticeWeight (Fin k) (fun _ => 0) (fun _ => s) n
      = Real.exp (-(s * ∑ j, ((n j : ℤ) : ℝ) ^ (2 : ℕ))) := by
  rw [polynomialGaussianLatticeWeight]
  rw [show (fun j : Fin k => (1 + (((n j).natAbs : ℕ) : ℝ)) ^ (0 : ℕ) *
      Real.exp (-s * ((n j : ℤ) : ℝ) ^ (2 : ℕ))) = fun j : Fin k =>
      Real.exp (-s * ((n j : ℤ) : ℝ) ^ (2 : ℕ)) by
    funext j
    rw [pow_zero, one_mul]]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The periodized Gaussian converges absolutely at every point of a compact set.** -/
theorem summable_norm_scaledGaussian_lattice {d k : ℕ} (emb : (Fin k → ℤ) →+ (Fin d → ℂ))
    (vec : (Fin k → ℤ) → Fin d → ℝ) (hvec : ∀ n i, emb n i = ((vec n i : ℝ) : ℂ))
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hdiscrete : ∀ n : Fin k → ℤ, kappa * ∑ j, ((n j : ℤ) : ℝ) ^ (2 : ℕ) ≤ ∑ i, (vec n i) ^ (2 : ℕ))
    (σ : Fin d → ℝ) (hσ : ∀ i, 0 < σ i) {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hσ₀le : ∀ i, σ₀ ≤ σ i)
    (center : Fin d → ℂ) {K : Set (Fin d → ℂ)} (hK : IsCompact K) {B : ℝ} (hB : 1 ≤ B)
    {x : Fin d → ℂ} (hx : x ∈ K) :
    Summable (fun n : Fin k → ℤ =>
      ‖(centeredComplexGaussian (fun i => B * σ i) center).1 (x + emb n)‖) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_norm_scaledGaussian_realTranslate_le σ hσ center hK hB
  have hs : (0 : ℝ) < σ₀ * kappa / 4 := by positivity
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_polynomialGaussianLatticeWeight (Fin k) (fun _ => 0)
      (fun _ => σ₀ * kappa / 4) (fun _ => hs)).mul_left C)
  have hpt : x + emb n = x + fun i => ((vec n i : ℝ) : ℂ) := by
    funext i
    rw [Pi.add_apply, Pi.add_apply, hvec n i]
  rw [hpt]
  refine le_trans (hC (vec n) x hx) ?_
  rw [polynomialGaussianLatticeWeight_zero_deg]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0
  have hlow : σ₀ * ∑ i, (vec n i) ^ (2 : ℕ) ≤ ∑ i, σ i * (vec n i) ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hσ₀le i) (sq_nonneg _)
  have hquarter : ∑ i, σ i / 4 * (vec n i) ^ (2 : ℕ) = (∑ i, σ i * (vec n i) ^ (2 : ℕ)) / 4 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hquarter]
  have hd := hdiscrete n
  nlinarith [hσ₀.le, hlow, hd, hkappa]

end

end GaloisForLFunctions.HTGeometry
