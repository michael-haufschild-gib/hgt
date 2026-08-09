import GaloisForLFunctions.RHTower.FiniteSectionZetaInterpolation

/-!
# A determinant of sampled zeta values bounds the Báez-Duarte distance

`FiniteSectionZetaInterpolation` leaves a finite section of the Báez-Duarte problem with exactly one escape
route: interpolating `ζ` at the sample points.  With one more sample point than generators that escape is
visible as a determinant.

Border the `N` sampled generator rows with the sampled target row, at `N+1` points of the strip:

`sampledBorderMatrix θ ρ` has rows `j ↦ −(θᵢ^{ρⱼ} − θᵢ)·ζ(ρⱼ)/ρⱼ` for `i < N` and last row `j ↦ 1/ρⱼ`.

Interpolation makes the last row the corresponding combination of the others, so the determinant vanishes
(`det_sampledBorderMatrix_eq_zero_of_interpolation`, by exhibiting a nonzero vector in the left kernel).
Hence

**`bdDist_pos_of_det_ne_zero` and `exists_bdDist_floor_of_det_ne_zero` — a nonvanishing bordered determinant
of sampled `ζ` values certifies a positive Báez-Duarte distance, with the explicit detector floor.**

This is the certificate in its most compact form: one determinant in the values `ζ(ρⱼ)` and the powers
`θᵢ^{ρⱼ}`, unconditional, with no zero of `ζ` involved.
-/

open MeasureTheory Set Complex Metric Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- The bordered matrix of sampled pairings: the `N` generator rows, then the target row. -/
def sampledBorderMatrix {N : ℕ} (θ : Fin N → ℝ) (ρ : Fin (N + 1) → ℂ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  Matrix.of (Fin.snoc
    (fun (i : Fin N) (j : Fin (N + 1)) =>
      -(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j))
    (fun (j : Fin (N + 1)) => 1 / ρ j) : Fin (N + 1) → Fin (N + 1) → ℂ)

theorem sampledBorderMatrix_castSucc {N : ℕ} (θ : Fin N → ℝ) (ρ : Fin (N + 1) → ℂ) (i : Fin N)
    (j : Fin (N + 1)) :
    sampledBorderMatrix θ ρ i.castSucc j
      = -(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j) := by
  simp [sampledBorderMatrix]

theorem sampledBorderMatrix_last {N : ℕ} (θ : Fin N → ℝ) (ρ : Fin (N + 1) → ℂ) (j : Fin (N + 1)) :
    sampledBorderMatrix θ ρ (Fin.last N) j = 1 / ρ j := by
  simp [sampledBorderMatrix]

/-- **Interpolation kills the determinant.**  If the section inverts `ζ` at the sample points then the
target row is the corresponding combination of the generator rows, which is a nonzero vector in the left
kernel of the bordered matrix. -/
theorem det_sampledBorderMatrix_eq_zero_of_interpolation {N : ℕ} (θ : Fin N → ℝ)
    (ρ : Fin (N + 1) → ℂ) (d : Fin N → ℂ)
    (hd : ∀ j, (∑ i, d i * (((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ))) * riemannZeta (ρ j) = 1) :
    (sampledBorderMatrix θ ρ).det = 0 := by
  refine Matrix.exists_vecMul_eq_zero_iff.1
    ⟨(Fin.snoc (fun i : Fin N => -d i) (-1) : Fin (N + 1) → ℂ), ?_, ?_⟩
  · intro h
    have hlast := congrFun h (Fin.last N)
    simp only [Fin.snoc_last, Pi.zero_apply] at hlast
    exact absurd hlast (by norm_num)
  · funext j
    rw [Pi.zero_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, sampledBorderMatrix_castSucc,
      sampledBorderMatrix_last]
    have hfactor : ∑ i : Fin N, (-d i) *
          (-(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j))
        = ((∑ i, d i * (((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ))) * riemannZeta (ρ j)) / ρ j := by
      rw [Finset.sum_mul, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hfactor, hd j]
    ring

/-! ## The certificate -/

/-- **A nonvanishing bordered determinant certifies a positive distance.**  The determinant is built from
the sampled values `ζ(ρⱼ)` and the powers `θᵢ^{ρⱼ}` alone. -/
theorem bdDist_pos_of_det_ne_zero {N : ℕ} (θ : Fin N → ℝ) (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1)
    (ρ : Fin (N + 1) → ℂ) (hρ : ∀ j, 1 / 2 < (ρ j).re) (hρ1 : ∀ j, (ρ j).re < 1)
    (hdet : (sampledBorderMatrix θ ρ).det ≠ 0) :
    0 < bdDist θ := by
  rcases interpolates_inv_zeta_or_exists_bdDist_floor θ hθ ρ hρ hρ1 with ⟨d, hd⟩ | h
  · exact absurd (det_sampledBorderMatrix_eq_zero_of_interpolation θ ρ d hd) hdet
  · exact h.1

/-- The same certificate, with the explicit detector floor it produces. -/
theorem exists_bdDist_floor_of_det_ne_zero {N : ℕ} (θ : Fin N → ℝ) (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1)
    (ρ : Fin (N + 1) → ℂ) (hρ : ∀ j, 1 / 2 < (ρ j).re) (hρ1 : ∀ j, (ρ j).re < 1)
    (hdet : (sampledBorderMatrix θ ρ).det ≠ 0) :
    ∃ a : Fin (N + 1) → ℂ, (∑ j, (starRingEnd ℂ) (a j) * (1 / ρ j) ≠ 0) ∧
      ‖∑ j, (starRingEnd ℂ) (a j) * (1 / ρ j)‖ / ‖detectorCombination ρ hρ a‖ ≤ bdDist θ := by
  rcases interpolates_inv_zeta_or_exists_bdDist_floor θ hθ ρ hρ hρ1 with ⟨d, hd⟩ | h
  · exact absurd (det_sampledBorderMatrix_eq_zero_of_interpolation θ ρ d hd) hdet
  · exact h.2

end RHTower

end
