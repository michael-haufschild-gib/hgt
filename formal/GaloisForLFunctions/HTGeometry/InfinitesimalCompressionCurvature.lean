import GaloisForLFunctions.HTGeometry.PagewiseHodgeFormation

/-!
# Infinitesimal curvature of an isometric compression

Let `S` be an orthogonally complemented closed subspace and split an isometric
operator family into its compression to `S` and its leakage into `Sᗮ`.  The
Pythagorean identity identifies the compression defect exactly with the squared
leakage norm.  Consequently, operator-norm convergence of leakage divided by a
positive parameter gives the second-order compression-defect limit on every
vector.

This is the abstract operator-theoretic implication needed by infinitesimal
Toeplitz/Hankel leakage arguments; identifying and estimating a concrete symbol
family remains separate analytic work.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Component of `U` rejected by the orthogonal projection onto `S`. -/
def orthogonalLeakage (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (U : E →L[ℂ] E) : E →L[ℂ] E :=
  U - S.starProjection.comp U

/-- Compression of `U` to the range of the orthogonal projection onto `S`. -/
def causalCompression (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (U : E →L[ℂ] E) : E →L[ℂ] E :=
  S.starProjection.comp U

/-- An isometry splits exactly into its compressed and leaked squared norms. -/
theorem norm_sq_causalCompression_add_orthogonalLeakage
    (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (U : E →L[ℂ] E) (hU : ∀ x, ‖U x‖ = ‖x‖) (x : E) :
    ‖causalCompression S U x‖ * ‖causalCompression S U x‖ +
        ‖orthogonalLeakage S U x‖ * ‖orthogonalLeakage S U x‖ =
      ‖x‖ * ‖x‖ := by
  have h := norm_sq_starProjection_add S (U x)
  rw [hU] at h
  simpa [causalCompression, orthogonalLeakage] using h.symm

/-- At every positive scale, normalized compression defect is exactly normalized
leakage energy. -/
theorem scaled_compression_defect_eq_norm_sq
    (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (U : E →L[ℂ] E) (hU : ∀ x, ‖U x‖ = ‖x‖) (x : E)
    {ω : ℝ} (hω : 0 < ω) :
    (‖x‖ * ‖x‖ - ‖causalCompression S U x‖ * ‖causalCompression S U x‖) /
          (ω * ω) =
      ‖(((ω : ℂ)⁻¹) • orthogonalLeakage S U) x‖ *
        ‖(((ω : ℂ)⁻¹) • orthogonalLeakage S U) x‖ := by
  have hsplit := norm_sq_causalCompression_add_orthogonalLeakage S U hU x
  have hdefect :
      ‖x‖ * ‖x‖ - ‖causalCompression S U x‖ * ‖causalCompression S U x‖ =
        ‖orthogonalLeakage S U x‖ * ‖orthogonalLeakage S U x‖ := by
    linarith
  have hω0 : ω ≠ 0 := ne_of_gt hω
  have hnorm : ‖(ω : ℂ)⁻¹‖ = ω⁻¹ := by
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω]
  rw [hdefect]
  simp only [smul_apply, norm_smul, hnorm]
  field_simp

/-- Operator-norm convergence of scaled leakage implies the exact vectorwise
second-order curvature law for the corresponding isometric compression. -/
theorem tendsto_scaled_compression_defect
    (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (U : ℝ → E →L[ℂ] E) (hU : ∀ ω x, ‖U ω x‖ = ‖x‖)
    (D : E →L[ℂ] E)
    (hlim : Tendsto (fun ω : ℝ => ((ω : ℂ)⁻¹) • orthogonalLeakage S (U ω))
      (nhdsWithin 0 (Ioi 0)) (𝓝 D))
    (x : E) :
    Tendsto
        (fun ω : ℝ =>
          (‖x‖ * ‖x‖ -
              ‖causalCompression S (U ω) x‖ * ‖causalCompression S (U ω) x‖) /
            (ω * ω))
        (nhdsWithin 0 (Ioi 0))
        (𝓝 (‖D x‖ * ‖D x‖)) := by
  have happ : Tendsto
      (fun ω : ℝ => (((ω : ℂ)⁻¹) • orthogonalLeakage S (U ω)) x)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (D x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun ω : ℝ =>
        ‖((ω : ℂ)⁻¹ • orthogonalLeakage S (U ω)) - D‖ * ‖x‖)
      (fun _ => norm_nonneg _) (fun ω => ?_) ?_
    · simpa only [sub_apply] using
        ((((ω : ℂ)⁻¹) • orthogonalLeakage S (U ω)) - D).le_opNorm x
    · have h0 : Tendsto (fun ω : ℝ =>
          ‖((ω : ℂ)⁻¹ • orthogonalLeakage S (U ω)) - D‖)
          (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
        rw [← tendsto_iff_norm_sub_tendsto_zero]
        exact hlim
      simpa using h0.mul_const ‖x‖
  have hnorm := happ.norm
  have hsq := hnorm.mul hnorm
  refine hsq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω
  exact (scaled_compression_defect_eq_norm_sq S (U ω) (hU ω) x hω).symm

end

end GaloisForLFunctions.HTGeometry
