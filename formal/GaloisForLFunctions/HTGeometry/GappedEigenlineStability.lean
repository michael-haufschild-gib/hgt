import Mathlib

/-!
# A gapped eigenline moves by at most the square root of the perturbation

If a self-adjoint operator has a unit eigenvector whose eigenvalue dominates the whole quadratic
form by a spectral gap, then every self-adjoint perturbation of size `δ` still has an eigenvector
within `√(2δ/Δ)` of it in the projective sense.

The proof needs no resolvent and no contour: the top Rayleigh vector of the perturbed operator is an
eigenvector, its Rayleigh value is at least the unperturbed value at the reference vector minus `δ`,
and the gap hypothesis converts that into a bound on how far it can tilt.
-/

open scoped InnerProductSpace

namespace HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- On unit vectors the quadratic form of an operator is bounded by its norm. -/
theorem abs_reApplyInnerSelf_le (V : E →L[ℂ] E) {x : E} (hx : ‖x‖ = 1) :
    |V.reApplyInnerSelf x| ≤ ‖V‖ := by
  have hVx : ‖V x‖ ≤ ‖V‖ := by
    have h := V.le_opNorm x
    rwa [hx, mul_one] at h
  calc |V.reApplyInnerSelf x| = |RCLike.re (⟪V x, x⟫_ℂ)| := rfl
    _ ≤ ‖(⟪V x, x⟫_ℂ)‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖V x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ = ‖V x‖ := by rw [hx, mul_one]
    _ ≤ ‖V‖ := hVx

/-- **The gapped eigenline is stable.**  A self-adjoint perturbation of size `δ` of a gap-`Δ`
dominant eigenvector leaves an eigenvector whose projective distance to it is at most
`√(2δ/Δ)`. -/
theorem exists_hasEigenvector_of_gap
    (H₀ V : E →L[ℂ] E) (hH₀ : IsSelfAdjoint H₀) (hV : IsSelfAdjoint V)
    (Φ : E) (hΦ : ‖Φ‖ = 1) (lam Δ δ : ℝ) (hΔ : 0 < Δ)
    (hΦeig : H₀ Φ = (lam : ℂ) • Φ)
    (hgap : ∀ x : E, H₀.reApplyInnerSelf x ≤ lam * ‖x‖ ^ (2 : ℕ) - Δ * (‖x‖ ^ (2 : ℕ) - ‖⟪Φ, x⟫_ℂ‖ ^ (2 : ℕ)))
    (hVnorm : ‖V‖ ≤ δ) :
    ∃ ψ : E, ‖ψ‖ = 1 ∧ (∃ μ : ℝ, (H₀ + V) ψ = (μ : ℂ) • ψ) ∧
      1 - ‖⟪Φ, ψ⟫_ℂ‖ ^ (2 : ℕ) ≤ 2 * δ / Δ := by
  classical
  set H : E →L[ℂ] E := H₀ + V with hHdef
  have hH : IsSelfAdjoint H := hH₀.add hV
  have hΦmem : Φ ∈ Metric.sphere (0 : E) 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hΦ
  obtain ⟨ψ, hψmem, hψmax⟩ :=
    (isCompact_sphere (0 : E) 1).exists_isMaxOn ⟨Φ, hΦmem⟩
      (H.reApplyInnerSelf_continuous.continuousOn)
  have hψnorm : ‖ψ‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hψmem
  have hψne : ψ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hψnorm
    exact zero_ne_one hψnorm
  have heig := hH.hasEigenvector_of_isMaxOn hψne (by rwa [hψnorm])
  refine ⟨ψ, hψnorm, ⟨⨆ x : {x : E // x ≠ 0}, H.rayleighQuotient x, ?_⟩, ?_⟩
  · exact heig.apply_eq_smul
  -- the Rayleigh comparison
  have hmax : H.reApplyInnerSelf Φ ≤ H.reApplyInnerSelf ψ := hψmax hΦmem
  have hsplit : ∀ x : E, H.reApplyInnerSelf x
      = H₀.reApplyInnerSelf x + V.reApplyInnerSelf x := by
    intro x
    simp [hHdef, ContinuousLinearMap.reApplyInnerSelf, inner_add_left, map_add]
  have hΦ₀ : H₀.reApplyInnerSelf Φ = lam := by
    rw [ContinuousLinearMap.reApplyInnerSelf, hΦeig, inner_smul_left]
    simp [inner_self_eq_norm_sq_to_K, hΦ]
  have hVΦ : -δ ≤ V.reApplyInnerSelf Φ := by
    have h := abs_reApplyInnerSelf_le V hΦ
    have := abs_le.mp (h.trans hVnorm)
    exact this.1
  have hVψ : V.reApplyInnerSelf ψ ≤ δ := by
    have h := abs_reApplyInnerSelf_le V hψnorm
    have := abs_le.mp (h.trans hVnorm)
    exact this.2
  have hgapψ : H₀.reApplyInnerSelf ψ ≤ lam - Δ * (1 - ‖⟪Φ, ψ⟫_ℂ‖ ^ (2 : ℕ)) := by
    have h := hgap ψ
    rwa [hψnorm, one_pow, mul_one] at h
  have hchain : lam - δ ≤ lam - Δ * (1 - ‖⟪Φ, ψ⟫_ℂ‖ ^ (2 : ℕ)) + δ := by
    calc lam - δ ≤ H₀.reApplyInnerSelf Φ + V.reApplyInnerSelf Φ := by
          rw [hΦ₀]; linarith
      _ = H.reApplyInnerSelf Φ := (hsplit Φ).symm
      _ ≤ H.reApplyInnerSelf ψ := hmax
      _ = H₀.reApplyInnerSelf ψ + V.reApplyInnerSelf ψ := hsplit ψ
      _ ≤ lam - Δ * (1 - ‖⟪Φ, ψ⟫_ℂ‖ ^ (2 : ℕ)) + δ := by linarith
  rw [le_div_iff₀ hΔ]
  nlinarith [hchain]

end HTGeometry
