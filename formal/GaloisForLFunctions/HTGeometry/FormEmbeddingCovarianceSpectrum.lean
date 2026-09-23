import GaloisForLFunctions.HTGeometry.FriedrichsFormOperator
import GaloisForLFunctions.HTGeometry.CfcEigenvectorRankOneAssembly

/-!
# Spectrum of the covariance of a contractive form embedding

Let `J : V →L[ℂ] H` be the embedding of a form domain into the ambient Hilbert space and
`C = J J†` its covariance (the bounded inverse of the Friedrichs operator `1 − Δ` when `J` is
injective with dense range).  `C` is positive, `‖C‖ ≤ ‖J‖²`, and when `J` is contractive its real
spectrum lies in `[0, 1]`.  A vector `v ∈ V` whose form inner product against `V` is the ambient
inner product of `J v` against `J(·)` (a form-harmonic vector) is fixed by `C` in the sense
`C (J v) = J v`.

Together with the rank-one assembly bound this gives, for `g ≥ c` on `[0, 1]`,
`g(1)·|⟪J v, F⟫|²/‖J v‖² + c·‖F − P F‖² ≤ Re⟪g(C) F, F⟫`.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The covariance `J J†` is a positive operator. -/
theorem formEmbeddingCovariance_isPositive (J : V →L[ℂ] H) :
    (formEmbeddingCovariance J).IsPositive := by
  have h := (ContinuousLinearMap.isPositive_one (E := V)).conj_adjoint J
  have hJ : J ∘L (1 : V →L[ℂ] V) ∘L J.adjoint = formEmbeddingCovariance J := by
    ext x; rfl
  rwa [hJ] at h

theorem formEmbeddingCovariance_nonneg (J : V →L[ℂ] H) : 0 ≤ formEmbeddingCovariance J :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (formEmbeddingCovariance_isPositive J)

/-- `‖J J†‖ ≤ ‖J‖²`. -/
theorem norm_formEmbeddingCovariance_le (J : V →L[ℂ] H) :
    ‖formEmbeddingCovariance J‖ ≤ ‖J‖ ^ (2 : ℕ) := by
  calc ‖formEmbeddingCovariance J‖ = ‖J.comp J.adjoint‖ := rfl
    _ ≤ ‖J‖ * ‖J.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖J‖ ^ (2 : ℕ) := by rw [ContinuousLinearMap.adjoint.norm_map, sq]

/-- For a contractive form embedding the real spectrum of the covariance lies in `[0, 1]`. -/
theorem spectrum_formEmbeddingCovariance_subset_Icc (J : V →L[ℂ] H) (hJ : ‖J‖ ≤ 1) :
    spectrum ℝ (formEmbeddingCovariance J) ⊆ Set.Icc 0 1 := by
  intro x hx
  refine ⟨spectrum_nonneg_of_nonneg (formEmbeddingCovariance_nonneg J) hx, ?_⟩
  have h1 := spectrum.subset_closedBall_norm_mul (𝕜 := ℝ) (formEmbeddingCovariance J) hx
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
  have h2 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h3 := norm_formEmbeddingCovariance_le J
  have h4 : ‖J‖ ^ (2 : ℕ) ≤ 1 := by
    have := norm_nonneg J
    nlinarith
  have h5 : ‖formEmbeddingCovariance J‖ * ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
    have := norm_nonneg (formEmbeddingCovariance J)
    calc ‖formEmbeddingCovariance J‖ * ‖(1 : H →L[ℂ] H)‖ ≤ ‖formEmbeddingCovariance J‖ * 1 :=
          mul_le_mul_of_nonneg_left h2 this
      _ ≤ 1 := by linarith
  exact (le_abs_self x).trans (h1.trans h5)

/-- A form-harmonic vector is fixed by the covariance: if `⟪v, w⟫_V = ⟪J v, J w⟫_H` for all `w`
then `J† (J v) = v`, hence `C (J v) = J v`. -/
theorem formEmbeddingCovariance_apply_eq_self (J : V →L[ℂ] H) {v : V}
    (hv : ∀ w : V, ⟪v, w⟫_ℂ = ⟪J v, J w⟫_ℂ) :
    formEmbeddingCovariance J (J v) = J v := by
  have hadj : J.adjoint (J v) = v := by
    apply ext_inner_right ℂ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left, hv]
  show J (J.adjoint (J v)) = J v
  rw [hadj]

/-- **Assembly bound for a contractive form embedding.**  For a form-harmonic `v` with `J v ≠ 0`
and a real `g` continuous on `[0, 1]` with `c ≤ g` there, every `F` satisfies
`g(1)·|⟪J v, F⟫|²/‖J v‖² + c·‖F − P F‖² ≤ Re⟪g(C) F, F⟫`, `P` the projection onto `ℂ·J v`. -/
theorem re_inner_cfc_formEmbeddingCovariance_ge (J : V →L[ℂ] H) (hJ : ‖J‖ ≤ 1) {v : V}
    (hv : ∀ w : V, ⟪v, w⟫_ℂ = ⟪J v, J w⟫_ℂ) (hv0 : J v ≠ 0) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc 0 1)) {c : ℝ} (hc : ∀ x ∈ Set.Icc (0 : ℝ) 1, c ≤ g x) (F : H) :
    g 1 * (‖⟪J v, F⟫_ℂ‖ ^ (2 : ℕ) / ‖J v‖ ^ (2 : ℕ)) + c * ‖F - (ℂ ∙ J v).starProjection F‖ ^ (2 : ℕ) ≤
      RCLike.re ⟪cfc g (formEmbeddingCovariance J) F, F⟫_ℂ := by
  have hsub := spectrum_formEmbeddingCovariance_subset_Icc J hJ
  exact re_inner_cfc_self_ge_rankOne (formEmbeddingCovariance J)
    (formEmbeddingCovariance_isSelfAdjoint J) (formEmbeddingCovariance_apply_eq_self J hv) hv0
    (hg.mono hsub) (fun x hx => hc x (hsub hx)) F

end GaloisForLFunctions.HTGeometry
