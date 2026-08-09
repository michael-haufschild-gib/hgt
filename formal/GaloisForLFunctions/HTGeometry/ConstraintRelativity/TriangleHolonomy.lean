import Mathlib

/-!
# Heterogeneous triangle identity and the singular-holonomy law

Three normed spaces with bounded transports around a cycle and three declared realizations have a
based cyclic defect that decomposes exactly into the three transported edge defects:

`Ω₀ = T₂₀T₁₂ e₀₁ + T₂₀ e₁₂ + e₂₀`.

Hence a nonzero cyclic defect cannot coexist with exactly compatible edges, and if edge accuracy
tends to zero while the cyclic defect stays bounded below, the transport norms must diverge at
least reciprocally to the edge accuracy.

The locally convex form is the same identity plus equicontinuity: equicontinuous transports send
edge-exactness to holonomy-exactness.
-/

namespace HTGeometry.ConstraintRelativity

open Filter Topology

/-! ## The exact triangle identity -/

section Algebraic

variable {R E₀ E₁ E₂ : Type*} [Ring R]
  [AddCommGroup E₀] [Module R E₀] [AddCommGroup E₁] [Module R E₁] [AddCommGroup E₂] [Module R E₂]

/-- **Theorem 3.1.**  The based cyclic defect is the sum of the transported edge defects. -/
theorem cyclicDefect_eq (T₀₁ : E₀ →ₗ[R] E₁) (T₁₂ : E₁ →ₗ[R] E₂) (T₂₀ : E₂ →ₗ[R] E₀)
    (x₀ : E₀) (x₁ : E₁) (x₂ : E₂) :
    T₂₀ (T₁₂ (T₀₁ x₀)) - x₀
      = T₂₀ (T₁₂ (T₀₁ x₀ - x₁)) + T₂₀ (T₁₂ x₁ - x₂) + (T₂₀ x₂ - x₀) := by
  simp only [map_sub]
  abel

/-- **Corollary 3.2.**  Exactly compatible edges force a flat cycle. -/
theorem cyclicDefect_eq_zero (T₀₁ : E₀ →ₗ[R] E₁) (T₁₂ : E₁ →ₗ[R] E₂) (T₂₀ : E₂ →ₗ[R] E₀)
    (x₀ : E₀) (x₁ : E₁) (x₂ : E₂)
    (h₀₁ : T₀₁ x₀ - x₁ = 0) (h₁₂ : T₁₂ x₁ - x₂ = 0) (h₂₀ : T₂₀ x₂ - x₀ = 0) :
    T₂₀ (T₁₂ (T₀₁ x₀)) - x₀ = 0 := by
  rw [cyclicDefect_eq, h₀₁, h₁₂, h₂₀, map_zero, map_zero]
  abel

end Algebraic

/-! ## The norm bound and singular amplification -/

section Normed

variable {E₀ E₁ E₂ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- **Card `(3.2)`.**  The cyclic defect is bounded by the transported edge defects. -/
theorem norm_cyclicDefect_le (T₀₁ : E₀ →L[ℝ] E₁) (T₁₂ : E₁ →L[ℝ] E₂) (T₂₀ : E₂ →L[ℝ] E₀)
    (x₀ : E₀) (x₁ : E₁) (x₂ : E₂) :
    ‖T₂₀ (T₁₂ (T₀₁ x₀)) - x₀‖
      ≤ ‖T₂₀.comp T₁₂‖ * ‖T₀₁ x₀ - x₁‖ + ‖T₂₀‖ * ‖T₁₂ x₁ - x₂‖ + ‖T₂₀ x₂ - x₀‖ := by
  have hid := cyclicDefect_eq (T₀₁ : E₀ →ₗ[ℝ] E₁) (T₁₂ : E₁ →ₗ[ℝ] E₂) (T₂₀ : E₂ →ₗ[ℝ] E₀)
    x₀ x₁ x₂
  have hrw : T₂₀ (T₁₂ (T₀₁ x₀)) - x₀
      = (T₂₀.comp T₁₂) (T₀₁ x₀ - x₁) + T₂₀ (T₁₂ x₁ - x₂) + (T₂₀ x₂ - x₀) := hid
  rw [hrw]
  refine le_trans (norm_add₃_le) ?_
  gcongr
  · exact (T₂₀.comp T₁₂).le_opNorm _
  · exact T₂₀.le_opNorm _

/-- **Theorem 4.1, `(4.3)`.**  The cyclic defect is at most three times the amplification times the
edge accuracy. -/
theorem norm_cyclicDefect_le_three_mul (T₀₁ : E₀ →L[ℝ] E₁) (T₁₂ : E₁ →L[ℝ] E₂) (T₂₀ : E₂ →L[ℝ] E₀)
    (x₀ : E₀) (x₁ : E₁) (x₂ : E₂) (M eps : ℝ)
    (hM₁ : ‖T₂₀.comp T₁₂‖ ≤ M) (hM₂ : ‖T₂₀‖ ≤ M) (hM₃ : (1 : ℝ) ≤ M)
    (he₀₁ : ‖T₀₁ x₀ - x₁‖ ≤ eps) (he₁₂ : ‖T₁₂ x₁ - x₂‖ ≤ eps) (he₂₀ : ‖T₂₀ x₂ - x₀‖ ≤ eps) :
    ‖T₂₀ (T₁₂ (T₀₁ x₀)) - x₀‖ ≤ 3 * (M * eps) := by
  have heps : 0 ≤ eps := le_trans (norm_nonneg _) he₀₁
  have hMpos : (0 : ℝ) ≤ M := le_trans zero_le_one hM₃
  have hbound := norm_cyclicDefect_le T₀₁ T₁₂ T₂₀ x₀ x₁ x₂
  have h1 : ‖T₂₀.comp T₁₂‖ * ‖T₀₁ x₀ - x₁‖ ≤ M * eps := by
    exact mul_le_mul hM₁ he₀₁ (norm_nonneg _) hMpos
  have h2 : ‖T₂₀‖ * ‖T₁₂ x₁ - x₂‖ ≤ M * eps := by
    exact mul_le_mul hM₂ he₁₂ (norm_nonneg _) hMpos
  have h3 : ‖T₂₀ x₂ - x₀‖ ≤ M * eps := by
    refine le_trans he₂₀ ?_
    nlinarith
  linarith

/-- **Theorem 4.1, item 2 / `(4.5)`.**  If the cyclic defect stays at least `κ` while the edge
accuracy is `ε > 0`, the amplification is at least `κ/(3ε)`. -/
theorem amplification_ge (T₀₁ : E₀ →L[ℝ] E₁) (T₁₂ : E₁ →L[ℝ] E₂) (T₂₀ : E₂ →L[ℝ] E₀)
    (x₀ : E₀) (x₁ : E₁) (x₂ : E₂) (M eps kappa : ℝ)
    (hM₁ : ‖T₂₀.comp T₁₂‖ ≤ M) (hM₂ : ‖T₂₀‖ ≤ M) (hM₃ : (1 : ℝ) ≤ M)
    (he₀₁ : ‖T₀₁ x₀ - x₁‖ ≤ eps) (he₁₂ : ‖T₁₂ x₁ - x₂‖ ≤ eps) (he₂₀ : ‖T₂₀ x₂ - x₀‖ ≤ eps)
    (heps : 0 < eps) (hkappa : kappa ≤ ‖T₂₀ (T₁₂ (T₀₁ x₀)) - x₀‖) :
    kappa / (3 * eps) ≤ M := by
  have hb := norm_cyclicDefect_le_three_mul T₀₁ T₁₂ T₂₀ x₀ x₁ x₂ M eps hM₁ hM₂ hM₃ he₀₁ he₁₂ he₂₀
  rw [div_le_iff₀ (by positivity)]
  nlinarith

omit [NormedSpace ℝ E₀] in
/-- **Theorem 4.1, item 1.**  Uniformly bounded amplification plus vanishing edge accuracy forces
the cyclic defect to vanish. -/
theorem cyclicDefect_tendsto_zero_of_bounded {ι : Type*} {l : Filter ι}
    (Ω : ι → E₀) (M : ℝ) (eps : ι → ℝ)
    (hbound : ∀ n, ‖Ω n‖ ≤ 3 * (M * eps n))
    (heps : Tendsto eps l (𝓝 0)) :
    Tendsto (fun n => ‖Ω n‖) l (𝓝 0) := by
  have hzero : Tendsto (fun n => 3 * (M * eps n)) l (𝓝 0) := by
    have := (heps.const_mul M).const_mul 3
    simpa using this
  refine squeeze_zero (fun n => norm_nonneg _) hbound hzero

end Normed

/-! ## The equicontinuous completion law -/

section LocallyConvex

variable {R E₀ E₁ E₂ : Type*} [Ring R]
  [AddCommGroup E₀] [Module R E₀] [TopologicalSpace E₀] [IsTopologicalAddGroup E₀]
  [AddCommGroup E₁] [Module R E₁] [TopologicalSpace E₁]
  [AddCommGroup E₂] [Module R E₂] [TopologicalSpace E₂]

/-- **Theorem 5.1.**  Equicontinuous transports send edge-exactness to holonomy-exactness.

The equicontinuity of the two transport families is written in its defining form at the origin:
every zero-neighbourhood of the target is reached from a single zero-neighbourhood of the source,
uniformly in the family. -/
theorem cyclicDefect_tendsto_zero_of_equicontinuous {ι : Type*} {l : Filter ι}
    (S : ι → E₁ → E₀) (T : ι → E₂ → E₀) (e₀₁ : ι → E₁) (e₁₂ : ι → E₂) (e₂₀ : ι → E₀)
    (hS : ∀ U ∈ 𝓝 (0 : E₀), ∃ V ∈ 𝓝 (0 : E₁), ∀ n, ∀ y ∈ V, S n y ∈ U)
    (hT : ∀ U ∈ 𝓝 (0 : E₀), ∃ V ∈ 𝓝 (0 : E₂), ∀ n, ∀ y ∈ V, T n y ∈ U)
    (h₀₁ : Tendsto e₀₁ l (𝓝 0)) (h₁₂ : Tendsto e₁₂ l (𝓝 0)) (h₂₀ : Tendsto e₂₀ l (𝓝 0)) :
    Tendsto (fun n => S n (e₀₁ n) + T n (e₁₂ n) + e₂₀ n) l (𝓝 0) := by
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨U₁, hU₁, hsub₁⟩ := exists_nhds_zero_half hU
  obtain ⟨U₂, hU₂, hsub₂⟩ := exists_nhds_zero_half hU₁
  obtain ⟨V₁, hV₁, hSV⟩ := hS U₂ hU₂
  obtain ⟨V₂, hV₂, hTV⟩ := hT U₂ hU₂
  filter_upwards [Filter.tendsto_def.1 h₀₁ V₁ hV₁, Filter.tendsto_def.1 h₁₂ V₂ hV₂,
    Filter.tendsto_def.1 h₂₀ U₁ hU₁] with n hn₁ hn₂ hn₃
  exact hsub₁ _ (hsub₂ _ (hSV n _ hn₁) _ (hTV n _ hn₂)) _ hn₃

end LocallyConvex

end HTGeometry.ConstraintRelativity
