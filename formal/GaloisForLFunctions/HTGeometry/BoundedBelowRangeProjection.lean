import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# The orthogonal projection onto the image of a subspace under a bounded-below operator

Let `Q` be the orthogonal projection of a Hilbert space onto a closed subspace `S`, and let `M` be a
bounded operator that is bounded below on `S`.  Then the Gram operator

`A = Q M* M Q + (1 - Q)`

is invertible, and

`P = M Q A⁻¹ Q M*`

is exactly the orthogonal projection onto `M(S)`.  Once `A` is invertible the proof is purely
algebraic: the identity `A (1 - Q) = 1 - Q` forces `A⁻¹` to fix the splitting, which gives
`P (M Q) = M Q`, hence idempotence, self-adjointness and the range identification.
-/

open ContinuousLinearMap
open scoped InnerProductSpace

namespace HTGeometry

section Invertibility

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A self-adjoint operator with a positive lower bound is invertible. -/
theorem isUnit_of_isSelfAdjoint_of_lower_bound {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) {m : ℝ}
    (hm : 0 < m) (hlow : ∀ x : H, m * ‖x‖ ≤ ‖A x‖) : IsUnit A := by
  have hanti : AntilipschitzWith (Real.toNNReal m⁻¹) A := by
    refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
    have h := hlow (x - y)
    rw [map_sub] at h
    have hcoe : ((Real.toNNReal m⁻¹ : NNReal) : ℝ) = m⁻¹ :=
      Real.coe_toNNReal _ (by positivity)
    rw [dist_eq_norm, dist_eq_norm, hcoe, inv_mul_eq_div, le_div_iff₀ hm]
    linarith [h]
  have hinj : Function.Injective A := hanti.injective
  have hclosed : IsClosed (Set.range (A : H → H)) := hanti.isClosed_range A.uniformContinuous
  have hcl : IsClosed ((LinearMap.range (A : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) := by
    simpa [LinearMap.coe_range] using hclosed
  haveI : CompleteSpace (LinearMap.range (A : H →ₗ[ℂ] H) : Submodule ℂ H) :=
    hcl.completeSpace_coe
  haveI : (LinearMap.range (A : H →ₗ[ℂ] H)).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace _
  have hbot : (LinearMap.range (A : H →ₗ[ℂ] H))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hzero : ∀ x : H, ⟪x, A y⟫_ℂ = 0 := by
      intro x
      have hmem : A x ∈ LinearMap.range (A : H →ₗ[ℂ] H) := ⟨x, rfl⟩
      have hx := (Submodule.mem_orthogonal _ y).mp hy (A x) hmem
      have h2 : ⟪x, (ContinuousLinearMap.adjoint A) y⟫_ℂ = ⟪A x, y⟫_ℂ :=
        ContinuousLinearMap.adjoint_inner_right A x y
      rw [hA.adjoint_eq] at h2
      rw [h2]
      exact hx
    have hAy : A y = 0 := by
      have := hzero (A y)
      exact inner_self_eq_zero.mp this
    have hy0 := hlow y
    rw [hAy, norm_zero] at hy0
    have : ‖y‖ ≤ 0 := by nlinarith [norm_nonneg y]
    exact norm_eq_zero.mp (le_antisymm this (norm_nonneg y))
  have hsurj : Function.Surjective A := by
    have htop : LinearMap.range (A : H →ₗ[ℂ] H) = ⊤ := by
      have := Submodule.orthogonal_orthogonal (LinearMap.range (A : H →ₗ[ℂ] H))
      rw [hbot, Submodule.bot_orthogonal_eq_top] at this
      exact this.symm
    exact LinearMap.range_eq_top.mp htop
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, hsurj⟩

end Invertibility

section Projection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Gram operator `A = Q M* M Q + (1 - Q)` of a bounded operator relative to a projection. -/
noncomputable def rangeProjectionGram (Q M : H →L[ℂ] H) : H →L[ℂ] H :=
  Q * (ContinuousLinearMap.adjoint M) * M * Q + (1 - Q)

/-- The closed-range projection formula `P = M Q A⁻¹ Q M*`. -/
noncomputable def rangeProjection (Q M : H →L[ℂ] H) : H →L[ℂ] H :=
  M * Q * Ring.inverse (rangeProjectionGram Q M) * Q * (ContinuousLinearMap.adjoint M)

variable {Q M : H →L[ℂ] H}

theorem rangeProjectionGram_isSelfAdjoint (hQ : IsSelfAdjoint Q) :
    IsSelfAdjoint (rangeProjectionGram Q M) := by
  have hstarQ : star Q = Q := hQ
  rw [IsSelfAdjoint, rangeProjectionGram, star_add, star_sub, star_one, hstarQ]
  rw [star_mul, star_mul, star_mul, hstarQ]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_adjoint]
  noncomm_ring

theorem rangeProjectionGram_mul_one_sub (hQ2 : IsIdempotentElem Q) :
    rangeProjectionGram Q M * (1 - Q) = 1 - Q := by
  have h : Q * Q = Q := hQ2
  have hQ0 : Q * (1 - Q) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  have hsq : (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
  rw [rangeProjectionGram]
  calc (Q * (ContinuousLinearMap.adjoint M) * M * Q + (1 - Q)) * (1 - Q)
      = Q * (ContinuousLinearMap.adjoint M) * M * (Q * (1 - Q)) + (1 - Q) * (1 - Q) := by
        noncomm_ring
    _ = 1 - Q := by
        rw [hQ0, mul_zero, zero_add, hsq, h]
        abel

theorem one_sub_mul_rangeProjectionGram (hQ2 : IsIdempotentElem Q) :
    (1 - Q) * rangeProjectionGram Q M = 1 - Q := by
  have h : Q * Q = Q := hQ2
  have hQ0 : (1 - Q) * Q = 0 := by rw [sub_mul, one_mul, h, sub_self]
  have hsq : (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
  rw [rangeProjectionGram]
  calc (1 - Q) * (Q * (ContinuousLinearMap.adjoint M) * M * Q + (1 - Q))
      = ((1 - Q) * Q) * ((ContinuousLinearMap.adjoint M) * M * Q) + (1 - Q) * (1 - Q) := by
        noncomm_ring
    _ = 1 - Q := by
        rw [hQ0, zero_mul, zero_add, hsq, h]
        abel

omit [CompleteSpace H] in
/-- Self-adjoint idempotents act as the identity on their range. -/
theorem apply_apply_of_isIdempotentElem (hQ2 : IsIdempotentElem Q) (y : H) : Q (Q y) = Q y := by
  have h : Q * Q = Q := hQ2
  calc Q (Q y) = (Q * Q) y := rfl
    _ = Q y := by rw [h]

/-- For a self-adjoint idempotent, `⟪x, Q x⟫ = ⟪Q x, Q x⟫`. -/
theorem inner_self_apply_eq (hQ : IsSelfAdjoint Q) (hQ2 : IsIdempotentElem Q) (x : H) :
    ⟪x, Q x⟫_ℂ = ⟪Q x, Q x⟫_ℂ := by
  have hstar : ContinuousLinearMap.adjoint Q = Q := hQ.adjoint_eq
  have h := ContinuousLinearMap.adjoint_inner_right Q x (Q x)
  rw [hstar, apply_apply_of_isIdempotentElem hQ2 x] at h
  exact h

/-- A self-adjoint idempotent is a contraction. -/
theorem norm_apply_le_of_isSelfAdjoint_isIdempotentElem (hQ : IsSelfAdjoint Q)
    (hQ2 : IsIdempotentElem Q) (x : H) : ‖Q x‖ ≤ ‖x‖ := by
  have hinner := inner_self_apply_eq hQ hQ2 x
  have h1 : ‖Q x‖ ^ 2 = (⟪x, Q x⟫_ℂ).re := by
    rw [hinner, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have h2 : (⟪x, Q x⟫_ℂ).re ≤ ‖x‖ * ‖Q x‖ := by
    calc (⟪x, Q x⟫_ℂ).re ≤ ‖⟪x, Q x⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖Q x‖ := norm_inner_le_norm _ _
  nlinarith [norm_nonneg (Q x), norm_nonneg x]

theorem re_inner_rangeProjectionGram (hQ : IsSelfAdjoint Q) (hQ2 : IsIdempotentElem Q) (x : H) :
    (⟪x, rangeProjectionGram Q M x⟫_ℂ).re
      = ‖M (Q x)‖ ^ 2 + ‖x‖ ^ 2 - ‖Q x‖ ^ 2 := by
  have hstar : ContinuousLinearMap.adjoint Q = Q := hQ.adjoint_eq
  have happ : rangeProjectionGram Q M x
      = Q ((ContinuousLinearMap.adjoint M) (M (Q x))) + (x - Q x) := by
    simp [rangeProjectionGram]
  have hA : ⟪x, Q ((ContinuousLinearMap.adjoint M) (M (Q x)))⟫_ℂ
      = ⟪Q x, (ContinuousLinearMap.adjoint M) (M (Q x))⟫_ℂ := by
    have h := ContinuousLinearMap.adjoint_inner_right Q x
      ((ContinuousLinearMap.adjoint M) (M (Q x)))
    rw [hstar] at h
    exact h
  have hB : ⟪Q x, (ContinuousLinearMap.adjoint M) (M (Q x))⟫_ℂ = ⟪M (Q x), M (Q x)⟫_ℂ :=
    ContinuousLinearMap.adjoint_inner_right M (Q x) (M (Q x))
  have h3 := inner_self_apply_eq hQ hQ2 x
  rw [happ, inner_add_right, hA, hB, inner_sub_right, h3]
  simp [inner_self_eq_norm_sq_to_K, Complex.add_re, Complex.sub_re, ← Complex.ofReal_pow]
  ring

/-- Positivity of the Gram operator: it is bounded below by `min (c²) 1`. -/
theorem lower_bound_rangeProjectionGram (hQ : IsSelfAdjoint Q) (hQ2 : IsIdempotentElem Q)
    {c : ℝ} (hc : 0 < c) (hbb : ∀ x : H, c * ‖Q x‖ ≤ ‖M (Q x)‖) (x : H) :
    min (c ^ 2) 1 * ‖x‖ ≤ ‖rangeProjectionGram Q M x‖ := by
  have hre := re_inner_rangeProjectionGram (M := M) hQ hQ2 x
  have hcs : (⟪x, rangeProjectionGram Q M x⟫_ℂ).re ≤ ‖x‖ * ‖rangeProjectionGram Q M x‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hQle := norm_apply_le_of_isSelfAdjoint_isIdempotentElem hQ hQ2 x
  have hM := hbb x
  have hMsq : c ^ 2 * ‖Q x‖ ^ 2 ≤ ‖M (Q x)‖ ^ 2 := by
    have hpos : (0 : ℝ) ≤ c * ‖Q x‖ := by positivity
    nlinarith [mul_self_le_mul_self hpos hM]
  have hQsq : ‖Q x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [norm_nonneg (Q x), norm_nonneg x]
  have hkey : min (c ^ 2) 1 * ‖x‖ ^ 2 ≤ ‖M (Q x)‖ ^ 2 + ‖x‖ ^ 2 - ‖Q x‖ ^ 2 := by
    rcases le_total (c ^ 2) 1 with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  rcases eq_or_lt_of_le (norm_nonneg x) with h0 | hx
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · have hchain : min (c ^ 2) 1 * ‖x‖ ^ 2 ≤ ‖x‖ * ‖rangeProjectionGram Q M x‖ := by
      rw [← hre] at hkey
      exact hkey.trans hcs
    nlinarith

/-- The Gram operator of an operator bounded below on the range of a projection is invertible. -/
theorem isUnit_rangeProjectionGram (hQ : IsSelfAdjoint Q) (hQ2 : IsIdempotentElem Q)
    {c : ℝ} (hc : 0 < c) (hbb : ∀ x : H, c * ‖Q x‖ ≤ ‖M (Q x)‖) :
    IsUnit (rangeProjectionGram Q M) :=
  isUnit_of_isSelfAdjoint_of_lower_bound (rangeProjectionGram_isSelfAdjoint hQ)
    (lt_min (pow_pos hc 2) one_pos) (lower_bound_rangeProjectionGram hQ hQ2 hc hbb)

section Algebra

variable (hQ : IsSelfAdjoint Q) (hQ2 : IsIdempotentElem Q)
  {c : ℝ} (hc : 0 < c) (hbb : ∀ x : H, c * ‖Q x‖ ≤ ‖M (Q x)‖)

include hQ hQ2 hc hbb

theorem inverse_rangeProjectionGram_mul_one_sub :
    Ring.inverse (rangeProjectionGram Q M) * (1 - Q) = 1 - Q := by
  have hu := isUnit_rangeProjectionGram hQ hQ2 hc hbb
  calc Ring.inverse (rangeProjectionGram Q M) * (1 - Q)
      = Ring.inverse (rangeProjectionGram Q M) * (rangeProjectionGram Q M * (1 - Q)) := by
        rw [rangeProjectionGram_mul_one_sub hQ2]
    _ = (Ring.inverse (rangeProjectionGram Q M) * rangeProjectionGram Q M) * (1 - Q) := by
        rw [mul_assoc]
    _ = 1 - Q := by rw [Ring.inverse_mul_cancel _ hu, one_mul]

theorem one_sub_mul_inverse_rangeProjectionGram :
    (1 - Q) * Ring.inverse (rangeProjectionGram Q M) = 1 - Q := by
  have hu := isUnit_rangeProjectionGram hQ hQ2 hc hbb
  calc (1 - Q) * Ring.inverse (rangeProjectionGram Q M)
      = ((1 - Q) * rangeProjectionGram Q M) * Ring.inverse (rangeProjectionGram Q M) := by
        rw [one_sub_mul_rangeProjectionGram hQ2]
    _ = (1 - Q) * (rangeProjectionGram Q M * Ring.inverse (rangeProjectionGram Q M)) := by
        rw [mul_assoc]
    _ = 1 - Q := by rw [Ring.mul_inverse_cancel _ hu, mul_one]

theorem star_inverse_rangeProjectionGram :
    star (Ring.inverse (rangeProjectionGram Q M)) = Ring.inverse (rangeProjectionGram Q M) := by
  have hu := isUnit_rangeProjectionGram hQ hQ2 hc hbb
  have hA : star (rangeProjectionGram Q M) = rangeProjectionGram Q M :=
    rangeProjectionGram_isSelfAdjoint hQ
  have h1 : rangeProjectionGram Q M * star (Ring.inverse (rangeProjectionGram Q M)) = 1 := by
    have := congrArg star (Ring.inverse_mul_cancel (rangeProjectionGram Q M) hu)
    rw [star_mul, star_one, hA] at this
    exact this
  have h2 : star (Ring.inverse (rangeProjectionGram Q M)) * rangeProjectionGram Q M = 1 := by
    have := congrArg star (Ring.mul_inverse_cancel (rangeProjectionGram Q M) hu)
    rw [star_mul, star_one, hA] at this
    exact this
  calc star (Ring.inverse (rangeProjectionGram Q M))
      = star (Ring.inverse (rangeProjectionGram Q M)) *
          (rangeProjectionGram Q M * Ring.inverse (rangeProjectionGram Q M)) := by
        rw [Ring.mul_inverse_cancel _ hu, mul_one]
    _ = (star (Ring.inverse (rangeProjectionGram Q M)) * rangeProjectionGram Q M) *
          Ring.inverse (rangeProjectionGram Q M) := by rw [mul_assoc]
    _ = Ring.inverse (rangeProjectionGram Q M) := by rw [h2, one_mul]

/-- **The projection formula reproduces `M Q` exactly.** -/
theorem rangeProjection_mul_self : rangeProjection Q M * (M * Q) = M * Q := by
  have hu := isUnit_rangeProjectionGram hQ hQ2 hc hbb
  have hQ0 : Q * (1 - Q) = 0 := by
    have h : Q * Q = Q := hQ2
    rw [mul_sub, mul_one, h, sub_self]
  have hTT : (Q * (ContinuousLinearMap.adjoint M)) * (M * Q)
      = rangeProjectionGram Q M - (1 - Q) := by
    rw [rangeProjectionGram]; noncomm_ring
  have hsplit : rangeProjection Q M * (M * Q)
      = (M * Q) * Ring.inverse (rangeProjectionGram Q M) *
          ((Q * (ContinuousLinearMap.adjoint M)) * (M * Q)) := by
    simp only [rangeProjection]; noncomm_ring
  rw [hsplit, hTT, mul_sub, mul_assoc ((M * Q)) (Ring.inverse (rangeProjectionGram Q M)),
    Ring.inverse_mul_cancel _ hu, mul_one,
    mul_assoc ((M * Q)) (Ring.inverse (rangeProjectionGram Q M)),
    inverse_rangeProjectionGram_mul_one_sub hQ hQ2 hc hbb, mul_assoc, hQ0, mul_zero, sub_zero]

theorem rangeProjection_isIdempotentElem : IsIdempotentElem (rangeProjection Q M) := by
  have hassoc : rangeProjection Q M * rangeProjection Q M
      = (rangeProjection Q M * (M * Q)) *
          (Ring.inverse (rangeProjectionGram Q M) * (Q * (ContinuousLinearMap.adjoint M))) := by
    simp only [rangeProjection]; noncomm_ring
  rw [IsIdempotentElem, hassoc, rangeProjection_mul_self hQ hQ2 hc hbb]
  simp only [rangeProjection]; noncomm_ring

theorem rangeProjection_isSelfAdjoint : IsSelfAdjoint (rangeProjection Q M) := by
  have hstarQ : star Q = Q := hQ
  have hAi := star_inverse_rangeProjectionGram hQ hQ2 hc hbb
  have hstarMa : star (ContinuousLinearMap.adjoint M) = M := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint]
  have hstarM : star M = ContinuousLinearMap.adjoint M := ContinuousLinearMap.star_eq_adjoint M
  rw [IsSelfAdjoint, rangeProjection]
  rw [star_mul, star_mul, star_mul, star_mul, hstarQ, hAi, hstarMa, hstarM]
  noncomm_ring

theorem range_rangeProjection :
    LinearMap.range (rangeProjection Q M : H →ₗ[ℂ] H)
      = LinearMap.range ((M * Q : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    refine ⟨(Ring.inverse (rangeProjectionGram Q M) * Q * (ContinuousLinearMap.adjoint M)) x, ?_⟩
    have : rangeProjection Q M
        = (M * Q) *
            (Ring.inverse (rangeProjectionGram Q M) * Q * (ContinuousLinearMap.adjoint M)) := by
      simp only [rangeProjection]; noncomm_ring
    rw [this]
    rfl
  · rintro y ⟨x, rfl⟩
    refine ⟨(M * Q : H →L[ℂ] H) x, ?_⟩
    exact congrArg (fun T : H →L[ℂ] H => T x) (rangeProjection_mul_self hQ hQ2 hc hbb)

/-- The projection formula lands in the image subspace. -/
theorem rangeProjection_mem_range (y : H) :
    rangeProjection Q M y ∈ LinearMap.range ((M * Q : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  have h := range_rangeProjection hQ hQ2 hc hbb
  have hy : rangeProjection Q M y ∈ LinearMap.range (rangeProjection Q M : H →ₗ[ℂ] H) := ⟨y, rfl⟩
  rwa [h] at hy

/-- The projection formula has orthogonal defect. -/
theorem sub_rangeProjection_mem_orthogonal (y : H) :
    y - rangeProjection Q M y
      ∈ (LinearMap.range ((M * Q : H →L[ℂ] H) : H →ₗ[ℂ] H))ᗮ := by
  have hsa := rangeProjection_isSelfAdjoint hQ hQ2 hc hbb
  have hstar : ContinuousLinearMap.adjoint (rangeProjection Q M) = rangeProjection Q M :=
    hsa.adjoint_eq
  refine (Submodule.mem_orthogonal _ _).mpr ?_
  rintro z ⟨x, rfl⟩
  have hfix : rangeProjection Q M ((M * Q : H →L[ℂ] H) x) = (M * Q : H →L[ℂ] H) x :=
    congrArg (fun T : H →L[ℂ] H => T x) (rangeProjection_mul_self hQ hQ2 hc hbb)
  have hmove : ⟪(M * Q : H →L[ℂ] H) x, rangeProjection Q M y⟫_ℂ
      = ⟪(M * Q : H →L[ℂ] H) x, y⟫_ℂ := by
    have h := ContinuousLinearMap.adjoint_inner_right (rangeProjection Q M)
      ((M * Q : H →L[ℂ] H) x) y
    rw [hstar, hfix] at h
    exact h
  have : ⟪(M * Q : H →L[ℂ] H) x, y - rangeProjection Q M y⟫_ℂ = 0 := by
    rw [inner_sub_right, hmove, sub_self]
  exact this

/-- **The closed-range projection formula.**  `M Q A⁻¹ Q M*` is the orthogonal projection onto
the image of the range of `Q` under `M`. -/
theorem starProjection_eq_rangeProjection {K : Submodule ℂ H} [K.HasOrthogonalProjection]
    (hK : K = LinearMap.range ((M * Q : H →L[ℂ] H) : H →ₗ[ℂ] H)) :
    K.starProjection = rangeProjection Q M := by
  ext y
  exact Submodule.eq_starProjection_of_mem_orthogonal
    (hK ▸ rangeProjection_mem_range hQ hQ2 hc hbb y)
    (hK ▸ sub_rangeProjection_mem_orthogonal hQ hQ2 hc hbb y)

end Algebra

end Projection

end HTGeometry
