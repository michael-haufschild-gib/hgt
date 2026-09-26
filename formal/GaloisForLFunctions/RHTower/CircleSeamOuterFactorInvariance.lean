import GaloisForLFunctions.RHTower.CircleSeamModulusMargin

/-!
# Outer factors change the seam margin by bounded factors only

Let `u, u₀` be circle phases with `conj u = conj(h) · conj u₀ · h⁻¹`, where `h` and `h⁻¹` are
bounded symbols without negative Fourier modes (an outer factor).  With `|h| ≤ A` and
`|h⁻¹| ≤ B`,

`1 − ‖(1 − P) U† P‖² ≥ (1 − ‖(1 − P) U₀† P‖²) / (AB)²`   (`one_sub_seam_sq_ge_of_outer_factor`).

Mechanism: `T_{ū} = T_{conj h} T_{ū₀} T_{h⁻¹}`.  The co-analytic multiplier on the left is
inverted by `P M_{conj(h⁻¹)}` on the Hardy part, and the analytic one on the right keeps Hardy
vectors Hardy.  The lower bound of `T_{ū₀}` therefore transfers with the loss `AB`.  Applied to
`xi`, `ζ` and the tail product `ζ / E_P`, which differ by zero-free factors, route 1's
seam criterion is the same statement up to explicit constants.
-/

noncomputable section

open Complex MeasureTheory ContinuousLinearMap

namespace RHTower

namespace SeamModulusMargin

/-- Pythagoras for the seam of a circle phase: for Hardy `f`,
`‖(1 − P) U† f‖² = ‖f‖² − ‖P U† f‖²`. -/
theorem seam_norm_sq_eq (u : CCMCirclePhase) (f : CCMCircleL2) :
    ‖u.conjMultiplier f - ccmCircleHardyProjection (u.conjMultiplier f)‖ ^ 2 =
      ‖f‖ ^ 2 - ‖ccmCircleHardyProjection (u.conjMultiplier f)‖ ^ 2 := by
  have hiso : ‖u.conjMultiplier f‖ = ‖f‖ := by
    have hsq : ‖u.conjMultiplier f‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, ← u.adjoint_multiplier,
        adjoint_inner_left]
      have := congrArg (fun T : CCMCircleL2 →L[ℂ] CCMCircleL2 => T f)
        u.multiplier_mul_conjMultiplier
      simp only [mul_apply_eq_comp, one_apply_eq_self] at this
      rw [← u.adjoint_multiplier] at this
      rw [this]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
  have hpy := norm_sq_eq_add_of_orthogonalProjection ccmCircleHardyProjection
    ccmCircleHardyProjection_idempotent ccmCircleHardyProjection_adjoint (u.conjMultiplier f)
  rw [hiso] at hpy
  linarith

theorem seam_apply_eq (u : CCMCirclePhase) (y : CCMCircleL2) :
    u.datum.adjointHankelSeam y =
      u.conjMultiplier (ccmCircleHardyProjection y) -
        ccmCircleHardyProjection (u.conjMultiplier (ccmCircleHardyProjection y)) := by
  change ((1 - ccmCircleHardyProjection) * adjoint u.multiplier * ccmCircleHardyProjection) y = _
  rw [u.adjoint_multiplier]
  simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self]

theorem norm_hardy_le (y : CCMCircleL2) : ‖ccmCircleHardyProjection y‖ ≤ ‖y‖ := by
  have := norm_sq_eq_add_of_orthogonalProjection ccmCircleHardyProjection
    ccmCircleHardyProjection_idempotent ccmCircleHardyProjection_adjoint y
  nlinarith [norm_nonneg (ccmCircleHardyProjection y), norm_nonneg y,
    sq_nonneg ‖y - ccmCircleHardyProjection y‖]

/-- Lower bound for the Hardy part of `U₀†f` from the seam norm. -/
theorem lower_of_seam (u : CCMCirclePhase) (f : CCMCircleL2)
    (hf : ccmCircleHardyProjection f = f) :
    (1 - ‖u.datum.adjointHankelSeam‖ ^ 2) * ‖f‖ ^ 2 ≤
      ‖ccmCircleHardyProjection (u.conjMultiplier f)‖ ^ 2 := by
  have happ := seam_apply_eq u f
  rw [hf] at happ
  have hsq := seam_norm_sq_eq u f
  rw [← happ] at hsq
  have hle : ‖u.datum.adjointHankelSeam f‖ ≤ ‖u.datum.adjointHankelSeam‖ * ‖f‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h2 := mul_self_le_mul_self (norm_nonneg _) hle
  nlinarith

/-- A seam bound from a lower bound on the Hardy part of `U† f`. -/
theorem seam_sq_le_of_lower (u : CCMCirclePhase) {c : ℝ} (_hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hlow : ∀ f : CCMCircleL2, ccmCircleHardyProjection f = f →
      c * ‖f‖ ^ 2 ≤ ‖ccmCircleHardyProjection (u.conjMultiplier f)‖ ^ 2) :
    ‖u.datum.adjointHankelSeam‖ ^ 2 ≤ 1 - c := by
  have hnn : 0 ≤ 1 - c := by linarith
  have hbound : ∀ y, ‖u.datum.adjointHankelSeam y‖ ≤ Real.sqrt (1 - c) * ‖y‖ := by
    intro y
    set f := ccmCircleHardyProjection y
    have hPf : ccmCircleHardyProjection f = f := hardy_idem y
    rw [seam_apply_eq]
    have hsq := seam_norm_sq_eq u f
    have hl := hlow f hPf
    have hfy := norm_hardy_le y
    have hfy2 : ‖f‖ ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hfy 2
    have hle : ‖u.conjMultiplier f - ccmCircleHardyProjection (u.conjMultiplier f)‖ ^ 2 ≤
        (1 - c) * ‖y‖ ^ 2 := by nlinarith
    calc ‖u.conjMultiplier f - ccmCircleHardyProjection (u.conjMultiplier f)‖
        = Real.sqrt (‖u.conjMultiplier f - ccmCircleHardyProjection (u.conjMultiplier f)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((1 - c) * ‖y‖ ^ 2) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt (1 - c) * ‖y‖ := by rw [Real.sqrt_mul hnn, Real.sqrt_sq (norm_nonneg _)]
  have hop : ‖u.datum.adjointHankelSeam‖ ≤ Real.sqrt (1 - c) :=
    ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) hbound
  calc ‖u.datum.adjointHankelSeam‖ ^ 2 ≤ Real.sqrt (1 - c) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hop 2
    _ = 1 - c := Real.sq_sqrt hnn

/-- The adjoint seam of a circle phase has norm at most one. -/
theorem seam_sq_le_one (u : CCMCirclePhase) : ‖u.datum.adjointHankelSeam‖ ^ 2 ≤ 1 := by
  have := seam_sq_le_of_lower u (c := 0) le_rfl zero_le_one
    (fun f _ => by rw [zero_mul]; positivity)
  linarith

/-- **Outer-factor quasi-invariance of the seam margin.** -/
theorem one_sub_seam_sq_ge_of_outer_factor (u u₀ : CCMCirclePhase)
    (h hi hc hic : CCMCircleBoundedSymbol)
    (hhi : ∀ n : ℤ, n < 0 → fourierCoeff hi.toFun n = 0)
    (hc_eq : ∀ z, hc.toFun z = starRingEnd ℂ (h.toFun z))
    (hic_eq : ∀ z, hic.toFun z = starRingEnd ℂ (hi.toFun z))
    (hinv : ∀ z, h.toFun z * hi.toFun z = 1)
    (hu : ∀ z, starRingEnd ℂ (u.toFun z) =
      hc.toFun z * (starRingEnd ℂ (u₀.toFun z) * hi.toFun z))
    (hAB : 0 < h.bound * hic.bound) :
    (1 - ‖u₀.datum.adjointHankelSeam‖ ^ 2) / (h.bound * hic.bound) ^ 2 ≤
      1 - ‖u.datum.adjointHankelSeam‖ ^ 2 := by
  set P := ccmCircleHardyProjection
  set μsq := 1 - ‖u₀.datum.adjointHankelSeam‖ ^ 2 with hμsq
  set K := h.bound * hic.bound with hK
  have hseam1 := seam_sq_le_one u
  by_cases hμ : μsq ≤ 0
  · have : μsq / K ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hμ (sq_nonneg K)
    linarith
  push Not at hμ
  -- `K ≥ 1`
  have hK1 : 1 ≤ K := by
    obtain ⟨z, -⟩ : ∃ z : AddCircle (1 : ℝ), True := ⟨0, trivial⟩
    have h1 : ‖h.toFun z‖ ≤ h.bound := h.norm_le z
    have h2 : ‖hic.toFun z‖ ≤ hic.bound := hic.norm_le z
    have h3 : ‖h.toFun z‖ * ‖hic.toFun z‖ = 1 := by
      rw [hic_eq z, Complex.norm_conj, ← norm_mul, hinv z, norm_one]
    calc (1 : ℝ) = ‖h.toFun z‖ * ‖hic.toFun z‖ := h3.symm
      _ ≤ K := mul_le_mul h1 h2 (norm_nonneg _) h.bound_nonneg
  -- the factorization of `U†`
  have hconj : ∀ f : CCMCircleL2, u.conjMultiplier f =
      ccmCircleMultiplier hc (u₀.conjMultiplier (ccmCircleMultiplier hi f)) := by
    intro f
    apply Lp.ext
    filter_upwards [u.conjMultiplier_coeFn f,
      ccmCircleMultiplier_coeFn hc (u₀.conjMultiplier (ccmCircleMultiplier hi f)),
      u₀.conjMultiplier_coeFn (ccmCircleMultiplier hi f),
      ccmCircleMultiplier_coeFn hi f] with z h1 h2 h3 h4
    rw [h1, h2, h3, h4, hu z]
    ring
  have hone : ccmCircleMultiplier hic * ccmCircleMultiplier hc = 1 := by
    rw [ccmCircleMultiplier_mul_eq hic hc (continuousCircleSymbol (fun _ => 1) continuous_const)
      (fun z => by rw [hic_eq z, hc_eq z, ← map_mul, mul_comm, hinv z, map_one]; rfl)]
    exact ccmCircleMultiplier_eq_one _ (fun _ => rfl)
  have hhone : ccmCircleMultiplier h * ccmCircleMultiplier hi = 1 := by
    rw [ccmCircleMultiplier_mul_eq h hi (continuousCircleSymbol (fun _ => 1) continuous_const)
      (fun z => by rw [hinv z]; rfl)]
    exact ccmCircleMultiplier_eq_one _ (fun _ => rfl)
  have hMic : ‖ccmCircleMultiplier hic‖ ≤ hic.bound :=
    MeasureTheory.norm_lpBoundedMulCLM_le _ _ _
  have hMh : ‖ccmCircleMultiplier h‖ ≤ h.bound :=
    MeasureTheory.norm_lpBoundedMulCLM_le _ _ _
  have hlow : ∀ f : CCMCircleL2, P f = f →
      (μsq / K ^ 2) * ‖f‖ ^ 2 ≤ ‖P (u.conjMultiplier f)‖ ^ 2 := by
    intro f hf
    set g := ccmCircleMultiplier hi f with hg
    have hPg : P g = g := hardy_multiplier_of_hardy hi hhi hf
    set w := u₀.conjMultiplier g with hw
    -- `P w = P(M_{hic} P(M_{hc} w))`
    have hback : P (ccmCircleMultiplier hic (P (ccmCircleMultiplier hc w))) = P w := by
      have hbc : ∀ z, hic.toFun z = starRingEnd ℂ (hi.toFun z) := hic_eq
      rw [hardy_coanalytic_hardy hi hic hhi hbc]
      have := congrArg (fun T : CCMCircleL2 →L[ℂ] CCMCircleL2 => T w) hone
      simp only [mul_apply_eq_comp, one_apply_eq_self] at this
      rw [this]
    have hPw : ‖P w‖ ≤ hic.bound * ‖P (ccmCircleMultiplier hc w)‖ := by
      calc ‖P w‖ = ‖P (ccmCircleMultiplier hic (P (ccmCircleMultiplier hc w)))‖ := by rw [hback]
        _ ≤ ‖ccmCircleMultiplier hic (P (ccmCircleMultiplier hc w))‖ := norm_hardy_le _
        _ ≤ ‖ccmCircleMultiplier hic‖ * ‖P (ccmCircleMultiplier hc w)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ hic.bound * ‖P (ccmCircleMultiplier hc w)‖ := by gcongr
    have hfg : ‖f‖ ≤ h.bound * ‖g‖ := by
      have hfeq : ccmCircleMultiplier h g = f := by
        have := congrArg (fun T : CCMCircleL2 →L[ℂ] CCMCircleL2 => T f) hhone
        simpa [mul_apply_eq_comp, hg] using this
      calc ‖f‖ = ‖ccmCircleMultiplier h g‖ := by rw [hfeq]
        _ ≤ ‖ccmCircleMultiplier h‖ * ‖g‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ h.bound * ‖g‖ := by gcongr
    have h0 : μsq * ‖g‖ ^ 2 ≤ ‖P w‖ ^ 2 := lower_of_seam u₀ g hPg
    have hU : u.conjMultiplier f = ccmCircleMultiplier hc w := hconj f
    rw [hU]
    set Q := ‖P (ccmCircleMultiplier hc w)‖ with hQ
    set nf := ‖f‖ with hnf
    set ng := ‖g‖ with hng
    set nw := ‖P w‖ with hnw
    have hA0 : 0 ≤ h.bound := h.bound_nonneg
    have hB0 : 0 ≤ hic.bound := hic.bound_nonneg
    have hnf0 : 0 ≤ nf := norm_nonneg _
    have hng0 : 0 ≤ ng := norm_nonneg _
    have hnw0 : 0 ≤ nw := norm_nonneg _
    have hQ0 : 0 ≤ Q := norm_nonneg _
    have e1 : nf ^ 2 ≤ h.bound ^ 2 * ng ^ 2 := by
      have := mul_self_le_mul_self hnf0 hfg
      nlinarith
    have e2 : nw ^ 2 ≤ hic.bound ^ 2 * Q ^ 2 := by
      have := mul_self_le_mul_self hnw0 hPw
      nlinarith
    have hKpos : 0 < K ^ 2 := pow_pos (lt_of_lt_of_le one_pos hK1) 2
    have hK2 : K ^ 2 = h.bound ^ 2 * hic.bound ^ 2 := by rw [hK, mul_pow]
    rw [div_mul_eq_mul_div, div_le_iff₀ hKpos, hK2]
    have s1 : μsq * nf ^ 2 ≤ μsq * (h.bound ^ 2 * ng ^ 2) :=
      mul_le_mul_of_nonneg_left e1 hμ.le
    have s2 : h.bound ^ 2 * (μsq * ng ^ 2) ≤ h.bound ^ 2 * nw ^ 2 :=
      mul_le_mul_of_nonneg_left h0 (sq_nonneg _)
    have s3 : h.bound ^ 2 * nw ^ 2 ≤ h.bound ^ 2 * (hic.bound ^ 2 * Q ^ 2) :=
      mul_le_mul_of_nonneg_left e2 (sq_nonneg _)
    nlinarith
  have hc0 : 0 ≤ μsq / K ^ 2 := div_nonneg hμ.le (sq_nonneg K)
  have hc1 : μsq / K ^ 2 ≤ 1 := by
    have hμ1 : μsq ≤ 1 := by rw [hμsq]; nlinarith [sq_nonneg ‖u₀.datum.adjointHankelSeam‖]
    have hK2 : 1 ≤ K ^ 2 := by nlinarith
    rw [div_le_one (pow_pos (lt_of_lt_of_le one_pos hK1) 2)]; linarith
  have := seam_sq_le_of_lower u hc0 hc1 hlow
  linarith

end SeamModulusMargin

end RHTower
