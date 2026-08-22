import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinUniqueness
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinFlowInvariance
import GaloisForLFunctions.HTGeometry.HilbertSchmidtBochner
import GaloisForLFunctions.HTGeometry.BochnerLoewner

/-!
# The Wasserstein equation for a probability measure

For a `ℙ`-valued random variable with law `μ` supported in a Loewner interval, the Wasserstein
equation reads `∫ Ψ_A(X) dμ(A) = 0` with `Ψ_A(X) = 1 - A # X⁻¹`.  Every estimate of the finite
theory is *pointwise in `A`*, so it transfers through the integral: applying the global strong
monotonicity to the one-point family `{A}` with weight `1` and integrating gives

`0 = ⟨∫Ψ_A(X)dμ - ∫Ψ_A(Y)dμ, X - Y⟩ ≥ (κ - C‖X-Y‖/N) ‖X-Y‖²_HS`   for every `N ≥ 1`,

which forces `X = Y`.  This is the uniqueness half of Theorem 5.1 (`wass_P2`).
-/

open scoped NNReal Ring BigOperators InnerProductSpace
open MeasureTheory ContinuousLinearMap

attribute [local instance] InnerProductSpace.complexToReal

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]

/-- The pointwise Wasserstein field of a single positive operator, as the one-point case of the
finite theory. -/
lemma wassField_unit (B X : E →L[ℂ] E) (hX : IsStrictlyPositive X) :
    wassField (Finset.univ : Finset Unit) (fun _ => (1 : ℝ)) (fun _ => B) X
      = (1 : E →L[ℂ] E) - gm B X⁻¹ʳ := by
  unfold wassField
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul, one_smul,
    gmInvMap_eq_gm hX]

/-- **Pointwise strong monotonicity of the Wasserstein field.** -/
theorem re_hsInner_single_sub_lower {B X Y : E →L[ℂ] E} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hB : IsStrictlyPositive B)
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hBα : α • (1 : E →L[ℂ] E) ≤ B) (hBβ : B ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y)) {N : ℕ} (hN : 0 < N) :
    (α * α / (2 * (β * (β * β))) - secondOrderConst α β * (‖X - Y‖ / (N : ℝ)))
        * hsNormSq (X - Y)
      ≤ RCLike.re (hsInner (((1 : E →L[ℂ] E) - gm B X⁻¹ʳ) - ((1 : E →L[ℂ] E) - gm B Y⁻¹ʳ))
          (X - Y)) := by
  have h := re_hsInner_wassField_sub_lower_global (s := (Finset.univ : Finset Unit))
    (w := fun _ => (1 : ℝ)) (Av := fun _ => B) hα hβ (fun _ _ => zero_le_one)
    (by simp) (fun _ _ => hB) (fun _ _ => hBα) (fun _ _ => hBβ)
    hXα hXβ hYα hYβ hPHS hN
  rwa [wassField_unit B X hX, wassField_unit B Y hY] at h

/-- **Theorem 5.1 (Kim–Mer–Pálfia), uniqueness.**  A measure-weighted Wasserstein equation has at
most one solution in a Loewner interval. -/
theorem eq_of_integral_wassField_eq_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Av : Ω → E →L[ℂ] E} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hA : ∀ w, IsStrictlyPositive (Av w))
    (hAα : ∀ w, α • (1 : E →L[ℂ] E) ≤ Av w) (hAβ : ∀ w, Av w ≤ β • (1 : E →L[ℂ] E))
    {X Y : E →L[ℂ] E} (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y))
    {F G : Ω → SLSpace E} (hFint : Integrable F μ) (hGint : Integrable G μ)
    (hFop : ∀ w, (F w).op = (1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ)
    (hGop : ∀ w, (G w).op = (1 : E →L[ℂ] E) - gm (Av w) Y⁻¹ʳ)
    (hFzero : ∫ w, F w ∂μ = 0) (hGzero : ∫ w, G w ∂μ = 0) :
    X = Y := by
  classical
  -- the difference as an element of `S²(ℋ)`
  have hsa : IsSelfAdjoint (X - Y) := hX.isSelfAdjoint.sub hY.isSelfAdjoint
  obtain ⟨Z, hZ⟩ : ∃ Z : SLSpace E, Z.op = X - Y :=
    ⟨⟨⟨X - Y, hPHS⟩, hsa⟩, rfl⟩
  -- both integrals pair to zero with `Z`
  have hz : hsInner (0 : E →L[ℂ] E) Z.op = 0 := by
    show ∑' i, inner ℂ ((0 : E →L[ℂ] E) (hsBasis ℂ E i)) (Z.op (hsBasis ℂ E i)) = 0
    simp
  have hFpair : ∫ w, RCLike.re (hsInner ((F w).op) Z.op) ∂μ = 0 := by
    rw [← SLSpace.re_hsInner_integral hFint Z, hFzero, SLSpace.op_zero, hz]
    simp
  have hGpair : ∫ w, RCLike.re (hsInner ((G w).op) Z.op) ∂μ = 0 := by
    rw [← SLSpace.re_hsInner_integral hGint Z, hGzero, SLSpace.op_zero, hz]
    simp
  -- integrability of the pairings
  have hIF : Integrable (fun w => RCLike.re (hsInner ((F w).op) Z.op)) μ := by
    have h := (innerSL ℝ Z).integrable_comp hFint
    refine h.congr (Filter.Eventually.of_forall fun w => ?_)
    show (inner ℝ Z (F w) : ℝ) = _
    rw [real_inner_comm]
    rfl
  have hIG : Integrable (fun w => RCLike.re (hsInner ((G w).op) Z.op)) μ := by
    have h := (innerSL ℝ Z).integrable_comp hGint
    refine h.congr (Filter.Eventually.of_forall fun w => ?_)
    show (inner ℝ Z (G w) : ℝ) = _
    rw [real_inner_comm]
    rfl
  -- the integrated strong monotonicity
  have hint : ∀ N : ℕ, 0 < N →
      (α * α / (2 * (β * (β * β))) - secondOrderConst α β * (‖X - Y‖ / (N : ℝ)))
        * hsNormSq (X - Y) ≤ 0 := by
    intro N hN
    have hptw : ∀ w, (α * α / (2 * (β * (β * β)))
          - secondOrderConst α β * (‖X - Y‖ / (N : ℝ))) * hsNormSq (X - Y)
        ≤ RCLike.re (hsInner ((F w).op) Z.op) - RCLike.re (hsInner ((G w).op) Z.op) := by
      intro w
      have h := re_hsInner_single_sub_lower hα hβ (hA w) hX hY (hAα w) (hAβ w)
        hXα hXβ hYα hYβ hPHS hN
      have hFHS : IsHilbertSchmidt ((F w).op) := (F w).isHS
      have hGHS : IsHilbertSchmidt ((G w).op) := (G w).isHS
      rw [← hFop w, ← hGop w, hsInner_sub_left hFHS hGHS hPHS, map_sub] at h
      rw [hZ]
      exact h
    have hmono := integral_mono (integrable_const _) (hIF.sub hIG) hptw
    simp only [Pi.sub_apply] at hmono
    rw [integral_const, integral_sub hIF hIG, hFpair, hGpair] at hmono
    simpa using hmono
  -- conclude
  have hnn : (0 : ℝ) ≤ hsNormSq (X - Y) := hsNormSq_nonneg _
  have hκ : (0 : ℝ) < α * α / (2 * (β * (β * β))) := by positivity
  have hzero : hsNormSq (X - Y) = 0 := by
    by_contra hcon
    have hpos : (0 : ℝ) < hsNormSq (X - Y) := lt_of_le_of_ne hnn (Ne.symm hcon)
    obtain ⟨N, hNge⟩ := exists_nat_ge
      (secondOrderConst α β * ‖X - Y‖ / (α * α / (2 * (β * (β * β)))) + 1)
    have hC0 : (0 : ℝ) ≤ secondOrderConst α β * ‖X - Y‖ := by
      have := (secondOrderConst_pos hα hβ).le
      positivity
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      have hq : (0 : ℝ) ≤ secondOrderConst α β * ‖X - Y‖
          / (α * α / (2 * (β * (β * β)))) := by positivity
      linarith
    have hNpos : (0 : ℕ) < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; norm_num at hN1
      · exact h
    have hNR : (0 : ℝ) < (N : ℝ) := by linarith
    have hdefect : secondOrderConst α β * (‖X - Y‖ / (N : ℝ))
        < α * α / (2 * (β * (β * β))) := by
      rw [mul_div_assoc', div_lt_iff₀ hNR]
      have h2 : secondOrderConst α β * ‖X - Y‖ / (α * α / (2 * (β * (β * β))))
          ≤ (N : ℝ) - 1 := by linarith
      rw [div_le_iff₀ hκ] at h2
      nlinarith [hκ]
    have := hint N hNpos
    nlinarith [this, hdefect, hpos]
  have := (hsNormSq_eq_zero_iff hPHS).mp hzero
  exact sub_eq_zero.mp this

/-! ### The measure-weighted field and its Loewner bounds -/

/-- The **Wasserstein field of a probability measure**, `Φ_μ(X) = ∫ (1 - A # X⁻¹) dμ(A)`. -/
noncomputable def wassFieldMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Av : Ω → E →L[ℂ] E) (X : E →L[ℂ] E) : E →L[ℂ] E :=
  ∫ w, ((1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ) ∂μ

/-- Two-sided Loewner bounds for `-Φ_μ` on a Loewner interval. -/
theorem neg_wassFieldMeasure_Icc {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Av : Ω → E →L[ℂ] E} {X : E →L[ℂ] E} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hX : IsStrictlyPositive X)
    (hA : ∀ w, IsStrictlyPositive (Av w))
    (hAα : ∀ w, α • (1 : E →L[ℂ] E) ≤ Av w) (hAβ : ∀ w, Av w ≤ β • (1 : E →L[ℂ] E))
    (hint : Integrable (fun w => (1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ) μ)
    {R : ℝ} (hR : 0 ≤ R)
    (hRlo : ∀ w, (Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1)
      - (gm (Av w) X⁻¹ʳ - 1) ≤ R • (1 : E →L[ℂ] E))
    (hRhi : ∀ w, (gm (Av w) X⁻¹ʳ - 1)
      - (Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1) ≤ R • (1 : E →L[ℂ] E)) :
    Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1 ≤ -wassFieldMeasure μ Av X
      ∧ -wassFieldMeasure μ Av X ≤ Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1 := by
  have hkey : ∀ w, Real.sqrt α • (X ^ (-(1/2) : ℝ)) ≤ gm (Av w) X⁻¹ʳ ∧
      gm (Av w) X⁻¹ʳ ≤ Real.sqrt β • (X ^ (-(1/2) : ℝ)) := by
    intro w
    refine ⟨?_, ?_⟩
    · rw [← gm_smul_one_ringInverse hα hX]
      exact gm_mono_left (IsStrictlyPositive.smul hα isStrictlyPositive_one) (hA w)
        hX.ringInverse (hAα w)
    · rw [← gm_smul_one_ringInverse hβ hX]
      exact gm_mono_left (hA w) (IsStrictlyPositive.smul hβ isStrictlyPositive_one)
        hX.ringInverse (hAβ w)
  have hneg : -wassFieldMeasure μ Av X = ∫ w, (gm (Av w) X⁻¹ʳ - 1) ∂μ := by
    unfold wassFieldMeasure
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    abel_nf
  have hnegint : Integrable (fun w => gm (Av w) X⁻¹ʳ - (1 : E →L[ℂ] E)) μ := by
    have hn := hint.neg
    refine hn.congr (Filter.Eventually.of_forall fun w => ?_)
    show -((1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ) = gm (Av w) X⁻¹ʳ - 1
    exact neg_sub _ _
  rw [hneg]
  constructor
  · have hc : ∫ _w : Ω, (Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1 : E →L[ℂ] E) ∂μ
        = Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1 := by
      rw [integral_const]
      simp
    rw [← hc]
    exact integral_mono_of_le (integrable_const _) hnegint hR
      (fun w => sub_le_sub_right (hkey w).1 1) hRhi
  · have hc : ∫ _w : Ω, (Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1 : E →L[ℂ] E) ∂μ
        = Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1 := by
      rw [integral_const]
      simp
    rw [← hc]
    exact integral_mono_of_le hnegint (integrable_const _) hR
      (fun w => sub_le_sub_right (hkey w).2 1) hRlo

/-- **Subtangentiality for the measure-weighted field.**  For every `X` in the Loewner interval
and every step `0 < λ ≤ 2α`, the explicit step `X + λ(-Φ_μ(X))` stays in the interval. -/
theorem sub_smul_wassFieldMeasure_mem_Icc {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Av : Ω → E →L[ℂ] E} {X : E →L[ℂ] E} {α β lam : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hlam : 0 < lam) (hlam2 : lam ≤ 2 * α)
    (hX : IsStrictlyPositive X)
    (hA : ∀ w, IsStrictlyPositive (Av w))
    (hAα : ∀ w, α • (1 : E →L[ℂ] E) ≤ Av w) (hAβ : ∀ w, Av w ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hint : Integrable (fun w => (1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ) μ)
    {R : ℝ} (hR : 0 ≤ R)
    (hRlo : ∀ w, (Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1)
      - (gm (Av w) X⁻¹ʳ - 1) ≤ R • (1 : E →L[ℂ] E))
    (hRhi : ∀ w, (gm (Av w) X⁻¹ʳ - 1)
      - (Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1) ≤ R • (1 : E →L[ℂ] E)) :
    α • (1 : E →L[ℂ] E) ≤ X - lam • wassFieldMeasure μ Av X
      ∧ X - lam • wassFieldMeasure μ Av X ≤ β • (1 : E →L[ℂ] E) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  obtain ⟨hlow, hupp⟩ := neg_wassFieldMeasure_Icc hα hβ hX hA hAα hAβ hint hR hRlo hRhi
  have hstep : X - lam • wassFieldMeasure μ Av X
      = X + lam • (-wassFieldMeasure μ Av X) := by
    rw [smul_neg]; abel_nf
  constructor
  · have h1 := smul_one_le_add_smul_rpow_neg_half hX hα hlam hlam2 hXα
    have h3 : X + lam • (Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1)
        ≤ X + lam • (-wassFieldMeasure μ Av X) :=
      add_le_add_right (smul_le_smul_of_nonneg_left hlow hlam.le) X
    rw [hstep]
    refine le_trans ?_ h3
    have h3' : X + lam • (Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1)
        = (X + (lam * Real.sqrt α) • (X ^ (-(1/2) : ℝ))) - lam • (1 : E →L[ℂ] E) := by
      rw [smul_sub, smul_smul]; abel_nf
    rw [h3']
    have h4 : (α : ℝ) • (1 : E →L[ℂ] E)
        = (α + lam) • (1 : E →L[ℂ] E) - lam • (1 : E →L[ℂ] E) := by
      rw [← sub_smul]; congr 1; ring
    rw [h4]
    exact sub_le_sub_right h1 _
  · have h1 := add_smul_rpow_neg_half_le_smul_one hX hα hαβ hlam hlam2 hXα hXβ
    have h3 : X + lam • (-wassFieldMeasure μ Av X)
        ≤ X + lam • (Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1) :=
      add_le_add_right (smul_le_smul_of_nonneg_left hupp hlam.le) X
    rw [hstep]
    refine le_trans h3 ?_
    have h3' : X + lam • (Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1)
        = (X + (lam * Real.sqrt β) • (X ^ (-(1/2) : ℝ))) - lam • (1 : E →L[ℂ] E) := by
      rw [smul_sub, smul_smul]; abel_nf
    rw [h3']
    have h4 : (β : ℝ) • (1 : E →L[ℂ] E)
        = (β + lam) • (1 : E →L[ℂ] E) - lam • (1 : E →L[ℂ] E) := by
      rw [← sub_smul]; congr 1; ring
    rw [h4]
    exact sub_le_sub_right h1 _

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
