import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinMeasure
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinExistenceStep

/-!
# The Wasserstein vector field of a probability measure

For a probability measure `μ` on a Loewner interval `[α·1, β·1]` the field

`Φ_μ(X) = ∫ (1 - A # X⁻¹) dμ(A)`

is realised as a Bochner integral in the real Hilbert space `S²(ℋ)` of self-adjoint
Hilbert–Schmidt operators.  Every estimate of the finite theory is pointwise in `A`, so the
Lipschitz bound and the strong monotonicity of the field survive integration verbatim; the
Loewner envelope `√α·X^{-1/2} - 1 ≤ -Φ_μ(X) ≤ √β·X^{-1/2} - 1` follows from monotonicity of the
Bochner integral, its uniform Loewner majorant being `(√β - √α)√(α⁻¹)·1`.
-/

open scoped NNReal Ring BigOperators InnerProductSpace
open Filter Topology MeasureTheory ContinuousLinearMap

attribute [local instance] InnerProductSpace.complexToReal

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]

/-! ### Pointwise specialisations of the finite theory -/

/-- The Wasserstein field of a single positive operator is self-adjoint. -/
lemma isSelfAdjoint_one_sub_gm (B X : E →L[ℂ] E) :
    IsSelfAdjoint ((1 : E →L[ℂ] E) - gm B X⁻¹ʳ) :=
  (IsSelfAdjoint.one (E →L[ℂ] E)).sub (gm_nonneg _ _).isSelfAdjoint

/-- The Loewner envelope of `A # X⁻¹` on a Loewner interval. -/
lemma gm_ringInverse_Icc {B X : E →L[ℂ] E} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hX : IsStrictlyPositive X) (hB : IsStrictlyPositive B)
    (hBα : α • (1 : E →L[ℂ] E) ≤ B) (hBβ : B ≤ β • (1 : E →L[ℂ] E)) :
    Real.sqrt α • (X ^ (-(1/2) : ℝ)) ≤ gm B X⁻¹ʳ
      ∧ gm B X⁻¹ʳ ≤ Real.sqrt β • (X ^ (-(1/2) : ℝ)) := by
  refine ⟨?_, ?_⟩
  · rw [← gm_smul_one_ringInverse hα hX]
    exact gm_mono_left (IsStrictlyPositive.smul hα isStrictlyPositive_one) hB
      hX.ringInverse hBα
  · rw [← gm_smul_one_ringInverse hβ hX]
    exact gm_mono_left hB (IsStrictlyPositive.smul hβ isStrictlyPositive_one)
      hX.ringInverse hBβ

/-- **The pointwise Wasserstein field is Lipschitz on a Loewner interval.** -/
theorem hsNorm_single_sub_le {B X Y : E →L[ℂ] E} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hB : IsStrictlyPositive B) (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hBα : α • (1 : E →L[ℂ] E) ≤ B) (hBβ : B ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y)) :
    hsNorm (((1 : E →L[ℂ] E) - gm B X⁻¹ʳ) - ((1 : E →L[ℂ] E) - gm B Y⁻¹ʳ))
      ≤ wassLipConst α β * hsNorm (X - Y) := by
  have h := hsNorm_wassField_sub_le (s := (Finset.univ : Finset Unit)) (w := fun _ => (1 : ℝ))
    (Av := fun _ => B) hα hβ (fun _ _ => zero_le_one) (by simp) (fun _ _ => hB) hX hY
    (fun _ _ => hBα) (fun _ _ => hBβ) hXα hXβ hYα hYβ hPHS
  rwa [wassField_unit B X hX, wassField_unit B Y hY] at h

/-! ### The field as an `S²(ℋ)`-valued map -/

open Classical in
/-- The pointwise Wasserstein field as an element of `S²(ℋ)`. -/
noncomputable def wassSL (B X : E →L[ℂ] E) : SLSpace E :=
  if h : IsHilbertSchmidt ((1 : E →L[ℂ] E) - gm B X⁻¹ʳ) then
    SLSpace.mk _ h (isSelfAdjoint_one_sub_gm B X)
  else 0

/-- On a Loewner interval the `S²(ℋ)`-valued field carries the Wasserstein field. -/
lemma wassSL_op {B X : E →L[ℂ] E} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hB : IsStrictlyPositive B) (hX : IsStrictlyPositive X)
    (hBα : α • (1 : E →L[ℂ] E) ≤ B) (hBβ : B ≤ β • (1 : E →L[ℂ] E))
    (hXβ : X ≤ β • (1 : E →L[ℂ] E)) (hHS : IsHilbertSchmidt (X - B)) :
    (wassSL B X).op = (1 : E →L[ℂ] E) - gm B X⁻¹ʳ := by
  have h1 : IsHilbertSchmidt ((1 : E →L[ℂ] E) - gm B X⁻¹ʳ) :=
    isHilbertSchmidt_one_sub_gm hB hX hα hβ hBα hBβ hXβ hHS
  have h2 : wassSL B X = SLSpace.mk _ h1 (isSelfAdjoint_one_sub_gm B X) := dif_pos h1
  rw [h2, SLSpace.op_mk]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The operator-valued integrand is integrable whenever the `S²(ℋ)`-valued one is. -/
lemma integrable_one_sub_gm {Av : Ω → E →L[ℂ] E} {X : E →L[ℂ] E}
    (hF : Integrable (fun w => wassSL (Av w) X) μ)
    (hop : ∀ w, (wassSL (Av w) X).op = (1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ) :
    Integrable (fun w => (1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ) μ := by
  have h := (SLSpace.opCLM E).integrable_comp hF
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  show (wassSL (Av w) X).op = _
  exact hop w

/-- The measure-weighted field is the image of the `S²(ℋ)`-valued Bochner integral. -/
theorem wassFieldMeasure_eq_op_integral {Av : Ω → E →L[ℂ] E} {X : E →L[ℂ] E}
    (hF : Integrable (fun w => wassSL (Av w) X) μ)
    (hop : ∀ w, (wassSL (Av w) X).op = (1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ) :
    wassFieldMeasure μ Av X = (∫ w, wassSL (Av w) X ∂μ).op := by
  rw [SLSpace.op_integral hF]
  unfold wassFieldMeasure
  exact integral_congr_ae (Filter.Eventually.of_forall fun w => (hop w).symm)

/-- The measure-weighted field is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_wassFieldMeasure {Av : Ω → E →L[ℂ] E} {X : E →L[ℂ] E}
    (hF : Integrable (fun w => wassSL (Av w) X) μ)
    (hop : ∀ w, (wassSL (Av w) X).op = (1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ) :
    IsHilbertSchmidt (wassFieldMeasure μ Av X) := by
  rw [wassFieldMeasure_eq_op_integral hF hop]
  exact SLSpace.isHilbertSchmidt_integral

/-- The measure-weighted field is self-adjoint. -/
theorem isSelfAdjoint_wassFieldMeasure {Av : Ω → E →L[ℂ] E} {X : E →L[ℂ] E}
    (hF : Integrable (fun w => wassSL (Av w) X) μ)
    (hop : ∀ w, (wassSL (Av w) X).op = (1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ) :
    IsSelfAdjoint (wassFieldMeasure μ Av X) := by
  rw [wassFieldMeasure_eq_op_integral hF hop]
  exact SLSpace.isSelfAdjoint_integral'

/-- The difference of two values of the field is one Bochner integral. -/
lemma wassFieldMeasure_sub_eq {Av : Ω → E →L[ℂ] E} {X Y : E →L[ℂ] E}
    (hFX : Integrable (fun w => wassSL (Av w) X) μ)
    (hFY : Integrable (fun w => wassSL (Av w) Y) μ)
    (hopX : ∀ w, (wassSL (Av w) X).op = (1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ)
    (hopY : ∀ w, (wassSL (Av w) Y).op = (1 : E →L[ℂ] E) - gm (Av w) Y⁻¹ʳ) :
    wassFieldMeasure μ Av X - wassFieldMeasure μ Av Y
      = (∫ w, (wassSL (Av w) X - wassSL (Av w) Y) ∂μ).op := by
  rw [integral_sub hFX hFY, SLSpace.op_sub,
    ← wassFieldMeasure_eq_op_integral hFX hopX, ← wassFieldMeasure_eq_op_integral hFY hopY]

/-! ### The Loewner envelope, with its majorant supplied -/

/-- **Lemma 4.7 for a probability measure.**  Two-sided Loewner bounds for `-Φ_μ`. -/
theorem neg_wassFieldMeasure_Icc' [IsProbabilityMeasure μ] {Av : Ω → E →L[ℂ] E}
    {X : E →L[ℂ] E} {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hX : IsStrictlyPositive X)
    (hA : ∀ w, IsStrictlyPositive (Av w))
    (hAα : ∀ w, α • (1 : E →L[ℂ] E) ≤ Av w) (hAβ : ∀ w, Av w ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X)
    (hint : Integrable (fun w => (1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ) μ) :
    Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1 ≤ -wassFieldMeasure μ Av X
      ∧ -wassFieldMeasure μ Av X ≤ Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1 := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hsq : Real.sqrt α ≤ Real.sqrt β := Real.sqrt_le_sqrt hαβ
  have hgap0 : (0 : ℝ) ≤ Real.sqrt β - Real.sqrt α := by linarith
  have hRnn : (0 : ℝ) ≤ (Real.sqrt β - Real.sqrt α) * Real.sqrt α⁻¹ :=
    mul_nonneg hgap0 (Real.sqrt_nonneg _)
  have hYb : (X ^ (-(1/2) : ℝ) : E →L[ℂ] E) ≤ (Real.sqrt α⁻¹) • (1 : E →L[ℂ] E) :=
    rpow_neg_half_le_smul_one hX hα hXα
  have hgap : (Real.sqrt β - Real.sqrt α) • (X ^ (-(1/2) : ℝ))
      ≤ ((Real.sqrt β - Real.sqrt α) * Real.sqrt α⁻¹) • (1 : E →L[ℂ] E) := by
    have h := smul_le_smul_of_nonneg_left hYb hgap0
    rwa [smul_smul] at h
  have hsplit : (Real.sqrt β - Real.sqrt α) • (X ^ (-(1/2) : ℝ))
      = Real.sqrt β • (X ^ (-(1/2) : ℝ)) - Real.sqrt α • (X ^ (-(1/2) : ℝ)) := sub_smul _ _ _
  have hRlo : ∀ w, (Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1) - (gm (Av w) X⁻¹ʳ - 1)
      ≤ ((Real.sqrt β - Real.sqrt α) * Real.sqrt α⁻¹) • (1 : E →L[ℂ] E) := by
    intro w
    have hid : (Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1) - (gm (Av w) X⁻¹ʳ - 1)
        = Real.sqrt β • (X ^ (-(1/2) : ℝ)) - gm (Av w) X⁻¹ʳ := by abel_nf
    rw [hid]
    refine le_trans ?_ hgap
    rw [hsplit]
    exact sub_le_sub_left (gm_ringInverse_Icc hα hβ hX (hA w) (hAα w) (hAβ w)).1 _
  have hRhi : ∀ w, (gm (Av w) X⁻¹ʳ - 1) - (Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1)
      ≤ ((Real.sqrt β - Real.sqrt α) * Real.sqrt α⁻¹) • (1 : E →L[ℂ] E) := by
    intro w
    have hid : (gm (Av w) X⁻¹ʳ - 1) - (Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1)
        = gm (Av w) X⁻¹ʳ - Real.sqrt α • (X ^ (-(1/2) : ℝ)) := by abel_nf
    rw [hid]
    refine le_trans ?_ hgap
    rw [hsplit]
    exact sub_le_sub_right (gm_ringInverse_Icc hα hβ hX (hA w) (hAα w) (hAβ w)).2 _
  exact neg_wassFieldMeasure_Icc hα hβ hX hA hAα hAβ hint hRnn hRlo hRhi

/-- **Subtangentiality of the Loewner interval for the measure-weighted field.** -/
theorem sub_smul_wassFieldMeasure_mem_Icc' [IsProbabilityMeasure μ] {Av : Ω → E →L[ℂ] E}
    {X : E →L[ℂ] E} {α β lam : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hlam : 0 < lam) (hlam2 : lam ≤ 2 * α)
    (hX : IsStrictlyPositive X)
    (hA : ∀ w, IsStrictlyPositive (Av w))
    (hAα : ∀ w, α • (1 : E →L[ℂ] E) ≤ Av w) (hAβ : ∀ w, Av w ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hint : Integrable (fun w => (1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ) μ) :
    α • (1 : E →L[ℂ] E) ≤ X - lam • wassFieldMeasure μ Av X
      ∧ X - lam • wassFieldMeasure μ Av X ≤ β • (1 : E →L[ℂ] E) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  obtain ⟨hlow, hupp⟩ := neg_wassFieldMeasure_Icc' hα hαβ hX hA hAα hAβ hXα hint
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

/-! ### Lipschitz bound and strong monotonicity -/

/-- **The measure-weighted Wasserstein field is Lipschitz on a Loewner interval.** -/
theorem hsNorm_wassFieldMeasure_sub_le [IsProbabilityMeasure μ] {Av : Ω → E →L[ℂ] E}
    {X Y : E →L[ℂ] E} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hA : ∀ w, IsStrictlyPositive (Av w))
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hAα : ∀ w, α • (1 : E →L[ℂ] E) ≤ Av w) (hAβ : ∀ w, Av w ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y))
    (hFX : Integrable (fun w => wassSL (Av w) X) μ)
    (hFY : Integrable (fun w => wassSL (Av w) Y) μ)
    (hopX : ∀ w, (wassSL (Av w) X).op = (1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ)
    (hopY : ∀ w, (wassSL (Av w) Y).op = (1 : E →L[ℂ] E) - gm (Av w) Y⁻¹ʳ) :
    hsNorm (wassFieldMeasure μ Av X - wassFieldMeasure μ Av Y)
      ≤ wassLipConst α β * hsNorm (X - Y) := by
  rw [wassFieldMeasure_sub_eq hFX hFY hopX hopY]
  refine SLSpace.hsNorm_integral_le.trans ?_
  have hbd : ∀ w, hsNorm ((wassSL (Av w) X - wassSL (Av w) Y).op)
      ≤ wassLipConst α β * hsNorm (X - Y) := by
    intro w
    rw [SLSpace.op_sub, hopX w, hopY w]
    exact hsNorm_single_sub_le hα hβ (hA w) hX hY (hAα w) (hAβ w) hXα hXβ hYα hYβ hPHS
  have hI : Integrable (fun w => hsNorm ((wassSL (Av w) X - wassSL (Av w) Y).op)) μ :=
    (hFX.sub hFY).norm
  have hmono := integral_mono hI (integrable_const _) hbd
  rw [integral_const] at hmono
  simpa using hmono

/-- **Global strong monotonicity of the measure-weighted Wasserstein field.** -/
theorem re_hsInner_wassFieldMeasure_sub_lower [IsProbabilityMeasure μ] {Av : Ω → E →L[ℂ] E}
    {X Y : E →L[ℂ] E} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hA : ∀ w, IsStrictlyPositive (Av w))
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hAα : ∀ w, α • (1 : E →L[ℂ] E) ≤ Av w) (hAβ : ∀ w, Av w ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y))
    (hFX : Integrable (fun w => wassSL (Av w) X) μ)
    (hFY : Integrable (fun w => wassSL (Av w) Y) μ)
    (hopX : ∀ w, (wassSL (Av w) X).op = (1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ)
    (hopY : ∀ w, (wassSL (Av w) Y).op = (1 : E →L[ℂ] E) - gm (Av w) Y⁻¹ʳ)
    {N : ℕ} (hN : 0 < N) :
    (α * α / (2 * (β * (β * β))) - secondOrderConst α β * (‖X - Y‖ / (N : ℝ)))
        * hsNormSq (X - Y)
      ≤ RCLike.re (hsInner (wassFieldMeasure μ Av X - wassFieldMeasure μ Av Y) (X - Y)) := by
  classical
  have hsa : IsSelfAdjoint (X - Y) := hX.isSelfAdjoint.sub hY.isSelfAdjoint
  obtain ⟨Z, hZ⟩ : ∃ Z : SLSpace E, Z.op = X - Y := ⟨SLSpace.mk _ hPHS hsa, rfl⟩
  have hpair : RCLike.re (hsInner (wassFieldMeasure μ Av X - wassFieldMeasure μ Av Y) (X - Y))
      = ∫ w, RCLike.re (hsInner ((wassSL (Av w) X - wassSL (Av w) Y).op) (X - Y)) ∂μ := by
    have h := SLSpace.re_hsInner_integral (hFX.sub hFY) Z
    rw [hZ] at h
    rw [wassFieldMeasure_sub_eq hFX hFY hopX hopY]
    exact h
  rw [hpair]
  have hI : Integrable
      (fun w => RCLike.re (hsInner ((wassSL (Av w) X - wassSL (Av w) Y).op) (X - Y))) μ := by
    have h := (innerSL ℝ Z).integrable_comp (hFX.sub hFY)
    refine h.congr (Filter.Eventually.of_forall fun w => ?_)
    show (inner ℝ Z (wassSL (Av w) X - wassSL (Av w) Y) : ℝ) = _
    rw [real_inner_comm, ← hZ]
    rfl
  have hptw : ∀ w, (α * α / (2 * (β * (β * β)))
        - secondOrderConst α β * (‖X - Y‖ / (N : ℝ))) * hsNormSq (X - Y)
      ≤ RCLike.re (hsInner ((wassSL (Av w) X - wassSL (Av w) Y).op) (X - Y)) := by
    intro w
    rw [SLSpace.op_sub, hopX w, hopY w]
    exact re_hsInner_single_sub_lower hα hβ (hA w) hX hY (hAα w) (hAβ w)
      hXα hXβ hYα hYβ hPHS hN
  have hmono := integral_mono (integrable_const _) hI hptw
  rw [integral_const] at hmono
  simpa using hmono

/-- **The explicit gradient step of the measure-weighted field contracts.** -/
theorem hsNormSq_gradientStepMeasure_sub_le [IsProbabilityMeasure μ] {Av : Ω → E →L[ℂ] E}
    {X Y : E →L[ℂ] E} {α β t : ℝ} (hα : 0 < α) (hβ : 0 < β) (ht : 0 ≤ t)
    (hA : ∀ w, IsStrictlyPositive (Av w))
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hAα : ∀ w, α • (1 : E →L[ℂ] E) ≤ Av w) (hAβ : ∀ w, Av w ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y))
    (hFX : Integrable (fun w => wassSL (Av w) X) μ)
    (hFY : Integrable (fun w => wassSL (Av w) Y) μ)
    (hopX : ∀ w, (wassSL (Av w) X).op = (1 : E →L[ℂ] E) - gm (Av w) X⁻¹ʳ)
    (hopY : ∀ w, (wassSL (Av w) Y).op = (1 : E →L[ℂ] E) - gm (Av w) Y⁻¹ʳ)
    {N : ℕ} (hN : 0 < N) :
    hsNormSq ((X - t • wassFieldMeasure μ Av X) - (Y - t • wassFieldMeasure μ Av Y))
      ≤ (1 - 2 * t * (α * α / (2 * (β * (β * β)))
          - secondOrderConst α β * (‖X - Y‖ / (N : ℝ)))
          + t ^ 2 * (wassLipConst α β) ^ 2) * hsNormSq (X - Y) := by
  obtain ⟨D, hDdef⟩ : ∃ z : E →L[ℂ] E,
      z = wassFieldMeasure μ Av X - wassFieldMeasure μ Av Y := ⟨_, rfl⟩
  have hDHS : IsHilbertSchmidt D := by
    rw [hDdef, wassFieldMeasure_sub_eq hFX hFY hopX hopY]
    exact SLSpace.isHilbertSchmidt_integral
  have hZ : (X - t • wassFieldMeasure μ Av X) - (Y - t • wassFieldMeasure μ Av Y)
      = (X - Y) - t • D := by rw [hDdef, smul_sub]; abel_nf
  rw [hZ]
  have hsq : hsNormSq (t • D) = t ^ 2 * hsNormSq D := by
    have h1 : hsNormSq (t • D) = (hsNorm (t • D)) ^ 2 := (sq_hsNorm _).symm
    rw [h1, hsNorm_real_smul, mul_pow, sq_abs, sq_hsNorm]
  have hexp : hsNormSq ((X - Y) - t • D)
      = hsNormSq (X - Y) - 2 * (t * RCLike.re (hsInner D (X - Y))) + t ^ 2 * hsNormSq D := by
    rw [hsNormSq_sub hPHS (hDHS.real_smul t), hsq, hsInner_real_smul_right]
    congr 2
    have hconj : RCLike.re (hsInner (X - Y) D) = RCLike.re (hsInner D (X - Y)) := by
      rw [hsInner_conj_symm (X - Y) D, RCLike.conj_re]
    simp [hconj]
  rw [hexp]
  have hmono : (α * α / (2 * (β * (β * β)))
        - secondOrderConst α β * (‖X - Y‖ / (N : ℝ))) * hsNormSq (X - Y)
      ≤ RCLike.re (hsInner D (X - Y)) := by
    rw [hDdef]
    exact re_hsInner_wassFieldMeasure_sub_lower hα hβ hA hX hY hAα hAβ hXα hXβ hYα hYβ
      hPHS hFX hFY hopX hopY hN
  have hlip : hsNormSq D ≤ (wassLipConst α β) ^ 2 * hsNormSq (X - Y) := by
    have h := hsNorm_wassFieldMeasure_sub_le hα hβ hA hX hY hAα hAβ hXα hXβ hYα hYβ
      hPHS hFX hFY hopX hopY
    rw [hDdef]
    have h2 : (hsNorm (wassFieldMeasure μ Av X - wassFieldMeasure μ Av Y)) ^ 2
        ≤ (wassLipConst α β * hsNorm (X - Y)) ^ 2 :=
      pow_le_pow_left₀ (hsNorm_nonneg _) h 2
    rw [sq_hsNorm, mul_pow, sq_hsNorm] at h2
    exact h2
  nlinarith [hmono, hlip, ht, sq_nonneg t, hsNormSq_nonneg (X - Y)]

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
