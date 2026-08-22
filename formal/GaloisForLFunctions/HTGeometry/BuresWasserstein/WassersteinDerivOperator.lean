import GaloisForLFunctions.HTGeometry.SelfAdjointHilbertSchmidtSpace
import GaloisForLFunctions.HTGeometry.CoerciveOperatorInvertible
import GaloisForLFunctions.HTGeometry.LyapunovInverseBounds
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinFieldCoercivity
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinFieldContraction

/-!
# The derivative of the Wasserstein field as an operator on `S²(ℋ)`

The derivative of the Wasserstein vector field restricts to a bounded operator on the real
Hilbert space of self-adjoint Hilbert–Schmidt operators, and Lemma 3.11 makes it coercive, hence
an isomorphism.  This is the statement "`D₂φ(t, X)` is an invertible linear operator on
`S²(ℋ)`" of Kim–Mer–Pálfia (arXiv:2607.29142).
-/

open scoped NNReal Ring BigOperators
open ContinuousLinearMap

attribute [local instance] InnerProductSpace.complexToReal

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]
variable {ι : Type*}

/-- The value of the derivative of the Wasserstein vector field. -/
noncomputable def wassDerivFun (s : Finset ι) (w : ι → ℝ) (Av : ι → E →L[ℂ] E)
    (X : E →L[ℂ] E) (u : ι → ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))ˣ) (Y : E →L[ℂ] E) :
    E →L[ℂ] E :=
  ∑ i ∈ s, w i • conjMap ((Av i) ^ (1/2 : ℝ))
    ((↑(u i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ)))

variable {s : Finset ι} {w : ι → ℝ} {Av : ι → E →L[ℂ] E} {X : E →L[ℂ] E}
variable {u : ι → ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))ˣ}

/-- The derivative preserves the Hilbert–Schmidt class. -/
lemma isHilbertSchmidt_wassDerivFun
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (hX : IsStrictlyPositive X)
    {Y : E →L[ℂ] E} (hY : IsHilbertSchmidt Y) (hYsa : IsSelfAdjoint Y)
    (hu : ∀ i ∈ s, (↑(u i) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    IsHilbertSchmidt (wassDerivFun s w Av X u Y) := by
  refine IsHilbertSchmidt.sum s fun i hi => ?_
  exact IsHilbertSchmidt.real_smul
    (isHilbertSchmidt_gmInvDeriv (hA i hi) hX hY hYsa (hu i hi)) _

/-- The derivative preserves self-adjointness. -/
lemma isSelfAdjoint_wassDerivFun
    (_hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (hX : IsStrictlyPositive X)
    {Y : E →L[ℂ] E} (hYsa : IsSelfAdjoint Y)
    (hu : ∀ i ∈ s, (↑(u i) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    IsSelfAdjoint (wassDerivFun s w Av X u Y) := by
  unfold wassDerivFun
  show star _ = _
  rw [star_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hPsa : IsSelfAdjoint ((Av i) ^ (1/2 : ℝ) : E →L[ℂ] E) := isSelfAdjoint_rpow _ _
  have hNsa : IsSelfAdjoint ((Av i) ^ (-(1/2) : ℝ) : E →L[ℂ] E) := isSelfAdjoint_rpow _ _
  have hqsa : IsSelfAdjoint (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ)) :=
    isSelfAdjoint_conjMap hNsa (hYsa.conjugate_self hX.ringInverse.isSelfAdjoint)
  have hysa := isSelfAdjoint_twisted_unit_inv (hu i hi) hqsa
  exact (IsSelfAdjoint.smul (star_trivial (w i)) (isSelfAdjoint_conjMap hPsa hysa)).star_eq

/-- The derivative is additive. -/
lemma wassDerivFun_add (Y Z : E →L[ℂ] E) :
    wassDerivFun s w Av X u (Y + Z)
      = wassDerivFun s w Av X u Y + wassDerivFun s w Av X u Z := by
  unfold wassDerivFun
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmul : (X⁻¹ʳ : E →L[ℂ] E) * (Y + Z) * X⁻¹ʳ
      = X⁻¹ʳ * Y * X⁻¹ʳ + X⁻¹ʳ * Z * X⁻¹ʳ := by noncomm_ring
  rw [hmul, map_add, map_add, map_add, smul_add]

/-- The derivative is real-homogeneous. -/
lemma wassDerivFun_smul (c : ℝ) (Y : E →L[ℂ] E) :
    wassDerivFun s w Av X u ((c : ℂ) • Y) = (c : ℂ) • wassDerivFun s w Av X u Y := by
  unfold wassDerivFun
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmul : (X⁻¹ʳ : E →L[ℂ] E) * ((c : ℂ) • Y) * X⁻¹ʳ
      = (c : ℝ) • (X⁻¹ʳ * Y * X⁻¹ʳ) := by
    rw [mul_smul_comm, smul_mul_assoc, Complex.coe_smul]
  rw [hmul, map_smul, map_smul, map_smul, smul_comm, Complex.coe_smul]

/-! ### The Hilbert–Schmidt bound -/

omit [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)] in
lemma hsNorm_conjMap_le {b Z : E →L[ℂ] E} (hZ : IsHilbertSchmidt Z) :
    hsNorm (conjMap b Z) ≤ ‖b‖ * ‖b‖ * hsNorm Z := by
  rw [conjMap_apply]
  exact hsNorm_sandwich_le hZ

/-- **Hilbert–Schmidt bound for one term of the derivative.** -/
lemma hsNorm_deriv_term_le {a Y : E →L[ℂ] E} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (ha : IsStrictlyPositive a) (hX : IsStrictlyPositive X)
    (haα : α • (1 : E →L[ℂ] E) ≤ a) (haβ : a ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hY : IsHilbertSchmidt Y) (hYsa : IsSelfAdjoint Y)
    {v : ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))ˣ}
    (hv : (↑v : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    hsNorm (conjMap (a ^ (1/2 : ℝ)) ((↑v⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
        (conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ))))
      ≤ (β * (β / 2) * (α⁻¹ * (α⁻¹ * α⁻¹))) * hsNorm Y := by
  have hαinv : (0 : ℝ) < α⁻¹ := inv_pos.mpr hα
  have hXinvn : ‖(X⁻¹ʳ : E →L[ℂ] E)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hX hα hXα
  have hP2 : ‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖ ≤ β :=
    norm_rpow_half_sq_le ha.nonneg hβ.le haβ
  have hN2 : ‖(a ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖ ≤ α⁻¹ :=
    norm_rpow_neg_half_sq_le ha hα haα
  -- the inner sandwich
  have hXYX : IsHilbertSchmidt ((X⁻¹ʳ : E →L[ℂ] E) * Y * X⁻¹ʳ) := (hY.comp_left _).comp_right _
  have hb1 : hsNorm ((X⁻¹ʳ : E →L[ℂ] E) * Y * X⁻¹ʳ) ≤ (α⁻¹ * α⁻¹) * hsNorm Y := by
    have h : hsNorm ((X⁻¹ʳ : E →L[ℂ] E) * (Y * X⁻¹ʳ))
        ≤ ‖(X⁻¹ʳ : E →L[ℂ] E)‖ * ‖(X⁻¹ʳ : E →L[ℂ] E)‖ * hsNorm Y := hsNorm_sandwich_le hY
    rw [← mul_assoc] at h
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hXinvn hXinvn (norm_nonneg _) hαinv.le) (hsNorm_nonneg _)
  have hqHS : IsHilbertSchmidt (conjMap (a ^ (-(1/2) : ℝ)) ((X⁻¹ʳ : E →L[ℂ] E) * Y * X⁻¹ʳ)) := by
    rw [conjMap_apply']
    exact (hXYX.comp_left _).comp_right _
  have hb2 : hsNorm (conjMap (a ^ (-(1/2) : ℝ)) ((X⁻¹ʳ : E →L[ℂ] E) * Y * X⁻¹ʳ))
      ≤ α⁻¹ * ((α⁻¹ * α⁻¹) * hsNorm Y) := by
    refine (hsNorm_conjMap_le hXYX).trans ?_
    exact mul_le_mul hN2 hb1 (hsNorm_nonneg _) hαinv.le
  -- the Lyapunov step
  have hyHS := isHilbertSchmidt_gmInvDerivSolution ha hX hY hYsa hv
  have hqsa : IsSelfAdjoint (conjMap (a ^ (-(1/2) : ℝ)) ((X⁻¹ʳ : E →L[ℂ] E) * Y * X⁻¹ʳ)) :=
    isSelfAdjoint_conjMap (isSelfAdjoint_rpow _ _)
      (hYsa.conjugate_self hX.ringInverse.isSelfAdjoint)
  have hlyap := lyapunov_twisted_unit_inv hv hqsa
  have hlb := smul_one_le_cfcSqrt_conjMap ha hX hβ haβ hXβ
  have hbnd := hsNorm_le_of_lyapunov ((CFC.sqrt_nonneg _).isSelfAdjoint) hyHS
    (inv_pos.mpr hβ) hlb hlyap
  have hy : hsNorm ((↑v⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      (conjMap (a ^ (-(1/2) : ℝ)) ((X⁻¹ʳ : E →L[ℂ] E) * Y * X⁻¹ʳ)))
      ≤ (β / 2) * (α⁻¹ * ((α⁻¹ * α⁻¹) * hsNorm Y)) := by
    have h2β : (0 : ℝ) < 2 * β⁻¹ := by positivity
    have hstep : (2 * β⁻¹) * hsNorm ((↑v⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
        (conjMap (a ^ (-(1/2) : ℝ)) ((X⁻¹ʳ : E →L[ℂ] E) * Y * X⁻¹ʳ)))
        ≤ α⁻¹ * ((α⁻¹ * α⁻¹) * hsNorm Y) := hbnd.trans hb2
    have hβne : β ≠ 0 := ne_of_gt hβ
    have hid : hsNorm ((↑v⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
        (conjMap (a ^ (-(1/2) : ℝ)) ((X⁻¹ʳ : E →L[ℂ] E) * Y * X⁻¹ʳ)))
        = (β / 2) * ((2 * β⁻¹) * hsNorm ((↑v⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
          (conjMap (a ^ (-(1/2) : ℝ)) ((X⁻¹ʳ : E →L[ℂ] E) * Y * X⁻¹ʳ)))) := by
      field_simp
    rw [hid]
    exact mul_le_mul_of_nonneg_left hstep (by positivity)
  refine (hsNorm_conjMap_le hyHS).trans ?_
  calc ‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖
        * hsNorm ((↑v⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
          (conjMap (a ^ (-(1/2) : ℝ)) ((X⁻¹ʳ : E →L[ℂ] E) * Y * X⁻¹ʳ)))
      ≤ β * ((β / 2) * (α⁻¹ * ((α⁻¹ * α⁻¹) * hsNorm Y))) :=
        mul_le_mul hP2 hy (hsNorm_nonneg _) hβ.le
    _ = (β * (β / 2) * (α⁻¹ * (α⁻¹ * α⁻¹))) * hsNorm Y := by ring

/-- **Hilbert–Schmidt bound for the derivative.** -/
lemma hsNorm_wassDerivFun_le {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (hX : IsStrictlyPositive X)
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    {Y : E →L[ℂ] E} (hY : IsHilbertSchmidt Y) (hYsa : IsSelfAdjoint Y)
    (hu : ∀ i ∈ s, (↑(u i) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    hsNorm (wassDerivFun s w Av X u Y)
      ≤ (β * (β / 2) * (α⁻¹ * (α⁻¹ * α⁻¹))) * hsNorm Y := by
  unfold wassDerivFun
  have hterm : ∀ i ∈ s, hsNorm (w i • conjMap ((Av i) ^ (1/2 : ℝ))
      ((↑(u i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
        (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ))))
      ≤ w i * ((β * (β / 2) * (α⁻¹ * (α⁻¹ * α⁻¹))) * hsNorm Y) := by
    intro i hi
    rw [hsNorm_real_smul, abs_of_nonneg (hw i hi)]
    exact mul_le_mul_of_nonneg_left
      (hsNorm_deriv_term_le hα hβ (hA i hi) hX (hAα i hi) (hAβ i hi) hXα hXβ hY hYsa (hu i hi))
      (hw i hi)
  have hHS : ∀ i ∈ s, IsHilbertSchmidt (w i • conjMap ((Av i) ^ (1/2 : ℝ))
      ((↑(u i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
        (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ)))) := fun i hi =>
    IsHilbertSchmidt.real_smul
      (isHilbertSchmidt_gmInvDeriv (hA i hi) hX hY hYsa (hu i hi)) _
  refine (hsNorm_sum_le hHS).trans ?_
  calc ∑ i ∈ s, hsNorm (w i • conjMap ((Av i) ^ (1/2 : ℝ))
        ((↑(u i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
          (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ))))
      ≤ ∑ i ∈ s, w i * ((β * (β / 2) * (α⁻¹ * (α⁻¹ * α⁻¹))) * hsNorm Y) :=
        Finset.sum_le_sum hterm
    _ = (β * (β / 2) * (α⁻¹ * (α⁻¹ * α⁻¹))) * hsNorm Y := by
        rw [← Finset.sum_mul, hwsum, one_mul]

/-! ### The bounded operator on `S²(ℋ)` and its invertibility -/

variable {α β : ℝ}

/-- The derivative of the Wasserstein vector field as a map of self-adjoint Hilbert–Schmidt
operators. -/
noncomputable def wassDerivSL (w : ι → ℝ)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (hX : IsStrictlyPositive X)
    (hu : ∀ i ∈ s, (↑(u i) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj))
    (Y : SLSpace E) : SLSpace E :=
  ⟨HSpace.mk (wassDerivFun s w Av X u (SLSpace.op Y))
      (isHilbertSchmidt_wassDerivFun hA hX Y.isHS Y.isSelfAdjoint hu),
    isSelfAdjoint_wassDerivFun hA hX Y.isSelfAdjoint hu⟩

lemma op_wassDerivSL (w : ι → ℝ)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (hX : IsStrictlyPositive X)
    (hu : ∀ i ∈ s, (↑(u i) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj))
    (Y : SLSpace E) :
    SLSpace.op (wassDerivSL w hA hX hu Y) = wassDerivFun s w Av X u (SLSpace.op Y) := rfl

/-- The derivative as a real-linear map on `S²(ℋ)`. -/
noncomputable def wassDerivLinearMap (w : ι → ℝ)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (hX : IsStrictlyPositive X)
    (hu : ∀ i ∈ s, (↑(u i) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    SLSpace E →ₗ[ℝ] SLSpace E where
  toFun := wassDerivSL w hA hX hu
  map_add' Y Z := by
    refine SLSpace.ext ?_
    rw [SLSpace.op_add, op_wassDerivSL, op_wassDerivSL, op_wassDerivSL, SLSpace.op_add,
      wassDerivFun_add]
  map_smul' c Y := by
    refine SLSpace.ext ?_
    rw [RingHom.id_apply, SLSpace.op_smul, op_wassDerivSL, op_wassDerivSL, SLSpace.op_smul,
      wassDerivFun_smul]

/-- **The derivative of the Wasserstein vector field is a bounded operator on `S²(ℋ)`.** -/
noncomputable def wassDerivCLM (w : ι → ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (hX : IsStrictlyPositive X)
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hu : ∀ i ∈ s, (↑(u i) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    SLSpace E →L[ℝ] SLSpace E :=
  LinearMap.mkContinuous (wassDerivLinearMap w hA hX hu)
    (β * (β / 2) * (α⁻¹ * (α⁻¹ * α⁻¹)))
    (fun Y => by
      show hsNorm (SLSpace.op (wassDerivSL w hA hX hu Y)) ≤ _
      rw [op_wassDerivSL]
      exact hsNorm_wassDerivFun_le hα hβ hw hwsum hA hX hAα hAβ hXα hXβ Y.isHS
        Y.isSelfAdjoint hu)

/-- **`D₂φ(X)` is an isomorphism of `S²(ℋ)`** (Kim–Mer–Pálfia, the invertibility step of
Theorems 3.12 and 3.16).  Coercivity is Lemma 3.11 and invertibility follows by Lax–Milgram. -/
theorem bijective_wassDerivCLM (w : ι → ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (hX : IsStrictlyPositive X)
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hu : ∀ i ∈ s, (↑(u i) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    Function.Bijective (wassDerivCLM w hα hβ hw hwsum hA hX hAα hAβ hXα hXβ hu) := by
  have hκ : (0 : ℝ) < α * α / (2 * (β * (β * β))) := by positivity
  refine bijective_of_coercive hκ fun Y => ?_
  have hlow := re_hsInner_wassFieldDeriv_lower (Av := Av) (w := w) hα hβ hw hwsum hA hAα hAβ
    hX hXβ Y.isHS Y.isSelfAdjoint hu
  have hnorm : ‖Y‖ * ‖Y‖ = hsNormSq (SLSpace.op Y) := by
    rw [SLSpace.norm_def, ← sq, sq_hsNorm]
  have hval : (inner ℝ (wassDerivCLM w hα hβ hw hwsum hA hX hAα hAβ hXα hXβ hu Y) Y : ℝ)
      = RCLike.re (hsInner (wassDerivFun s w Av X u (SLSpace.op Y)) (SLSpace.op Y)) := rfl
  rw [hval, mul_assoc, hnorm]
  exact hlow

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
