import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinSecondOrder
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinFieldCoercivity

/-!
# Local strong monotonicity of the Wasserstein vector field

Coercivity of the derivative (Lemma 3.11) together with the derivative-free second-order estimate
gives strong monotonicity of `Φ` on a Loewner interval, up to a defect linear in `‖X - Y‖`:

`⟨Φ(X) - Φ(Y), X - Y⟩_HS ≥ (κ - C ‖X - Y‖) ‖X - Y‖²_HS`,

with `κ = α²/(2β³)` from Lemma 3.11 and `C = secondOrderConst α β`.  This is the inequality that
makes the explicit gradient step `X ↦ X - t Φ(X)` a contraction, and hence the engine of the
homotopy continuation.
-/

open scoped NNReal Ring BigOperators
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → E →L[ℂ] E}

/-- The increment of the Wasserstein field is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_wassField_sub {X Y : E →L[ℂ] E} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hXβ : X ≤ β • (1 : E →L[ℂ] E)) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y)) :
    IsHilbertSchmidt (wassField s w Av X - wassField s w Av Y) := by
  have hid : wassField s w Av X - wassField s w Av Y
      = ∑ i ∈ s, w i • (gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ) := by
    unfold wassField
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [gmInvMap_eq_gm hX, gmInvMap_eq_gm hY, ← smul_sub]
    congr 1
    abel
  rw [hid]
  refine IsHilbertSchmidt.sum s fun i hi => ?_
  have hγ : (0 : ℝ) < Real.sqrt (α * β⁻¹) := Real.sqrt_pos.mpr (by positivity)
  refine IsHilbertSchmidt.real_smul ?_ _
  refine isHilbertSchmidt_gm_sub (hA i hi) hY.ringInverse hX.ringInverse hγ hβ
    (hAβ i hi) ?_ ?_ (isHilbertSchmidt_ringInverse_sub hY hX hPHS)
  · exact smul_one_le_gm (hA i hi) hY.ringInverse hα (inv_pos.mpr hβ) (hAα i hi)
      (smul_one_le_ringInverse_of_le_smul_one hY hβ hYβ)
  · exact smul_one_le_gm (hA i hi) hX.ringInverse hα (inv_pos.mpr hβ) (hAα i hi)
      (smul_one_le_ringInverse_of_le_smul_one hX hβ hXβ)

/-- **Local strong monotonicity of the Wasserstein vector field.** -/
theorem re_hsInner_wassField_sub_lower {X Y : E →L[ℂ] E} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y)) (hPsa : IsSelfAdjoint (X - Y))
    {v : ι → ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))ˣ}
    (hv : ∀ i ∈ s, (↑(v i) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) Y⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    (α * α / (2 * (β * (β * β))) - secondOrderConst α β * ‖X - Y‖) * hsNormSq (X - Y)
      ≤ RCLike.re (hsInner (wassField s w Av X - wassField s w Av Y) (X - Y)) := by
  have hΦHS : IsHilbertSchmidt (wassField s w Av X - wassField s w Av Y) :=
    isHilbertSchmidt_wassField_sub hα hβ hA hX hY hAα hAβ hXβ hYβ hPHS
  have hDHS : IsHilbertSchmidt (wassDerivFun s w Av Y v (X - Y)) :=
    isHilbertSchmidt_wassDerivFun hA hY hPHS hPsa hv
  obtain ⟨R, hRdef⟩ : ∃ z : E →L[ℂ] E,
      z = (wassField s w Av X - wassField s w Av Y)
        - wassDerivFun s w Av Y v (X - Y) := ⟨_, rfl⟩
  have hRHS : IsHilbertSchmidt R := by rw [hRdef]; exact hΦHS.sub hDHS
  have hsplit : wassField s w Av X - wassField s w Av Y
      = wassDerivFun s w Av Y v (X - Y) + R := by rw [hRdef]; abel
  have hadd : RCLike.re (hsInner (wassField s w Av X - wassField s w Av Y) (X - Y))
      = RCLike.re (hsInner (wassDerivFun s w Av Y v (X - Y)) (X - Y))
        + RCLike.re (hsInner R (X - Y)) := by
    rw [hsplit, hsInner_add_left hDHS hRHS hPHS, map_add]
  rw [hadd]
  -- coercivity of the derivative
  have hcoer : (α * α / (2 * (β * (β * β)))) * hsNormSq (X - Y)
      ≤ RCLike.re (hsInner (wassDerivFun s w Av Y v (X - Y)) (X - Y)) :=
    re_hsInner_wassFieldDeriv_lower (Av := Av) (w := w) hα hβ hw hwsum hA hAα hAβ
      hY hYβ hPHS hPsa hv
  -- the second-order remainder
  have hRn : hsNorm R ≤ secondOrderConst α β * (‖X - Y‖ * hsNorm (X - Y)) := by
    rw [hRdef]
    exact hsNorm_wassField_increment_sub_deriv_le hα hβ hw hwsum hA hX hY hAα hAβ
      hXα hXβ hYα hYβ hPHS hPsa hv
  have hcs : ‖hsInner R (X - Y)‖ ≤ hsNorm R * hsNorm (X - Y) := norm_hsInner_le hRHS hPHS
  have hre : -(hsNorm R * hsNorm (X - Y)) ≤ RCLike.re (hsInner R (X - Y)) := by
    have h1 : RCLike.re (-(hsInner R (X - Y))) ≤ ‖-(hsInner R (X - Y))‖ := RCLike.re_le_norm _
    rw [map_neg, norm_neg] at h1
    linarith [hcs]
  have hsq : hsNorm (X - Y) * hsNorm (X - Y) = hsNormSq (X - Y) := by
    rw [← sq, sq_hsNorm]
  have hZnn : (0 : ℝ) ≤ ‖X - Y‖ := norm_nonneg _
  have hHnn : (0 : ℝ) ≤ hsNorm (X - Y) := hsNorm_nonneg _
  have hprod : -(secondOrderConst α β * ‖X - Y‖ * hsNormSq (X - Y))
      ≤ RCLike.re (hsInner R (X - Y)) := by
    refine le_trans ?_ hre
    have hb : hsNorm R * hsNorm (X - Y)
        ≤ (secondOrderConst α β * (‖X - Y‖ * hsNorm (X - Y))) * hsNorm (X - Y) :=
      mul_le_mul_of_nonneg_right hRn hHnn
    have hb2 : (secondOrderConst α β * (‖X - Y‖ * hsNorm (X - Y))) * hsNorm (X - Y)
        = secondOrderConst α β * ‖X - Y‖ * hsNormSq (X - Y) := by
      rw [← hsq]; ring
    rw [hb2] at hb
    linarith
  linarith [hcoer, hprod]

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
