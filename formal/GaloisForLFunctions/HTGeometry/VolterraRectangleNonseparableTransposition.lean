import GaloisForLFunctions.HTGeometry.VolterraRectangleTransposition

/-!
# Nonseparable rectangle Volterra transposition

The literal cyclic Peierls source is coupled in the two null variables by its
retained center time.  This file supplies the mixed-test version of rectangle
Volterra transposition: the test is the mixed derivative of one function
vanishing on the two outgoing faces, rather than a product of one-variable
primitives.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section
set_option autoImplicit false

private def rowPrimitive (F : ℝ × ℝ → ℂ) (u v : ℝ) : ℂ :=
  ∫ b in (0 : ℝ)..v, F (u, b)

private theorem rowPrimitive_continuous (F : ℝ × ℝ → ℂ) (hF : Continuous F) (v : ℝ) :
    Continuous (fun u => rowPrimitive F u v) := by
  unfold rowPrimitive
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun u b : ℝ => F (u, b)) hF 0 v

private theorem rowPrimitive_hasDerivAt (F : ℝ × ℝ → ℂ) (hF : Continuous F) (u v : ℝ) :
    HasDerivAt (fun v => rowPrimitive F u v) (F (u, v)) v := by
  unfold rowPrimitive
  exact intervalIntegral.integral_hasDerivAt_right
    ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 v)
    ((hF.comp (continuous_const.prodMk continuous_id)).stronglyMeasurableAtFilter _ _)
    (hF.comp (continuous_const.prodMk continuous_id)).continuousAt

private theorem doublePrimitive_continuous (F : ℝ × ℝ → ℂ) (hF : Continuous F) :
    Continuous (fun p : ℝ × ℝ => ∫ a in (0 : ℝ)..p.1, ∫ b in (0 : ℝ)..p.2, F (a, b)) := by
  have hi : Continuous (fun p : (ℝ × ℝ) × ℝ => ∫ b in (0 : ℝ)..p.1.2, F (p.2, b)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := 0)
      (f := fun p : (ℝ × ℝ) × ℝ => fun b => F (p.2, b))
      (hF.comp (continuous_fst.snd.prodMk continuous_snd)) continuous_fst.snd
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0)
    (f := fun p : ℝ × ℝ => fun a => ∫ b in (0 : ℝ)..p.2, F (a, b)) hi continuous_fst

/-- Mixed-test compact-null transposition of a rectangle Volterra kernel.

`Wv` is the `v`-derivative of `W`; its `u`-derivative is the (not necessarily
separable) test `H`.  The two face conditions are exactly those of the double
backward primitive of `H`. -/
theorem rectangle_volterra_nonseparable_transposition
    (K F : ℝ × ℝ → ℂ) (Q : ℂ) (U V : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hF : Continuous F)
    (hK : ∀ u v, 0 ≤ u → 0 ≤ v →
      K (u, v) = Q + ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b))
    (H W Wv : ℝ × ℝ → ℂ)
    (hH : Continuous H) (hW : Continuous W) (hWv : Continuous Wv)
    (hWv_u : ∀ u v, HasDerivAt (fun a => Wv (a, v)) (H (u, v)) u)
    (hW_v : ∀ u v, HasDerivAt (fun b => W (u, b)) (Wv (u, v)) v)
    (hWvU : ∀ v, Wv (U, v) = 0) (hWV : ∀ u, W (u, V) = 0) :
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, K (u, v) * H (u, v)) =
      Q * W (0, 0) + ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, F (u, v) * W (u, v) := by
  have hD := doublePrimitive_continuous F hF
  have hrowJoint : Continuous (fun p : ℝ × ℝ => rowPrimitive F p.1 p.2) := by
    unfold rowPrimitive
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := 0) (f := fun p : ℝ × ℝ => fun b => F (p.1, b))
      (hF.comp (continuous_fst.fst.prodMk continuous_snd)) continuous_snd
  have hPH : Continuous (fun p : ℝ × ℝ =>
      (Q + ∫ a in (0 : ℝ)..p.1, ∫ b in (0 : ℝ)..p.2, F (a, b)) * H p) :=
    (continuous_const.add hD).mul hH
  have hleft :
      (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, K (u, v) * H (u, v)) =
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
          (Q + ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) * H (u, v) := by
    apply intervalIntegral.integral_congr
    intro u hu
    apply intervalIntegral.integral_congr
    intro v hv
    have hu0 : 0 ≤ u := (show u ∈ Icc 0 U by simpa [uIcc_of_le hU] using hu).1
    have hv0 : 0 ≤ v := (show v ∈ Icc 0 V by simpa [uIcc_of_le hV] using hv).1
    change K (u, v) * H (u, v) =
      (Q + ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) * H (u, v)
    rw [hK u v hu0 hv0]
  have hswapPH :
      (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
        (Q + ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) * H (u, v)) =
        ∫ v in (0 : ℝ)..V, ∫ u in (0 : ℝ)..U,
          (Q + ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) * H (u, v) := by
    apply intervalIntegral_intervalIntegral_swap
    exact hPH.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc) |>.mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hfirst (v : ℝ) :
      (∫ u in (0 : ℝ)..U,
        (Q + ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) * H (u, v)) =
        -Q * Wv (0, v) - ∫ u in (0 : ℝ)..U, rowPrimitive F u v * Wv (u, v) := by
    have hrow := rowPrimitive_continuous F hF v
    have hPder (u : ℝ) : HasDerivAt
        (fun z => Q + ∫ a in (0 : ℝ)..z, rowPrimitive F a v) (rowPrimitive F u v) u := by
      apply HasDerivAt.const_add Q
      exact intervalIntegral.integral_hasDerivAt_right (hrow.intervalIntegrable 0 u)
        (hrow.stronglyMeasurableAtFilter _ _) hrow.continuousAt
    have hP : Continuous (fun z => Q + ∫ a in (0 : ℝ)..z, rowPrimitive F a v) :=
      continuous_iff_continuousAt.mpr (fun u => (hPder u).continuousAt)
    have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hP.continuousOn (hWv.comp (continuous_id.prodMk continuous_const)).continuousOn
      (fun u _ => hPder u) (fun u _ => hWv_u u v)
      (hrow.intervalIntegrable 0 U)
      ((hH.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 U)
    simpa [Function.comp_apply, hWvU, rowPrimitive] using hparts
  have hRW : Continuous (fun p : ℝ × ℝ => rowPrimitive F p.1 p.2 * Wv p) :=
    hrowJoint.mul hWv
  have hJ : Continuous (fun v => ∫ u in (0 : ℝ)..U, rowPrimitive F u v * Wv (u, v)) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun v u : ℝ => rowPrimitive F u v * Wv (u, v))
      (hRW.comp (continuous_snd.prodMk continuous_fst)) 0 U
  have hWv0 : Continuous (fun v => Wv (0, v)) :=
    hWv.comp (continuous_const.prodMk continuous_id)
  have hWv0_integral : (∫ v in (0 : ℝ)..V, Wv (0, v)) = -W (0, 0) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ => hW_v 0 v) (hWv0.intervalIntegrable 0 V)
    rw [hWV 0] at h
    simpa only [zero_sub] using h
  have hinner (u : ℝ) :
      (∫ v in (0 : ℝ)..V, rowPrimitive F u v * Wv (u, v)) =
        -(∫ v in (0 : ℝ)..V, F (u, v) * W (u, v)) := by
    have hrow : Continuous (fun v : ℝ => rowPrimitive F u v) :=
      hrowJoint.comp (show Continuous (fun v : ℝ => (u, v)) from
        continuous_const.prodMk continuous_id)
    have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hrow.continuousOn (hW.comp (continuous_const.prodMk continuous_id)).continuousOn
      (fun v _ => rowPrimitive_hasDerivAt F hF u v) (fun v _ => hW_v u v)
      ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 V)
      ((hWv.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 V)
    simpa [Function.comp_apply, hWV, rowPrimitive] using hparts
  have hswapRW :
      (∫ v in (0 : ℝ)..V, ∫ u in (0 : ℝ)..U, rowPrimitive F u v * Wv (u, v)) =
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, rowPrimitive F u v * Wv (u, v) := by
    apply intervalIntegral_intervalIntegral_swap
    exact (hRW.comp (continuous_snd.prodMk continuous_fst)).continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc) |>.mono_set
        (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hrowW :
      (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, rowPrimitive F u v * Wv (u, v)) =
        -(∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, F (u, v) * W (u, v)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u _
    exact hinner u
  calc
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, K (u, v) * H (u, v)) =
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
          (Q + ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) * H (u, v) := hleft
    _ = ∫ v in (0 : ℝ)..V, ∫ u in (0 : ℝ)..U,
          (Q + ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b)) * H (u, v) := hswapPH
    _ = ∫ v in (0 : ℝ)..V,
          (-Q * Wv (0, v) - ∫ u in (0 : ℝ)..U, rowPrimitive F u v * Wv (u, v)) := by
      apply intervalIntegral.integral_congr
      intro v _
      exact hfirst v
    _ = (-Q) * (∫ v in (0 : ℝ)..V, Wv (0, v)) -
          ∫ v in (0 : ℝ)..V, ∫ u in (0 : ℝ)..U, rowPrimitive F u v * Wv (u, v) := by
      have hminus : Continuous (fun v : ℝ => (-Q) * Wv (0, v)) := continuous_const.mul hWv0
      rw [intervalIntegral.integral_sub (hminus.intervalIntegrable 0 V) (hJ.intervalIntegrable 0 V),
        intervalIntegral.integral_const_mul]
    _ = Q * W (0, 0) -
          ∫ v in (0 : ℝ)..V, ∫ u in (0 : ℝ)..U, rowPrimitive F u v * Wv (u, v) := by
      rw [hWv0_integral]
      ring
    _ = Q * W (0, 0) -
          ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, rowPrimitive F u v * Wv (u, v) := by
      rw [hswapRW]
    _ = Q * W (0, 0) + ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, F (u, v) * W (u, v) := by
      rw [hrowW]
      ring

/-- First rectangle primitive, with the integration order chosen so its second
coordinate derivative is an ordinary one-variable fundamental-theorem step. -/
def reverseDoublePrimitive (H : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  ∫ b in (0 : ℝ)..p.2, ∫ a in (0 : ℝ)..p.1, H (a, b)

private theorem reverseDoublePrimitive_continuous (H : ℝ × ℝ → ℂ) (hH : Continuous H) :
    Continuous (reverseDoublePrimitive H) := by
  have hi : Continuous (fun p : (ℝ × ℝ) × ℝ => ∫ a in (0 : ℝ)..p.1.1, H (a, p.2)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := 0)
      (f := fun p : (ℝ × ℝ) × ℝ => fun a => H (a, p.2))
      (hH.comp (continuous_snd.prodMk continuous_fst.snd)) continuous_fst.fst
  unfold reverseDoublePrimitive
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0)
    (f := fun p : ℝ × ℝ => fun b => ∫ a in (0 : ℝ)..p.1, H (a, b)) hi continuous_snd

private theorem reverseDoublePrimitive_hasDerivAt (H : ℝ × ℝ → ℂ) (hH : Continuous H)
    (u v : ℝ) :
    HasDerivAt (fun b => reverseDoublePrimitive H (u, b))
      (∫ a in (0 : ℝ)..u, H (a, v)) v := by
  have hi : Continuous (fun b => ∫ a in (0 : ℝ)..u, H (a, b)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun b a : ℝ => H (a, b))
      (hH.comp (continuous_snd.prodMk continuous_fst)) 0 u
  unfold reverseDoublePrimitive
  exact intervalIntegral.integral_hasDerivAt_right (hi.intervalIntegrable 0 v)
    (hi.stronglyMeasurableAtFilter _ _) hi.continuousAt

/-- The `v` derivative of the double backward rectangle primitive. -/
def backwardRectangleVertical (H : ℝ × ℝ → ℂ) (U : ℝ) (p : ℝ × ℝ) : ℂ :=
  (∫ a in (0 : ℝ)..p.1, H (a, p.2)) - ∫ a in (0 : ℝ)..U, H (a, p.2)

private theorem backwardRectangleVertical_continuous (H : ℝ × ℝ → ℂ)
    (U : ℝ) (hH : Continuous H) :
    Continuous (backwardRectangleVertical H U) := by
  have hi : Continuous (fun p : ℝ × ℝ => ∫ a in (0 : ℝ)..p.1, H (a, p.2)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := 0) (f := fun p : ℝ × ℝ => fun a => H (a, p.2))
      (hH.comp (continuous_snd.prodMk continuous_fst.snd)) continuous_fst
  have hU : Continuous (fun p : ℝ × ℝ => ∫ a in (0 : ℝ)..U, H (a, p.2)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun p a : ℝ => H (a, p))
      (hH.comp (continuous_snd.prodMk continuous_fst)) 0 U |>.comp continuous_snd
  exact hi.sub hU

private theorem backwardRectangleVertical_hasDerivAt (H : ℝ × ℝ → ℂ)
    (U u v : ℝ) (hH : Continuous H) :
    HasDerivAt (fun a => backwardRectangleVertical H U (a, v)) (H (u, v)) u := by
  have hu : Continuous (fun a => H (a, v)) := hH.comp (continuous_id.prodMk continuous_const)
  unfold backwardRectangleVertical
  convert (intervalIntegral.integral_hasDerivAt_right (hu.intervalIntegrable 0 u)
    (hu.stronglyMeasurableAtFilter _ _) hu.continuousAt).sub
      (hasDerivAt_const u (∫ a in (0 : ℝ)..U, H (a, v))) using 1
  · rfl
  · funext a
    rfl
  · rw [sub_zero]

private theorem backwardRectangleVertical_face (H : ℝ × ℝ → ℂ) (U v : ℝ) :
    backwardRectangleVertical H U (U, v) = 0 := by
  unfold backwardRectangleVertical
  simp

/-- Double backward primitive of a mixed rectangle test.  It vanishes on the
two outgoing faces and retains every coupling in `H`. -/
def backwardRectanglePrimitive (H : ℝ × ℝ → ℂ) (U V : ℝ) (p : ℝ × ℝ) : ℂ :=
  reverseDoublePrimitive H p - reverseDoublePrimitive H (U, p.2) -
    reverseDoublePrimitive H (p.1, V) + reverseDoublePrimitive H (U, V)

private theorem backwardRectanglePrimitive_continuous (H : ℝ × ℝ → ℂ)
    (U V : ℝ) (hH : Continuous H) :
    Continuous (backwardRectanglePrimitive H U V) := by
  have hR := reverseDoublePrimitive_continuous H hH
  exact ((hR.sub (hR.comp (continuous_const.prodMk continuous_snd))).sub
    (hR.comp (continuous_fst.prodMk continuous_const))).add continuous_const

private theorem backwardRectanglePrimitive_hasDerivAt (H : ℝ × ℝ → ℂ)
    (U V u v : ℝ) (hH : Continuous H) :
    HasDerivAt (fun b => backwardRectanglePrimitive H U V (u, b))
      (backwardRectangleVertical H U (u, v)) v := by
  have h1 := reverseDoublePrimitive_hasDerivAt H hH u v
  have h2 := reverseDoublePrimitive_hasDerivAt H hH U v
  unfold backwardRectanglePrimitive backwardRectangleVertical
  convert ((h1.sub h2).sub (hasDerivAt_const v (reverseDoublePrimitive H (u, V)))).add
    (hasDerivAt_const v (reverseDoublePrimitive H (U, V))) using 1
  · rfl
  · funext b
    rfl
  · simp

private theorem backwardRectanglePrimitive_face (H : ℝ × ℝ → ℂ) (U V u : ℝ) :
    backwardRectanglePrimitive H U V (u, V) = 0 := by
  unfold backwardRectanglePrimitive
  ring

/-- Closed compact-null transposition for every continuous mixed test.  No
factorization, artificial source split, or derivative premise survives. -/
theorem rectangle_volterra_continuous_test_transposition
    (K F : ℝ × ℝ → ℂ) (Q : ℂ) (U V : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hF : Continuous F)
    (hK : ∀ u v, 0 ≤ u → 0 ≤ v →
      K (u, v) = Q + ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, F (a, b))
    (H : ℝ × ℝ → ℂ) (hH : Continuous H) :
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, K (u, v) * H (u, v)) =
      Q * backwardRectanglePrimitive H U V (0, 0) +
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
          F (u, v) * backwardRectanglePrimitive H U V (u, v) := by
  exact rectangle_volterra_nonseparable_transposition K F Q U V hU hV hF hK H
    (backwardRectanglePrimitive H U V) (backwardRectangleVertical H U)
    hH (backwardRectanglePrimitive_continuous H U V hH)
    (backwardRectangleVertical_continuous H U hH)
    (fun u v => backwardRectangleVertical_hasDerivAt H U u v hH)
    (fun u v => backwardRectanglePrimitive_hasDerivAt H U V u v hH)
    (fun v => backwardRectangleVertical_face H U v)
    (fun u => backwardRectanglePrimitive_face H U V u)

end

end GaloisForLFunctions.HTGeometry
