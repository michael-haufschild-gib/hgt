import GaloisForLFunctions.HTGeometry.LogNormalEquationTrace

/-!
# Signed half-log trace without positivity

The logarithmic normal-equation trace argument previously required nonnegativity of the profile at
penalized maxima and a nonnegative auxiliary numerator at penalized minima. Those conditions exclude
the signed zero modes for which the argument was designed.

This module removes both conditions. Four sign-free square-root weight-removal estimates control the
weight mismatch by `|f X|`; their sum bounds the near transport term using only the first moment of
the Gamma kernel. The resulting critical-point error tends to zero and yields the literal signed
half-log trace theorem from the normal equation, with no positivity hypothesis.
-/

open MeasureTheory Set Filter

namespace GaloisForLFunctions.HTGeometry

private theorem sqrt_add_sub_le_mul_div
    {X s : ℝ} (hX : 0 < X) (hs : 0 ≤ s) :
    Real.sqrt (X + s) - Real.sqrt X ≤ Real.sqrt (X + s) * s / X := by
  have hXs : 0 ≤ X + s := by linarith
  have hA : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  have hB : 0 ≤ Real.sqrt (X + s) := Real.sqrt_nonneg _
  have hA2 : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX.le
  have hB2 : Real.sqrt (X + s) ^ 2 = X + s := Real.sq_sqrt hXs
  have hdiff : 0 ≤ Real.sqrt (X + s) - Real.sqrt X :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hid :
      (Real.sqrt (X + s) - Real.sqrt X) *
        (Real.sqrt (X + s) + Real.sqrt X) = s := by
    nlinarith
  have hden :
      X ≤ Real.sqrt (X + s) * (Real.sqrt (X + s) + Real.sqrt X) := by
    nlinarith [mul_nonneg hA hB]
  have hmul := mul_le_mul_of_nonneg_left hden hdiff
  have heq :
      (Real.sqrt (X + s) - Real.sqrt X) *
          (Real.sqrt (X + s) * (Real.sqrt (X + s) + Real.sqrt X)) =
        Real.sqrt (X + s) * s := by
    calc
      _ = Real.sqrt (X + s) *
          ((Real.sqrt (X + s) - Real.sqrt X) *
            (Real.sqrt (X + s) + Real.sqrt X)) := by ring
      _ = Real.sqrt (X + s) * s := by rw [hid]
  rw [le_div_iff₀ hX]
  exact hmul.trans_eq heq

private theorem sqrt_sub_gap_le_mul_div
    {X s : ℝ} (hX : 0 < X) (hs : 0 ≤ s) (hsX : s ≤ X / 2) :
    Real.sqrt X - Real.sqrt (X - s) ≤ 2 * Real.sqrt (X - s) * s / X := by
  have hXs : 0 ≤ X - s := by linarith
  have hA : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  have hC : 0 ≤ Real.sqrt (X - s) := Real.sqrt_nonneg _
  have hA2 : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX.le
  have hC2 : Real.sqrt (X - s) ^ 2 = X - s := Real.sq_sqrt hXs
  have hdiff : 0 ≤ Real.sqrt X - Real.sqrt (X - s) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hid :
      (Real.sqrt X - Real.sqrt (X - s)) *
        (Real.sqrt X + Real.sqrt (X - s)) = s := by
    nlinarith
  have hden :
      X ≤ 2 * Real.sqrt (X - s) *
        (Real.sqrt X + Real.sqrt (X - s)) := by
    nlinarith [mul_nonneg hA hC]
  have hmul := mul_le_mul_of_nonneg_left hden hdiff
  have heq :
      (Real.sqrt X - Real.sqrt (X - s)) *
          (2 * Real.sqrt (X - s) *
            (Real.sqrt X + Real.sqrt (X - s))) =
        2 * Real.sqrt (X - s) * s := by
    calc
      _ = 2 * Real.sqrt (X - s) *
          ((Real.sqrt X - Real.sqrt (X - s)) *
            (Real.sqrt X + Real.sqrt (X - s))) := by ring
      _ = 2 * Real.sqrt (X - s) * s := by rw [hid]
  rw [le_div_iff₀ hX]
  exact hmul.trans_eq heq

private theorem sqrt_le_two_mul_sqrt_sub
    {X s : ℝ} (hX : 0 < X) (hsX : s ≤ X / 2) :
    Real.sqrt X ≤ 2 * Real.sqrt (X - s) := by
  have hXs : 0 ≤ X - s := by linarith
  have hA : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  have hC : 0 ≤ Real.sqrt (X - s) := Real.sqrt_nonneg _
  have hA2 : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX.le
  have hC2 : Real.sqrt (X - s) ^ 2 = X - s := Real.sq_sqrt hXs
  nlinarith [sq_nonneg (Real.sqrt X - 2 * Real.sqrt (X - s))]

theorem le_of_weighted_le_forward_signed
    {f : ℝ → ℝ} {X s δ M : ℝ} (hX : 0 < X) (hs : 0 ≤ s)
    (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hf : |f X| ≤ M)
    (hw : Real.sqrt (X + s) * f (X + s) ≤ Real.sqrt X * f X + δ * s) :
    f (X + s) ≤ f X + (δ / Real.sqrt X + M / X) * s := by
  have hXs : 0 < X + s := by linarith
  have hA : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hB : 0 < Real.sqrt (X + s) := Real.sqrt_pos.mpr hXs
  have hroot : Real.sqrt X ≤ Real.sqrt (X + s) := Real.sqrt_le_sqrt (by linarith)
  have hgap := sqrt_add_sub_le_mul_div hX hs
  have hfle : -M ≤ f X := (abs_le.mp hf).1
  apply le_of_mul_le_mul_left (a := Real.sqrt (X + s))
  have hδterm : δ * s * Real.sqrt X ≤ δ * s * Real.sqrt (X + s) := by
    exact mul_le_mul_of_nonneg_left hroot (mul_nonneg hδ hs)
  have hMterm :
      (Real.sqrt (X + s) - Real.sqrt X) * M ≤
        Real.sqrt (X + s) * (M / X * s) := by
    have := mul_le_mul_of_nonneg_right hgap hM
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hδscaled :
      δ * s ≤ Real.sqrt (X + s) * (δ / Real.sqrt X * s) := by
    apply le_of_mul_le_mul_left (a := Real.sqrt X)
    · calc
        Real.sqrt X * (δ * s) = δ * s * Real.sqrt X := by ring
        _ ≤ δ * s * Real.sqrt (X + s) := hδterm
        _ = Real.sqrt X * (Real.sqrt (X + s) * (δ / Real.sqrt X * s)) := by
          field_simp
    · exact hA
  have hsign :
      (Real.sqrt X - Real.sqrt (X + s)) * f X ≤
        (Real.sqrt (X + s) - Real.sqrt X) * M := by
    have hneg : -f X ≤ M := by linarith
    have := mul_le_mul_of_nonneg_left hneg
      (sub_nonneg.mpr hroot)
    nlinarith
  have hfterm :
      Real.sqrt X * f X ≤ Real.sqrt (X + s) * f X +
        Real.sqrt (X + s) * (M / X * s) := by
    nlinarith [hsign, hMterm]
  · have hscaled :
        Real.sqrt (X + s) * f (X + s) ≤
          Real.sqrt (X + s) * (f X + (δ / Real.sqrt X + M / X) * s) := by
      calc
        _ ≤ Real.sqrt X * f X + δ * s := hw
        _ ≤ (Real.sqrt (X + s) * f X + Real.sqrt (X + s) * (M / X * s)) +
            Real.sqrt (X + s) * (δ / Real.sqrt X * s) := by linarith
        _ = _ := by ring
    exact hscaled
  · exact hB

theorem le_of_weighted_le_backward_signed
    {f : ℝ → ℝ} {X s δ M : ℝ} (hX : 0 < X) (hs : 0 ≤ s)
    (hsX : s ≤ X / 2) (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hf : |f X| ≤ M)
    (hw : Real.sqrt (X - s) * f (X - s) ≤ Real.sqrt X * f X + δ * s) :
    f (X - s) ≤ f X + (2 * δ / Real.sqrt X + 2 * M / X) * s := by
  have hXs : 0 < X - s := by linarith
  have hA : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hC : 0 < Real.sqrt (X - s) := Real.sqrt_pos.mpr hXs
  have hroot : Real.sqrt (X - s) ≤ Real.sqrt X := Real.sqrt_le_sqrt (by linarith)
  have htwo := sqrt_le_two_mul_sqrt_sub hX hsX
  have hgap := sqrt_sub_gap_le_mul_div hX hs hsX
  have hfle : f X ≤ M := (abs_le.mp hf).2
  apply le_of_mul_le_mul_left (a := Real.sqrt (X - s))
  have hδterm : δ * s * Real.sqrt X ≤ 2 * δ * s * Real.sqrt (X - s) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left htwo (mul_nonneg hδ hs)
  have hMterm :
      (Real.sqrt X - Real.sqrt (X - s)) * M ≤
        Real.sqrt (X - s) * (2 * M / X * s) := by
    have := mul_le_mul_of_nonneg_right hgap hM
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hδscaled :
      δ * s ≤ Real.sqrt (X - s) * (2 * δ / Real.sqrt X * s) := by
    apply le_of_mul_le_mul_left (a := Real.sqrt X)
    · calc
        Real.sqrt X * (δ * s) = δ * s * Real.sqrt X := by ring
        _ ≤ 2 * δ * s * Real.sqrt (X - s) := hδterm
        _ = Real.sqrt X * (Real.sqrt (X - s) * (2 * δ / Real.sqrt X * s)) := by
          field_simp
    · exact hA
  have hsign :
      (Real.sqrt X - Real.sqrt (X - s)) * f X ≤
        (Real.sqrt X - Real.sqrt (X - s)) * M :=
    mul_le_mul_of_nonneg_left hfle (sub_nonneg.mpr hroot)
  have hfterm :
      Real.sqrt X * f X ≤ Real.sqrt (X - s) * f X +
        Real.sqrt (X - s) * (2 * M / X * s) := by
    nlinarith [hsign, hMterm]
  · have hscaled :
        Real.sqrt (X - s) * f (X - s) ≤
          Real.sqrt (X - s) * (f X + (2 * δ / Real.sqrt X + 2 * M / X) * s) := by
      calc
        _ ≤ Real.sqrt X * f X + δ * s := hw
        _ ≤ (Real.sqrt (X - s) * f X + Real.sqrt (X - s) * (2 * M / X * s)) +
            Real.sqrt (X - s) * (2 * δ / Real.sqrt X * s) := by linarith
        _ = _ := by ring
    exact hscaled
  · exact hC

theorem le_of_weighted_ge_forward_signed
    {f : ℝ → ℝ} {X s δ M : ℝ} (hX : 0 < X) (hs : 0 ≤ s)
    (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hf : |f X| ≤ M)
    (hw : Real.sqrt X * f X - δ * s ≤ Real.sqrt (X + s) * f (X + s)) :
    f X - (δ / Real.sqrt X + M / X) * s ≤ f (X + s) := by
  have hXs : 0 < X + s := by linarith
  have hA : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hB : 0 < Real.sqrt (X + s) := Real.sqrt_pos.mpr hXs
  have hroot : Real.sqrt X ≤ Real.sqrt (X + s) := Real.sqrt_le_sqrt (by linarith)
  have hgap := sqrt_add_sub_le_mul_div hX hs
  have hfle : f X ≤ M := (abs_le.mp hf).2
  apply le_of_mul_le_mul_left (a := Real.sqrt (X + s))
  have hδterm : δ * s * Real.sqrt X ≤ δ * s * Real.sqrt (X + s) := by
    exact mul_le_mul_of_nonneg_left hroot (mul_nonneg hδ hs)
  have hMterm :
      (Real.sqrt (X + s) - Real.sqrt X) * M ≤
        Real.sqrt (X + s) * (M / X * s) := by
    have := mul_le_mul_of_nonneg_right hgap hM
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hδscaled :
      δ * s ≤ Real.sqrt (X + s) * (δ / Real.sqrt X * s) := by
    apply le_of_mul_le_mul_left (a := Real.sqrt X)
    · calc
        Real.sqrt X * (δ * s) = δ * s * Real.sqrt X := by ring
        _ ≤ δ * s * Real.sqrt (X + s) := hδterm
        _ = Real.sqrt X * (Real.sqrt (X + s) * (δ / Real.sqrt X * s)) := by
          field_simp
    · exact hA
  have hsign :
      (Real.sqrt (X + s) - Real.sqrt X) * f X ≤
        (Real.sqrt (X + s) - Real.sqrt X) * M :=
    mul_le_mul_of_nonneg_left hfle (sub_nonneg.mpr hroot)
  · have hscaled :
        Real.sqrt (X + s) * (f X - (δ / Real.sqrt X + M / X) * s) ≤
          Real.sqrt (X + s) * f (X + s) := by
      calc
        _ = Real.sqrt (X + s) * f X -
            Real.sqrt (X + s) * (δ / Real.sqrt X * s) -
            Real.sqrt (X + s) * (M / X * s) := by ring
        _ ≤ Real.sqrt X * f X - δ * s := by linarith [hsign, hMterm, hδscaled]
        _ ≤ _ := hw
    exact hscaled
  · exact hB

theorem le_of_weighted_ge_backward_signed
    {f : ℝ → ℝ} {X s δ M : ℝ} (hX : 0 < X) (hs : 0 ≤ s)
    (hsX : s ≤ X / 2) (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hf : |f X| ≤ M)
    (hw : Real.sqrt X * f X - δ * s ≤ Real.sqrt (X - s) * f (X - s)) :
    f X - (2 * δ / Real.sqrt X + 2 * M / X) * s ≤ f (X - s) := by
  have hXs : 0 < X - s := by linarith
  have hA : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hC : 0 < Real.sqrt (X - s) := Real.sqrt_pos.mpr hXs
  have htwo := sqrt_le_two_mul_sqrt_sub hX hsX
  have hgap := sqrt_sub_gap_le_mul_div hX hs hsX
  have hflow : -M ≤ f X := (abs_le.mp hf).1
  apply le_of_mul_le_mul_left (a := Real.sqrt (X - s))
  have hδterm : δ * s * Real.sqrt X ≤ 2 * δ * s * Real.sqrt (X - s) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left htwo (mul_nonneg hδ hs)
  have hMterm :
      (Real.sqrt X - Real.sqrt (X - s)) * M ≤
        Real.sqrt (X - s) * (2 * M / X * s) := by
    have := mul_le_mul_of_nonneg_right hgap hM
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hδscaled :
      δ * s ≤ Real.sqrt (X - s) * (2 * δ / Real.sqrt X * s) := by
    apply le_of_mul_le_mul_left (a := Real.sqrt X)
    · calc
        Real.sqrt X * (δ * s) = δ * s * Real.sqrt X := by ring
        _ ≤ 2 * δ * s * Real.sqrt (X - s) := hδterm
        _ = Real.sqrt X * (Real.sqrt (X - s) * (2 * δ / Real.sqrt X * s)) := by
          field_simp
    · exact hA
  have hsign :
      (Real.sqrt (X - s) - Real.sqrt X) * f X ≤
        (Real.sqrt X - Real.sqrt (X - s)) * M := by
    have := mul_le_mul_of_nonneg_left hflow
      (sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith : X - s ≤ X)))
    nlinarith
  · have hscaled :
        Real.sqrt (X - s) * (f X - (2 * δ / Real.sqrt X + 2 * M / X) * s) ≤
          Real.sqrt (X - s) * f (X - s) := by
      calc
        _ = Real.sqrt (X - s) * f X -
            Real.sqrt (X - s) * (2 * δ / Real.sqrt X * s) -
            Real.sqrt (X - s) * (2 * M / X * s) := by ring
        _ ≤ Real.sqrt X * f X - δ * s := by linarith [hsign, hMterm, hδscaled]
        _ ≤ _ := hw
    exact hscaled
  · exact hC

/-- A penalized maximum gives a sign-free linear near-shift lower bound. -/
theorem neg_mul_le_secondDifference_of_weighted_signed
    {f : ℝ → ℝ} {X s δ M : ℝ} (hX : 0 < X) (hs : 0 ≤ s)
    (hsX : s ≤ X / 2) (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hf : |f X| ≤ M)
    (hp : Real.sqrt (X + s) * f (X + s) ≤ Real.sqrt X * f X + δ * s)
    (hm : Real.sqrt (X - s) * f (X - s) ≤ Real.sqrt X * f X + δ * s) :
    -((3 * δ / Real.sqrt X + 3 * M / X) * s) ≤ secondDifference f X s := by
  have hp' := le_of_weighted_le_forward_signed hX hs hδ hM hf hp
  have hm' := le_of_weighted_le_backward_signed hX hs hsX hδ hM hf hm
  have hsum := add_le_add hp' hm'
  have hcoeff :
      (δ / Real.sqrt X + M / X) * s +
          (2 * δ / Real.sqrt X + 2 * M / X) * s =
        (3 * δ / Real.sqrt X + 3 * M / X) * s := by ring
  unfold secondDifference
  rw [← hcoeff]
  linarith

/-- A penalized minimum gives the mirrored sign-free linear near-shift upper bound. -/
theorem secondDifference_le_of_weighted_signed
    {f : ℝ → ℝ} {X s δ M : ℝ} (hX : 0 < X) (hs : 0 ≤ s)
    (hsX : s ≤ X / 2) (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hf : |f X| ≤ M)
    (hp : Real.sqrt X * f X - δ * s ≤ Real.sqrt (X + s) * f (X + s))
    (hm : Real.sqrt X * f X - δ * s ≤ Real.sqrt (X - s) * f (X - s)) :
    secondDifference f X s ≤ (3 * δ / Real.sqrt X + 3 * M / X) * s := by
  have hp' := le_of_weighted_ge_forward_signed hX hs hδ hM hf hp
  have hm' := le_of_weighted_ge_backward_signed hX hs hsX hδ hM hf hm
  have hsum := add_le_add hp' hm'
  have hcoeff :
      (δ / Real.sqrt X + M / X) * s +
          (2 * δ / Real.sqrt X + 2 * M / X) * s =
        (3 * δ / Real.sqrt X + 3 * M / X) * s := by ring
  unfold secondDifference
  rw [← hcoeff]
  linarith

/-- The near transport integral at a signed penalized maximum. -/
theorem neg_le_integral_transport_near_signed
    {f : ℝ → ℝ} {X δ M : ℝ} (hX : 0 < X) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hf : |f X| ≤ M)
    (hint : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hp : ∀ s, 0 ≤ s → s ≤ X / 2 →
      Real.sqrt (X + s) * f (X + s) ≤ Real.sqrt X * f X + δ * s)
    (hm : ∀ s, 0 ≤ s → s ≤ X / 2 →
      Real.sqrt (X - s) * f (X - s) ≤ Real.sqrt X * f X + δ * s) :
    -((3 * δ / Real.sqrt X + 3 * M / X) *
        ∫ s in Ioc 0 (X / 2), s * gammaTransportKernel s)
      ≤ ∫ s in Ioc 0 (X / 2), secondDifference f X s * gammaTransportKernel s := by
  let C := 3 * δ / Real.sqrt X + 3 * M / X
  have hmom : IntegrableOn (fun s => s * gammaTransportKernel s) (Ioc 0 (X / 2)) :=
    integrableOn_id_mul_gammaTransportKernel_Ioi_zero.mono_set fun _ hx => hx.1
  have hdom : IntegrableOn (fun s => -(C * (s * gammaTransportKernel s)))
      (Ioc 0 (X / 2)) := (hmom.const_mul C).neg
  have hpt : ∀ s ∈ Ioc (0 : ℝ) (X / 2),
      -(C * (s * gammaTransportKernel s)) ≤
        secondDifference f X s * gammaTransportKernel s := by
    intro s hsI
    have hk := gammaTransportKernel_pos hsI.1
    have hsd := neg_mul_le_secondDifference_of_weighted_signed
      hX hsI.1.le hsI.2 hδ hM hf
      (hp s hsI.1.le hsI.2) (hm s hsI.1.le hsI.2)
    dsimp [C] at hsd ⊢
    nlinarith
  have hmono := setIntegral_mono_on hdom hint measurableSet_Ioc hpt
  simpa only [integral_neg, integral_const_mul] using hmono

/-- The near transport integral at a signed penalized minimum. -/
theorem integral_transport_near_le_signed
    {f : ℝ → ℝ} {X δ M : ℝ} (hX : 0 < X) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hf : |f X| ≤ M)
    (hint : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hp : ∀ s, 0 ≤ s → s ≤ X / 2 →
      Real.sqrt X * f X - δ * s ≤ Real.sqrt (X + s) * f (X + s))
    (hm : ∀ s, 0 ≤ s → s ≤ X / 2 →
      Real.sqrt X * f X - δ * s ≤ Real.sqrt (X - s) * f (X - s)) :
    (∫ s in Ioc 0 (X / 2), secondDifference f X s * gammaTransportKernel s)
      ≤ (3 * δ / Real.sqrt X + 3 * M / X) *
        ∫ s in Ioc 0 (X / 2), s * gammaTransportKernel s := by
  let C := 3 * δ / Real.sqrt X + 3 * M / X
  have hmom : IntegrableOn (fun s => s * gammaTransportKernel s) (Ioc 0 (X / 2)) :=
    integrableOn_id_mul_gammaTransportKernel_Ioi_zero.mono_set fun _ hx => hx.1
  have hdom : IntegrableOn (fun s => C * (s * gammaTransportKernel s))
      (Ioc 0 (X / 2)) := hmom.const_mul C
  have hpt : ∀ s ∈ Ioc (0 : ℝ) (X / 2),
      secondDifference f X s * gammaTransportKernel s ≤
        C * (s * gammaTransportKernel s) := by
    intro s hsI
    have hk := gammaTransportKernel_pos hsI.1
    have hsd := secondDifference_le_of_weighted_signed
      hX hsI.1.le hsI.2 hδ hM hf
      (hp s hsI.1.le hsI.2) (hm s hsI.1.le hsI.2)
    dsimp [C] at hsd ⊢
    nlinarith
  have hmono := setIntegral_mono_on hint hdom measurableSet_Ioc hpt
  simpa only [integral_const_mul] using hmono

/-- Sign-free transport lower bound at a penalized maximum. -/
theorem neg_le_gammaTransport_of_maximizer_signed
    {f : ℝ → ℝ} {X δ M : ℝ} (hX : 0 < X) (hδ : 0 ≤ δ)
    (hFb : ∀ x, |f x| ≤ M) (hmeas : Measurable f)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hp : ∀ s, 0 ≤ s → s ≤ X / 2 →
      Real.sqrt (X + s) * f (X + s) ≤ Real.sqrt X * f X + δ * s)
    (hm : ∀ s, 0 ≤ s → s ≤ X / 2 →
      Real.sqrt (X - s) * f (X - s) ≤ Real.sqrt X * f X + δ * s) :
    -((3 * δ / Real.sqrt X + 3 * M / X) *
        (∫ s in Ioc (0 : ℝ) (X / 2), s * gammaTransportKernel s)
      + 4 * M * (-Real.log (1 - Real.exp (-(X / 2))))) ≤ gammaTransport f X := by
  have hM : 0 ≤ M := (abs_nonneg (f X)).trans (hFb X)
  have hX2 : (0 : ℝ) < X / 2 := by linarith
  have hsd : Measurable fun s => secondDifference f X s := by
    unfold secondDifference
    fun_prop
  have hfar : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioi (X / 2)) := by
    have hdom : IntegrableOn (fun s => 4 * M * gammaTransportKernel s) (Ioi (X / 2)) :=
      (integrableOn_gammaTransportKernel_Ioi hX2).const_mul _
    refine Integrable.mono' hdom (hsd.mul measurable_gammaTransportKernel).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hk := gammaTransportKernel_pos (hX2.trans hs)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hk]
    exact mul_le_mul_of_nonneg_right (abs_secondDifference_le_of_bounded hFb X s) hk.le
  rw [gammaTransport_split hX hnear hfar]
  have hnearbd := neg_le_integral_transport_near_signed hX hδ hM (hFb X) hnear hp hm
  have hfarbd := abs_integral_transport_far_le (F := f) X hX2 hFb hmeas
  linarith [hnearbd, neg_le_of_abs_le hfarbd]

/-- Sign-free transport upper bound at a penalized minimum. -/
theorem gammaTransport_le_of_minimizer_signed
    {f : ℝ → ℝ} {X δ M : ℝ} (hX : 0 < X) (hδ : 0 ≤ δ)
    (hFb : ∀ x, |f x| ≤ M) (hmeas : Measurable f)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hp : ∀ s, 0 ≤ s → s ≤ X / 2 →
      Real.sqrt X * f X - δ * s ≤ Real.sqrt (X + s) * f (X + s))
    (hm : ∀ s, 0 ≤ s → s ≤ X / 2 →
      Real.sqrt X * f X - δ * s ≤ Real.sqrt (X - s) * f (X - s)) :
    gammaTransport f X ≤
      (3 * δ / Real.sqrt X + 3 * M / X) *
          (∫ s in Ioc (0 : ℝ) (X / 2), s * gammaTransportKernel s)
        + 4 * M * (-Real.log (1 - Real.exp (-(X / 2)))) := by
  have hM : 0 ≤ M := (abs_nonneg (f X)).trans (hFb X)
  have hX2 : (0 : ℝ) < X / 2 := by linarith
  have hsd : Measurable fun s => secondDifference f X s := by
    unfold secondDifference
    fun_prop
  have hfar : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioi (X / 2)) := by
    have hdom : IntegrableOn (fun s => 4 * M * gammaTransportKernel s) (Ioi (X / 2)) :=
      (integrableOn_gammaTransportKernel_Ioi hX2).const_mul _
    refine Integrable.mono' hdom (hsd.mul measurable_gammaTransportKernel).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hk := gammaTransportKernel_pos (hX2.trans hs)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hk]
    exact mul_le_mul_of_nonneg_right (abs_secondDifference_le_of_bounded hFb X s) hk.le
  rw [gammaTransport_split hX hnear hfar]
  have hnearbd := integral_transport_near_le_signed hX hδ hM (hFb X) hnear hp hm
  have hfarbd := abs_integral_transport_far_le (F := f) X hX2 hFb hmeas
  linarith [hnearbd, le_of_abs_le hfarbd]

/-- Direct sign-free transport bound from the penalized maximum. -/
theorem neg_le_gammaTransport_of_isMaxOn_signed
    {f : ℝ → ℝ} {X δ M L₀ a : ℝ} (hX : 0 < X) (hδ : 0 ≤ δ)
    (hFb : ∀ x, |f x| ≤ M) (hmeas : Measurable f)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hmax : IsMaxOn (penalized (fun L => Real.sqrt L * f L) δ L₀) (Ici a) X)
    (ha : a ≤ X / 2) :
    -((3 * δ / Real.sqrt X + 3 * M / X) *
        (∫ s in Ioc (0 : ℝ) (X / 2), s * gammaTransportKernel s)
      + 4 * M * (-Real.log (1 - Real.exp (-(X / 2))))) ≤ gammaTransport f X := by
  apply neg_le_gammaTransport_of_maximizer_signed hX hδ hFb hmeas hnear
  · intro s hs hsX
    exact (le_of_isMaxOn_penalized_shift hmax hδ hs
      (by simp only [mem_Ici]; linarith) (by simp only [mem_Ici]; linarith)).1
  · intro s hs hsX
    exact (le_of_isMaxOn_penalized_shift hmax hδ hs
      (by simp only [mem_Ici]; linarith) (by simp only [mem_Ici]; linarith)).2

/-- Direct sign-free transport bound from the penalized minimum. -/
theorem gammaTransport_le_of_isMaxOn_neg_signed
    {f : ℝ → ℝ} {X δ M L₀ a : ℝ} (hX : 0 < X) (hδ : 0 ≤ δ)
    (hFb : ∀ x, |f x| ≤ M) (hmeas : Measurable f)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hmax : IsMaxOn (penalized (fun L => -(Real.sqrt L * f L)) δ L₀) (Ici a) X)
    (ha : a ≤ X / 2) :
    gammaTransport f X ≤
      (3 * δ / Real.sqrt X + 3 * M / X) *
          (∫ s in Ioc (0 : ℝ) (X / 2), s * gammaTransportKernel s)
        + 4 * M * (-Real.log (1 - Real.exp (-(X / 2)))) := by
  apply gammaTransport_le_of_minimizer_signed hX hδ hFb hmeas hnear
  · intro s hs hsX
    exact (le_of_isMaxOn_penalized_neg_shift hmax hδ hs
      (by simp only [mem_Ici]; linarith) (by simp only [mem_Ici]; linarith)).1
  · intro s hs hsX
    exact (le_of_isMaxOn_penalized_neg_shift hmax hδ hs
      (by simp only [mem_Ici]; linarith) (by simp only [mem_Ici]; linarith)).2

/-- Sign-free transport error along a critical-point family. -/
noncomputable def signedTransportBound
    (X : ℝ → ℝ) (M : ℝ) (L₀ : ℝ) : ℝ :=
  (3 * (Real.sqrt L₀)⁻¹ / Real.sqrt (X L₀) + 3 * M / X L₀) *
      (∫ s in Ioc (0 : ℝ) (X L₀ / 2), s * gammaTransportKernel s) +
    4 * M * (-Real.log (1 - Real.exp (-(X L₀ / 2))))

/-- The sign-free transport error vanishes along every divergent critical-point family. -/
theorem tendsto_signedTransportBound
    {X : ℝ → ℝ} {M : ℝ} (hX : Tendsto X atTop atTop) :
    Tendsto (signedTransportBound X M) atTop (nhds 0) := by
  have h1 : Tendsto
      (fun L₀ => 3 * (Real.sqrt L₀)⁻¹ / Real.sqrt (X L₀)) atTop (nhds 0) := by
    refine tendsto_bounded_div_sqrt_comp (K := 3) hX ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L₀ hL
    have hs : (1 : ℝ) ≤ Real.sqrt L₀ := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hL
    have hinv : (Real.sqrt L₀)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      exact Or.inr hs
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_inv,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    linarith [inv_nonneg.mpr (Real.sqrt_nonneg L₀)]
  have h2 : Tendsto (fun L₀ => 3 * M / X L₀) atTop (nhds 0) :=
    tendsto_bounded_div_atTop (K := |3 * M|) hX
      (Filter.Eventually.of_forall fun _ => le_rfl)
  have hcoef : Tendsto
      (fun L₀ => 3 * (Real.sqrt L₀)⁻¹ / Real.sqrt (X L₀) + 3 * M / X L₀)
      atTop (nhds 0) := by
    simpa using h1.add h2
  have hmom : ∀ᶠ L₀ in atTop,
      |∫ s in Ioc (0 : ℝ) (X L₀ / 2), s * gammaTransportKernel s| ≤
        |∫ s in Ioi (0 : ℝ), s * gammaTransportKernel s| := by
    filter_upwards with L₀
    have hle := integral_Ioc_id_mul_kernel_le (X L₀ / 2)
    have hnn : 0 ≤ ∫ s in Ioc (0 : ℝ) (X L₀ / 2), s * gammaTransportKernel s := by
      refine setIntegral_nonneg measurableSet_Ioc fun s hs => ?_
      exact (mul_pos hs.1 (gammaTransportKernel_pos hs.1)).le
    rw [abs_of_nonneg hnn]
    exact hle.trans (le_abs_self _)
  have hprod : Tendsto
      (fun L₀ =>
        (3 * (Real.sqrt L₀)⁻¹ / Real.sqrt (X L₀) + 3 * M / X L₀) *
          ∫ s in Ioc (0 : ℝ) (X L₀ / 2), s * gammaTransportKernel s)
      atTop (nhds 0) := tendsto_zero_mul_of_eventually_bounded hcoef hmom
  have htail : Tendsto
      (fun L₀ => 4 * M * (-Real.log (1 - Real.exp (-(X L₀ / 2)))))
      atTop (nhds 0) := by
    have h := tendsto_kernelTailMass_atTop.comp
      ((tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)).comp hX)
    simpa using h.const_mul (4 * M)
  change Tendsto
    (fun L₀ =>
      (3 * (Real.sqrt L₀)⁻¹ / Real.sqrt (X L₀) + 3 * M / X L₀) *
          (∫ s in Ioc (0 : ℝ) (X L₀ / 2), s * gammaTransportKernel s) +
        4 * M * (-Real.log (1 - Real.exp (-(X L₀ / 2)))))
    atTop (nhds 0)
  simpa using hprod.add htail

/-- Upper trace numerator for the sign-free equation theorem. -/
noncomputable def signedTraceBoundNumerator
    (X : ℝ → ℝ) (M T : ℝ) (L₀ : ℝ) : ℝ :=
  T + signedTransportBound X M L₀

/-- Lower trace numerator for the sign-free equation theorem. -/
noncomputable def signedTraceBoundNumeratorLower
    (X : ℝ → ℝ) (M T : ℝ) (L₀ : ℝ) : ℝ :=
  T - signedTransportBound X M L₀

theorem tendsto_signedTraceBoundNumerator
    {X : ℝ → ℝ} {M T : ℝ} (hX : Tendsto X atTop atTop) :
    Tendsto (signedTraceBoundNumerator X M T) atTop (nhds T) := by
  change Tendsto (fun L₀ => T + signedTransportBound X M L₀) atTop (nhds T)
  simpa using (tendsto_signedTransportBound (M := M) hX).const_add T

theorem tendsto_signedTraceBoundNumeratorLower
    {X : ℝ → ℝ} {M T : ℝ} (hX : Tendsto X atTop atTop) :
    Tendsto (signedTraceBoundNumeratorLower X M T) atTop (nhds T) := by
  change Tendsto (fun L₀ => T - signedTransportBound X M L₀) atTop (nhds T)
  simpa using (tendsto_signedTransportBound (M := M) hX).const_sub T

/-- Sign-free upper trace bound at a penalized maximum. -/
theorem halfLog_base_le_of_equation_isMaxOn_signed
    {f : ℝ → ℝ} {X δ M L₀ a S T : ℝ}
    (hX : 0 < X) (hδ : 0 ≤ δ) (hFb : ∀ x, |f x| ≤ M) (hmeas : Measurable f)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hmax : IsMaxOn (penalized (fun L => Real.sqrt L * f L) δ L₀) (Ici a) X)
    (ha : a ≤ X / 2) (hL₀ : L₀ ∈ Ici a)
    (heq : logDirichlet f X + gammaTransport f X = S) (hS : S ≤ T) :
    Real.sqrt L₀ * f L₀ ≤
      (T + ((3 * δ / Real.sqrt X + 3 * M / X) *
            (∫ s in Ioc (0 : ℝ) (X / 2), s * gammaTransportKernel s) +
          4 * M * (-Real.log (1 - Real.exp (-(X / 2)))))) /
        (2 * Real.sqrt X) + halfLogAverage f X := by
  have hbase : Real.sqrt L₀ * f L₀ ≤ Real.sqrt X * f X :=
    le_value_of_isMaxOn_penalized hmax hδ hL₀
  exact hbase.trans (halfLog_le_of_equation hX heq hS
    (neg_le_gammaTransport_of_isMaxOn_signed hX hδ hFb hmeas hnear hmax ha))

/-- Sign-free lower trace bound at a penalized minimum. -/
theorem le_halfLog_base_of_equation_isMaxOn_neg_signed
    {f : ℝ → ℝ} {X δ M L₀ a S T : ℝ}
    (hX : 0 < X) (hδ : 0 ≤ δ) (hFb : ∀ x, |f x| ≤ M) (hmeas : Measurable f)
    (hnear : IntegrableOn (fun s => secondDifference f X s * gammaTransportKernel s)
      (Ioc 0 (X / 2)))
    (hmax : IsMaxOn (penalized (fun L => -(Real.sqrt L * f L)) δ L₀) (Ici a) X)
    (ha : a ≤ X / 2) (hL₀ : L₀ ∈ Ici a)
    (heq : logDirichlet f X + gammaTransport f X = S) (hS : T ≤ S) :
    (T - ((3 * δ / Real.sqrt X + 3 * M / X) *
            (∫ s in Ioc (0 : ℝ) (X / 2), s * gammaTransportKernel s) +
          4 * M * (-Real.log (1 - Real.exp (-(X / 2)))))) /
        (2 * Real.sqrt X) + halfLogAverage f X ≤ Real.sqrt L₀ * f L₀ := by
  have hbase : Real.sqrt X * f X ≤ Real.sqrt L₀ * f L₀ := by
    have := le_value_of_isMaxOn_penalized hmax hδ hL₀
    linarith
  exact (le_halfLog_of_equation hX heq hS
    (gammaTransport_le_of_isMaxOn_neg_signed hX hδ hFb hmeas hnear hmax ha)).trans hbase

/-- Equation-driven upper squeeze along a signed maximizer family. -/
theorem eventually_halfLog_le_of_equation_signed
    {F X S : ℝ → ℝ} {a M T : ℝ}
    (hFb : ∀ x, |F x| ≤ M) (hmeas : Measurable F)
    (hnear : ∀ Y, IntegrableOn (fun s => secondDifference F Y s * gammaTransportKernel s)
      (Ioc 0 (Y / 2)))
    (heq : ∀ Y, a ≤ Y → logDirichlet F Y + gammaTransport F Y = S Y)
    (hS : ∀ Y, a ≤ Y → S Y ≤ T)
    (hXmax : ∀ L₀ : ℝ, 0 < L₀ →
      IsMaxOn (penalized (fun L => Real.sqrt L * F L) (Real.sqrt L₀)⁻¹ L₀)
        (Ici a) (X L₀))
    (hXint : ∀ᶠ L₀ in atTop, a ≤ X L₀ / 2)
    (hXpos : ∀ᶠ L₀ in atTop, 0 < X L₀) :
    ∀ᶠ L₀ in atTop, Real.sqrt L₀ * F L₀ ≤
      signedTraceBoundNumerator X M T L₀ / (2 * Real.sqrt (X L₀)) +
        halfLogAverage F (X L₀) := by
  filter_upwards [hXint, hXpos, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop a]
    with L₀ hint hpos hL₀ hmem
  have hδ : (0 : ℝ) ≤ (Real.sqrt L₀)⁻¹ := by positivity
  simpa only [signedTraceBoundNumerator, signedTransportBound] using
    halfLog_base_le_of_equation_isMaxOn_signed hpos hδ hFb hmeas (hnear _)
      (hXmax L₀ hL₀) hint hmem (heq _ (by linarith)) (hS _ (by linarith))

/-- Equation-driven lower squeeze along a signed minimizer family. -/
theorem eventually_le_halfLog_of_equation_signed
    {F X S : ℝ → ℝ} {a M T : ℝ}
    (hFb : ∀ x, |F x| ≤ M) (hmeas : Measurable F)
    (hnear : ∀ Y, IntegrableOn (fun s => secondDifference F Y s * gammaTransportKernel s)
      (Ioc 0 (Y / 2)))
    (heq : ∀ Y, a ≤ Y → logDirichlet F Y + gammaTransport F Y = S Y)
    (hS : ∀ Y, a ≤ Y → T ≤ S Y)
    (hXmax : ∀ L₀ : ℝ, 0 < L₀ →
      IsMaxOn (penalized (fun L => -(Real.sqrt L * F L)) (Real.sqrt L₀)⁻¹ L₀)
        (Ici a) (X L₀))
    (hXint : ∀ᶠ L₀ in atTop, a ≤ X L₀ / 2)
    (hXpos : ∀ᶠ L₀ in atTop, 0 < X L₀) :
    ∀ᶠ L₀ in atTop,
      signedTraceBoundNumeratorLower X M T L₀ / (2 * Real.sqrt (X L₀)) +
        halfLogAverage F (X L₀) ≤ Real.sqrt L₀ * F L₀ := by
  filter_upwards [hXint, hXpos, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop a]
    with L₀ hint hpos hL₀ hmem
  have hδ : (0 : ℝ) ≤ (Real.sqrt L₀)⁻¹ := by positivity
  simpa only [signedTraceBoundNumeratorLower, signedTransportBound] using
    le_halfLog_base_of_equation_isMaxOn_neg_signed hpos hδ hFb hmeas (hnear _)
      (hXmax L₀ hL₀) hint hmem (heq _ (by linarith)) (hS _ (by linarith))

/-- Genuine signed half-log trace theorem: no positivity or one-sided numerator hypothesis. -/
theorem tendsto_halfLogTrace_of_equation_signed
    {F S : ℝ → ℝ} {a α M T Tl B : ℝ}
    (hFb : ∀ x, |F x| ≤ M) (hmeas : Measurable F)
    (hHcont : ContinuousOn (fun L => Real.sqrt L * F L) (Ici a))
    (hHup : ∀ L ∈ Ici a, Real.sqrt L * F L ≤ B)
    (hHlow : ∀ L ∈ Ici a, -B ≤ Real.sqrt L * F L)
    (hnear : ∀ Y, IntegrableOn (fun s => secondDifference F Y s * gammaTransportKernel s)
      (Ioc 0 (Y / 2)))
    (heq : ∀ Y, a ≤ Y → logDirichlet F Y + gammaTransport F Y = S Y)
    (hSu : ∀ Y, a ≤ Y → S Y ≤ T) (hSl : ∀ Y, a ≤ Y → Tl ≤ S Y)
    (hA : Tendsto (halfLogAverage F) atTop (nhds α)) :
    Tendsto (fun L => Real.sqrt L * F L) atTop (nhds α) := by
  obtain ⟨Xu, hXu⟩ := exists_maximizer_family (B := B) hHcont hHup
  obtain ⟨Xl, hXl⟩ := exists_minimizer_family (B := B) hHcont hHlow
  have hlocu := eventually_localised_of_isMaxOn_family hHup hHlow
    (fun L₀ h => (hXu L₀ h).2) (fun L₀ h => (hXu L₀ h).1)
  have hlocl := eventually_localised_of_isMaxOn_family
    (H := fun L => -(Real.sqrt L * F L))
    (fun L hL => by simpa using neg_le_neg (hHlow L hL))
    (fun L hL => by simpa using neg_le_neg (hHup L hL))
    (fun L₀ h => (hXl L₀ h).2) (fun L₀ h => (hXl L₀ h).1)
  have hXudiv := tendsto_atTop_of_localised hlocu
  have hXldiv := tendsto_atTop_of_localised hlocl
  have hXupos : ∀ᶠ L₀ in atTop, 0 < Xu L₀ := by
    filter_upwards [eventually_le_of_localised hlocu 1] with L₀ h
    linarith
  have hXlpos : ∀ᶠ L₀ in atTop, 0 < Xl L₀ := by
    filter_upwards [eventually_le_of_localised hlocl 1] with L₀ h
    linarith
  have hXuint : ∀ᶠ L₀ in atTop, a ≤ Xu L₀ / 2 := by
    filter_upwards [eventually_le_of_localised hlocu (2 * a)] with L₀ h
    linarith
  have hXlint : ∀ᶠ L₀ in atTop, a ≤ Xl L₀ / 2 := by
    filter_upwards [eventually_le_of_localised hlocl (2 * a)] with L₀ h
    linarith
  have hup := eventually_halfLog_le_of_equation_signed hFb hmeas hnear heq hSu
    (fun L₀ h => (hXu L₀ h).2) hXuint hXupos
  have hlow := eventually_le_halfLog_of_equation_signed hFb hmeas hnear heq hSl
    (fun L₀ h => (hXl L₀ h).2) hXlint hXlpos
  exact tendsto_halfLogTrace_of_convergent_families hXudiv hXldiv
    (tendsto_signedTraceBoundNumerator hXudiv)
    (tendsto_signedTraceBoundNumeratorLower hXldiv)
    hup hlow hA
    (isBoundedUnder_le_of_eventually_le hHup)
    (isBoundedUnder_ge_of_eventually_le hHlow)
    (isCoboundedUnder_le_of_eventually_le hHlow)
    (isCoboundedUnder_ge_of_eventually_le hHup)

/-- Signed theorem with averaged-trace integrability chained. -/
theorem tendsto_halfLogTrace_of_equation_of_integrable_signed
    {F S : ℝ → ℝ} {a M T Tl B L₀ : ℝ}
    (hFb : ∀ x, |F x| ≤ M) (hmeas : Measurable F) (hFcont : Continuous F)
    (hHcont : ContinuousOn (fun L => Real.sqrt L * F L) (Ici a))
    (hHup : ∀ L ∈ Ici a, Real.sqrt L * F L ≤ B)
    (hHlow : ∀ L ∈ Ici a, -B ≤ Real.sqrt L * F L)
    (hnear : ∀ Y, IntegrableOn (fun s => secondDifference F Y s * gammaTransportKernel s)
      (Ioc 0 (Y / 2)))
    (heq : ∀ Y, a ≤ Y → logDirichlet F Y + gammaTransport F Y = S Y)
    (hSu : ∀ Y, a ≤ Y → S Y ≤ T) (hSl : ∀ Y, a ≤ Y → Tl ≤ S Y)
    (hL₀ : 0 < L₀)
    (hAint : IntegrableOn
      (fun L => logDirichlet F L / (4 * L * Real.sqrt L)) (Ioi L₀)) :
    Tendsto (fun L => Real.sqrt L * F L) atTop
      (nhds (halfLogAverage F L₀ +
        ∫ x in Ioi L₀, logDirichlet F x / (4 * x * Real.sqrt x))) :=
  tendsto_halfLogTrace_of_equation_signed hFb hmeas hHcont hHup hHlow hnear heq hSu hSl
    (tendsto_halfLogAverage hFcont hL₀ hAint)

/-- Signed half-log trace for a mollified exact normal equation. Unlike the earlier mollified
capstone, this requires neither positivity of the mollified profile nor a one-sided numerator
condition at its minimizers. -/
theorem tendsto_halfLogTrace_mollified_signed
    {ρ f S : ℝ → ℝ} {ε K M Mρ a T Tl B L₀ : ℝ}
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hsupp : ∀ t, ε < |t| → ρ t = 0)
    (hfc : Continuous f) (hK : ∀ x y, |f x - f y| ≤ K * |x - y|)
    (hM : ∀ x, |f x| ≤ M) (hfz : ∀ y, y < 0 → f y = 0)
    (heq : ∀ Y, fullLogDirichlet f Y + gammaTransport f Y = S Y)
    (hmb : ∀ x, |mollify ρ f x| ≤ Mρ) (hmm : Measurable (mollify ρ f))
    (hmc : Continuous (mollify ρ f))
    (ha : 0 ≤ a)
    (hHcont : ContinuousOn (fun L => Real.sqrt L * mollify ρ f L) (Ici a))
    (hHup : ∀ L ∈ Ici a, Real.sqrt L * mollify ρ f L ≤ B)
    (hHlow : ∀ L ∈ Ici a, -B ≤ Real.sqrt L * mollify ρ f L)
    (hnear : ∀ Y, IntegrableOn
      (fun s => secondDifference (mollify ρ f) Y s * gammaTransportKernel s)
        (Ioc 0 (Y / 2)))
    (hSu : ∀ Y, a ≤ Y →
      (mollify ρ S Y + 2 * mollify (firstMomentKernel ρ) f Y) +
        fullPrimitive (mollify ρ f) 0 ≤ T)
    (hSl : ∀ Y, a ≤ Y → Tl ≤
      (mollify ρ S Y + 2 * mollify (firstMomentKernel ρ) f Y) +
        fullPrimitive (mollify ρ f) 0)
    (hL₀ : 0 < L₀)
    (hAint : IntegrableOn
      (fun L => logDirichlet (mollify ρ f) L / (4 * L * Real.sqrt L)) (Ioi L₀)) :
    Tendsto (fun L => Real.sqrt L * mollify ρ f L) atTop
      (nhds (halfLogAverage (mollify ρ f) L₀ +
        ∫ x in Ioi L₀,
          logDirichlet (mollify ρ f) x / (4 * x * Real.sqrt x))) :=
  tendsto_halfLogTrace_of_equation_of_integrable_signed hmb hmm hmc hHcont hHup hHlow hnear
    (fun _ hY => mollified_equation_halfLine hρ hcρ hsupp hfc hK hM hfz hmb hmm heq
      (le_trans ha hY)) hSu hSl hL₀ hAint

end GaloisForLFunctions.HTGeometry
