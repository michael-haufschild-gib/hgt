import GaloisForLFunctions.HilbertMetric.FourthJetCoalescedCusp
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedLocalThreePoint

/-!
# Fourth center jet and the coalesced Hedenmalm cusp

The arbitrary derivative-product integral already available for the center-mixed theta density
contains all higher center jets.  This file extracts the third through fifth jets, proves their
derivative chain and odd cancellation at the reflection center, and connects a strict fourth
Hankel jet to a nested positive-definite three-point cusp.

The final transfer theorem is generic in the one remaining source inequality.  It introduces no
positivity or Riemann-hypothesis assumption: whenever the displayed, concrete fourth jet has the
strict sign, the cusp follows by the unconditional derivative and matrix algebra below.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Third center derivative of the center-mixed density. -/
def thetaCuspCenterMixedDensityThirdJet (a t : ℝ) : ℝ :=
  thetaCuspCenterMixedDerivativeProductIntegral 3 0 a t -
    3 * thetaCuspCenterMixedDerivativeProductIntegral 2 1 a t +
      3 * thetaCuspCenterMixedDerivativeProductIntegral 1 2 a t -
        thetaCuspCenterMixedDerivativeProductIntegral 0 3 a t

/-- Fourth center derivative of the center-mixed density. -/
def thetaCuspCenterMixedDensityFourthJet (a t : ℝ) : ℝ :=
  thetaCuspCenterMixedDerivativeProductIntegral 4 0 a t -
    4 * thetaCuspCenterMixedDerivativeProductIntegral 3 1 a t +
      6 * thetaCuspCenterMixedDerivativeProductIntegral 2 2 a t -
        4 * thetaCuspCenterMixedDerivativeProductIntegral 1 3 a t +
          thetaCuspCenterMixedDerivativeProductIntegral 0 4 a t

/-- Fifth center derivative of the center-mixed density. -/
def thetaCuspCenterMixedDensityFifthJet (a t : ℝ) : ℝ :=
  thetaCuspCenterMixedDerivativeProductIntegral 5 0 a t -
    5 * thetaCuspCenterMixedDerivativeProductIntegral 4 1 a t +
      10 * thetaCuspCenterMixedDerivativeProductIntegral 3 2 a t -
        10 * thetaCuspCenterMixedDerivativeProductIntegral 2 3 a t +
          5 * thetaCuspCenterMixedDerivativeProductIntegral 1 4 a t -
            thetaCuspCenterMixedDerivativeProductIntegral 0 5 a t

theorem hasDerivAt_thetaCuspCenterMixedDensitySecondJet
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    HasDerivAt (thetaCuspCenterMixedDensitySecondJet a)
      (thetaCuspCenterMixedDensityThirdJet a t) t := by
  have h20 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 2 0 t
  have h11 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 1 1 t
  have h02 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 0 2 t
  unfold thetaCuspCenterMixedDensitySecondJet thetaCuspCenterMixedDensityThirdJet
  convert (h20.sub (h11.const_mul 2)).add h02 using 1
  all_goals first | rfl | ring

theorem hasDerivAt_thetaCuspCenterMixedDensityThirdJet
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    HasDerivAt (thetaCuspCenterMixedDensityThirdJet a)
      (thetaCuspCenterMixedDensityFourthJet a t) t := by
  have h30 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 3 0 t
  have h21 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 2 1 t
  have h12 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 1 2 t
  have h03 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 0 3 t
  unfold thetaCuspCenterMixedDensityThirdJet thetaCuspCenterMixedDensityFourthJet
  convert (((h30.sub (h21.const_mul 3)).add (h12.const_mul 3)).sub h03) using 1
  all_goals first | rfl | ring

theorem hasDerivAt_thetaCuspCenterMixedDensityFourthJet
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    HasDerivAt (thetaCuspCenterMixedDensityFourthJet a)
      (thetaCuspCenterMixedDensityFifthJet a t) t := by
  have h40 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 4 0 t
  have h31 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 3 1 t
  have h22 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 2 2 t
  have h13 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 1 3 t
  have h04 := hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha 0 4 t
  unfold thetaCuspCenterMixedDensityFourthJet thetaCuspCenterMixedDensityFifthJet
  convert ((((h40.sub (h31.const_mul 4)).add (h22.const_mul 6)).sub
    (h13.const_mul 4)).add h04) using 1
  all_goals first | rfl | ring

theorem continuous_thetaCuspCenterMixedDensityFifthJet
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    Continuous (thetaCuspCenterMixedDensityFifthJet a) := by
  have hcont (m n : ℕ) :
      Continuous (thetaCuspCenterMixedDerivativeProductIntegral m n a) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha m n t).continuousAt
  unfold thetaCuspCenterMixedDensityFifthJet
  fun_prop

theorem thetaCuspCenterMixedDensityThirdJet_zero
    (a : ℝ) :
    thetaCuspCenterMixedDensityThirdJet a 0 = 0 := by
  rw [thetaCuspCenterMixedDensityThirdJet,
    thetaCuspCenterMixedDerivativeProductIntegral_zero_comm 3 0,
    thetaCuspCenterMixedDerivativeProductIntegral_zero_comm 2 1]
  ring

theorem thetaCuspCenterMixedDensityFifthJet_zero
    (a : ℝ) :
    thetaCuspCenterMixedDensityFifthJet a 0 = 0 := by
  rw [thetaCuspCenterMixedDensityFifthJet,
    thetaCuspCenterMixedDerivativeProductIntegral_zero_comm 5 0,
    thetaCuspCenterMixedDerivativeProductIntegral_zero_comm 4 1,
    thetaCuspCenterMixedDerivativeProductIntegral_zero_comm 3 2]
  ring

/-- A strict fourth derivative Hankel determinant opens the coalesced scalar wall for the actual
center-mixed theta density. -/
theorem exists_thetaCuspCenterMixedCoalescedWall_pos_right_of_fourthJet
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hfourth :
      0 < thetaCuspCenterMixedDensity a 0 *
          thetaCuspCenterMixedDensityFourthJet a 0 -
        thetaCuspCenterMixedDensitySecondJet a 0 ^ 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y, 0 < y → y < δ →
      0 < HilbertMetric.threePointCoalescedWall
        (thetaCuspCenterMixedDensity a)
        (thetaCuspCenterMixedDensityFirstJet a)
        (thetaCuspCenterMixedDensitySecondJet a) y := by
  exact HilbertMetric.exists_threePointCoalescedWall_pos_right
    (fun t => hasDerivAt_thetaCuspCenterMixedDensity ha0.le ha t)
    (fun t => hasDerivAt_thetaCuspCenterMixedDensityFirstJet ha0.le ha t)
    (fun t => hasDerivAt_thetaCuspCenterMixedDensitySecondJet ha0.le ha t)
    (fun t => hasDerivAt_thetaCuspCenterMixedDensityThirdJet ha0.le ha t)
    (fun t => hasDerivAt_thetaCuspCenterMixedDensityFourthJet ha0.le ha t)
    (continuous_thetaCuspCenterMixedDensityFifthJet ha0.le ha)
    (thetaCuspCenterMixedDensityFirstJet_zero a)
    (thetaCuspCenterMixedDensityThirdJet_zero a)
    (thetaCuspCenterMixedDensitySecondJet_zero_neg ha0 ha)
    hfourth

/-- **Fourth-jet coalesced cusp transfer.**  Once the concrete strict fourth center jet is
positive, every sufficiently small positive second gap admits a positive first-gap interval of
positive-definite actual theta three-point matrices. -/
theorem exists_thetaCuspCenterMixed_coalescedCusp_posDef_of_fourthJet
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hfourth :
      0 < thetaCuspCenterMixedDensity a 0 *
          thetaCuspCenterMixedDensityFourthJet a 0 -
        thetaCuspCenterMixedDensitySecondJet a 0 ^ 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, 0 < y → y < δ →
      ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, 0 < x → x < ε →
        Matrix.PosDef (thetaCuspCenterMixedThreePointMatrix a x y) := by
  rcases exists_thetaCuspCenterMixedCoalescedWall_pos_right_of_fourthJet
      ha0 ha hfourth with ⟨δ, hδ, hwall⟩
  refine ⟨δ, hδ, fun y hy hyδ => ?_⟩
  let f := thetaCuspCenterMixedDensity a
  have hlocal := HilbertMetric.exists_threePointCorrelationDeterminantPath_pos_right
    (fun t => hasDerivAt_thetaCuspCenterMixedDensity ha0.le ha t)
    (fun t => hasDerivAt_thetaCuspCenterMixedDensityFirstJet ha0.le ha t)
    (continuous_thetaCuspCenterMixedDensitySecondJet ha0.le ha)
    (thetaCuspCenterMixedDensityFirstJet_zero a)
    (hwall y hy hyδ)
  rcases hlocal with ⟨ε, hε, hdet⟩
  refine ⟨ε, hε, fun x hx hxε => ?_⟩
  have hdetpos :
      0 < HilbertMetric.threePointCorrelationDeterminantPath f y x :=
    hdet x hx hxε
  have hfx0 : 0 ≤ f x := (thetaCuspCenterMixedDensity_pos ha0 ha x).le
  have hfxlt : f x < f 0 := thetaCuspCenterMixedDensity_lt_zero ha0 ha hx
  have hposdef := (HilbertMetric.threePointCorrelationMatrix_posDef_iff
    (thetaCuspCenterMixedDensity_pos ha0 ha 0) hfx0 hfxlt).2 hdetpos
  simpa [thetaCuspCenterMixedThreePointMatrix,
    HilbertMetric.threePointCorrelationDeterminantPath, f] using hposdef

end

end RHTower
