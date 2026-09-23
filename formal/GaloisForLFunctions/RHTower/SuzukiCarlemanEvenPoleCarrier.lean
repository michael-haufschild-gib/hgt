import GaloisForLFunctions.RHTower.SuzukiOneSidedCarlemanSeam

/-!
# Suzuki's even right-sheet pole carrier

For the odd phase-one Suzuki source, reflection exchanges the two compact convolution triangles:

`TLeft z = -TRight (-z)`.

Together with `TRight + TLeft = interior`, this fixes the reflection-odd part of the right triangle
to one half of the compact interval channel.  Since the zero-shift Xi multiplier and the phase-one
characteristic are both odd, their product is even.  Consequently the projected sine clock is
exactly the entire odd half of the right Carleman sheet, while every possible Xi pole lies in one
even carrier

`M W - (TRight z + TRight (-z)) / 2`.

This file proves the dependency-closed parity allocation and connects upper-half-plane analyticity
of that even carrier exactly to RH.  It does not assume or assert the missing Euler--Gamma
continuation theorem.

No estimate, numerical computation, RH assumption, or unproved positivity premise is used.
-/

open Complex GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Reflection projections -/

/-- Reflection-even part of a complex spectral function. -/
def suzukiReflectionEvenPart (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (F z + F (-z)) / 2

/-- Reflection-odd part of a complex spectral function. -/
def suzukiReflectionOddPart (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (F z - F (-z)) / 2

theorem suzukiReflectionEvenPart_add_oddPart (F : ℂ → ℂ) (z : ℂ) :
    suzukiReflectionEvenPart F z + suzukiReflectionOddPart F z = F z := by
  simp only [suzukiReflectionEvenPart, suzukiReflectionOddPart]
  ring

/-! ## The physical triangle fixes the odd half -/

/-- Reflection of an odd compact source through an even convolution kernel exchanges the two
triangles with a minus sign.  Once their sum is the compact interval channel, the odd part of the
right triangle is exactly half that channel. -/
theorem suzukiRightTriangle_oddPart_eq_half_interior
    (rightTriangle leftTriangle interior : ℂ → ℂ)
    (hreflect : ∀ z, leftTriangle z = -rightTriangle (-z))
    (hsum : ∀ z,
      suzukiCarlemanInteriorPart rightTriangle leftTriangle z = interior z)
    (z : ℂ) :
    suzukiReflectionOddPart rightTriangle z = (2 : ℂ)⁻¹ * interior z := by
  have h := hsum z
  rw [suzukiCarlemanInteriorPart, hreflect z] at h
  rw [suzukiReflectionOddPart, ← h]
  ring

/-! ## The even pole carrier -/

/-- The reflection-even component left after removing the even half of the right triangle from the
zero-shift multiplier channel. -/
def suzukiEvenCarlemanPoleCarrier
    (M W rightTriangle : ℂ → ℂ) (z : ℂ) : ℂ :=
  M z * W z - suzukiReflectionEvenPart rightTriangle z

/-- Odd multiplier and odd characteristic make the pole carrier even. -/
theorem suzukiEvenCarlemanPoleCarrier_even
    {M W : ℂ → ℂ} (hM : Function.Odd M) (hW : Function.Odd W)
    (rightTriangle : ℂ → ℂ) :
    Function.Even (suzukiEvenCarlemanPoleCarrier M W rightTriangle) := by
  intro z
  simp only [suzukiEvenCarlemanPoleCarrier, suzukiReflectionEvenPart,
    hM z, hW z, neg_neg]
  ring

/-- The even carrier is literally the reflection-even part of the selected right sheet. -/
theorem suzukiEvenCarlemanPoleCarrier_eq_evenPart_rightSheet
    {M W : ℂ → ℂ} (hM : Function.Odd M) (hW : Function.Odd W)
    (rightTriangle : ℂ → ℂ) (z : ℂ) :
    suzukiEvenCarlemanPoleCarrier M W rightTriangle z =
      suzukiReflectionEvenPart
        (suzukiCarlemanRightSheet M W rightTriangle) z := by
  simp only [suzukiEvenCarlemanPoleCarrier, suzukiReflectionEvenPart,
    suzukiCarlemanRightSheet, hM z, hW z]
  ring

/-- Exact right-sheet decomposition: its only non-even component is minus one half of the compact
interval channel. -/
theorem suzukiCarlemanRightSheet_eq_evenPoleCarrier_sub_halfInterior
    (M W rightTriangle leftTriangle interior : ℂ → ℂ)
    (hreflect : ∀ z, leftTriangle z = -rightTriangle (-z))
    (hsum : ∀ z,
      suzukiCarlemanInteriorPart rightTriangle leftTriangle z = interior z)
    (z : ℂ) :
    suzukiCarlemanRightSheet M W rightTriangle z =
      suzukiEvenCarlemanPoleCarrier M W rightTriangle z - (2 : ℂ)⁻¹ * interior z := by
  have hodd := suzukiRightTriangle_oddPart_eq_half_interior
    rightTriangle leftTriangle interior hreflect hsum z
  rw [suzukiCarlemanRightSheet, suzukiEvenCarlemanPoleCarrier,
    ← suzukiReflectionEvenPart_add_oddPart rightTriangle z, hodd]
  ring

/-- Adding the entire half-interior term does not change the local continuation problem. -/
theorem analyticAt_suzukiCarlemanRightSheet_iff_evenPoleCarrier
    (M W rightTriangle leftTriangle interior : ℂ → ℂ)
    (hreflect : ∀ z, leftTriangle z = -rightTriangle (-z))
    (hsum : ∀ z,
      suzukiCarlemanInteriorPart rightTriangle leftTriangle z = interior z)
    {z : ℂ} (hI : AnalyticAt ℂ interior z) :
    AnalyticAt ℂ (suzukiCarlemanRightSheet M W rightTriangle) z ↔
      AnalyticAt ℂ (suzukiEvenCarlemanPoleCarrier M W rightTriangle) z := by
  have hhalf : AnalyticAt ℂ (fun w => (2 : ℂ)⁻¹ * interior w) z :=
    analyticAt_const.mul hI
  have hright :
      suzukiCarlemanRightSheet M W rightTriangle =
        fun w => suzukiEvenCarlemanPoleCarrier M W rightTriangle w -
          (2 : ℂ)⁻¹ * interior w := by
    funext w
    exact suzukiCarlemanRightSheet_eq_evenPoleCarrier_sub_halfInterior
      M W rightTriangle leftTriangle interior hreflect hsum w
  have hcarrier :
      suzukiEvenCarlemanPoleCarrier M W rightTriangle =
        fun w => suzukiCarlemanRightSheet M W rightTriangle w +
          (2 : ℂ)⁻¹ * interior w := by
    funext w
    have h := congrFun hright w
    calc
      suzukiEvenCarlemanPoleCarrier M W rightTriangle w =
          (suzukiEvenCarlemanPoleCarrier M W rightTriangle w -
            (2 : ℂ)⁻¹ * interior w) + (2 : ℂ)⁻¹ * interior w := by ring
      _ = suzukiCarlemanRightSheet M W rightTriangle w +
          (2 : ℂ)⁻¹ * interior w := by rw [← h]
  constructor
  · intro hR
    rw [hcarrier]
    exact hR.add hhalf
  · intro hC
    rw [hright]
    exact hC.sub hhalf

/-! ## Opposite parity after admissible two-shift sewing -/

/-- Reflection of an even compact source through an even convolution kernel exchanges the two
triangles without a sign.  Their compact interval sum therefore fixes the even part of the right
triangle. -/
theorem suzukiRightTriangle_evenPart_eq_half_interior
    (rightTriangle leftTriangle interior : ℂ → ℂ)
    (hreflect : ∀ z, leftTriangle z = rightTriangle (-z))
    (hsum : ∀ z,
      suzukiCarlemanInteriorPart rightTriangle leftTriangle z = interior z)
    (z : ℂ) :
    suzukiReflectionEvenPart rightTriangle z = (2 : ℂ)⁻¹ * interior z := by
  have h := hsum z
  rw [suzukiCarlemanInteriorPart, hreflect z] at h
  rw [suzukiReflectionEvenPart, ← h]
  ring

/-- The reflection-odd component left after removing the odd half of the right triangle from an
odd-multiplier/even-characteristic channel. -/
def suzukiOddCarlemanPoleCarrier
    (M W rightTriangle : ℂ → ℂ) (z : ℂ) : ℂ :=
  M z * W z - suzukiReflectionOddPart rightTriangle z

/-- Odd multiplier and even characteristic make the complementary pole carrier odd. -/
theorem suzukiOddCarlemanPoleCarrier_odd
    {M W : ℂ → ℂ} (hM : Function.Odd M) (hW : Function.Even W)
    (rightTriangle : ℂ → ℂ) :
    Function.Odd (suzukiOddCarlemanPoleCarrier M W rightTriangle) := by
  intro z
  simp only [suzukiOddCarlemanPoleCarrier, suzukiReflectionOddPart,
    hM z, hW z, neg_neg]
  ring

/-- The odd carrier is literally the reflection-odd part of the selected right sheet. -/
theorem suzukiOddCarlemanPoleCarrier_eq_oddPart_rightSheet
    {M W : ℂ → ℂ} (hM : Function.Odd M) (hW : Function.Even W)
    (rightTriangle : ℂ → ℂ) (z : ℂ) :
    suzukiOddCarlemanPoleCarrier M W rightTriangle z =
      suzukiReflectionOddPart
        (suzukiCarlemanRightSheet M W rightTriangle) z := by
  simp only [suzukiOddCarlemanPoleCarrier, suzukiReflectionOddPart,
    suzukiCarlemanRightSheet, hM z, hW z]
  ring

/-- Exact right-sheet decomposition for an even effective source: its entire compact interval is
the even half, while every possible arithmetic pole lies in the odd carrier. -/
theorem suzukiCarlemanRightSheet_eq_oddPoleCarrier_sub_halfInterior
    (M W rightTriangle leftTriangle interior : ℂ → ℂ)
    (hreflect : ∀ z, leftTriangle z = rightTriangle (-z))
    (hsum : ∀ z,
      suzukiCarlemanInteriorPart rightTriangle leftTriangle z = interior z)
    (z : ℂ) :
    suzukiCarlemanRightSheet M W rightTriangle z =
      suzukiOddCarlemanPoleCarrier M W rightTriangle z - (2 : ℂ)⁻¹ * interior z := by
  have heven := suzukiRightTriangle_evenPart_eq_half_interior
    rightTriangle leftTriangle interior hreflect hsum z
  rw [suzukiCarlemanRightSheet, suzukiOddCarlemanPoleCarrier,
    ← suzukiReflectionEvenPart_add_oddPart rightTriangle z, heven]
  ring

/-- Adding the entire even half-interior does not change the local continuation problem. -/
theorem analyticAt_suzukiCarlemanRightSheet_iff_oddPoleCarrier
    (M W rightTriangle leftTriangle interior : ℂ → ℂ)
    (hreflect : ∀ z, leftTriangle z = rightTriangle (-z))
    (hsum : ∀ z,
      suzukiCarlemanInteriorPart rightTriangle leftTriangle z = interior z)
    {z : ℂ} (hI : AnalyticAt ℂ interior z) :
    AnalyticAt ℂ (suzukiCarlemanRightSheet M W rightTriangle) z ↔
      AnalyticAt ℂ (suzukiOddCarlemanPoleCarrier M W rightTriangle) z := by
  have hhalf : AnalyticAt ℂ (fun w => (2 : ℂ)⁻¹ * interior w) z :=
    analyticAt_const.mul hI
  have hright :
      suzukiCarlemanRightSheet M W rightTriangle =
        fun w => suzukiOddCarlemanPoleCarrier M W rightTriangle w -
          (2 : ℂ)⁻¹ * interior w := by
    funext w
    exact suzukiCarlemanRightSheet_eq_oddPoleCarrier_sub_halfInterior
      M W rightTriangle leftTriangle interior hreflect hsum w
  have hcarrier :
      suzukiOddCarlemanPoleCarrier M W rightTriangle =
        fun w => suzukiCarlemanRightSheet M W rightTriangle w +
          (2 : ℂ)⁻¹ * interior w := by
    funext w
    have h := congrFun hright w
    calc
      suzukiOddCarlemanPoleCarrier M W rightTriangle w =
          (suzukiOddCarlemanPoleCarrier M W rightTriangle w -
            (2 : ℂ)⁻¹ * interior w) + (2 : ℂ)⁻¹ * interior w := by ring
      _ = suzukiCarlemanRightSheet M W rightTriangle w +
          (2 : ℂ)⁻¹ * interior w := by rw [← h]
  constructor
  · intro hR
    rw [hcarrier]
    exact hR.add hhalf
  · intro hC
    rw [hright]
    exact hC.sub hhalf

/-! ### The sheet-jump invariant -/

/-- The carrier before choosing source parity: subtract half the physical triangle imbalance from
the arithmetic multiplier channel. -/
def suzukiCarlemanJumpPoleCarrier
    (M W rightTriangle leftTriangle : ℂ → ℂ) (z : ℂ) : ℂ :=
  M z * W z - (rightTriangle z - leftTriangle z) / 2

/-- The jump carrier is exactly one half of the difference of the continued right and left
Carleman sheets. -/
theorem two_mul_suzukiCarlemanJumpPoleCarrier_eq_sheet_difference
    (M W rightTriangle leftTriangle : ℂ → ℂ) (z : ℂ) :
    2 * suzukiCarlemanJumpPoleCarrier M W rightTriangle leftTriangle z =
      suzukiCarlemanRightSheet M W rightTriangle z -
        suzukiCarlemanLeftSheet M W leftTriangle z := by
  simp only [suzukiCarlemanJumpPoleCarrier, suzukiCarlemanRightSheet,
    suzukiCarlemanLeftSheet]
  ring

/-- For an odd source, the parity-even carrier is the sheet-jump carrier. -/
theorem suzukiCarlemanJumpPoleCarrier_eq_evenPoleCarrier
    (M W rightTriangle leftTriangle : ℂ → ℂ)
    (hreflect : ∀ z, leftTriangle z = -rightTriangle (-z)) (z : ℂ) :
    suzukiCarlemanJumpPoleCarrier M W rightTriangle leftTriangle z =
      suzukiEvenCarlemanPoleCarrier M W rightTriangle z := by
  simp only [suzukiCarlemanJumpPoleCarrier, suzukiEvenCarlemanPoleCarrier,
    suzukiReflectionEvenPart, hreflect z]
  ring

/-- For an even source, the parity-odd carrier is the same sheet-jump carrier. -/
theorem suzukiCarlemanJumpPoleCarrier_eq_oddPoleCarrier
    (M W rightTriangle leftTriangle : ℂ → ℂ)
    (hreflect : ∀ z, leftTriangle z = rightTriangle (-z)) (z : ℂ) :
    suzukiCarlemanJumpPoleCarrier M W rightTriangle leftTriangle z =
      suzukiOddCarlemanPoleCarrier M W rightTriangle z := by
  simp only [suzukiCarlemanJumpPoleCarrier, suzukiOddCarlemanPoleCarrier,
    suzukiReflectionOddPart, hreflect z]

/-! ### The affine-sewn source really has the opposite parity -/

/-- Product of two odd source characteristics is even, including the affine sewing scalar. -/
theorem suzukiAffineSewnCharacteristic_even_of_odd
    {WAlpha WBeta : ℂ → ℂ}
    (hWAlpha : Function.Odd WAlpha) (hWBeta : Function.Odd WBeta)
    (alpha beta : ℂ) :
    Function.Even (suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta) := by
  intro z
  simp only [suzukiAffineSewnCharacteristic, hWAlpha z, hWBeta z]
  ring

/-- Sewing two odd source characteristics converts the two individual minus-reflection laws into
a plus-reflection law for the sewn triangles. -/
theorem suzukiAffineSewnTriangle_reflection_of_odd
    {WAlpha WBeta rightAlpha rightBeta leftAlpha leftBeta : ℂ → ℂ}
    (hWAlpha : Function.Odd WAlpha) (hWBeta : Function.Odd WBeta)
    (hreflectAlpha : ∀ z, leftAlpha z = -rightAlpha (-z))
    (hreflectBeta : ∀ z, leftBeta z = -rightBeta (-z))
    (alpha beta gamma z : ℂ) :
    suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
        leftAlpha leftBeta z =
      suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
        rightAlpha rightBeta (-z) := by
  simp only [suzukiAffineSewnIntervalPart, hreflectAlpha z, hreflectBeta z,
    hWAlpha z, hWBeta z]
  ring

/-- Affine sewing commutes exactly with the sum of the two physical convolution triangles. -/
theorem suzukiAffineSewnCarlemanInteriorPart
    (alpha beta gamma : ℂ)
    (WAlpha WBeta rightAlpha rightBeta leftAlpha leftBeta : ℂ → ℂ) (z : ℂ) :
    suzukiCarlemanInteriorPart
        (suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
          rightAlpha rightBeta)
        (suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
          leftAlpha leftBeta) z =
      suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
        (suzukiCarlemanInteriorPart rightAlpha leftAlpha)
        (suzukiCarlemanInteriorPart rightBeta leftBeta) z := by
  simp only [suzukiCarlemanInteriorPart, suzukiAffineSewnIntervalPart]
  ring

/-- The projected sine clock computes the total sewn compact interval, not either sewn triangle
separately.  This is the exact connector between physical one-sided triangles and the existing
projected source theorem. -/
theorem suzukiAffineSewnCarlemanInteriorPart_projectedSineClock
    (a : ℝ) (alpha beta gamma AAlpha ABeta : ℂ)
    (WAlpha WBeta rightAlpha rightBeta leftAlpha leftBeta : ℂ → ℂ)
    (hsumAlpha : ∀ z,
      suzukiCarlemanInteriorPart rightAlpha leftAlpha z =
        suzukiProjectedSineClock a AAlpha z)
    (hsumBeta : ∀ z,
      suzukiCarlemanInteriorPart rightBeta leftBeta z =
        suzukiProjectedSineClock a ABeta z)
    (z : ℂ) :
    suzukiCarlemanInteriorPart
        (suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
          rightAlpha rightBeta)
        (suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
          leftAlpha leftBeta) z =
      suzukiProjectedSineClock a 1 z *
        ((beta - gamma) * WBeta z * AAlpha -
          (alpha - gamma) * WAlpha z * ABeta) := by
  rw [suzukiAffineSewnCarlemanInteriorPart]
  simp only [suzukiAffineSewnIntervalPart, hsumAlpha z, hsumBeta z]
  simp only [suzukiProjectedSineClock]
  ring

/-- For two odd source characteristics, the existing projected clock is exactly twice the even
part of the admissible sewn right triangle. -/
theorem suzukiAffineSewnRightTriangle_evenPart_eq_half_projectedSineClock
    (a : ℝ) (alpha beta gamma AAlpha ABeta : ℂ)
    (WAlpha WBeta rightAlpha rightBeta leftAlpha leftBeta : ℂ → ℂ)
    (hWAlpha : Function.Odd WAlpha) (hWBeta : Function.Odd WBeta)
    (hreflectAlpha : ∀ z, leftAlpha z = -rightAlpha (-z))
    (hreflectBeta : ∀ z, leftBeta z = -rightBeta (-z))
    (hsumAlpha : ∀ z,
      suzukiCarlemanInteriorPart rightAlpha leftAlpha z =
        suzukiProjectedSineClock a AAlpha z)
    (hsumBeta : ∀ z,
      suzukiCarlemanInteriorPart rightBeta leftBeta z =
        suzukiProjectedSineClock a ABeta z)
    (z : ℂ) :
    suzukiReflectionEvenPart
        (suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
          rightAlpha rightBeta) z =
      (2 : ℂ)⁻¹ *
        (suzukiProjectedSineClock a 1 z *
          ((beta - gamma) * WBeta z * AAlpha -
            (alpha - gamma) * WAlpha z * ABeta)) := by
  apply suzukiRightTriangle_evenPart_eq_half_interior
    (suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
      rightAlpha rightBeta)
    (suzukiAffineSewnIntervalPart alpha beta gamma WAlpha WBeta
      leftAlpha leftBeta)
    (fun w => suzukiProjectedSineClock a 1 w *
      ((beta - gamma) * WBeta w * AAlpha -
        (alpha - gamma) * WAlpha w * ABeta))
  · intro w
    exact suzukiAffineSewnTriangle_reflection_of_odd hWAlpha hWBeta
      hreflectAlpha hreflectBeta alpha beta gamma w
  · intro w
    exact suzukiAffineSewnCarlemanInteriorPart_projectedSineClock
      a alpha beta gamma AAlpha ABeta WAlpha WBeta
      rightAlpha rightBeta leftAlpha leftBeta hsumAlpha hsumBeta w

/-- The admissible two-shift right-sheet pole carrier at target shift zero. -/
def suzukiAffineSewnOddCarlemanPoleCarrier
    (alpha beta : ℂ)
    (WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiOddCarlemanPoleCarrier (suzukiShiftedXiMultiplier 0)
    (suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta)
    (suzukiAffineSewnIntervalPart alpha beta 0 WAlpha WBeta rightAlpha rightBeta) z

/-- The actual admissible two-shift carrier is odd. -/
theorem suzukiAffineSewnOddCarlemanPoleCarrier_odd
    {WAlpha WBeta : ℂ → ℂ}
    (hWAlpha : Function.Odd WAlpha) (hWBeta : Function.Odd WBeta)
    (alpha beta : ℂ) (rightAlpha rightBeta : ℂ → ℂ) :
    Function.Odd
      (suzukiAffineSewnOddCarlemanPoleCarrier alpha beta
        WAlpha WBeta rightAlpha rightBeta) := by
  exact suzukiOddCarlemanPoleCarrier_odd suzukiZeroShiftMultiplier_odd
    (suzukiAffineSewnCharacteristic_even_of_odd hWAlpha hWBeta alpha beta)
    (suzukiAffineSewnIntervalPart alpha beta 0 WAlpha WBeta rightAlpha rightBeta)

/-- **Admissible sewn odd-carrier RH criterion.**  Two distinct actual source shifts remove the
need for zero-shift source admissibility.  Their sewn right sheet is analytic off the real axis
exactly when its odd pole carrier is, because the sewn compact interval is its entire even half. -/
theorem riemannHypothesis_iff_suzukiAffineSewnOddCarlemanPoleCarrier_analytic_offReal
    {alpha beta : ℂ}
    {WAlpha WBeta rightAlpha rightBeta leftAlpha leftBeta : ℂ → ℂ}
    (hab : alpha ≠ beta)
    (hWAlpha : ∀ z, AnalyticAt ℂ WAlpha z)
    (hWBeta : ∀ z, AnalyticAt ℂ WBeta z)
    (hRAlpha : ∀ z, AnalyticAt ℂ rightAlpha z)
    (hRBeta : ∀ z, AnalyticAt ℂ rightBeta z)
    (hLAlpha : ∀ z, AnalyticAt ℂ leftAlpha z)
    (hLBeta : ∀ z, AnalyticAt ℂ leftBeta z)
    (hrealAlpha : ∀ z, WAlpha z = 0 → z.im = 0)
    (hrealBeta : ∀ z, WBeta z = 0 → z.im = 0)
    (hoddAlpha : Function.Odd WAlpha) (hoddBeta : Function.Odd WBeta)
    (hreflectAlpha : ∀ z, leftAlpha z = -rightAlpha (-z))
    (hreflectBeta : ∀ z, leftBeta z = -rightBeta (-z)) :
    RiemannHypothesis ↔
      ∀ z : ℂ, z.im ≠ 0 →
        AnalyticAt ℂ
          (suzukiAffineSewnOddCarlemanPoleCarrier alpha beta
            WAlpha WBeta rightAlpha rightBeta) z := by
  let P : ℂ → ℂ := suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta
  let right : ℂ → ℂ :=
    suzukiAffineSewnIntervalPart alpha beta 0 WAlpha WBeta rightAlpha rightBeta
  let left : ℂ → ℂ :=
    suzukiAffineSewnIntervalPart alpha beta 0 WAlpha WBeta leftAlpha leftBeta
  let interior : ℂ → ℂ := suzukiCarlemanInteriorPart right left
  have hright : ∀ z, AnalyticAt ℂ right z := fun z =>
    analyticAt_suzukiAffineSewnIntervalPart
      (hWAlpha z) (hWBeta z) (hRAlpha z) (hRBeta z)
  have hleft : ∀ z, AnalyticAt ℂ left z := fun z =>
    analyticAt_suzukiAffineSewnIntervalPart
      (hWAlpha z) (hWBeta z) (hLAlpha z) (hLBeta z)
  have hinterior : ∀ z, AnalyticAt ℂ interior z := fun z =>
    (hright z).add (hleft z)
  have hreflect : ∀ z, left z = right (-z) := fun z =>
    suzukiAffineSewnTriangle_reflection_of_odd hoddAlpha hoddBeta
      hreflectAlpha hreflectBeta alpha beta 0 z
  have hbase :=
    riemannHypothesis_iff_suzukiAffineSewnExterior_analytic_offReal
      (gamma := 0) hab hWAlpha hWBeta hRAlpha hRBeta hrealAlpha hrealBeta
  have hsew :
      suzukiAffineSewnExterior alpha beta 0 WAlpha WBeta rightAlpha rightBeta =
        suzukiCarlemanRightSheet (suzukiShiftedXiMultiplier 0) P right := by
    funext z
    rw [suzukiAffineSewnExterior_eq_zeroShift]
    rfl
  rw [hsew] at hbase
  constructor
  · intro hRH z hz
    have hs := hbase.mp hRH z hz
    exact (analyticAt_suzukiCarlemanRightSheet_iff_oddPoleCarrier
      (suzukiShiftedXiMultiplier 0) P right left interior hreflect
      (fun _ => rfl) (hinterior z)).mp hs
  · intro hc
    apply hbase.mpr
    intro z hz
    exact (analyticAt_suzukiCarlemanRightSheet_iff_oddPoleCarrier
      (suzukiShiftedXiMultiplier 0) P right left interior hreflect
      (fun _ => rfl) (hinterior z)).mpr (hc z hz)

/-! ## Suzuki phase-one specialization and RH connector -/

/-- At zero shift and phase one, the carrier is even by the already-proved Suzuki source parity. -/
theorem suzukiZeroShiftPhaseOneEvenCarlemanPoleCarrier_even
    {A E : ℂ → ℂ} (hpar : SuzukiParityPair A E) (rightTriangle : ℂ → ℂ) :
    Function.Even
      (suzukiEvenCarlemanPoleCarrier (suzukiShiftedXiMultiplier 0)
        (suzukiCharacteristicPencil A E 1) rightTriangle) := by
  exact suzukiEvenCarlemanPoleCarrier_even suzukiZeroShiftMultiplier_odd
    (fun z => suzukiCharacteristicPencil_one_odd hpar z) rightTriangle

/-- For the projected compact interval law, the entire odd half of the right sheet is exactly the
negative sine clock `-A sin(a z)`. -/
theorem suzukiZeroShiftPhaseOneRightSheet_eq_evenPoleCarrier_sub_sine
    (A E rightTriangle leftTriangle : ℂ → ℂ) (a : ℝ) (endpointSum : ℂ)
    (hreflect : ∀ z, leftTriangle z = -rightTriangle (-z))
    (hsum : ∀ z,
      suzukiCarlemanInteriorPart rightTriangle leftTriangle z =
        suzukiProjectedSineClock a endpointSum z)
    (z : ℂ) :
    suzukiCarlemanRightSheet (suzukiShiftedXiMultiplier 0)
        (suzukiCharacteristicPencil A E 1) rightTriangle z =
      suzukiEvenCarlemanPoleCarrier (suzukiShiftedXiMultiplier 0)
          (suzukiCharacteristicPencil A E 1) rightTriangle z -
        endpointSum * Complex.sin ((a : ℂ) * z) := by
  rw [suzukiCarlemanRightSheet_eq_evenPoleCarrier_sub_halfInterior
    (suzukiShiftedXiMultiplier 0) (suzukiCharacteristicPencil A E 1)
    rightTriangle leftTriangle (suzukiProjectedSineClock a endpointSum)
    hreflect hsum z]
  simp only [suzukiProjectedSineClock]
  ring

/-- **Even-carrier RH criterion.**  For the actual phase-one reflected source, the projected
interval clock is already an entire odd summand.  RH is equivalent to upper-half-plane analyticity
of the remaining even Volterra carrier. -/
theorem riemannHypothesis_iff_suzukiEvenCarlemanPoleCarrier_analytic_upper
    {A E rightTriangle leftTriangle interior : ℂ → ℂ}
    (hA : ∀ z, AnalyticAt ℂ A z) (hE : ∀ z, AnalyticAt ℂ E z)
    (hT : ∀ z, AnalyticAt ℂ rightTriangle z)
    (hI : ∀ z, AnalyticAt ℂ interior z)
    (hreal : SuzukiAllAngleRealZeros A E)
    (hreflect : ∀ z, leftTriangle z = -rightTriangle (-z))
    (hsum : ∀ z,
      suzukiCarlemanInteriorPart rightTriangle leftTriangle z = interior z) :
    RiemannHypothesis ↔
      ∀ z : ℂ, 0 < z.im →
        AnalyticAt ℂ
          (suzukiEvenCarlemanPoleCarrier (suzukiShiftedXiMultiplier 0)
            (suzukiCharacteristicPencil A E 1) rightTriangle) z := by
  have hbase :=
    riemannHypothesis_iff_suzukiRightCarlemanExterior_analytic_upper
      (eta := 0) (u := 1) hA hE hT hreal
      (norm_one : ‖(1 : ℂ)‖ = 1)
  constructor
  · intro hRH z hz
    have hright := hbase.mp hRH z hz
    change AnalyticAt ℂ
      (suzukiCarlemanRightSheet (suzukiShiftedXiMultiplier 0)
        (suzukiCharacteristicPencil A E 1) rightTriangle) z at hright
    exact (analyticAt_suzukiCarlemanRightSheet_iff_evenPoleCarrier
      (suzukiShiftedXiMultiplier 0) (suzukiCharacteristicPencil A E 1)
      rightTriangle leftTriangle interior hreflect hsum (hI z)).mp hright
  · intro hcarrier
    apply hbase.mpr
    intro z hz
    change AnalyticAt ℂ
      (suzukiCarlemanRightSheet (suzukiShiftedXiMultiplier 0)
        (suzukiCharacteristicPencil A E 1) rightTriangle) z
    exact (analyticAt_suzukiCarlemanRightSheet_iff_evenPoleCarrier
      (suzukiShiftedXiMultiplier 0) (suzukiCharacteristicPencil A E 1)
      rightTriangle leftTriangle interior hreflect hsum (hI z)).mpr (hcarrier z hz)

/-! ## Weyl-phase selection and exact pole orientation -/

/-- Candidate Weyl quotient formed from one exterior carrier and one characteristic function. -/
def suzukiExteriorWeylQuotient (carrier characteristic : ℂ → ℂ) (z : ℂ) : ℂ :=
  -carrier z / characteristic z

/-- Pairing two even channels leaves an even quotient. -/
theorem suzukiExteriorWeylQuotient_even
    {carrier characteristic : ℂ → ℂ}
    (hcarrier : Function.Even carrier) (hcharacteristic : Function.Even characteristic) :
    Function.Even (suzukiExteriorWeylQuotient carrier characteristic) := by
  intro z
  simp only [suzukiExteriorWeylQuotient, hcarrier z, hcharacteristic z]

/-- Pairing the even pole carrier with an odd characteristic produces the odd parity required of
an even-measure Weyl function. -/
theorem suzukiExteriorWeylQuotient_odd
    {carrier characteristic : ℂ → ℂ}
    (hcarrier : Function.Even carrier) (hcharacteristic : Function.Odd characteristic) :
    Function.Odd (suzukiExteriorWeylQuotient carrier characteristic) := by
  intro z
  simp only [suzukiExteriorWeylQuotient, hcarrier z, hcharacteristic z]
  ring

/-- The other parity pairing is also reflection-odd: an odd carrier divided by an even
characteristic.  This is the pairing forced by admissible two-shift sewing. -/
theorem suzukiExteriorWeylQuotient_odd_of_odd_even
    {carrier characteristic : ℂ → ℂ}
    (hcarrier : Function.Odd carrier) (hcharacteristic : Function.Even characteristic) :
    Function.Odd (suzukiExteriorWeylQuotient carrier characteristic) := by
  intro z
  simp only [suzukiExteriorWeylQuotient, hcarrier z, hcharacteristic z]
  ring

/-- After division by an even nonvanishing characteristic, the exterior Weyl candidate is exactly
the negative reflection-odd part of the normalized right sheet. -/
theorem suzukiExteriorWeylQuotient_oddCarrier_eq_neg_oddPart_normalizedRightSheet
    {M W : ℂ → ℂ} (hM : Function.Odd M) (hW : Function.Even W)
    (rightTriangle : ℂ → ℂ) {z : ℂ} (hW0 : W z ≠ 0) :
    suzukiExteriorWeylQuotient
        (suzukiOddCarlemanPoleCarrier M W rightTriangle) W z =
      -suzukiReflectionOddPart
        (fun w => suzukiCarlemanRightSheet M W rightTriangle w / W w) z := by
  rw [suzukiExteriorWeylQuotient,
    suzukiOddCarlemanPoleCarrier_eq_oddPart_rightSheet hM hW]
  simp only [suzukiReflectionOddPart, hW z]
  field_simp [hW0]

/-- Weyl candidate carried by the actual admissible two-shift sheet jump. -/
def suzukiAffineSewnExteriorWeylQuotient
    (alpha beta : ℂ)
    (WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiExteriorWeylQuotient
    (suzukiAffineSewnOddCarlemanPoleCarrier alpha beta
      WAlpha WBeta rightAlpha rightBeta)
    (suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta) z

/-- The admissible sewn exterior quotient has the parity of an even-measure Weyl function. -/
theorem suzukiAffineSewnExteriorWeylQuotient_odd
    {WAlpha WBeta : ℂ → ℂ}
    (hWAlpha : Function.Odd WAlpha) (hWBeta : Function.Odd WBeta)
    (alpha beta : ℂ) (rightAlpha rightBeta : ℂ → ℂ) :
    Function.Odd
      (suzukiAffineSewnExteriorWeylQuotient alpha beta
        WAlpha WBeta rightAlpha rightBeta) := by
  exact suzukiExteriorWeylQuotient_odd_of_odd_even
    (suzukiAffineSewnOddCarlemanPoleCarrier_odd hWAlpha hWBeta
      alpha beta rightAlpha rightBeta)
    (suzukiAffineSewnCharacteristic_even_of_odd hWAlpha hWBeta alpha beta)

/-- Away from the characteristic divisor, the admissible Weyl candidate is the negative odd
part of the already-formalized projectively normalized affine exterior observable. -/
theorem suzukiAffineSewnExteriorWeylQuotient_eq_neg_oddPart_normalizedExterior
    {WAlpha WBeta : ℂ → ℂ}
    (hWAlpha : Function.Odd WAlpha) (hWBeta : Function.Odd WBeta)
    (alpha beta : ℂ) (rightAlpha rightBeta : ℂ → ℂ)
    {z : ℂ}
    (hP0 : suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z ≠ 0) :
    suzukiAffineSewnExteriorWeylQuotient alpha beta
        WAlpha WBeta rightAlpha rightBeta z =
      -suzukiReflectionOddPart
        (suzukiAffineSewnNormalizedExterior alpha beta 0
          WAlpha WBeta rightAlpha rightBeta) z := by
  let P : ℂ → ℂ := suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta
  let right : ℂ → ℂ :=
    suzukiAffineSewnIntervalPart alpha beta 0 WAlpha WBeta rightAlpha rightBeta
  have hPeven : Function.Even P :=
    suzukiAffineSewnCharacteristic_even_of_odd hWAlpha hWBeta alpha beta
  have hnormalized :
      suzukiAffineSewnNormalizedExterior alpha beta 0
          WAlpha WBeta rightAlpha rightBeta =
        fun w => suzukiCarlemanRightSheet
          (suzukiShiftedXiMultiplier 0) P right w / P w := by
    funext w
    rw [suzukiAffineSewnNormalizedExterior, suzukiAffineSewnExterior_eq_zeroShift]
    rfl
  rw [hnormalized]
  exact suzukiExteriorWeylQuotient_oddCarrier_eq_neg_oddPart_normalizedRightSheet
    suzukiZeroShiftMultiplier_odd hPeven right hP0

/-- An even Schwarz-real quotient has real value at `i`, so it cannot have Donoghue normalization
`m(i)=i`.  This is the parity no-go for pairing the even carrier with `W_{-1}`. -/
theorem even_schwarz_value_I_ne_I
    {q : ℂ → ℂ} (heven : Function.Even q)
    (hschwarz : ∀ z, q ((starRingEnd ℂ) z) = (starRingEnd ℂ) (q z)) :
    q I ≠ I := by
  have hevenI := heven I
  have hschwarzI := hschwarz I
  rw [Complex.conj_I] at hschwarzI
  have hself : q I = (starRingEnd ℂ) (q I) := by
    rw [← hschwarzI, hevenI]
  intro hq
  rw [hq, Complex.conj_I] at hself
  have hne : (I : ℂ) ≠ -I := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  exact hne hself

/-- Cross-multiplied Pick kernel for the phase-corrected exterior quotient. -/
def suzukiExteriorWeylGram
    (carrier characteristic : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (characteristic z * (starRingEnd ℂ) (carrier w) -
      carrier z * (starRingEnd ℂ) (characteristic w)) /
    (z - (starRingEnd ℂ) w)

/-- The cross-multiplied kernel is exactly the Pick kernel of `-carrier/characteristic`, conjugated
by the nonvanishing characteristic gauge. -/
theorem suzukiExteriorWeylGram_eq_gauged_pick
    {carrier characteristic : ℂ → ℂ} {z w : ℂ}
    (hz : characteristic z ≠ 0) (hw : characteristic w ≠ 0) :
    suzukiExteriorWeylGram carrier characteristic z w =
      characteristic z * (starRingEnd ℂ) (characteristic w) *
        ((suzukiExteriorWeylQuotient carrier characteristic z -
            (starRingEnd ℂ) (suzukiExteriorWeylQuotient carrier characteristic w)) /
          (z - (starRingEnd ℂ) w)) := by
  simp only [suzukiExteriorWeylGram, suzukiExteriorWeylQuotient, map_neg, map_div₀]
  field_simp [hz, hw]
  all_goals ring

/-- Phase-one exterior quotient selected by the parity no-go. -/
def suzukiPhaseOneExteriorWeylQuotient
    (A E rightTriangle : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiExteriorWeylQuotient
    (suzukiEvenCarlemanPoleCarrier (suzukiShiftedXiMultiplier 0)
      (suzukiCharacteristicPencil A E 1) rightTriangle)
    (suzukiCharacteristicPencil A E 1) z

/-- The phase-corrected exterior quotient is odd for Suzuki's reflected source. -/
theorem suzukiPhaseOneExteriorWeylQuotient_odd
    {A E : ℂ → ℂ} (hpar : SuzukiParityPair A E) (rightTriangle : ℂ → ℂ) :
    Function.Odd (suzukiPhaseOneExteriorWeylQuotient A E rightTriangle) := by
  exact suzukiExteriorWeylQuotient_odd
    (suzukiZeroShiftPhaseOneEvenCarlemanPoleCarrier_even hpar rightTriangle)
    (fun z => suzukiCharacteristicPencil_one_odd hpar z)

/-- Entire right triangles have analytic reflection-even parts. -/
theorem analyticAt_suzukiReflectionEvenPart
    {F : ℂ → ℂ} (hF : ∀ w, AnalyticAt ℂ F w) (z : ℂ) :
    AnalyticAt ℂ (suzukiReflectionEvenPart F) z := by
  have hneg : AnalyticAt ℂ (fun w => F (-w)) z :=
    by fun_prop
  change AnalyticAt ℂ (fun w => (F w + F (-w)) / 2) z
  fun_prop

/-- Entire right triangles also have analytic reflection-odd parts. -/
theorem analyticAt_suzukiReflectionOddPart
    {F : ℂ → ℂ} (hF : ∀ w, AnalyticAt ℂ F w) (z : ℂ) :
    AnalyticAt ℂ (suzukiReflectionOddPart F) z := by
  have hneg : AnalyticAt ℂ (fun w => F (-w)) z :=
    by fun_prop
  change AnalyticAt ℂ (fun w => (F w - F (-w)) / 2) z
  fun_prop

/-- **Parity-independent Xi-pole orientation.**  For any even characteristic, division of the
odd jump carrier by that same characteristic removes its source normalization.  Every Xi-zero
coefficient is `-multiplicity/z²`. -/
theorem meromorphicTrailingCoeffAt_suzukiExteriorWeylQuotient_oddCarrier_of_XiC_zero
    {W rightTriangle : ℂ → ℂ} {z : ℂ}
    (hz : XiC z = 0)
    (hW : AnalyticAt ℂ W z) (hW0 : W z ≠ 0)
    (hT : ∀ w, AnalyticAt ℂ rightTriangle w) :
    meromorphicTrailingCoeffAt
        (suzukiExteriorWeylQuotient
          (suzukiOddCarlemanPoleCarrier (suzukiShiftedXiMultiplier 0)
            W rightTriangle) W) z =
      -((analyticOrderAt XiC z).toNat : ℂ) / z ^ (2 : ℕ) := by
  let C : ℂ → ℂ :=
    suzukiOddCarlemanPoleCarrier (suzukiShiftedXiMultiplier 0) W rightTriangle
  let factor : ℂ → ℂ := fun w => -(W w)⁻¹
  have hOddT : AnalyticAt ℂ (suzukiReflectionOddPart rightTriangle) z :=
    analyticAt_suzukiReflectionOddPart hT z
  have hC : MeromorphicAt C z :=
    (meromorphicAt_suzukiShiftedXiMultiplier 0 z).mul hW.meromorphicAt |>.sub
      hOddT.meromorphicAt
  have hfactor : AnalyticAt ℂ factor z := by
    exact hW.inv hW0 |>.neg
  have hfactor0 : factor z ≠ 0 := by
    dsimp only [factor]
    exact neg_ne_zero.mpr (inv_ne_zero hW0)
  have hCtrail := meromorphicTrailingCoeffAt_suzukiExteriorRemainder
    (eta := 0) (W := W) (intervalPart := suzukiReflectionOddPart rightTriangle)
    hz hW hW0 hOddT
  change meromorphicTrailingCoeffAt C z =
      ((analyticOrderAt XiC z).toNat : ℂ) * W z / z ^ (2 : ℕ) at hCtrail
  have hfun :
      suzukiExteriorWeylQuotient C W = fun w => factor w * C w := by
    funext w
    simp only [suzukiExteriorWeylQuotient, factor]
    rw [div_eq_mul_inv]
    ring
  change meromorphicTrailingCoeffAt (suzukiExteriorWeylQuotient C W) z = _
  rw [hfun, hfactor.meromorphicAt.meromorphicTrailingCoeffAt_fun_mul hC,
    hfactor.meromorphicTrailingCoeffAt_of_ne_zero hfactor0, hCtrail]
  dsimp only [factor]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    -(W z)⁻¹ *
        (((analyticOrderAt XiC z).toNat : ℂ) * W z * (z ^ (2 : ℕ))⁻¹) =
      -(((analyticOrderAt XiC z).toNat : ℂ) * ((W z)⁻¹ * W z)) *
        (z ^ (2 : ℕ))⁻¹ := by ring
    _ = -((analyticOrderAt XiC z).toNat : ℂ) * (z ^ (2 : ℕ))⁻¹ := by
      rw [inv_mul_cancel₀ hW0]
      ring

/-- The universal negative Xi-pole coefficient survives unconditional admissible two-shift
sewing and is independent of both source shifts and both source normalizations. -/
theorem meromorphicTrailingCoeffAt_suzukiAffineSewnExteriorWeylQuotient_of_XiC_zero
    {alpha beta : ℂ}
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ} {z : ℂ}
    (hz : XiC z = 0)
    (hWAlpha : ∀ w, AnalyticAt ℂ WAlpha w)
    (hWBeta : ∀ w, AnalyticAt ℂ WBeta w)
    (hP0 : suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z ≠ 0)
    (hRAlpha : ∀ w, AnalyticAt ℂ rightAlpha w)
    (hRBeta : ∀ w, AnalyticAt ℂ rightBeta w) :
    meromorphicTrailingCoeffAt
        (suzukiAffineSewnExteriorWeylQuotient alpha beta
          WAlpha WBeta rightAlpha rightBeta) z =
      -((analyticOrderAt XiC z).toNat : ℂ) / z ^ (2 : ℕ) := by
  have hP : AnalyticAt ℂ
      (suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta) z :=
    analyticAt_suzukiAffineSewnCharacteristic (hWAlpha z) (hWBeta z)
  have hright : ∀ w, AnalyticAt ℂ
      (suzukiAffineSewnIntervalPart alpha beta 0
        WAlpha WBeta rightAlpha rightBeta) w := fun w =>
    analyticAt_suzukiAffineSewnIntervalPart
      (hWAlpha w) (hWBeta w) (hRAlpha w) (hRBeta w)
  exact meromorphicTrailingCoeffAt_suzukiExteriorWeylQuotient_oddCarrier_of_XiC_zero
    hz hP hP0 hright

/-- **Universal Xi-pole orientation.**  Dividing the even right-sheet carrier by the same
phase-one characteristic cancels every source normalization from its pole coefficient.  At any Xi
zero not shared by that characteristic, the exterior Weyl quotient has coefficient
`-multiplicity/z²`; on a real Xi zero this is the required negative Herglotz residue. -/
theorem meromorphicTrailingCoeffAt_suzukiPhaseOneExteriorWeylQuotient_of_XiC_zero
    {A E rightTriangle : ℂ → ℂ} {z : ℂ}
    (hz : XiC z = 0)
    (hA : AnalyticAt ℂ A z) (hE : AnalyticAt ℂ E z)
    (hW0 : suzukiCharacteristicPencil A E 1 z ≠ 0)
    (hT : ∀ w, AnalyticAt ℂ rightTriangle w) :
    meromorphicTrailingCoeffAt
        (suzukiPhaseOneExteriorWeylQuotient A E rightTriangle) z =
      -((analyticOrderAt XiC z).toNat : ℂ) / z ^ (2 : ℕ) := by
  let W : ℂ → ℂ := suzukiCharacteristicPencil A E 1
  let C : ℂ → ℂ :=
    suzukiEvenCarlemanPoleCarrier (suzukiShiftedXiMultiplier 0) W rightTriangle
  let factor : ℂ → ℂ := fun w => -(W w)⁻¹
  have hW : AnalyticAt ℂ W z := hA.add (analyticAt_const.mul hE)
  have hEvenT : AnalyticAt ℂ (suzukiReflectionEvenPart rightTriangle) z :=
    analyticAt_suzukiReflectionEvenPart hT z
  have hC : MeromorphicAt C z :=
    (meromorphicAt_suzukiShiftedXiMultiplier 0 z).mul hW.meromorphicAt |>.sub
      hEvenT.meromorphicAt
  have hfactor : AnalyticAt ℂ factor z := by
    exact hW.inv hW0 |>.neg
  have hfactor0 : factor z ≠ 0 := by
    dsimp only [factor]
    exact neg_ne_zero.mpr (inv_ne_zero hW0)
  have hCtrail := meromorphicTrailingCoeffAt_suzukiExteriorRemainder
    (eta := 0) (W := W) (intervalPart := suzukiReflectionEvenPart rightTriangle)
    hz hW hW0 hEvenT
  change meromorphicTrailingCoeffAt C z =
      ((analyticOrderAt XiC z).toNat : ℂ) * W z / z ^ (2 : ℕ) at hCtrail
  have hfun : suzukiPhaseOneExteriorWeylQuotient A E rightTriangle =
      fun w => factor w * C w := by
    funext w
    simp only [suzukiPhaseOneExteriorWeylQuotient, suzukiExteriorWeylQuotient,
      factor, C, W]
    rw [div_eq_mul_inv]
    ring
  rw [hfun, hfactor.meromorphicAt.meromorphicTrailingCoeffAt_fun_mul hC,
    hfactor.meromorphicTrailingCoeffAt_of_ne_zero hfactor0, hCtrail]
  dsimp only [factor]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    -(W z)⁻¹ *
        (((analyticOrderAt XiC z).toNat : ℂ) * W z * (z ^ (2 : ℕ))⁻¹) =
      -(((analyticOrderAt XiC z).toNat : ℂ) * ((W z)⁻¹ * W z)) *
        (z ^ (2 : ℕ))⁻¹ := by ring
    _ = -((analyticOrderAt XiC z).toNat : ℂ) * (z ^ (2 : ℕ))⁻¹ := by
      rw [inv_mul_cancel₀ hW0]
      ring

end

end RHTower
