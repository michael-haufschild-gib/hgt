import GaloisForLFunctions.RHTower.SuzukiCausalEntryThirdJetBoundaryLaw

/-!
# Moving-cut realization of the causal-entry transport data

The causal-entry jet chain transports a delayed hinge across the aperture wall using three
derivative laws for the moving-cut integrals

`B(ell) = ∫_{-a}^{a-ell} v`,  `A(ell) = ∫_{-a}^{a-ell} (a-ell-y) v(y) dy`,
`H(ell) = ∫_{a-ell}^{a} v(y) e^{i z y} dy`.

Here those three laws are proved for a continuous source, so the transport chain and the
entry-wall jet classification hold with no derivative hypothesis left open.  The first moment is
differentiated without differentiating under the integral sign: it is the exact combination
`(a-ell)·B(ell) − ∫_{-a}^{a-ell} y v(y) dy`, whose two moving-endpoint terms cancel.
-/

open Complex intervalIntegral MeasureTheory

namespace RHTower

noncomputable section

variable {v : ℝ → ℂ} {z : ℂ} {a ell : ℝ}

/-! ## The moving-cut integrals -/

/-- Source mass to the left of the moving cut `a - ell`. -/
def suzukiMovingCutMass (v : ℝ → ℂ) (a ell : ℝ) : ℂ :=
  ∫ y in (-a)..(a - ell), v y

/-- First moment of the source about the moving cut `a - ell`. -/
def suzukiMovingCutFirstMoment (v : ℝ → ℂ) (a ell : ℝ) : ℂ :=
  ∫ y in (-a)..(a - ell), ((a - ell - y : ℝ) : ℂ) * v y

/-- Oscillatory moment of the source on the moving window `[a - ell, a]`. -/
def suzukiMovingCutHighMoment (v : ℝ → ℂ) (z : ℂ) (a ell : ℝ) : ℂ :=
  ∫ y in (a - ell)..a, v y * suzukiOscillatoryKernel z y

/-- Characteristic function of the source on the whole aperture. -/
def suzukiApertureCharacteristic (v : ℝ → ℂ) (z : ℂ) (a : ℝ) : ℂ :=
  ∫ y in (-a)..a, v y * suzukiOscillatoryKernel z y

/-! ## Values at the entry wall -/

theorem suzukiMovingCutMass_entryWall (v : ℝ → ℂ) (a : ℝ) :
    suzukiMovingCutMass v a (2 * a) = 0 := by
  simp [suzukiMovingCutMass, show a - 2 * a = -a by ring]

theorem suzukiMovingCutFirstMoment_entryWall (v : ℝ → ℂ) (a : ℝ) :
    suzukiMovingCutFirstMoment v a (2 * a) = 0 := by
  simp [suzukiMovingCutFirstMoment, show a - 2 * a = -a by ring]

theorem suzukiMovingCutHighMoment_entryWall (v : ℝ → ℂ) (z : ℂ) (a : ℝ) :
    suzukiMovingCutHighMoment v z a (2 * a) = suzukiApertureCharacteristic v z a := by
  simp [suzukiMovingCutHighMoment, suzukiApertureCharacteristic,
    show a - 2 * a = -a by ring]

/-! ## The three transport derivatives -/

/-- The moving cut carries the source mass off at the endpoint density. -/
theorem hasDerivAt_suzukiMovingCutMass (hv : Continuous v) (a ell : ℝ) :
    HasDerivAt (suzukiMovingCutMass v a) (-(v (a - ell))) ell := by
  have h1 : HasDerivAt (fun u : ℝ => ∫ y in (-a)..u, v y) (v (a - ell)) (a - ell) :=
    (hv.integral_hasStrictDerivAt (-a) (a - ell)).hasDerivAt
  have h2 : HasDerivAt (fun u : ℝ => a - u) (-1 : ℝ) ell := by
    simpa using (hasDerivAt_id ell).const_sub a
  have h3 := h1.scomp ell h2
  rw [neg_smul, one_smul] at h3
  exact h3

/-- The first moment about the moving cut is the exact combination of the mass and the linear
moment, so its two moving-endpoint contributions cancel. -/
theorem suzukiMovingCutFirstMoment_eq (hv : Continuous v) (a ell : ℝ) :
    suzukiMovingCutFirstMoment v a ell =
      ((a - ell : ℝ) : ℂ) * suzukiMovingCutMass v a ell -
        ∫ y in (-a)..(a - ell), (y : ℂ) * v y := by
  have hc : Continuous fun y : ℝ => ((a - ell : ℝ) : ℂ) * v y := by continuity
  have hl : Continuous fun y : ℝ => (y : ℂ) * v y := by continuity
  have hsplit : (fun y : ℝ => ((a - ell - y : ℝ) : ℂ) * v y) =
      fun y : ℝ => ((a - ell : ℝ) : ℂ) * v y - (y : ℂ) * v y := by
    funext y
    push_cast
    ring
  rw [suzukiMovingCutFirstMoment, hsplit,
    intervalIntegral.integral_sub (hc.intervalIntegrable _ _) (hl.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  rfl

/-- The first moment about the moving cut differentiates to minus the mass. -/
theorem hasDerivAt_suzukiMovingCutFirstMoment (hv : Continuous v) (a ell : ℝ) :
    HasDerivAt (suzukiMovingCutFirstMoment v a) (-(suzukiMovingCutMass v a ell)) ell := by
  have hl : Continuous fun y : ℝ => (y : ℂ) * v y := by continuity
  have hofReal : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 (a - ell) :=
    Complex.ofRealCLM.hasDerivAt
  have hN0 : HasDerivAt (fun u : ℝ => ∫ y in (-a)..u, v y) (v (a - ell)) (a - ell) :=
    (hv.integral_hasStrictDerivAt (-a) (a - ell)).hasDerivAt
  have hN1 : HasDerivAt (fun u : ℝ => ∫ y in (-a)..u, (y : ℂ) * v y)
      (((a - ell : ℝ) : ℂ) * v (a - ell)) (a - ell) :=
    (hl.integral_hasStrictDerivAt (-a) (a - ell)).hasDerivAt
  have hprod : HasDerivAt (fun u : ℝ => (u : ℂ) * ∫ y in (-a)..u, v y)
      (1 * (∫ y in (-a)..(a - ell), v y) + ((a - ell : ℝ) : ℂ) * v (a - ell)) (a - ell) :=
    hofReal.mul hN0
  have hG : HasDerivAt
      (fun u : ℝ => (u : ℂ) * (∫ y in (-a)..u, v y) - ∫ y in (-a)..u, (y : ℂ) * v y)
      (∫ y in (-a)..(a - ell), v y) (a - ell) := by
    have h := hprod.sub hN1
    rw [show (1 : ℂ) * (∫ y in (-a)..(a - ell), v y) + ((a - ell : ℝ) : ℂ) * v (a - ell) -
        ((a - ell : ℝ) : ℂ) * v (a - ell) = ∫ y in (-a)..(a - ell), v y by ring] at h
    exact h
  have hcut : HasDerivAt (fun u : ℝ => a - u) (-1 : ℝ) ell := by
    simpa using (hasDerivAt_id ell).const_sub a
  have hcomp := hG.scomp ell hcut
  rw [neg_smul, one_smul] at hcomp
  have hfun : (fun u : ℝ => ((a - u : ℝ) : ℂ) * (∫ y in (-a)..(a - u), v y) -
      ∫ y in (-a)..(a - u), (y : ℂ) * v y) = suzukiMovingCutFirstMoment v a := by
    funext u
    rw [suzukiMovingCutFirstMoment_eq hv a u, suzukiMovingCutMass]
  rw [← hfun]
  exact hcomp

/-- The moving oscillatory window gains the endpoint density weighted by the kernel. -/
theorem hasDerivAt_suzukiMovingCutHighMoment (hv : Continuous v) (z : ℂ) (a ell : ℝ) :
    HasDerivAt (suzukiMovingCutHighMoment v z a)
      (suzukiOscillatoryKernel z (a - ell) * v (a - ell)) ell := by
  have hK : Continuous fun y : ℝ => v y * suzukiOscillatoryKernel z y := by
    refine hv.mul ?_
    unfold suzukiOscillatoryKernel
    continuity
  have h1 : HasDerivAt (fun u : ℝ => ∫ y in u..a, v y * suzukiOscillatoryKernel z y)
      (-(v (a - ell) * suzukiOscillatoryKernel z (a - ell))) (a - ell) :=
    (intervalIntegral.integral_hasStrictDerivAt_left (hK.intervalIntegrable _ _)
      (hK.stronglyMeasurableAtFilter _ _) hK.continuousAt).hasDerivAt
  have h2 : HasDerivAt (fun u : ℝ => a - u) (-1 : ℝ) ell := by
    simpa using (hasDerivAt_id ell).const_sub a
  have h3 := h1.scomp ell h2
  rw [neg_smul, one_smul, neg_neg] at h3
  have hmul : v (a - ell) * suzukiOscillatoryKernel z (a - ell) =
      suzukiOscillatoryKernel z (a - ell) * v (a - ell) := mul_comm _ _
  rw [hmul] at h3
  exact h3

/-! ## The transport chain with every hypothesis discharged -/

/-- **First cancellation, realized.**  For a continuous source the completed near-entry channel
differentiates to the entry current with no derivative hypothesis assumed. -/
theorem hasDerivAt_suzukiDelayedHingeNearCompletedJet0_movingCut
    (hv : Continuous v) (z : ℂ) (a ell : ℝ) :
    HasDerivAt
      (fun u => suzukiDelayedHingeNearCompletedJet0 a u
        (suzukiMovingCutHighMoment v z a u) (suzukiMovingCutFirstMoment v a u)
        (suzukiMovingCutMass v a u) z)
      (suzukiDelayedHingeNearCompletedJet1 a ell
        (suzukiMovingCutHighMoment v z a ell) (suzukiMovingCutMass v a ell) z) ell :=
  hasDerivAt_suzukiDelayedHingeNearCompletedJet0 a ell z (v (a - ell))
    (suzukiMovingCutHighMoment v z a) (suzukiMovingCutFirstMoment v a)
    (suzukiMovingCutMass v a)
    (hasDerivAt_suzukiMovingCutFirstMoment hv a ell)
    (hasDerivAt_suzukiMovingCutMass hv a ell)
    (hasDerivAt_suzukiMovingCutHighMoment hv z a ell)

/-- **Second cancellation, realized.**  The endpoint density leaves the derivative of the entry
current. -/
theorem hasDerivAt_suzukiDelayedHingeEntryCurrent_movingCut
    (hv : Continuous v) (z : ℂ) (a ell : ℝ) :
    HasDerivAt
      (fun u => suzukiDelayedHingeEntryCurrent a u
        (suzukiMovingCutHighMoment v z a u) (suzukiMovingCutMass v a u) z)
      (I * z * suzukiOscillatoryKernel z ell * suzukiMovingCutHighMoment v z a ell) ell :=
  hasDerivAt_suzukiDelayedHingeEntryCurrent a ell z (v (a - ell))
    (suzukiMovingCutHighMoment v z a) (suzukiMovingCutMass v a)
    (hasDerivAt_suzukiMovingCutMass hv a ell)
    (hasDerivAt_suzukiMovingCutHighMoment hv z a ell)

/-- **First jet, realized.** -/
theorem hasDerivAt_suzukiDelayedHingeNearCompletedJet1_movingCut
    (hv : Continuous v) (z : ℂ) (a ell : ℝ) :
    HasDerivAt
      (fun u => suzukiDelayedHingeNearCompletedJet1 a u
        (suzukiMovingCutHighMoment v z a u) (suzukiMovingCutMass v a u) z)
      (suzukiDelayedHingeNearCompletedJet2 ell (suzukiMovingCutHighMoment v z a ell) z) ell :=
  hasDerivAt_suzukiDelayedHingeNearCompletedJet1 a ell z (v (a - ell))
    (suzukiMovingCutHighMoment v z a) (suzukiMovingCutMass v a)
    (hasDerivAt_suzukiMovingCutMass hv a ell)
    (hasDerivAt_suzukiMovingCutHighMoment hv z a ell)

/-- **Second jet, realized.**  The endpoint trace enters the transport chain here for the first
time, and its coefficient is the zero-extension boundary value `v(-a)` at the entry wall. -/
theorem hasDerivAt_suzukiDelayedHingeNearCompletedJet2_movingCut
    (hv : Continuous v) (z : ℂ) (a ell : ℝ) :
    HasDerivAt
      (fun u => suzukiDelayedHingeNearCompletedJet2 u (suzukiMovingCutHighMoment v z a u) z)
      (suzukiDelayedHingeNearCompletedJet3 a ell
        (suzukiMovingCutHighMoment v z a ell) (v (a - ell)) z) ell :=
  hasDerivAt_suzukiDelayedHingeNearCompletedJet2 a ell z (v (a - ell))
    (suzukiMovingCutHighMoment v z a)
    (hasDerivAt_suzukiMovingCutHighMoment hv z a ell)

/-! ## Entry-wall classification for the realized channels -/

/-- The realized near channel is the far channel at the entry wall. -/
theorem suzukiDelayedHingeNearCompletedJet0_movingCut_entryWall (v : ℝ → ℂ) (z : ℂ) (a : ℝ) :
    suzukiDelayedHingeNearCompletedJet0 a (2 * a)
        (suzukiMovingCutHighMoment v z a (2 * a)) (suzukiMovingCutFirstMoment v a (2 * a))
        (suzukiMovingCutMass v a (2 * a)) z =
      suzukiDelayedHingeFarCompletedJet0 (2 * a) (suzukiApertureCharacteristic v z a) z := by
  rw [suzukiMovingCutMass_entryWall, suzukiMovingCutFirstMoment_entryWall,
    suzukiMovingCutHighMoment_entryWall]
  exact suzukiDelayedHingeCompletedJet0_entryWall a _ z

/-- Realized first jets agree at the entry wall. -/
theorem suzukiDelayedHingeNearCompletedJet1_movingCut_entryWall (v : ℝ → ℂ) (z : ℂ) (a : ℝ) :
    suzukiDelayedHingeNearCompletedJet1 a (2 * a)
        (suzukiMovingCutHighMoment v z a (2 * a)) (suzukiMovingCutMass v a (2 * a)) z =
      suzukiDelayedHingeFarCompletedJet1 (2 * a) (suzukiApertureCharacteristic v z a) z := by
  rw [suzukiMovingCutMass_entryWall, suzukiMovingCutHighMoment_entryWall]
  exact suzukiDelayedHingeCompletedJet1_entryWall a _ z

/-- Realized second jets agree at the entry wall. -/
theorem suzukiDelayedHingeNearCompletedJet2_movingCut_entryWall (v : ℝ → ℂ) (z : ℂ) (a : ℝ) :
    suzukiDelayedHingeNearCompletedJet2 (2 * a) (suzukiMovingCutHighMoment v z a (2 * a)) z =
      suzukiDelayedHingeFarCompletedJet2 (2 * a) (suzukiApertureCharacteristic v z a) z := by
  rw [suzukiMovingCutHighMoment_entryWall]
  rfl

/-- **Third-jet entry law for the realized source.**  The first near/far wall defect is exactly
`z² e^{i a z} v(-a)`: a delayed hinge enters with matching value, slope, and curvature, and its
complete third-jet coefficient is the zero-extension endpoint trace. -/
theorem suzukiDelayedHingeNearCompletedJet3_movingCut_entryWall_sub
    (v : ℝ → ℂ) (z : ℂ) (a : ℝ) :
    suzukiDelayedHingeNearCompletedJet3 a (2 * a)
        (suzukiMovingCutHighMoment v z a (2 * a)) (v (a - 2 * a)) z -
      suzukiDelayedHingeFarCompletedJet3 (2 * a) (suzukiApertureCharacteristic v z a) z =
        z ^ 2 * suzukiOscillatoryKernel z a * v (-a) := by
  rw [suzukiMovingCutHighMoment_entryWall, show a - 2 * a = -a by ring]
  exact suzukiDelayedHingeCompletedJet3_entryWall_sub a _ (v (-a)) z

/-- A source vanishing at the left aperture endpoint crosses the entry wall with a vanishing
third-jet defect. -/
theorem suzukiDelayedHingeNearCompletedJet3_movingCut_entryWall_eq_of_dirichlet
    (v : ℝ → ℂ) (z : ℂ) (a : ℝ) (hv : v (-a) = 0) :
    suzukiDelayedHingeNearCompletedJet3 a (2 * a)
        (suzukiMovingCutHighMoment v z a (2 * a)) (v (a - 2 * a)) z =
      suzukiDelayedHingeFarCompletedJet3 (2 * a) (suzukiApertureCharacteristic v z a) z := by
  have h := suzukiDelayedHingeNearCompletedJet3_movingCut_entryWall_sub v z a
  rw [hv, mul_zero] at h
  exact sub_eq_zero.mp h

end

end RHTower
