import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinActualMixedDerivative

/-!
# Actual signed Whittaker mode second jets and Maass normalization

Corpus conjecture C-A.9t2b begins by testing the literal full-second-jet Maass
normalization on every individual Whittaker Fourier mode.  The corpus already
proves the first Bessel derivative and the finite two-step Maass shift word,
but did not certify the radial second derivative needed by `D4BMFullSecondJet`.

This module recovers that derivative from the already-proved first raised-word
identity, constructs genuine signed two-variable mode jets, and compares their
literal `R_2 R_0` and `L_(-2) L_0` values with the corpus finite shift words.
This is the mode-level route-killing test before differentiating the infinite
signed tail.

RH chain:

actual signed mode jets -> full signed tail normal convergence -> canonical
raise/lower weld -> literal truncated Green/Stokes -> full cusp current ->
balanced BM `++-` coefficient -> negative BM leg -> left-QNM -> HC94 -> RH.
-/

open Complex Real Filter Set Topology

namespace RHTower
noncomputable section

/-- Total real-height formula for the first radial derivative of `sqrt(Y) K_nu(cY)`. -/
def d4BMWhittakerP0FirstJet
    (c : D4BMPositiveReal) (nu : ℂ) (Y : ℝ) : ℂ :=
  ((1 / (2 * Real.sqrt Y) : ℝ) : ℂ) *
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder ((c : ℝ) * Y) nu +
    (Real.sqrt Y : ℂ) * (c : ℂ) * (-(1 / 2 : ℂ)) *
      (GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          ((c : ℝ) * Y) (nu + 1) +
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          ((c : ℝ) * Y) (nu - 1))

@[simp] theorem d4BM_whittakerP0FirstJet_eq_deriv
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) :
    d4BMWhittakerP0FirstJet c nu (Y : ℝ) =
      d4BMWhittakerP0Deriv c nu Y := by
  rfl

/-- Explicit first raised-mode shift word, regarded as a total height function. -/
def d4BMPositiveFrequencyRaiseZeroShift
    (c : D4BMPositiveReal) (nu : ℂ) (Y : ℝ) : ℂ :=
  (1 / 2 : ℂ) * d4BMWhittakerP0 c nu Y -
    d4BMWhittakerP1 c nu Y -
    (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu + 1) Y -
    (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu - 1) Y

theorem hasDerivAt_d4BMPositiveFrequencyRaiseZeroShift
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) :
    HasDerivAt (d4BMPositiveFrequencyRaiseZeroShift c nu)
      (d4BMPositiveFrequencyRaiseZeroModeDeriv c nu Y) (Y : ℝ) := by
  unfold d4BMPositiveFrequencyRaiseZeroShift
  exact d4BM_hasDerivAt_positiveFrequencyRaiseZeroMode c nu Y

/-- Explicit first lowered-mode shift word, regarded as a total height function. -/
def d4BMPositiveFrequencyLowerZeroShift
    (c : D4BMPositiveReal) (nu : ℂ) (Y : ℝ) : ℂ :=
  (1 / 2 : ℂ) * d4BMWhittakerP0 c nu Y +
    d4BMWhittakerP1 c nu Y -
    (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu + 1) Y -
    (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu - 1) Y

theorem hasDerivAt_d4BMPositiveFrequencyLowerZeroShift
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) :
    HasDerivAt (d4BMPositiveFrequencyLowerZeroShift c nu)
      (d4BMPositiveFrequencyLowerZeroModeDeriv c nu Y) (Y : ℝ) := by
  unfold d4BMPositiveFrequencyLowerZeroShift
  exact d4BM_hasDerivAt_positiveFrequencyLowerZeroMode c nu Y

/-- The first radial jet is the raised word divided by height plus `c` times the mode. -/
theorem d4BM_whittakerP0FirstJet_eq_raiseZeroShift_div_add
    (c : D4BMPositiveReal) (nu : ℂ) {Y : ℝ} (hY : 0 < Y) :
    d4BMWhittakerP0FirstJet c nu Y =
      d4BMPositiveFrequencyRaiseZeroShift c nu Y / (Y : ℂ) +
        (c : ℂ) * d4BMWhittakerP0 c nu Y := by
  let Yp : D4BMPositiveReal := ⟨Y, hY⟩
  have hword := d4BM_positiveFrequencyRaiseZeroMode_eq c nu Yp
  unfold d4BMPositiveFrequencyRaiseZeroMode
    d4BMPositiveFrequencyMaassRaiseAt at hword
  rw [← d4BM_whittakerP0FirstJet_eq_deriv c nu Yp] at hword
  have hword' :
      (Y : ℂ) * d4BMWhittakerP0FirstJet c nu Y -
          (c : ℂ) * (Y : ℂ) * d4BMWhittakerP0 c nu Y =
        d4BMPositiveFrequencyRaiseZeroShift c nu Y := by
    simpa [Yp, d4BMPositiveFrequencyRaiseZeroShift] using hword
  have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  field_simp [hYne]
  linear_combination hword'

/-- The first radial jet is the lowered word divided by height minus `c` times the mode. -/
theorem d4BM_whittakerP0FirstJet_eq_lowerZeroShift_div_sub
    (c : D4BMPositiveReal) (nu : ℂ) {Y : ℝ} (hY : 0 < Y) :
    d4BMWhittakerP0FirstJet c nu Y =
      d4BMPositiveFrequencyLowerZeroShift c nu Y / (Y : ℂ) -
        (c : ℂ) * d4BMWhittakerP0 c nu Y := by
  let Yp : D4BMPositiveReal := ⟨Y, hY⟩
  have hword := d4BM_positiveFrequencyLowerZeroMode_eq c nu Yp
  unfold d4BMPositiveFrequencyLowerZeroMode
    d4BMPositiveFrequencyMaassLowerAt at hword
  rw [← d4BM_whittakerP0FirstJet_eq_deriv c nu Yp] at hword
  have hword' :
      (Y : ℂ) * d4BMWhittakerP0FirstJet c nu Y +
          (c : ℂ) * (Y : ℂ) * d4BMWhittakerP0 c nu Y =
        d4BMPositiveFrequencyLowerZeroShift c nu Y := by
    simpa [Yp, d4BMPositiveFrequencyLowerZeroShift] using hword
  have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  field_simp [hYne]
  linear_combination hword'

/-- Radial second jet reconstructed from the derivative of the first raised word. -/
def d4BMWhittakerP0SecondJet
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) : ℂ :=
  d4BMPositiveFrequencyRaiseZeroModeDeriv c nu Y / (Y : ℂ) -
    d4BMPositiveFrequencyRaiseZeroShift c nu (Y : ℝ) / (Y : ℂ) ^ (2 : ℕ) +
    (c : ℂ) * d4BMWhittakerP0FirstJet c nu (Y : ℝ)

/-- The reconstructed radial second jet is the genuine derivative of the first jet. -/
theorem hasDerivAt_d4BMWhittakerP0FirstJet
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) :
    HasDerivAt (d4BMWhittakerP0FirstJet c nu)
      (d4BMWhittakerP0SecondJet c nu Y) (Y : ℝ) := by
  have hR := hasDerivAt_d4BMPositiveFrequencyRaiseZeroShift c nu Y
  have hYc : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 (Y : ℝ) :=
    (hasDerivAt_id (Y : ℝ)).ofReal_comp
  have hYne : ((Y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Y.2.ne'
  have hquot := hR.div hYc hYne
  have hP0 := d4BM_hasDerivAt_whittakerP0 c nu Y
  have hright := hquot.add (hP0.const_mul (c : ℂ))
  have heq : d4BMWhittakerP0FirstJet c nu =ᶠ[𝓝 (Y : ℝ)]
      (fun q : ℝ =>
        d4BMPositiveFrequencyRaiseZeroShift c nu q / (q : ℂ) +
          (c : ℂ) * d4BMWhittakerP0 c nu q) := by
    filter_upwards [eventually_gt_nhds Y.2] with q hq
    exact d4BM_whittakerP0FirstJet_eq_raiseZeroShift_div_add c nu hq
  refine (hright.congr_of_eventuallyEq heq).congr_deriv ?_
  simp [d4BMWhittakerP0SecondJet]
  field_simp [hYne]

/-- The genuine second radial jet also has the lowering-word reconstruction. -/
theorem d4BM_whittakerP0SecondJet_eq_lowerZero
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) :
    d4BMWhittakerP0SecondJet c nu Y =
      d4BMPositiveFrequencyLowerZeroModeDeriv c nu Y / (Y : ℂ) -
        d4BMPositiveFrequencyLowerZeroShift c nu (Y : ℝ) / (Y : ℂ) ^ (2 : ℕ) -
        (c : ℂ) * d4BMWhittakerP0FirstJet c nu (Y : ℝ) := by
  have hL := hasDerivAt_d4BMPositiveFrequencyLowerZeroShift c nu Y
  have hYc : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 (Y : ℝ) :=
    (hasDerivAt_id (Y : ℝ)).ofReal_comp
  have hYne : ((Y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Y.2.ne'
  have hquot := hL.div hYc hYne
  have hP0 := d4BM_hasDerivAt_whittakerP0 c nu Y
  have hright := hquot.sub (hP0.const_mul (c : ℂ))
  have heq : d4BMWhittakerP0FirstJet c nu =ᶠ[𝓝 (Y : ℝ)]
      (fun q : ℝ =>
        d4BMPositiveFrequencyLowerZeroShift c nu q / (q : ℂ) -
          (c : ℂ) * d4BMWhittakerP0 c nu q) := by
    filter_upwards [eventually_gt_nhds Y.2] with q hq
    exact d4BM_whittakerP0FirstJet_eq_lowerZeroShift_div_sub c nu hq
  have hlower := hright.congr_of_eventuallyEq heq
  have hlower' : HasDerivAt (d4BMWhittakerP0FirstJet c nu)
      (d4BMPositiveFrequencyLowerZeroModeDeriv c nu Y / (Y : ℂ) -
        d4BMPositiveFrequencyLowerZeroShift c nu (Y : ℝ) / (Y : ℂ) ^ (2 : ℕ) -
        (c : ℂ) * d4BMWhittakerP0FirstJet c nu (Y : ℝ)) (Y : ℝ) := by
    refine hlower.congr_deriv ?_
    rw [d4BM_whittakerP0FirstJet_eq_deriv]
    field_simp [hYne]
  exact (hasDerivAt_d4BMWhittakerP0FirstJet c nu Y).unique hlower'

/-- Positive Fourier scale `2*pi*(N+1)`. -/
def d4BMPositiveFourierScale (N : ℕ) : D4BMPositiveReal :=
  ⟨2 * Real.pi * ((N : ℝ) + 1), by positivity⟩

/-- Complex horizontal logarithmic derivative of a signed Fourier phase. -/
def d4BMSignedFourierRate (negative : Bool) (N : ℕ) : ℂ :=
  (d4BMFourierSign negative : ℂ) *
    (d4BMPositiveFourierScale N : ℂ) * Complex.I

/-- A single signed square-root Whittaker Fourier mode. -/
def d4BMSignedWhittakerMode
    (negative : Bool) (N : ℕ) (nu : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinFourierPhase negative N x *
    d4BMWhittakerP0 (d4BMPositiveFourierScale N) nu Y

/-- Horizontal first jet of one signed mode. -/
def d4BMSignedWhittakerModeHorizontalFirstJet
    (negative : Bool) (N : ℕ) (nu : ℂ) (x Y : ℝ) : ℂ :=
  d4BMSignedFourierRate negative N *
    d4BMSignedWhittakerMode negative N nu x Y

/-- Vertical first jet of one signed mode. -/
def d4BMSignedWhittakerModeVerticalFirstJet
    (negative : Bool) (N : ℕ) (nu : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinFourierPhase negative N x *
    d4BMWhittakerP0FirstJet (d4BMPositiveFourierScale N) nu Y

/-- Horizontal pure second jet of one signed mode. -/
def d4BMSignedWhittakerModeHorizontalSecondJet
    (negative : Bool) (N : ℕ) (nu : ℂ) (x Y : ℝ) : ℂ :=
  d4BMSignedFourierRate negative N ^ (2 : ℕ) *
    d4BMSignedWhittakerMode negative N nu x Y

/-- Mixed second jet of one signed mode. -/
def d4BMSignedWhittakerModeMixedSecondJet
    (negative : Bool) (N : ℕ) (nu : ℂ) (x Y : ℝ) : ℂ :=
  d4BMSignedFourierRate negative N *
    d4BMSignedWhittakerModeVerticalFirstJet negative N nu x Y

/-- Vertical pure second jet of one signed mode at positive height. -/
def d4BMSignedWhittakerModeVerticalSecondJet
    (negative : Bool) (N : ℕ) (nu : ℂ) (x : ℝ)
    (Y : D4BMPositiveReal) : ℂ :=
  d4BMCompletedEisensteinFourierPhase negative N x *
    d4BMWhittakerP0SecondJet (d4BMPositiveFourierScale N) nu Y

/-- The corpus signed Fourier phase has its literal signed frequency derivative. -/
theorem hasDerivAt_d4BMCompletedEisensteinFourierPhase
    (negative : Bool) (N : ℕ) (x : ℝ) :
    HasDerivAt (d4BMCompletedEisensteinFourierPhase negative N)
      (d4BMSignedFourierRate negative N *
        d4BMCompletedEisensteinFourierPhase negative N x) x := by
  let r : ℝ := d4BMFourierSign negative *
    (2 * Real.pi * ((N : ℝ) + 1))
  have hrR : HasDerivAt (fun y : ℝ => r * y) r x := by
    simpa using (hasDerivAt_id x).const_mul r
  have hrC : HasDerivAt (fun y : ℝ => ((r * y : ℝ) : ℂ)) (r : ℂ) x :=
    hrR.ofReal_comp
  have harg := hrC.mul_const Complex.I
  have hexp := harg.cexp
  have hfun : d4BMCompletedEisensteinFourierPhase negative N =
      (fun y : ℝ => Complex.exp ((((r * y : ℝ) : ℂ)) * Complex.I)) := by
    funext y
    unfold d4BMCompletedEisensteinFourierPhase
    congr 1
    dsimp only [r]
    push_cast
    ring
  rw [hfun]
  convert hexp using 1
  dsimp [d4BMSignedFourierRate, d4BMPositiveFourierScale, r]
  push_cast
  ring

/-- Actual horizontal derivative of one signed Whittaker mode. -/
theorem hasDerivAt_d4BMSignedWhittakerMode_horizontal
    (negative : Bool) (N : ℕ) (nu : ℂ) (x Y : ℝ) :
    HasDerivAt (fun q : ℝ => d4BMSignedWhittakerMode negative N nu q Y)
      (d4BMSignedWhittakerModeHorizontalFirstJet negative N nu x Y) x := by
  have h := (hasDerivAt_d4BMCompletedEisensteinFourierPhase negative N x).mul_const
    (d4BMWhittakerP0 (d4BMPositiveFourierScale N) nu Y)
  change HasDerivAt
    (fun q : ℝ => d4BMCompletedEisensteinFourierPhase negative N q *
      d4BMWhittakerP0 (d4BMPositiveFourierScale N) nu Y)
    (d4BMSignedFourierRate negative N *
      (d4BMCompletedEisensteinFourierPhase negative N x *
        d4BMWhittakerP0 (d4BMPositiveFourierScale N) nu Y)) x
  apply h.congr_deriv
  ring

/-- Actual second horizontal derivative of one signed Whittaker mode. -/
theorem hasDerivAt_d4BMSignedWhittakerModeHorizontalFirstJet_horizontal
    (negative : Bool) (N : ℕ) (nu : ℂ) (x Y : ℝ) :
    HasDerivAt
      (fun q : ℝ => d4BMSignedWhittakerModeHorizontalFirstJet negative N nu q Y)
      (d4BMSignedWhittakerModeHorizontalSecondJet negative N nu x Y) x := by
  have h := (hasDerivAt_d4BMSignedWhittakerMode_horizontal negative N nu x Y).const_mul
    (d4BMSignedFourierRate negative N)
  change HasDerivAt
    (fun q : ℝ => d4BMSignedFourierRate negative N *
      d4BMSignedWhittakerMode negative N nu q Y)
    (d4BMSignedFourierRate negative N ^ (2 : ℕ) *
      d4BMSignedWhittakerMode negative N nu x Y) x
  apply h.congr_deriv
  unfold d4BMSignedWhittakerModeHorizontalFirstJet
  ring

/-- Actual vertical derivative of one signed Whittaker mode. -/
theorem hasDerivAt_d4BMSignedWhittakerMode_vertical
    (negative : Bool) (N : ℕ) (nu : ℂ) (x : ℝ)
    (Y : D4BMPositiveReal) :
    HasDerivAt (fun q : ℝ => d4BMSignedWhittakerMode negative N nu x q)
      (d4BMSignedWhittakerModeVerticalFirstJet negative N nu x Y) (Y : ℝ) := by
  have h := (d4BM_hasDerivAt_whittakerP0 (d4BMPositiveFourierScale N) nu Y).const_mul
    (d4BMCompletedEisensteinFourierPhase negative N x)
  change HasDerivAt
    (fun q : ℝ => d4BMCompletedEisensteinFourierPhase negative N x *
      d4BMWhittakerP0 (d4BMPositiveFourierScale N) nu q)
    (d4BMCompletedEisensteinFourierPhase negative N x *
      d4BMWhittakerP0FirstJet (d4BMPositiveFourierScale N) nu Y) (Y : ℝ)
  rw [d4BM_whittakerP0FirstJet_eq_deriv]
  exact h

/-- Actual mixed derivative of one signed Whittaker mode. -/
theorem hasDerivAt_d4BMSignedWhittakerModeVerticalFirstJet_horizontal
    (negative : Bool) (N : ℕ) (nu : ℂ) (x Y : ℝ) :
    HasDerivAt
      (fun q : ℝ => d4BMSignedWhittakerModeVerticalFirstJet negative N nu q Y)
      (d4BMSignedWhittakerModeMixedSecondJet negative N nu x Y) x := by
  have h := (hasDerivAt_d4BMCompletedEisensteinFourierPhase negative N x).mul_const
    (d4BMWhittakerP0FirstJet (d4BMPositiveFourierScale N) nu Y)
  change HasDerivAt
    (fun q : ℝ => d4BMCompletedEisensteinFourierPhase negative N q *
      d4BMWhittakerP0FirstJet (d4BMPositiveFourierScale N) nu Y)
    (d4BMSignedFourierRate negative N *
      (d4BMCompletedEisensteinFourierPhase negative N x *
        d4BMWhittakerP0FirstJet (d4BMPositiveFourierScale N) nu Y)) x
  apply h.congr_deriv
  ring

/-- Actual second vertical derivative of one signed Whittaker mode. -/
theorem hasDerivAt_d4BMSignedWhittakerModeVerticalFirstJet_vertical
    (negative : Bool) (N : ℕ) (nu : ℂ) (x : ℝ)
    (Y : D4BMPositiveReal) :
    HasDerivAt
      (fun q : ℝ => d4BMSignedWhittakerModeVerticalFirstJet negative N nu x q)
      (d4BMSignedWhittakerModeVerticalSecondJet negative N nu x Y) (Y : ℝ) := by
  have h := (hasDerivAt_d4BMWhittakerP0FirstJet
    (d4BMPositiveFourierScale N) nu Y).const_mul
      (d4BMCompletedEisensteinFourierPhase negative N x)
  simpa [d4BMSignedWhittakerModeVerticalFirstJet,
    d4BMSignedWhittakerModeVerticalSecondJet] using h

/-- Genuine full second jet of a signed Whittaker mode in the active `(x,Y)` plane. -/
def d4BMActualSignedWhittakerModeFullSecondJet
    (negative : Bool) (N : ℕ) (nu : ℂ) (x : ℝ)
    (Y : D4BMPositiveReal) : D4BMFullSecondJet where
  first :=
    { value := d4BMSignedWhittakerMode negative N nu x Y
      tau := 0
      horizonX := d4BMSignedWhittakerModeHorizontalFirstJet negative N nu x Y
      sigma := d4BMSignedWhittakerModeVerticalFirstJet negative N nu x Y
      xi := 0 }
  tauTau := 0
  tauHorizonX := 0
  tauSigma := 0
  tauXi := 0
  horizonXHorizonX := d4BMSignedWhittakerModeHorizontalSecondJet negative N nu x Y
  horizonXSigma := d4BMSignedWhittakerModeMixedSecondJet negative N nu x Y
  horizonXXi := 0
  sigmaSigma := d4BMSignedWhittakerModeVerticalSecondJet negative N nu x Y
  sigmaXi := 0
  xiXi := 0

/-- On a positive Fourier mode, the literal full-jet raising operator is the
existing radial two-step raising word, with the original phase retained. -/
theorem d4BM_actualPositiveWhittakerMode_raise_eq_phase_mul
    (N : ℕ) (nu : ℂ) (x : ℝ) (Y : D4BMPositiveReal) :
    d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ)
        (d4BMActualSignedWhittakerModeFullSecondJet false N nu x Y) =
      d4BMCompletedEisensteinFourierPhase false N x *
        d4BMPositiveFrequencyRaiseTwoRaiseZeroMode
          (d4BMPositiveFourierScale N) nu Y := by
  have hfirst := d4BM_whittakerP0FirstJet_eq_raiseZeroShift_div_add
    (d4BMPositiveFourierScale N) nu Y.2
  have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast Y.2.ne'
  have hrate : d4BMSignedFourierRate false N =
      (d4BMPositiveFourierScale N : ℂ) * Complex.I := by
    simp [d4BMSignedFourierRate, d4BMFourierSign]
  have hmode :
      d4BMPositiveFrequencyRaiseTwoRaiseZeroMode
          (d4BMPositiveFourierScale N) nu Y =
        d4BMPositiveFrequencyMaassRaiseAt 2
          (d4BMPositiveFourierScale N) Y
          (d4BMPositiveFrequencyRaiseZeroShift
            (d4BMPositiveFourierScale N) nu Y)
          (d4BMPositiveFrequencyRaiseZeroModeDeriv
            (d4BMPositiveFourierScale N) nu Y) := by
    rfl
  rw [hmode]
  unfold d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet
    d4BMActualSignedWhittakerModeFullSecondJet
    d4BMSignedWhittakerModeHorizontalSecondJet
    d4BMSignedWhittakerModeMixedSecondJet
    d4BMSignedWhittakerModeHorizontalFirstJet
    d4BMSignedWhittakerModeVerticalSecondJet
    d4BMSignedWhittakerModeVerticalFirstJet
    d4BMSignedWhittakerMode
    d4BMPositiveFrequencyMaassRaiseAt
    d4BMWhittakerP0SecondJet
  rw [hrate]
  simp only [Int.cast_ofNat]
  rw [d4BM_whittakerP0FirstJet_eq_deriv] at hfirst ⊢
  field_simp [hYne] at hfirst ⊢
  simp_rw [Complex.I_sq] at ⊢
  linear_combination
    (d4BMCompletedEisensteinFourierPhase false N x *
      (2 - (Y : ℂ) * (d4BMPositiveFourierScale N : ℂ))) * hfirst

/-- On a positive Fourier mode, the literal full-jet lowering operator is the
existing radial two-step lowering word, with the original phase retained. -/
theorem d4BM_actualPositiveWhittakerMode_lower_eq_phase_mul
    (N : ℕ) (nu : ℂ) (x : ℝ) (Y : D4BMPositiveReal) :
    d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ)
        (d4BMActualSignedWhittakerModeFullSecondJet false N nu x Y) =
      d4BMCompletedEisensteinFourierPhase false N x *
        d4BMPositiveFrequencyLowerNegTwoLowerZeroMode
          (d4BMPositiveFourierScale N) nu Y := by
  have hfirst := d4BM_whittakerP0FirstJet_eq_lowerZeroShift_div_sub
    (d4BMPositiveFourierScale N) nu Y.2
  have hsecond := d4BM_whittakerP0SecondJet_eq_lowerZero
    (d4BMPositiveFourierScale N) nu Y
  have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast Y.2.ne'
  have hrate : d4BMSignedFourierRate false N =
      (d4BMPositiveFourierScale N : ℂ) * Complex.I := by
    simp [d4BMSignedFourierRate, d4BMFourierSign]
  have hmode :
      d4BMPositiveFrequencyLowerNegTwoLowerZeroMode
          (d4BMPositiveFourierScale N) nu Y =
        d4BMPositiveFrequencyMaassLowerAt (-2)
          (d4BMPositiveFourierScale N) Y
          (d4BMPositiveFrequencyLowerZeroShift
            (d4BMPositiveFourierScale N) nu Y)
          (d4BMPositiveFrequencyLowerZeroModeDeriv
            (d4BMPositiveFourierScale N) nu Y) := by
    rfl
  rw [hmode]
  unfold d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet
    d4BMActualSignedWhittakerModeFullSecondJet
    d4BMSignedWhittakerModeHorizontalSecondJet
    d4BMSignedWhittakerModeMixedSecondJet
    d4BMSignedWhittakerModeHorizontalFirstJet
    d4BMSignedWhittakerModeVerticalSecondJet
    d4BMSignedWhittakerModeVerticalFirstJet
    d4BMSignedWhittakerMode
    d4BMPositiveFrequencyMaassLowerAt
  rw [hsecond, hrate]
  rw [d4BM_whittakerP0FirstJet_eq_deriv] at hfirst ⊢
  rw [hfirst]
  field_simp [hYne]
  simp_rw [Complex.I_sq] at ⊢
  ring

/-- On a negative Fourier mode, literal raising exchanges with the positive-frequency
lowering word, as forced by the signed phase. -/
theorem d4BM_actualNegativeWhittakerMode_raise_eq_phase_mul_lower
    (N : ℕ) (nu : ℂ) (x : ℝ) (Y : D4BMPositiveReal) :
    d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (Y : ℂ)
        (d4BMActualSignedWhittakerModeFullSecondJet true N nu x Y) =
      d4BMCompletedEisensteinFourierPhase true N x *
        d4BMPositiveFrequencyLowerNegTwoLowerZeroMode
          (d4BMPositiveFourierScale N) nu Y := by
  have hfirst := d4BM_whittakerP0FirstJet_eq_lowerZeroShift_div_sub
    (d4BMPositiveFourierScale N) nu Y.2
  have hsecond := d4BM_whittakerP0SecondJet_eq_lowerZero
    (d4BMPositiveFourierScale N) nu Y
  have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast Y.2.ne'
  have hrate : d4BMSignedFourierRate true N =
      -(d4BMPositiveFourierScale N : ℂ) * Complex.I := by
    simp [d4BMSignedFourierRate, d4BMFourierSign]
  have hmode :
      d4BMPositiveFrequencyLowerNegTwoLowerZeroMode
          (d4BMPositiveFourierScale N) nu Y =
        d4BMPositiveFrequencyMaassLowerAt (-2)
          (d4BMPositiveFourierScale N) Y
          (d4BMPositiveFrequencyLowerZeroShift
            (d4BMPositiveFourierScale N) nu Y)
          (d4BMPositiveFrequencyLowerZeroModeDeriv
            (d4BMPositiveFourierScale N) nu Y) := by
    rfl
  rw [hmode]
  unfold d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet
    d4BMActualSignedWhittakerModeFullSecondJet
    d4BMSignedWhittakerModeHorizontalSecondJet
    d4BMSignedWhittakerModeMixedSecondJet
    d4BMSignedWhittakerModeHorizontalFirstJet
    d4BMSignedWhittakerModeVerticalSecondJet
    d4BMSignedWhittakerModeVerticalFirstJet
    d4BMSignedWhittakerMode
    d4BMPositiveFrequencyMaassLowerAt
  rw [hsecond, hrate]
  rw [d4BM_whittakerP0FirstJet_eq_deriv] at hfirst ⊢
  rw [hfirst]
  field_simp [hYne]
  simp_rw [Complex.I_sq] at ⊢
  ring

/-- On a negative Fourier mode, literal lowering exchanges with the positive-frequency
raising word, as forced by the signed phase. -/
theorem d4BM_actualNegativeWhittakerMode_lower_eq_phase_mul_raise
    (N : ℕ) (nu : ℂ) (x : ℝ) (Y : D4BMPositiveReal) :
    d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (Y : ℂ)
        (d4BMActualSignedWhittakerModeFullSecondJet true N nu x Y) =
      d4BMCompletedEisensteinFourierPhase true N x *
        d4BMPositiveFrequencyRaiseTwoRaiseZeroMode
          (d4BMPositiveFourierScale N) nu Y := by
  have hfirst := d4BM_whittakerP0FirstJet_eq_raiseZeroShift_div_add
    (d4BMPositiveFourierScale N) nu Y.2
  have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast Y.2.ne'
  have hrate : d4BMSignedFourierRate true N =
      -(d4BMPositiveFourierScale N : ℂ) * Complex.I := by
    simp [d4BMSignedFourierRate, d4BMFourierSign]
  have hmode :
      d4BMPositiveFrequencyRaiseTwoRaiseZeroMode
          (d4BMPositiveFourierScale N) nu Y =
        d4BMPositiveFrequencyMaassRaiseAt 2
          (d4BMPositiveFourierScale N) Y
          (d4BMPositiveFrequencyRaiseZeroShift
            (d4BMPositiveFourierScale N) nu Y)
          (d4BMPositiveFrequencyRaiseZeroModeDeriv
            (d4BMPositiveFourierScale N) nu Y) := by
    rfl
  rw [hmode]
  unfold d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet
    d4BMActualSignedWhittakerModeFullSecondJet
    d4BMSignedWhittakerModeHorizontalSecondJet
    d4BMSignedWhittakerModeMixedSecondJet
    d4BMSignedWhittakerModeHorizontalFirstJet
    d4BMSignedWhittakerModeVerticalSecondJet
    d4BMSignedWhittakerModeVerticalFirstJet
    d4BMSignedWhittakerMode
    d4BMPositiveFrequencyMaassRaiseAt
    d4BMWhittakerP0SecondJet
  rw [hrate]
  rw [d4BM_whittakerP0FirstJet_eq_deriv] at hfirst ⊢
  rw [hfirst]
  field_simp [hYne]
  simp_rw [Complex.I_sq] at ⊢
  ring

end
end RHTower
