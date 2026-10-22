import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMReducedGreenResponse
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourcePrincipalContinuation

/-! Frequency continuation of the original reduced-source response at an independent angular parameter. -/
open Complex Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def continuedReducedGreen (w chi s a J : ℂ) (t : ℝ) : ℂ :=
  continuedTortoiseGreen w chi s a J (reducedGreenGradient chi s J) t-
    radialLift s w a (continuedOnset s w) t*J

def continuedReducedGreenFirst (w chi s a J : ℂ) (t : ℝ) : ℂ :=
  continuedTortoiseGreenFirst w chi s a J (reducedGreenGradient chi s J) t-
    radialLiftFirst s w a (continuedOnset s w) t*J

def continuedReducedGreenSecond (w chi s a J : ℂ) (t : ℝ) : ℂ :=
  continuedTortoiseGreenSecond w chi s a J (reducedGreenGradient chi s J) t-
    radialLiftSecond s w a (continuedOnset s w) t*J

/-- The continued family is the original source response on the genuine overlap. -/
theorem continuedReducedGreen_eq_original (w chi s a J : ℂ) (hw : w.im ≠ 0)
    (hwr : -1 < w.re) (hs : (2*s).re < w.re) (t : ℝ) (ht : t < 0) :
    continuedReducedGreen w chi s a J t =
      reducedGreen w chi s a J (onsetTransform (2*s) w) t := by
  unfold continuedReducedGreen reducedGreen
  rw [continuedTortoiseGreen_eq_original _ _ _ _ _ _ hw hwr hs t ht,
    continuedOnset,← onsetTransform_eq (2*s) w hs]

/-- The same reduced-source response is meromorphic through the full fundamental-frequency strip. -/
theorem continuedReducedGreen_meromorphicAt (w chi s a J : ℂ) (hw : w.im ≠ 0)
    (hwr : -2 < w.re) (t : ℝ) (ht : t < 0) :
    MeromorphicAt (fun v => continuedReducedGreen v chi s a J t) w :=
  (continuedTortoiseGreen_meromorphicAt _ _ _ _ _ _ hw hwr t ht).sub
    ((radialLift_continued_meromorphic s a t w).mul
      (show AnalyticAt ℂ (fun _ : ℂ => J) w from analyticAt_const).meromorphicAt)

/-- Continued radial jets retain the original source-dependent lift subtraction. -/
theorem continuedReducedGreen_hasDerivAt (w chi s a J : ℂ) (hw : w.im ≠ 0)
    (hwr : -2 < w.re) (t : ℝ) (ht : t < 0) :
    HasDerivAt (continuedReducedGreen w chi s a J) (continuedReducedGreenFirst w chi s a J t) t ∧
    HasDerivAt (continuedReducedGreenFirst w chi s a J) (continuedReducedGreenSecond w chi s a J t) t := by
  have hg := continuedTortoiseGreen_hasDerivAt w chi s a J (reducedGreenGradient chi s J) hw hwr t ht
  exact ⟨hg.1.sub ((radialLift_hasDerivAt s w a (continuedOnset s w) t).mul_const J),
    hg.2.sub ((radialLiftFirst_hasDerivAt s w a (continuedOnset s w) t).mul_const J)⟩

/-- The continued family solves its actual reduced-source equation away from the original connection zeros. -/
theorem continuedReducedGreen_equation (w chi s a J : ℂ) (hw : w.im ≠ 0)
    (hwr : -2 < w.re) (hc : connection w chi ≠ 0) (t : ℝ) (ht : t < 0) :
    w^(2 : ℕ)*continuedReducedGreen w chi s a J t-continuedReducedGreenSecond w chi s a J t+
      (horizonCoordinate t:ℂ)*(1/4+chi^(2 : ℕ))*continuedReducedGreen w chi s a J t =
        reducedCoefficient s w a (continuedOnset s w) t*J := by
  have he := continuedTortoiseGreen_equation w chi s a J (reducedGreenGradient chi s J) hw hwr hc t ht
  dsimp only [continuedReducedGreen,continuedReducedGreenSecond]
  dsimp [originalForcing,reducedGreenGradient,reducedCoefficient,reducedPolynomial,
    radialLift,radialLiftSecond,horizonCoordinate] at he ⊢
  push_cast at he ⊢
  linear_combination he

end
end RHTower.D4BMJointSource
