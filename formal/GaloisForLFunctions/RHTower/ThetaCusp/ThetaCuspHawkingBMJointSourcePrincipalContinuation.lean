import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceTortoiseContinuation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourcePrincipalEquation

/-! Continuation retains all three original principal responses and their full-square lift subtraction. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The actual fixed-onset amplitude is meromorphic at every independent frequency. -/
theorem sourceAmplitude_continued_meromorphic (s a : ℂ) (t : ℝ) :
    Meromorphic (fun w => sourceAmplitude s w a (continuedOnset s w) t) := by
  intro w
  have hi : MeromorphicAt (fun u : ℂ => 1/(u-2*s)) w :=
    (show AnalyticAt ℂ (fun _ : ℂ => (1:ℂ)) w from analyticAt_const).meromorphicAt.div
      (show AnalyticAt ℂ (fun u : ℂ => u-2*s) w by fun_prop).meromorphicAt
  have hT := hi.add ((onsetCorrection_entire (2*s)).analyticAt w).meromorphicAt
  have hp : AnalyticAt ℂ (fun u : ℂ => Complex.exp (u*(t:ℂ))*power (2*s) (1+radialUnit t)*a^(2 : ℕ)) w := by fun_prop
  exact hp.meromorphicAt.mul hT

/-- Meromorphy of the full-square lift with its original smooth onset retained. -/
theorem radialLift_continued_meromorphic (s a : ℂ) (t : ℝ) :
    Meromorphic (fun w => radialLift s w a (continuedOnset s w) t) := by
  intro w
  have h := (sourceAmplitude_continued_meromorphic s a t w).mul
    (show AnalyticAt ℂ (fun _ : ℂ => (radialUnit t:ℂ)^(3 : ℕ)) w from analyticAt_const).meromorphicAt
  exact (show AnalyticAt ℂ (fun _ : ℂ => -s*(s-1)/4) w from analyticAt_const).meromorphicAt.mul h

/-- Meromorphy of the original reduced source coefficient, including every differentiated amplitude term. -/
theorem reducedCoefficient_continued_meromorphic (s a : ℂ) (t : ℝ) :
    Meromorphic (fun w => reducedCoefficient s w a (continuedOnset s w) t) := by
  intro w
  exact (sourceAmplitude_continued_meromorphic s a t w).mul
    (show AnalyticAt ℂ (fun u => reducedPolynomial s u (radialUnit t)) w by
      unfold reducedPolynomial liftSecondPolynomial amplitudeRate; fun_prop).meromorphicAt

/-- The continued original principal response minus its exact full-square lift. -/
def continuedPrincipalDifference (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (i : Fin 3) (t : ℝ) : ℂ :=
  continuedTortoiseGreen w (principalFrequency q i) (physicalRate q branch) a
      (principalAmplitude q i) (principalGradient q branch i) t-
    radialLift (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*principalAmplitude q i

def continuedPrincipalDifferenceFirst (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (i : Fin 3) (t : ℝ) : ℂ :=
  continuedTortoiseGreenFirst w (principalFrequency q i) (physicalRate q branch) a
      (principalAmplitude q i) (principalGradient q branch i) t-
    radialLiftFirst (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*principalAmplitude q i

def continuedPrincipalDifferenceSecond (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (i : Fin 3) (t : ℝ) : ℂ :=
  continuedTortoiseGreenSecond w (principalFrequency q i) (physicalRate q branch) a
      (principalAmplitude q i) (principalGradient q branch i) t-
    radialLiftSecond (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*principalAmplitude q i

/-- Exact equality to the original principal subtraction in the genuine source convergence chamber. -/
theorem continuedPrincipalDifference_eq_original (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -1 < w.re) (hs : (2*physicalRate q branch).re < w.re)
    (i : Fin 3) (t : ℝ) (ht : t < 0) :
    continuedPrincipalDifference q branch w a i t =
      principalDifference q branch w a (onsetTransform (2*physicalRate q branch) w) i t := by
  rw [continuedPrincipalDifference,principalDifference,
    continuedTortoiseGreen_eq_original _ _ _ _ _ _ hw hwre hs t ht]
  rw [continuedOnset,← onsetTransform_eq (2*physicalRate q branch) w hs]

/-- Each original principal correction has a frequency-meromorphic germ throughout the continued strip. -/
theorem continuedPrincipalDifference_meromorphicAt (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (i : Fin 3) (t : ℝ) (ht : t < 0) :
    MeromorphicAt (fun u => continuedPrincipalDifference q branch u a i t) w :=
  (continuedTortoiseGreen_meromorphicAt _ _ _ _ _ _ hw hwre t ht).sub
    ((radialLift_continued_meromorphic _ a t w).mul
      (show AnalyticAt ℂ (fun _ : ℂ => principalAmplitude q i) w from analyticAt_const).meromorphicAt)

/-- The continued principal jets are actual radial derivatives of the original subtraction. -/
theorem continuedPrincipalDifference_hasDerivAt (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (i : Fin 3) (t : ℝ) (ht : t < 0) :
    HasDerivAt (continuedPrincipalDifference q branch w a i)
        (continuedPrincipalDifferenceFirst q branch w a i t) t ∧
      HasDerivAt (continuedPrincipalDifferenceFirst q branch w a i)
        (continuedPrincipalDifferenceSecond q branch w a i t) t := by
  have hg := continuedTortoiseGreen_hasDerivAt w (principalFrequency q i) (physicalRate q branch) a
    (principalAmplitude q i) (principalGradient q branch i) hw hwre t ht
  exact ⟨hg.1.sub ((radialLift_hasDerivAt _ _ _ _ t).mul_const _),
    hg.2.sub ((radialLiftFirst_hasDerivAt _ _ _ _ t).mul_const _)⟩

/-- The second displayed principal jet is the actual iterated derivative. -/
theorem continuedPrincipalDifference_secondDerivative (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (i : Fin 3) (t : ℝ) (ht : t < 0) :
    deriv (deriv (continuedPrincipalDifference q branch w a i)) t =
      continuedPrincipalDifferenceSecond q branch w a i t := by
  have he : deriv (continuedPrincipalDifference q branch w a i) =ᶠ[𝓝 t]
      continuedPrincipalDifferenceFirst q branch w a i := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with x hx
    exact (continuedPrincipalDifference_hasDerivAt q branch w a hw hwre i x hx).1.deriv
  rw [he.deriv_eq]
  exact (continuedPrincipalDifference_hasDerivAt q branch w a hw hwre i t ht).2.deriv

/-- Every continued principal difference solves its original reduced squared-source equation. -/
theorem continuedPrincipalDifference_equation (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (i : Fin 3)
    (hc : connection w (principalFrequency q i) ≠ 0) (t : ℝ) (ht : t < 0) :
    w^(2 : ℕ)*continuedPrincipalDifference q branch w a i t-
        deriv (deriv (continuedPrincipalDifference q branch w a i)) t-
        (horizonCoordinate t:ℂ)*principalExponent q i*(principalExponent q i-1)*
          continuedPrincipalDifference q branch w a i t =
      reducedCoefficient (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*principalAmplitude q i := by
  have he := continuedTortoiseGreen_equation w (principalFrequency q i) (physicalRate q branch) a
    (principalAmplitude q i) (principalGradient q branch i) hw hwre hc t ht
  rw [principalFrequency_parameter] at he
  rw [continuedPrincipalDifference_secondDerivative q branch w a hw hwre i t ht]
  dsimp only [continuedPrincipalDifference,continuedPrincipalDifferenceSecond]
  dsimp [originalForcing,principalGradient,reducedCoefficient,reducedPolynomial,
    radialLift,radialLiftSecond,horizonCoordinate] at he ⊢
  push_cast at he ⊢
  linear_combination he

end
end RHTower.D4BMJointSource
