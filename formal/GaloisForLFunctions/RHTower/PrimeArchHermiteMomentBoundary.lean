import Mathlib.Data.Real.Basic

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# A Gaussian–Hermite boundary for the K-RVM source determinant

The paper density is the standard Gaussian times `1 + t P`, where
`P = -He₄ + He₆ - 2 He₈ + He₁₀`. Its normalized even moments through
degree ten are `(1, 3-24t, 15+360t, 105-65520t, 945+378000t)`.
The exact cumulant-to-Hankel calculation below gives a negative first open
determinant while the first four prime--archimedean moments and the
source-style radius and rescaled score inequalities are positive.

The Gaussian integral identity and strong log-concavity of this density are
paper-proved in the K-RVM card; this Lean leaf proves the exact algebraic
moment boundary, without asserting those analytic facts in Lean.
-/

namespace RHTower
noncomputable section

/-- Even standard-Gaussian moments, in their Wick recurrence coordinates. -/
def gaussianEvenWickMoment : ℕ → ℝ
  | 0 => 1
  | n + 1 => (2*n+1)*gaussianEvenWickMoment n

/-- Moment correction from the polynomial
`-He₄+He₆-2He₈+He₁₀ = X¹⁰-47X⁸+687X⁶-3586X⁴+5616X²-1173`. -/
def hermiteBoundaryWickCorrection (j : ℕ) : ℝ :=
  gaussianEvenWickMoment (j+5)-47*gaussianEvenWickMoment (j+4)+
    687*gaussianEvenWickMoment (j+3)-3586*gaussianEvenWickMoment (j+2)+
    5616*gaussianEvenWickMoment (j+1)-1173*gaussianEvenWickMoment j

/-- The polynomial has zero mass and second-moment correction; its next four
even-moment corrections are exact. The Wick recurrence is the algebraic
counterpart of Gaussian integration by parts. -/
theorem hermiteBoundaryWickCorrection_exact :
    hermiteBoundaryWickCorrection 0=0 ∧
    hermiteBoundaryWickCorrection 1=0 ∧
    hermiteBoundaryWickCorrection 2=-24 ∧
    hermiteBoundaryWickCorrection 3=360 ∧
    hermiteBoundaryWickCorrection 4=-65520 ∧
    hermiteBoundaryWickCorrection 5=378000 := by
  norm_num [hermiteBoundaryWickCorrection, gaussianEvenWickMoment]

def hermiteB (t : ℝ) : ℝ := 3 - 24*t
def hermiteC (t : ℝ) : ℝ := 15 + 360*t
def hermiteE (t : ℝ) : ℝ := 105 - 65520*t
def hermiteF (t : ℝ) : ℝ := 945 + 378000*t

/-- The moment tuple used below is exactly the Wick moment tuple of the
displayed Gaussian--Hermite polynomial perturbation. -/
theorem hermiteMoments_eq_wick (t : ℝ) :
    hermiteB t = gaussianEvenWickMoment 2 +
        t*hermiteBoundaryWickCorrection 2 ∧
    hermiteC t = gaussianEvenWickMoment 3 +
        t*hermiteBoundaryWickCorrection 3 ∧
    hermiteE t = gaussianEvenWickMoment 4 +
        t*hermiteBoundaryWickCorrection 4 ∧
    hermiteF t = gaussianEvenWickMoment 5 +
        t*hermiteBoundaryWickCorrection 5 := by
  obtain ⟨_, _, h2, h3, h4, h5⟩ := hermiteBoundaryWickCorrection_exact
  rw [h2, h3, h4, h5]
  norm_num [hermiteB, hermiteC, hermiteE, hermiteF,
    gaussianEvenWickMoment] <;> (repeat' constructor) <;> ring

def hermiteV (t : ℝ) : ℝ := 1/2 - hermiteB t/6
def hermiteW (t : ℝ) : ℝ := hermiteC t/120 - hermiteB t/8 + 1/4
def hermiteZ (t : ℝ) : ℝ :=
  hermiteC t/180 + (hermiteB t)^2/144 - hermiteB t/12 + 1/8 - hermiteE t/5040
def hermiteY (t : ℝ) : ℝ :=
  (hermiteF t - 9*hermiteE t + 504*hermiteV t*hermiteC t -
    15120*hermiteW t*hermiteB t + 181440*hermiteZ t)/362880
def hermiteDet (t : ℝ) : ℝ :=
  (hermiteW t - (hermiteV t)^2)*hermiteY t -
    ((hermiteZ t)^2-2*hermiteV t*hermiteW t*hermiteZ t+(hermiteW t)^3)

/-- Exact tangent-cone law at a Gaussian moment tuple: the leading
size-three determinant coefficient is `w*y-z²`; the lower moment `v`
enters one order later. -/
theorem gaussianTangentDet_factor (t v w z y : ℝ) :
    (t*w-(t*v)^2)*(t*y) -
      ((t*z)^2-2*(t*v)*(t*w)*(t*z)+(t*w)^3) =
    t^2*(w*y-z^2+t*(2*v*w*z-v^2*y-w^3)) := by
  ring

/-! The four even Hermite modes diagonalize the tangent of the
prime--archimedean cumulant map at the Gaussian source. -/

def gaussianHermiteB (p t : ℝ) : ℝ := 3 + 24*p*t
def gaussianHermiteC (p q t : ℝ) : ℝ := 15 + (360*p+720*q)*t
def gaussianHermiteE (p q r t : ℝ) : ℝ :=
  105 + (5040*p+20160*q+40320*r)*t
def gaussianHermiteF (p q r s t : ℝ) : ℝ :=
  945 + (75600*p+453600*q+1814400*r+3628800*s)*t
def gaussianHermiteV (p t : ℝ) : ℝ := 1/2 - gaussianHermiteB p t/6
def gaussianHermiteW (p q t : ℝ) : ℝ :=
  gaussianHermiteC p q t/120 - gaussianHermiteB p t/8 + 1/4
def gaussianHermiteZ (p q r t : ℝ) : ℝ :=
  gaussianHermiteC p q t/180 + (gaussianHermiteB p t)^2/144 -
    gaussianHermiteB p t/12 + 1/8 - gaussianHermiteE p q r t/5040
def gaussianHermiteY (p q r s t : ℝ) : ℝ :=
  (gaussianHermiteF p q r s t - 9*gaussianHermiteE p q r t +
    504*gaussianHermiteV p t*gaussianHermiteC p q t -
    15120*gaussianHermiteW p q t*gaussianHermiteB p t +
    181440*gaussianHermiteZ p q r t)/362880
def gaussianHermiteDet (p q r s t : ℝ) : ℝ :=
  (gaussianHermiteW p q t-(gaussianHermiteV p t)^2)*gaussianHermiteY p q r s t -
    ((gaussianHermiteZ p q r t)^2-
      2*(gaussianHermiteV p t)*(gaussianHermiteW p q t)*(gaussianHermiteZ p q r t)+
      (gaussianHermiteW p q t)^3)

private theorem gaussianHermiteV_eq (p t : ℝ) : gaussianHermiteV p t = -4*p*t := by
  unfold gaussianHermiteV gaussianHermiteB
  ring
private theorem gaussianHermiteW_eq (p q t : ℝ) : gaussianHermiteW p q t = 6*q*t := by
  unfold gaussianHermiteW gaussianHermiteB gaussianHermiteC
  ring
private theorem gaussianHermiteZ_eq (p q r t : ℝ) :
    gaussianHermiteZ p q r t = -8*r*t+4*p^2*t^2 := by
  unfold gaussianHermiteZ gaussianHermiteB gaussianHermiteC gaussianHermiteE
  ring
private theorem gaussianHermiteY_eq (p q r s t : ℝ) :
    gaussianHermiteY p q r s t = 10*s*t-10*p*q*t^2 := by
  unfold gaussianHermiteY
  rw [gaussianHermiteV_eq, gaussianHermiteW_eq, gaussianHermiteZ_eq]
  unfold gaussianHermiteB gaussianHermiteC gaussianHermiteE gaussianHermiteF
  ring

/-- Exact Gaussian--Hermite tangent-cone classification for the first
prime--archimedean size-three determinant. Its leading sign is the
two-by-two Hermite coefficient minor `60*q*s-64*r²`. -/
theorem gaussianHermiteDet_exact (p q r s t : ℝ) :
    gaussianHermiteDet p q r s t = t^2 * (
      60*q*s-64*r^2 +
      t*(-60*p*q^2-160*p^2*s+64*p^2*r+384*p*q*r-216*q^3) +
      t^2*(-32*p^3*q-16*p^4)) := by
  unfold gaussianHermiteDet
  rw [gaussianHermiteV_eq, gaussianHermiteW_eq,
    gaussianHermiteZ_eq, gaussianHermiteY_eq]
  ring

private theorem hermiteV_eq (t : ℝ) : hermiteV t = 4*t := by
  unfold hermiteV hermiteB
  ring
private theorem hermiteW_eq (t : ℝ) : hermiteW t = 6*t := by
  unfold hermiteW hermiteB hermiteC
  ring
private theorem hermiteZ_eq (t : ℝ) : hermiteZ t = t*(16+4*t) := by
  unfold hermiteZ hermiteB hermiteC hermiteE
  ring
private theorem hermiteY_eq (t : ℝ) : hermiteY t = t*(10+10*t) := by
  unfold hermiteY
  rw [hermiteV_eq, hermiteW_eq, hermiteZ_eq]
  unfold hermiteB hermiteC hermiteE hermiteF
  ring
/-- Exact size-three determinant of the Gaussian--Hermite moment tuple. -/
theorem hermiteDet_eq (t : ℝ) :
    hermiteDet t = t^2*(-196+324*t+16*t^2) := by
  unfold hermiteDet
  rw [hermiteV_eq, hermiteW_eq, hermiteZ_eq, hermiteY_eq]
  ring

/-- Spatial scaling of the source moments preserves the determinant sign;
the determinant has weight eighteen. -/
theorem hermiteDet_spatialScale (s t : ℝ) :
    ((s^2)*(s^6*hermiteW t)-(s^4*hermiteV t)^2)*(s^10*hermiteY t) -
      ((s^2)*(s^8*hermiteZ t)^2 -
        2*(s^4*hermiteV t)*(s^6*hermiteW t)*(s^8*hermiteZ t) +
        (s^6*hermiteW t)^3) = s^18*hermiteDet t := by
  unfold hermiteDet
  ring

/-- Negative size-three prime--archimedean determinant for small positive perturbation. -/
theorem hermitePerturbation_det_neg {t : ℝ} (ht : 0 < t) (ht1 : t < 1/2) :
    hermiteDet t < 0 := by
  rw [hermiteDet_eq]
  have ht2 : t^2 < t/2 := by nlinarith [mul_pos ht (by linarith : 0 < 1/2-t)]
  have hpol : -196+324*t+16*t^2 < 0 := by nlinarith
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos ht) hpol


/-- The same shape has the low-order signs and source-style radius/score bounds
at sufficiently small positive perturbation. The score inequality is the
fifth-moment recurrence after spatial rescaling by `1/10`. -/
theorem hermitePerturbation_sourceLikeConstraints {t : ℝ}
    (ht : 0 < t) (htsmall : t < 1/1000) :
    0 < hermiteV t ∧ 0 < hermiteW t ∧
    0 < hermiteW t - (hermiteV t)^2 ∧
    0 < hermiteZ t ∧
    0 < hermiteY t ∧
    0 < 21 * hermiteC t - 25 * (hermiteB t)^2 ∧
    14 * (hermiteB t)^2 < 9 * hermiteC t ∧
    303 * hermiteF t / 100 < 145 * hermiteE t ∧
    hermiteDet t < 0 := by
  have ht1 : t < 1/2 := by linarith
  have ht2 : t^2 < t := by nlinarith [mul_pos ht (by linarith : 0 < 1-t)]
  rw [hermiteV_eq, hermiteW_eq, hermiteZ_eq, hermiteY_eq]
  refine ⟨by positivity, by positivity, ?_, by positivity, by positivity,
    ?_, ?_, ?_, hermitePerturbation_det_neg ht ht1⟩
  · nlinarith
  · dsimp [hermiteC, hermiteB]
    nlinarith
  · dsimp [hermiteC, hermiteB]
    nlinarith
  · dsimp [hermiteF, hermiteE]
    linarith

end
end RHTower
