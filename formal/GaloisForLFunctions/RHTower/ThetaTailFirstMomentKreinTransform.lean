import GaloisForLFunctions.RHTower.ThetaTailFirstMomentKernel
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceSpectrumExact
import GaloisForLFunctions.RHTower.WeightedLaplaceShift

/-!
# Bilateral theta transform and the integrated Krein difference

The actual theta-cusp source has an entire bilateral Laplace transform.  Its two translated
first-moment channels are evaluated exactly, and their integrated Krein difference is identified
with the logarithmic-derivative Bezoutian.  All definitions retain literal source integrals.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- Bilateral Laplace transform of the actual completed theta-cusp source. -/
def thetaBilateralLaplace (w : ℂ) : ℂ :=
  thetaCuspFourierLaplace (I * w)

/-- First bilateral Laplace moment of the actual completed theta-cusp source. -/
def thetaBilateralLaplaceMoment (w : ℂ) : ℂ :=
  ∫ x : ℝ, (x : ℂ) * (thetaCuspFullSource x : ℂ) *
    Complex.exp (w * (x : ℂ))

lemma thetaBilateralLaplace_eq_integral (w : ℂ) :
    thetaBilateralLaplace w =
      ∫ x : ℝ, (thetaCuspFullSource x : ℂ) * Complex.exp (w * (x : ℂ)) := by
  unfold thetaBilateralLaplace thetaCuspFourierLaplace
  apply integral_congr_ae
  filter_upwards with x
  unfold thetaCuspFourierLaplaceIntegrand
  rw [show -I * (I * w) * (x : ℂ) = w * (x : ℂ) by
    rw [← mul_assoc, neg_mul, I_mul_I]
    ring]
  ring

lemma integrable_thetaBilateralLaplace (w : ℂ) :
    Integrable (fun x : ℝ =>
      (thetaCuspFullSource x : ℂ) * Complex.exp (w * (x : ℂ))) := by
  have h := HedenmalmThetaSource.integrable_thetaCuspFourierLaplaceIntegrand_all (I * w)
  apply h.congr
  filter_upwards with x
  unfold thetaCuspFourierLaplaceIntegrand
  rw [show -I * (I * w) * (x : ℂ) = w * (x : ℂ) by
    rw [← mul_assoc, neg_mul, I_mul_I]
    ring]
  ring

lemma integrable_thetaBilateralLaplaceMoment (w : ℂ) :
    Integrable (fun x : ℝ =>
      (x : ℂ) * (thetaCuspFullSource x : ℂ) * Complex.exp (w * (x : ℂ))) := by
  have h :=
    HedenmalmThetaSource.integrable_thetaCuspFourierLaplaceDerivativeIntegrand_all (I * w)
  have h' := h.const_mul I
  apply h'.congr
  filter_upwards with x
  unfold thetaCuspFourierLaplaceDerivativeIntegrand thetaCuspFourierLaplaceIntegrand
  rw [show -I * (I * w) * (x : ℂ) = w * (x : ℂ) by
    rw [← mul_assoc, neg_mul, I_mul_I]
    ring]
  rw [show I * ((-I * (x : ℂ)) *
      (Complex.exp (w * (x : ℂ)) * (thetaCuspFullSource x : ℂ))) =
      (x : ℂ) * (thetaCuspFullSource x : ℂ) * Complex.exp (w * (x : ℂ)) by
    calc
      I * ((-I * (x : ℂ)) *
          (Complex.exp (w * (x : ℂ)) * (thetaCuspFullSource x : ℂ))) =
          (I * -I) * (x : ℂ) *
            (Complex.exp (w * (x : ℂ)) * (thetaCuspFullSource x : ℂ)) := by ring
      _ = (x : ℂ) * (thetaCuspFullSource x : ℂ) *
          Complex.exp (w * (x : ℂ)) := by
        rw [show I * -I = (1 : ℂ) by rw [mul_neg, I_mul_I]; ring]
        ring]

theorem thetaBilateralLaplace_eq_XiC (w : ℂ) :
    thetaBilateralLaplace w = XiC (I * w) := by
  exact HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all (I * w)

/-- First source moment is complex derivative of bilateral transform. -/
theorem deriv_thetaBilateralLaplace (w : ℂ) :
    deriv thetaBilateralLaplace w = thetaBilateralLaplaceMoment w := by
  have houter :=
    HedenmalmThetaSource.hasDerivAt_thetaCuspFourierLaplace_all (I * w)
  have hinner : HasDerivAt (fun z : ℂ => I * z) I w := by
    simpa using (hasDerivAt_id w).const_mul I
  have hcomp := houter.comp w hinner
  have hvalue :
      (∫ x : ℝ, thetaCuspFourierLaplaceDerivativeIntegrand (I * w) x) * I =
        thetaBilateralLaplaceMoment w := by
    rw [← MeasureTheory.integral_mul_const]
    unfold thetaBilateralLaplaceMoment
    apply integral_congr_ae
    filter_upwards with x
    unfold thetaCuspFourierLaplaceDerivativeIntegrand thetaCuspFourierLaplaceIntegrand
    rw [show -I * (I * w) * (x : ℂ) = w * (x : ℂ) by
      rw [← mul_assoc, neg_mul, I_mul_I]
      ring]
    calc
      ((-I * (x : ℂ)) *
          (Complex.exp (w * (x : ℂ)) * (thetaCuspFullSource x : ℂ))) * I =
          (-I * I) * (x : ℂ) *
            (Complex.exp (w * (x : ℂ)) * (thetaCuspFullSource x : ℂ)) := by ring
      _ = (x : ℂ) * (thetaCuspFullSource x : ℂ) *
          Complex.exp (w * (x : ℂ)) := by
        rw [show -I * I = (1 : ℂ) by rw [neg_mul, I_mul_I]; ring]
        ring
  rw [← hvalue]
  exact hcomp.deriv

/-- Source-integral realization of positive Krein channel. -/
def thetaTailKreinPlusTransform (c : ℝ) (w : ℂ) (s : ℝ) : ℂ :=
  ∫ x : ℝ, ((x + s + c : ℝ) : ℂ) * (thetaCuspFullSource (x + s) : ℂ) *
    Complex.exp (w * (x : ℂ))

/-- Source-integral realization of negative Krein channel. -/
def thetaTailKreinMinusTransform (c : ℝ) (w : ℂ) (s : ℝ) : ℂ :=
  ∫ x : ℝ, ((x + s - c : ℝ) : ℂ) * (thetaCuspFullSource (x + s) : ℂ) *
    Complex.exp (w * (x : ℂ))

lemma thetaTailKreinPlusTransform_eq (c : ℝ) (w : ℂ) (s : ℝ) :
    thetaTailKreinPlusTransform c w s =
      Complex.exp (-(w * (s : ℂ))) *
        (thetaBilateralLaplaceMoment w + (c : ℂ) * thetaBilateralLaplace w) := by
  let G : ℝ → ℂ := fun y =>
    ((y + c : ℝ) : ℂ) * (thetaCuspFullSource y : ℂ) *
      Complex.exp (w * ((y - s : ℝ) : ℂ))
  have htrans := MeasureTheory.integral_add_right_eq_self (μ := volume) G s
  have hpoint (x : ℝ) :
      G (x + s) = ((x + s + c : ℝ) : ℂ) *
        (thetaCuspFullSource (x + s) : ℂ) * Complex.exp (w * (x : ℂ)) := by
    dsimp [G]
    congr 2
    push_cast
    ring
  unfold thetaTailKreinPlusTransform
  rw [show (fun x : ℝ => ((x + s + c : ℝ) : ℂ) *
      (thetaCuspFullSource (x + s) : ℂ) * Complex.exp (w * (x : ℂ))) =
      fun x => G (x + s) by funext x; exact (hpoint x).symm]
  rw [htrans]
  have hbase := integrable_thetaBilateralLaplace w
  have hmoment := integrable_thetaBilateralLaplaceMoment w
  rw [show G = fun y : ℝ => Complex.exp (-(w * (s : ℂ))) *
      (((y : ℂ) * (thetaCuspFullSource y : ℂ) * Complex.exp (w * (y : ℂ))) +
       ((c : ℂ) * ((thetaCuspFullSource y : ℂ) * Complex.exp (w * (y : ℂ))))) by
    funext y
    dsimp [G]
    rw [show w * ((y - s : ℝ) : ℂ) = -(w * (s : ℂ)) + w * (y : ℂ) by
      push_cast
      ring, Complex.exp_add]
    push_cast
    ring]
  rw [MeasureTheory.integral_const_mul, integral_add hmoment (hbase.const_mul (c : ℂ)),
    MeasureTheory.integral_const_mul, thetaBilateralLaplaceMoment,
    ← thetaBilateralLaplace_eq_integral]

lemma thetaTailKreinMinusTransform_eq (c : ℝ) (w : ℂ) (s : ℝ) :
    thetaTailKreinMinusTransform c w s =
      Complex.exp (-(w * (s : ℂ))) *
        (thetaBilateralLaplaceMoment w - (c : ℂ) * thetaBilateralLaplace w) := by
  simpa [thetaTailKreinMinusTransform, thetaTailKreinPlusTransform, sub_eq_add_neg]
    using thetaTailKreinPlusTransform_eq (-c) w s

/-- Logarithmic-derivative Bezoutian of actual bilateral theta transform. -/
def thetaBilateralLaplaceBezoutian (w v : ℂ) : ℂ :=
  (thetaBilateralLaplaceMoment w * (starRingEnd ℂ) (thetaBilateralLaplace v) +
    thetaBilateralLaplace w * (starRingEnd ℂ) (thetaBilateralLaplaceMoment v)) /
      (w + (starRingEnd ℂ) v)

/-- Integrated Krein difference equals actual theta-transform Bezoutian throughout right half of
two-variable Laplace domain. -/
theorem integral_thetaTailKreinDifference_eq_bilateralLaplaceBezoutian
    {c : ℝ} (hc : 0 < c) {w v : ℂ}
    (hwv : 0 < (w + (starRingEnd ℂ) v).re) :
    (1 / (2 * c : ℂ)) * ∫ s in Ioi (0 : ℝ),
      (thetaTailKreinPlusTransform c w s *
          (starRingEnd ℂ) (thetaTailKreinPlusTransform c v s) -
        thetaTailKreinMinusTransform c w s *
          (starRingEnd ℂ) (thetaTailKreinMinusTransform c v s)) =
      thetaBilateralLaplaceBezoutian w v := by
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
  let q : ℂ := w + (starRingEnd ℂ) v
  let N : ℂ :=
    thetaBilateralLaplaceMoment w * (starRingEnd ℂ) (thetaBilateralLaplace v) +
      thetaBilateralLaplace w * (starRingEnd ℂ) (thetaBilateralLaplaceMoment v)
  have hconjexp (z : ℂ) (s : ℝ) :
      (starRingEnd ℂ) (Complex.exp (-(z * (s : ℂ)))) =
        Complex.exp (-((starRingEnd ℂ) z * (s : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  have hpoint (s : ℝ) :
      thetaTailKreinPlusTransform c w s *
          (starRingEnd ℂ) (thetaTailKreinPlusTransform c v s) -
        thetaTailKreinMinusTransform c w s *
          (starRingEnd ℂ) (thetaTailKreinMinusTransform c v s) =
      (2 * c : ℂ) * N * Complex.exp (-(q * (s : ℂ))) := by
    rw [thetaTailKreinPlusTransform_eq, thetaTailKreinPlusTransform_eq,
      thetaTailKreinMinusTransform_eq, thetaTailKreinMinusTransform_eq]
    simp only [map_mul]
    rw [hconjexp v s]
    simp only [map_add, map_sub, map_mul, Complex.conj_ofReal]
    have hexp :
        Complex.exp (-(w * (s : ℂ))) *
          Complex.exp (-((starRingEnd ℂ) v * (s : ℂ))) =
        Complex.exp (-(q * (s : ℂ))) := by
      rw [← Complex.exp_add]
      dsimp [q]
      congr 1
      ring
    dsimp [N]
    calc
      _ = (2 * c : ℂ) *
          (thetaBilateralLaplaceMoment w *
              (starRingEnd ℂ) (thetaBilateralLaplace v) +
            thetaBilateralLaplace w *
              (starRingEnd ℂ) (thetaBilateralLaplaceMoment v)) *
            (Complex.exp (-(w * (s : ℂ))) *
              Complex.exp (-((starRingEnd ℂ) v * (s : ℂ)))) := by ring
      _ = _ := by rw [hexp]
  have hq : 0 < q.re := by simpa [q] using hwv
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s _ => hpoint s),
    MeasureTheory.integral_const_mul,
    GaloisForLFunctions.RHTower.integral_cexp_neg_mul_Ioi_zero hq]
  dsimp [thetaBilateralLaplaceBezoutian, N, q]
  field_simp [hcne, show w + (starRingEnd ℂ) v ≠ 0 by
    intro h
    rw [h] at hwv
    simp at hwv]

end RHTower
