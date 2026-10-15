import GaloisForLFunctions.RHTower.ThetaRenewalFullDivisorCharge
import GaloisForLFunctions.RHTower.ThetaCuspPrimeArchSourceEquation
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The full renewal divisor as an absolutely summable prime boundary current

For a theta source `k`, let `H(w)` be its positive-ray transform and `I_n(w)`
its prefix through `log n`. The compensated von Mangoldt current

`J_n(w,z) = Lambda(n) n^(-1/2-w) (z-I_n(w))`

is absolutely summable exactly when `Re w > 1/2` or `z=H(w)`. At the correct
counterterm it is the literal positive-ray transform of the full prime source,
with absolute Fubini valid for every complex parameter. The proof never splits
the compensating prefix from a divergent Euler series.

For the physical renewal charge, `z=i C(lambda)-c lambda` and `w=-2lambda`.
The seam identity gives `z=H(w)-XiC(2i lambda)/2`. Thus admission of the
renewal current is exactly `Re lambda < -1/4` or full-divisor membership.
Throughout the critical strip it retains arbitrary zeros without a
critical-axis or simplicity premise.

At every admitted divisor point the current satisfies the complete arithmetic
Ward balance, retaining Gamma, both pole channels, the source moment and the
local Archimedean term. This is a boundary representation and counterterm
classification. It does not prove that the admitted charge is real or prove RH.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta

noncomputable section

namespace RHTower.ThetaSourceWard

private theorem positiveRay_exp_bound {w : ℂ} {r t : ℝ}
    (hw : w.re ≤ r) (ht : 0 ≤ t) :
    ‖Complex.exp (w * t)‖ ≤ ‖Complex.exp ((r : ℂ) * t)‖ := by
  simp only [Complex.norm_exp, Complex.re_mul_ofReal, Complex.ofReal_re]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hw ht)

private theorem integrableOn_exp_of_le {f : ℝ → ℂ} {w : ℂ} {r : ℝ}
    (hf : Integrable (fun t : ℝ => f t * Complex.exp ((r : ℂ) * t)))
    (hc : Continuous f) (hw : w.re ≤ r) :
    IntegrableOn (fun t : ℝ => f t * Complex.exp (w * t)) (Ioi 0) := by
  refine (hf.norm.integrableOn (s := Ioi 0)).mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_left (positiveRay_exp_bound hw (le_of_lt ht)) (norm_nonneg _)

theorem summable_integral_norm_primeSourceTerm_positiveRay (S : ThetaSource) (w : ℂ) :
    Summable (fun n : ℕ =>
      ∫ t in Ioi (0 : ℝ), ‖primeSourceTerm S n t * Complex.exp (w * t)‖) := by
  let r : ℝ := max w.re 1 + 1
  have hr : 1 / 2 < (r : ℂ).re := by
    simp only [Complex.ofReal_re]
    dsimp [r]
    linarith [le_max_right w.re 1]
  have hwr : w.re ≤ r := by dsimp [r]; linarith [le_max_left w.re 1]
  apply Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun t => norm_nonneg _) _
    (summable_integral_norm_primeSourceTerm_laplace S hr)
  intro n
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ),
        ‖primeSourceTerm S n t * Complex.exp ((r : ℂ) * t)‖ := by
      apply setIntegral_mono_on
        (integrable_primeSourceTerm_laplace S w n).norm.integrableOn
        (integrable_primeSourceTerm_laplace S r n).norm.integrableOn measurableSet_Ioi
      intro t ht
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left (positiveRay_exp_bound hwr (le_of_lt ht))
        (norm_nonneg _)
    _ ≤ _ := setIntegral_le_integral (integrable_primeSourceTerm_laplace S r n).norm
      (Eventually.of_forall fun t => norm_nonneg _)

theorem integrableOn_fullPrimeSource_positiveRay (S : ThetaSource) (w : ℂ) :
    IntegrableOn (fun t : ℝ => fullPrimeSource S t * Complex.exp (w * t)) (Ioi 0) := by
  let r : ℝ := max w.re 1 + 1
  have hr : 1 / 2 < (r : ℂ).re := by
    simp only [Complex.ofReal_re]
    dsimp [r]
    linarith [le_max_right w.re 1]
  exact integrableOn_exp_of_le (fullPrimeSource_laplace_integrable S hr)
    (fullPrimeSource_continuous S) (by dsimp [r]; linarith [le_max_left w.re 1])

private theorem integral_positiveRay_translate (f : ℝ → ℂ) (h : ℝ) :
    (∫ t in Ioi (0 : ℝ), f (t + h)) = ∫ t in Ioi h, f t := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have he : (Ioi (0 : ℝ)).indicator (fun t => f (t + h)) =
      fun t => (Ioi h).indicator f (t + h) := by
    funext t
    have he : h < t + h ↔ 0 < t := by constructor <;> intro ht <;> linarith
    simp only [Set.indicator, Set.mem_Ioi, he]
  rw [he, integral_add_right_eq_self]

/-- The finite prefix stays paired with the one-sided source transform. -/
def primeBoundaryTerm (S : ThetaSource) (w : ℂ) (n : ℕ) : ℂ :=
  primeCoefficient n * Complex.exp (-w * (Real.log n : ℂ)) *
    ((∫ t in Ioi (0 : ℝ), laplaceIntegrand S w t) -
      ∫ t in (0 : ℝ)..Real.log n, laplaceIntegrand S w t)

theorem primeBoundaryTerm_eq_integral (S : ThetaSource) (w : ℂ) (n : ℕ) :
    primeBoundaryTerm S w n =
      ∫ t in Ioi (0 : ℝ), primeSourceTerm S n t * Complex.exp (w * t) := by
  have htail := intervalIntegral.integral_Ioi_sub_Ioi' (a := 0)
    (integrable_laplaceIntegrand S w).integrableOn
    ((integrable_laplaceIntegrand S w).integrableOn (s := Ioi (Real.log n)))
  have hprefix : (∫ t in Ioi (0 : ℝ), laplaceIntegrand S w t) -
      (∫ t in (0 : ℝ)..Real.log n, laplaceIntegrand S w t) =
        ∫ t in Ioi (Real.log n), laplaceIntegrand S w t := by
    linear_combination htail
  simp_rw [primeSourceTerm_laplace_point]
  rw [integral_const_mul, integral_positiveRay_translate, primeBoundaryTerm,
    primeCoefficient_laplace, hprefix]

theorem summable_norm_primeBoundaryTerm (S : ThetaSource) (w : ℂ) :
    Summable (fun n => ‖primeBoundaryTerm S w n‖) := by
  simp_rw [primeBoundaryTerm_eq_integral]
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_integral_le_integral_norm _)
    (summable_integral_norm_primeSourceTerm_positiveRay S w)

theorem tsum_primeBoundaryTerm (S : ThetaSource) (w : ℂ) :
    (∑' n, primeBoundaryTerm S w n) =
      ∫ t in Ioi (0 : ℝ), fullPrimeSource S t * Complex.exp (w * t) := by
  simp_rw [primeBoundaryTerm_eq_integral]
  rw [integral_tsum_of_summable_integral_norm
    (fun n => (integrable_primeSourceTerm_laplace S w n).integrableOn)
    (summable_integral_norm_primeSourceTerm_positiveRay S w)]
  apply integral_congr_ae
  filter_upwards with t
  exact tsum_mul_right

/-- Every Gamma and pole term is integrable on the positive ray in the critical strip. -/
theorem integrableOn_primeBoundary_archimedean {w : ℂ} (hw : w.re ≤ 3 / 4) :
    IntegrableOn (fun t : ℝ => gammaSource t * Complex.exp (w * t)) (Ioi 0) ∧
      IntegrableOn (fun t : ℝ => polarSource (1 / 2) t * Complex.exp (w * t)) (Ioi 0) ∧
      IntegrableOn (fun t : ℝ => polarSource (-1 / 2) t * Complex.exp (w * t)) (Ioi 0) := by
  exact ⟨integrableOn_exp_of_le
    (gammaSource_laplace_integrable (w := (3 / 4 : ℝ)) (by norm_num) (by norm_num))
    gammaSource_continuous hw,
    integrableOn_exp_of_le (polarSource_laplace_integrable (1 / 2)
      (w := (3 / 4 : ℝ)) (by norm_num)) (polarSource_continuous (by norm_num)) hw,
    integrableOn_exp_of_le (polarSource_laplace_integrable (-1 / 2)
      (w := (3 / 4 : ℝ)) (by norm_num)) (polarSource_continuous (by norm_num)) hw⟩

/-- The complete arithmetic balance retains Gamma, both poles, the source moment,
and the local Archimedean term. No Euler series is continued term by term. -/
theorem tsum_primeBoundaryTerm_eq_archimedean {w : ℂ} (hw : w.re ≤ 3 / 4) :
    (∑' n, primeBoundaryTerm thetaCuspTiltSource w n) =
      (∫ t in Ioi (0 : ℝ), gammaSource t * Complex.exp (w * t)) +
      (∫ t in Ioi (0 : ℝ), polarSource (1 / 2) t * Complex.exp (w * t)) +
      (∫ t in Ioi (0 : ℝ), polarSource (-1 / 2) t * Complex.exp (w * t)) -
      archConstant * (∫ t in Ioi (0 : ℝ), laplaceIntegrand thetaCuspTiltSource w t) -
      (∫ t in Ioi (0 : ℝ), (t : ℂ) * (thetaCuspFullSource t : ℂ) *
        Complex.exp (w * t)) := by
  obtain ⟨hg, hp, hm⟩ := integrableOn_primeBoundary_archimedean hw
  have hk := (integrable_laplaceIntegrand thetaCuspTiltSource w).integrableOn (s := Ioi 0)
  have ht := (momentIntegrand_integrable w).integrableOn (s := Ioi 0)
  have hgp : IntegrableOn (fun t : ℝ => gammaSource t * Complex.exp (w * t) +
      polarSource (1 / 2) t * Complex.exp (w * t)) (Ioi 0) := hg.add hp
  have hgpm : IntegrableOn (fun t : ℝ => gammaSource t * Complex.exp (w * t) +
      polarSource (1 / 2) t * Complex.exp (w * t) +
      polarSource (-1 / 2) t * Complex.exp (w * t)) (Ioi 0) := hgp.add hm
  have hgpmk : IntegrableOn (fun t : ℝ => gammaSource t * Complex.exp (w * t) +
      polarSource (1 / 2) t * Complex.exp (w * t) +
      polarSource (-1 / 2) t * Complex.exp (w * t) -
      archConstant * laplaceIntegrand thetaCuspTiltSource w t) (Ioi 0) :=
    hgpm.sub (hk.const_mul archConstant)
  rw [tsum_primeBoundaryTerm, ← integral_const_mul]
  rw [← integral_add hg hp, ← integral_add hgp hm,
    ← integral_sub hgpm (hk.const_mul archConstant), ← integral_sub hgpmk ht]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  have h := complete_theta_source_equation t
  simp only [laplaceIntegrand, thetaCuspTiltSource_k]
  linear_combination -(Complex.exp (w * t)) * h

/-- The uncompensated prime coefficient is not absolutely summable at or
to the left of the Euler boundary. -/
theorem not_summable_norm_primeBoundaryCoefficient {w : ℂ} (hw : w.re ≤ 1 / 2) :
    ¬ Summable (fun n : ℕ =>
      ‖primeCoefficient n * Complex.exp (-w * (Real.log n : ℂ))‖) := by
  intro hs
  have hsp : Summable (fun p : Nat.Primes =>
      ‖primeCoefficient p * Complex.exp (-w * (Real.log (p : ℕ) : ℂ))‖) :=
    hs.comp_injective Subtype.val_injective
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply Nat.Primes.not_summable_one_div
  apply Summable.of_nonneg_of_le (fun p => by positivity) _
    (hsp.mul_left (Real.log 2)⁻¹)
  intro p
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hl2 : Real.log 2 ≤ Real.log (p : ℝ) := Real.log_le_log (by norm_num) hp2
  have hn : ‖primeCoefficient p * Complex.exp (-w * (Real.log (p : ℕ) : ℂ))‖ =
      Real.log (p : ℝ) * Real.exp (-(1 / 2 + w.re) * Real.log (p : ℝ)) := by
    rw [primeCoefficient, ArithmeticFunction.vonMangoldt_apply_prime p.2,
      mul_assoc, ← Complex.exp_add, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hlog, Complex.norm_exp]
    congr 2
    simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re,
      Complex.ofReal_re, Complex.mul_re, Complex.neg_im, Complex.ofReal_im, mul_zero,
      sub_zero]
    ring
  have he : Real.exp (-Real.log (p : ℝ)) ≤
      Real.exp (-(1 / 2 + w.re) * Real.log (p : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlower : Real.log 2 / (p : ℝ) ≤
      ‖primeCoefficient p * Complex.exp (-w * (Real.log (p : ℕ) : ℂ))‖ := by
    rw [hn]
    calc
      _ ≤ Real.log (p : ℝ) / (p : ℝ) := div_le_div_of_nonneg_right hl2 hp.le
      _ = Real.log (p : ℝ) * Real.exp (-Real.log (p : ℝ)) := by
        rw [Real.exp_neg, Real.exp_log hp, div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left he hlog.le
  calc
    1 / (p : ℝ) = (Real.log 2)⁻¹ * (Real.log 2 / (p : ℝ)) := by
      field_simp [hlog2.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (inv_nonneg.mpr hlog2.le)

/-- The same finite-prefix current with a proposed seam counterterm. -/
def primeBoundaryCounterterm (S : ThetaSource) (w z : ℂ) (n : ℕ) : ℂ :=
  primeCoefficient n * Complex.exp (-w * (Real.log n : ℂ)) *
    (z - ∫ t in (0 : ℝ)..Real.log n, laplaceIntegrand S w t)

/-- Below the Euler boundary the source tail is the unique admissible
counterterm. Absolute convergence cannot survive an incorrect constant. -/
theorem summable_norm_primeBoundaryCounterterm_iff (S : ThetaSource) {w : ℂ}
    (hw : w.re ≤ 1 / 2) (z : ℂ) :
    Summable (fun n => ‖primeBoundaryCounterterm S w z n‖) ↔
      z = ∫ t in Ioi (0 : ℝ), laplaceIntegrand S w t := by
  constructor
  · intro hz
    by_contra hne
    have hd := hz.of_norm.sub (summable_norm_primeBoundaryTerm S w).of_norm
    have he : Summable (fun n : ℕ =>
        (primeCoefficient n * Complex.exp (-w * (Real.log n : ℂ))) *
          (z - ∫ t in Ioi (0 : ℝ), laplaceIntegrand S w t)) := by
      apply hd.congr
      intro n
      simp only [primeBoundaryCounterterm, primeBoundaryTerm]
      ring
    have hc := (summable_mul_right_iff (sub_ne_zero.mpr hne)).mp he
    exact not_summable_norm_primeBoundaryCoefficient hw hc.norm
  · intro hz
    simpa only [primeBoundaryCounterterm, hz, primeBoundaryTerm] using
      summable_norm_primeBoundaryTerm S w

private theorem theta_positiveRay_eq_loop (lam : ℂ) :
    (∫ t in Ioi (0 : ℝ), laplaceIntegrand thetaCuspTiltSource (-2 * lam) t) =
      thetaLoopA lam - (evenKernel (0 : UnitAddCircle) 1 : ℂ) * lam := by
  have hi : I * (I * lam) = -lam := by rw [← mul_assoc, I_mul_I]; ring
  have h := thetaOneSidedConnection_two_mul_eq_denominator (I * lam)
  rw [hi, neg_neg, sub_neg_eq_add] at h
  calc
    _ = thetaOneSidedConnection (2 * (I * lam)) := by
      unfold thetaOneSidedConnection
      apply integral_congr_ae
      filter_upwards with t
      simp only [laplaceIntegrand, thetaCuspTiltSource_k]
      congr 2
      linear_combination (-2 * (t : ℂ)) * hi
    _ = _ := by
      rw [h, thetaLoopA]
      linear_combination (evenKernel (0 : UnitAddCircle) 1 : ℂ) * hi

/-- Complete admission law: above the Euler boundary every counterterm is
admitted; on and below it only the exact source seam is admitted. -/
theorem primeBoundaryCounterterm_admission (S : ThetaSource) (w z : ℂ) :
    Summable (fun n => ‖primeBoundaryCounterterm S w z n‖) ↔
      1 / 2 < w.re ∨ z = ∫ t in Ioi (0 : ℝ), laplaceIntegrand S w t := by
  by_cases hw : 1 / 2 < w.re
  · have hc : Summable (fun n =>
        primeCoefficient n * Complex.exp (-w * (Real.log n : ℂ))) := by
      simp_rw [primeCoefficient_laplace]
      exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simp; linarith)
    have he := (summable_norm_primeBoundaryTerm S w).of_norm.add
      (hc.mul_right (z - ∫ t in Ioi (0 : ℝ), laplaceIntegrand S w t))
    have ha : Summable (primeBoundaryCounterterm S w z) := by
      apply he.congr
      intro n
      simp only [primeBoundaryTerm, primeBoundaryCounterterm]
      ring
    exact ⟨fun _ => Or.inl hw, fun _ => ha.norm⟩
  · rw [summable_norm_primeBoundaryCounterterm_iff S (le_of_not_gt hw)]
    simp only [hw, false_or]

/-- The proposed renewal-charge counterterm differs from the source seam
by exactly half the full two-ended function. -/
theorem renewalChargeCounterterm_eq (lam : ℂ) :
    I * thetaRenewalFullCharge lam - (evenKernel (0 : UnitAddCircle) 1 : ℂ) * lam =
      (∫ t in Ioi (0 : ℝ), laplaceIntegrand thetaCuspTiltSource (-2 * lam) t) -
        XiC (2 * I * lam) / 2 := by
  rw [theta_positiveRay_eq_loop, thetaRenewalFullCharge, XiC_two_I_mul_eq_thetaLoop]
  field_simp
  ring

/-- Literal prime current whose counterterm is the full renewal charge. -/
def renewalPrimeBoundaryTerm (lam : ℂ) (n : ℕ) : ℂ :=
  primeBoundaryCounterterm thetaCuspTiltSource (-2 * lam)
    (I * thetaRenewalFullCharge lam - (evenKernel (0 : UnitAddCircle) 1 : ℂ) * lam) n

/-- Absolute prime-boundary admission detects the complete divisor, with
no critical-axis or simplicity premise. -/
theorem summable_norm_renewalPrimeBoundaryTerm_iff {lam : ℂ} (hlam : -(1 / 4) ≤ lam.re) :
    Summable (fun n => ‖renewalPrimeBoundaryTerm lam n‖) ↔ XiC (2 * I * lam) = 0 := by
  have hw : (-2 * lam).re ≤ 1 / 2 := by simp only [mul_re]; norm_num; linarith
  unfold renewalPrimeBoundaryTerm
  rw [summable_norm_primeBoundaryCounterterm_iff thetaCuspTiltSource hw,
    renewalChargeCounterterm_eq, sub_eq_self, div_eq_zero_iff]
  norm_num

/-- The global admission set consists exactly of the left Euler half-plane
and the full Xi divisor; the critical strip contains only the latter. -/
theorem renewalPrimeBoundary_admission (lam : ℂ) :
    Summable (fun n => ‖renewalPrimeBoundaryTerm lam n‖) ↔
      lam.re < -(1 / 4) ∨ XiC (2 * I * lam) = 0 := by
  have hw : 1 / 2 < (-2 * lam).re ↔ lam.re < -(1 / 4) := by
    simp only [mul_re]
    norm_num
    constructor <;> intro h <;> linarith
  unfold renewalPrimeBoundaryTerm
  rw [primeBoundaryCounterterm_admission, hw, renewalChargeCounterterm_eq,
    sub_eq_self, div_eq_zero_iff]
  norm_num

theorem renewalPrimeBoundaryTerm_at_divisor {lam : ℂ} (hzero : XiC (2 * I * lam) = 0)
    (n : ℕ) :
    renewalPrimeBoundaryTerm lam n = primeBoundaryTerm thetaCuspTiltSource (-2 * lam) n := by
  simp only [renewalPrimeBoundaryTerm, primeBoundaryCounterterm, renewalChargeCounterterm_eq,
    hzero, zero_div, sub_zero, primeBoundaryTerm]

/-- The admitted full-divisor charge obeys the complete Gamma--pole Ward balance. -/
theorem renewalPrimeBoundary_balance {lam : ℂ} (hs : |lam.re| < 1 / 4)
    (hzero : XiC (2 * I * lam) = 0) :
    (∑' n, renewalPrimeBoundaryTerm lam n) =
      (∫ t in Ioi (0 : ℝ), gammaSource t * Complex.exp ((-2 * lam) * t)) +
      (∫ t in Ioi (0 : ℝ), polarSource (1 / 2) t * Complex.exp ((-2 * lam) * t)) +
      (∫ t in Ioi (0 : ℝ), polarSource (-1 / 2) t * Complex.exp ((-2 * lam) * t)) -
      archConstant * (I * thetaRenewalFullCharge lam -
        (evenKernel (0 : UnitAddCircle) 1 : ℂ) * lam) -
      (∫ t in Ioi (0 : ℝ), (t : ℂ) * (thetaCuspFullSource t : ℂ) *
        Complex.exp ((-2 * lam) * t)) := by
  have hw : (-2 * lam).re ≤ 3 / 4 := by
    simp only [mul_re]; norm_num; linarith [abs_lt.mp hs |>.1]
  simp_rw [renewalPrimeBoundaryTerm_at_divisor hzero]
  rw [tsum_primeBoundaryTerm_eq_archimedean hw, renewalChargeCounterterm_eq,
    hzero, zero_div, sub_zero]

end RHTower.ThetaSourceWard
