import GaloisForLFunctions.BiScaleUncertainty.SquarefreeGaussianCompletion
import GaloisForLFunctions.RHTower.GammaThetaSupportWeightBounds
import GaloisForLFunctions.RHTower.JointAncestryGammaThetaBooleanClosedCreation
import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy

/-!
# The actual Gamma--theta source over every finite prime support

The synchronized coefficients, independent prime phases, and literal completed-theta Mellin
grades admit one simultaneous `L2` completion. Every complex formation parameter is allowed.
The finite-head argument removes the artificial disk restriction from a total-trace bound.
No grade normalization, prime cutoff, or Xi-divisor assumption is present.
-/

open Complex Real MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.BiScaleUncertainty HedenmalmThetaSource

private theorem thetaFullSource_envelope_abs (y : ℝ) :
    thetaCuspFullSource y ≤ thetaEnvelopeUpper * thetaEnvelope |y| := by
  rcases le_total 0 y with hy | hy
  · simpa only [abs_of_nonneg hy] using thetaCuspFullSource_le_envelope hy
  · rw [abs_of_nonpos hy, ← thetaCuspFullSource_neg y]
    exact thetaCuspFullSource_le_envelope (by linarith)

/-- A genuine positive exponential moment in the variable `exp(2y)`, at every additional
Mellin grade. This is stronger than separate integrability of each grade. -/
theorem integrable_exp_exp_actualThetaGrade_sq (r : ℕ) :
    Integrable (fun y : ℝ => Real.exp (Real.exp (2 * y)) *
      (Real.exp (2 * (r : ℝ) * y) * thetaCuspFullSource y ^ 2)) := by
  let D : ℝ := 2 * (r : ℝ) + 10
  let C : ℝ := thetaEnvelopeUpper ^ 2 * Real.exp (D ^ 2 / 40)
  have hdecay : Integrable (fun y : ℝ => Real.exp (-|y|)) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    apply IntegrableOn.union
    · refine (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1) 0).congr_fun ?_
        measurableSet_Iic
      intro y hy
      change y ≤ 0 at hy
      simp only [abs_of_nonpos hy, neg_neg, one_mul]
    · refine (integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).congr_fun ?_
        measurableSet_Ioi
      intro y hy
      change 0 < y at hy
      simp only [abs_of_pos hy, neg_one_mul]
  have hm : Measurable (fun y : ℝ => Real.exp (Real.exp (2 * y)) *
      (Real.exp (2 * (r : ℝ) * y) * thetaCuspFullSource y ^ 2)) := by
    have htheta := contDiff_thetaCuspFullSource.continuous.measurable
    fun_prop
  apply (hdecay.const_mul C).mono' hm.aestronglyMeasurable
  refine Eventually.of_forall fun y => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have htheta0 := (thetaCuspFullSource_pos y).le
  have htheta := thetaFullSource_envelope_abs y
  have hsquare : thetaCuspFullSource y ^ 2 ≤
      thetaEnvelopeUpper ^ 2 * Real.exp (9 * |y| - 2 * Real.pi * Real.exp (2 * |y|)) := by
    calc
      thetaCuspFullSource y ^ 2 ≤ (thetaEnvelopeUpper * thetaEnvelope |y|) ^ 2 :=
        pow_le_pow_left₀ htheta0 htheta 2
      _ = thetaEnvelopeUpper ^ 2 *
          Real.exp (9 * |y| - 2 * Real.pi * Real.exp (2 * |y|)) := by
        simp only [thetaEnvelope, mul_pow, ← Real.exp_nat_mul]
        rw [← Real.exp_add]
        congr 2
        push_cast
        ring
  have hexp : 2 * |y| ^ 2 ≤ Real.exp (2 * |y|) := by
    have := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * |y|)
    nlinarith only [this, abs_nonneg y]
  have hquad : D * |y| - 5 * Real.exp (2 * |y|) ≤ D ^ 2 / 40 := by
    nlinarith [sq_nonneg (20 * |y| - D)]
  have hrate : 6 * Real.exp (2 * |y|) ≤ 2 * Real.pi * Real.exp (2 * |y|) :=
    mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) (Real.exp_pos _).le
  have hyabs : Real.exp (2 * y) ≤ Real.exp (2 * |y|) :=
    Real.exp_le_exp.mpr (by linarith [le_abs_self y])
  have hrabs : 2 * (r : ℝ) * y ≤ 2 * (r : ℝ) * |y| :=
    mul_le_mul_of_nonneg_left (le_abs_self y) (by positivity)
  have hpower : Real.exp (2 * y) + 2 * (r : ℝ) * y + 9 * |y| -
      2 * Real.pi * Real.exp (2 * |y|) ≤ D ^ 2 / 40 - |y| := by
    dsimp [D] at hquad ⊢
    linarith
  calc
    Real.exp (Real.exp (2 * y)) * (Real.exp (2 * (r : ℝ) * y) * thetaCuspFullSource y ^ 2) ≤
        Real.exp (Real.exp (2 * y)) * (Real.exp (2 * (r : ℝ) * y) *
          (thetaEnvelopeUpper ^ 2 *
            Real.exp (9 * |y| - 2 * Real.pi * Real.exp (2 * |y|)))) := by gcongr
    _ = thetaEnvelopeUpper ^ 2 * Real.exp (Real.exp (2 * y) +
        2 * (r : ℝ) * y + 9 * |y| - 2 * Real.pi * Real.exp (2 * |y|)) := by
      rw [show Real.exp (2 * y) + 2 * (r : ℝ) * y + 9 * |y| -
          2 * Real.pi * Real.exp (2 * |y|) =
          Real.exp (2 * y) + (2 * (r : ℝ) * y +
            (9 * |y| - 2 * Real.pi * Real.exp (2 * |y|))) by ring,
        Real.exp_add, Real.exp_add]
      ring
    _ ≤ thetaEnvelopeUpper ^ 2 * Real.exp (D ^ 2 / 40 - |y|) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hpower) (sq_nonneg _)
    _ = C * Real.exp (-|y|) := by
      rw [sub_eq_add_neg, Real.exp_add]
      dsimp [C]
      ring

/-- One freely specified phase per prime, with one common complex formation parameter. -/
def jasGammaThetaPrimeAmplitude (z : ℂ) (tau : Nat.Primes → ℝ) (p : Nat.Primes) : ℂ :=
  z * Complex.exp ((tau p : ℂ) * Complex.I)

@[simp] theorem norm_jasGammaThetaPrimeAmplitude
    (z : ℂ) (tau : Nat.Primes → ℝ) (p : Nat.Primes) :
    ‖jasGammaThetaPrimeAmplitude z tau p‖ = ‖z‖ := by
  simp [jasGammaThetaPrimeAmplitude, Complex.norm_exp]

/-- The unchanged support coefficient and actual theta grade, before taking the `L2` quotient. -/
def jasGammaThetaFullSourceFun (x : ℝ) (z : ℂ) (tau : Nat.Primes → ℝ) (r : ℕ)
    (v : JASGammaThetaSupport × ℝ) : ℂ :=
  (∏ p ∈ v.1, jasGammaThetaPrimeAmplitude z tau p) *
    (gammaSewnSynchronizedLcmWeight x v.1 : ℂ) *
    ((Real.exp (((v.1.card : ℝ) + (r : ℝ)) * v.2) * thetaCuspFullSource v.2 : ℝ) : ℂ)

theorem measurable_jasGammaThetaFullSourceFun
    (x : ℝ) (z : ℂ) (tau : Nat.Primes → ℝ) (r : ℕ) :
    Measurable (jasGammaThetaFullSourceFun x z tau r) := by
  apply measurable_from_prod_countable_right
  intro P
  have htheta := contDiff_thetaCuspFullSource.continuous.measurable
  unfold jasGammaThetaFullSourceFun
  fun_prop

/-- Exact norm identity: all independent prime phases survive in the source but disappear only
from this admission estimate. -/
theorem norm_sq_jasGammaThetaFullSourceFun
    (x : ℝ) (z : ℂ) (tau : Nat.Primes → ℝ) (r : ℕ)
    (P : JASGammaThetaSupport) (y : ℝ) :
    ‖jasGammaThetaFullSourceFun x z tau r (P, y)‖ ^ 2 =
      ‖z‖ ^ (2 * P.card) * gammaSewnSynchronizedLcmWeight x P ^ 2 *
        (Real.exp (2 * (P.card : ℝ) * y) *
          (Real.exp (2 * (r : ℝ) * y) * thetaCuspFullSource y ^ 2)) := by
  simp only [jasGammaThetaFullSourceFun, norm_mul, norm_prod,
    norm_jasGammaThetaPrimeAmplitude, Finset.prod_const, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← pow_mul, show P.card * 2 = 2 * P.card by omega, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (((P.card : ℝ) + (r : ℝ)) * y) =
      2 * (P.card : ℝ) * y + 2 * (r : ℝ) * y by ring, Real.exp_add]
  ring

theorem memLp_jasGammaThetaFullSourceFun
    {x : ℝ} (hx : 0 < x) (z : ℂ) (tau : Nat.Primes → ℝ) (r : ℕ) :
    MemLp (jasGammaThetaFullSourceFun x z tau r) 2
      ((Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ)) := by
  let b : Nat.Primes → ℝ := fun p => ‖z‖ ^ 2 * ((p : ℝ)⁻¹) ^ 2
  have hb : ∀ p, 0 ≤ b p := fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs : Summable b := summable_primeReciprocal_sq.mul_left (‖z‖ ^ 2)
  apply memLp_squarefree_gaussian_majorant b hb hs
    (fun y => Real.exp (2 * y))
    (fun y => Real.exp (2 * (r : ℝ) * y) * thetaCuspFullSource y ^ 2)
    (by fun_prop)
    (by have htheta := contDiff_thetaCuspFullSource.continuous.measurable; fun_prop)
    (fun y => (Real.exp_pos _).le) (fun y => by positivity)
    (c := 1) (by norm_num)
    (by simpa only [one_mul] using integrable_exp_exp_actualThetaGrade_sq r)
    _ (measurable_jasGammaThetaFullSourceFun x z tau r)
  intro P y
  rw [norm_sq_jasGammaThetaFullSourceFun]
  have hW := gammaSewnSynchronizedLcmWeight_le_primeReciprocalProduct hx P
  have hW0 := (jasGammaSynchronizedLcmWeight_pos hx P).le
  have hWsq := pow_le_pow_left₀ hW0 hW 2
  have hprod : (∏ p ∈ P, (b p * Real.exp (2 * y))) =
      ‖z‖ ^ (2 * P.card) * (∏ p ∈ P, (p : ℝ)⁻¹) ^ 2 *
        Real.exp (2 * (P.card : ℝ) * y) := by
    simp only [b, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow]
    rw [← pow_mul, ← Real.exp_nat_mul]
    congr 1
    congr 1
    ring
  rw [hprod]
  nlinarith [mul_le_mul_of_nonneg_left hWsq
    (show 0 ≤ ‖z‖ ^ (2 * P.card) * Real.exp (2 * (P.card : ℝ) * y) *
      (Real.exp (2 * (r : ℝ) * y) * thetaCuspFullSource y ^ 2) by positivity)]

/-- The all-prime, all-support source in the existing Gamma--theta Hilbert carrier. -/
def jasGammaThetaFullSource {x : ℝ} (hx : 0 < x)
    (z : ℂ) (tau : Nat.Primes → ℝ) (r : ℕ) : JASGammaThetaL2 :=
  (memLp_jasGammaThetaFullSourceFun hx z tau r).toLp
    (jasGammaThetaFullSourceFun x z tau r)

theorem jasGammaThetaFullSource_coeFn {x : ℝ} (hx : 0 < x)
    (z : ℂ) (tau : Nat.Primes → ℝ) (r : ℕ) :
    (jasGammaThetaFullSource hx z tau r : JASGammaThetaSupport × ℝ → ℂ) =ᵐ[
      (Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ)]
      jasGammaThetaFullSourceFun x z tau r :=
  MemLp.coeFn_toLp (memLp_jasGammaThetaFullSourceFun hx z tau r)

/-- Every fixed support recovers its literal coefficient and theta grade after completion. -/
theorem jasGammaThetaFullSource_section {x : ℝ} (hx : 0 < x)
    (z : ℂ) (tau : Nat.Primes → ℝ) (r : ℕ) (P : JASGammaThetaSupport) :
    (fun y => (jasGammaThetaFullSource hx z tau r : JASGammaThetaSupport × ℝ → ℂ) (P, y))
      =ᵐ[volume] fun y => jasGammaThetaFullSourceFun x z tau r (P, y) :=
  Measure.ae_count_iff.mp
    (Measure.ae_ae_of_ae_prod (jasGammaThetaFullSource_coeFn hx z tau r)) P

/-- The vacuum coordinate guarantees a nonzero completed source at every formation parameter. -/
theorem jasGammaThetaFullSource_ne_zero {x : ℝ} (hx : 0 < x)
    (z : ℂ) (tau : Nat.Primes → ℝ) (r : ℕ) :
    jasGammaThetaFullSource hx z tau r ≠ 0 := by
  intro hzero
  have hz : (jasGammaThetaFullSource hx z tau r : JASGammaThetaSupport × ℝ → ℂ)
      =ᵐ[(Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ)] 0 := by
    rw [hzero]
    exact Lp.coeFn_zero ℂ 2 _
  have hzsection := Measure.ae_count_iff.mp (Measure.ae_ae_of_ae_prod hz)
    (∅ : JASGammaThetaSupport)
  obtain ⟨y, hy, hyzero⟩ :=
    ((jasGammaThetaFullSource_section hx z tau r ∅).and hzsection).exists
  have hpos : 0 < Real.exp ((r : ℝ) * y) * thetaCuspFullSource y :=
    mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos y)
  apply (Complex.ofReal_ne_zero.mpr hpos.ne')
  simpa [jasGammaThetaFullSourceFun, gammaSewnSynchronizedLcmWeight] using hy.symm.trans hyzero

/-- Simultaneous square-norm summability of every actual support/grade packet. -/
theorem summable_jasGammaThetaFullSupport_energy
    {x : ℝ} (hx : 0 < x) (z : ℂ) (tau : Nat.Primes → ℝ) (r : ℕ) :
    Summable (fun P : JASGammaThetaSupport =>
      ‖z‖ ^ (2 * P.card) * gammaSewnSynchronizedLcmWeight x P ^ 2 *
        ‖jointAncestryCompletedThetaGradeL2 (P.card + r)‖ ^ 2) := by
  have hm := measurable_jasGammaThetaFullSourceFun x z tau r
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp
    (memLp_jasGammaThetaFullSourceFun hx z tau r)
  have houter := ((integrable_prod_iff (hm.norm.pow_const 2).aestronglyMeasurable).mp hi).2
  apply (integrable_count_iff.mp houter).congr
  intro P
  simp only [Real.norm_eq_abs, abs_sq]
  rw [abs_of_nonneg (integral_nonneg fun y => sq_nonneg
    ‖jasGammaThetaFullSourceFun x z tau r (P, y)‖),
    norm_sq_jointAncestryCompletedThetaGradeL2, ← integral_const_mul]
  apply integral_congr_ae
  refine Eventually.of_forall fun y => ?_
  dsimp only
  rw [norm_sq_jasGammaThetaFullSourceFun]
  have he : Real.exp (2 * (P.card : ℝ) * y) * Real.exp (2 * (r : ℝ) * y) =
      Real.exp (2 * ((P.card + r : ℕ) : ℝ) * y) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [← he]
  ring

end

end RHTower
