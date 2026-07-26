import GaloisForLFunctions.RHTower.PrimeArchThetaAtomLikelihoodRatio
import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Exact spectral law for the normalized higher Riemann-theta tail

The natural affine coordinate

`B(x) = π exp(x)^2 - 3/2`

turns every higher-to-first theta-atom likelihood ratio into the Laplace transform of one positive
Dirac mass plus one positive Lebesgue ray.  Summing over all higher atoms gives a canonical positive
spectral measure for the complete normalized theta tail.  Its exponentially tilted moments form a
strictly positive Hankel hierarchy at every finite order.

There are no numerical bounds in this module.  All identities are exact and all statements are
unconditional.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- The spectral gap between the `n`th square and the first square. -/
def thetaCuspLikelihoodGap (n : ℕ) : ℝ := (n : ℝ) ^ 2 - 1

/-- The affine-exponential coordinate in which the normalized theta tail is a Laplace transform. -/
def thetaCuspLikelihoodCoordinate (x : ℝ) : ℝ :=
  Real.pi * Real.exp x ^ 2 - 3 / 2

/-- The exact transformed likelihood ratio contributed by the `n`th theta atom. -/
def thetaCuspAtomLikelihoodSpectralTerm (n : ℕ) (B : ℝ) : ℝ :=
  Real.exp (-(3 / 2 : ℝ) * thetaCuspLikelihoodGap n) *
    ((n : ℝ) ^ 4 * Real.exp (-B * thetaCuspLikelihoodGap n) +
      (3 / 2 : ℝ) * (n : ℝ) ^ 2 * thetaCuspLikelihoodGap n *
        Real.exp (-B * thetaCuspLikelihoodGap n) / B)

theorem thetaCuspLikelihoodCoordinate_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspLikelihoodCoordinate x := by
  have hexp : 1 ≤ Real.exp x := Real.one_le_exp hx
  have hsq : 1 ≤ Real.exp x ^ 2 := by nlinarith [Real.exp_pos x]
  unfold thetaCuspLikelihoodCoordinate
  nlinarith [Real.pi_gt_three, Real.pi_pos]

theorem thetaCuspLikelihoodGap_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < thetaCuspLikelihoodGap n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [thetaCuspLikelihoodGap]
  nlinarith

theorem thetaCuspSourceTerm_eq_scaleForm (n : ℕ) (x : ℝ) :
    thetaCuspSourceTerm x n =
      (Real.exp (x / 2) * 2 * Real.pi * Real.exp x ^ 2) *
        (n : ℝ) ^ 2 *
        (2 * (Real.pi * Real.exp x ^ 2) * (n : ℝ) ^ 2 - 3) *
        Real.exp (-(Real.pi * Real.exp x ^ 2) * (n : ℝ) ^ 2) := by
  unfold thetaCuspSourceTerm thetaCuspSeed
  ring

private theorem thetaCuspAtomLikelihoodRatio_eq_scaleForm
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    thetaCuspAtomLikelihoodRatio n x =
      (n : ℝ) ^ 2 *
        (2 * (Real.pi * Real.exp x ^ 2) * (n : ℝ) ^ 2 - 3) /
          (2 * (Real.pi * Real.exp x ^ 2) - 3) *
        Real.exp (-(Real.pi * Real.exp x ^ 2) * thetaCuspLikelihoodGap n) := by
  have hfirst := thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    (n := 1) hx (by norm_num)
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hden : 2 * (Real.pi * Real.exp x ^ 2) - 3 ≠ 0 := by
    unfold thetaCuspLikelihoodCoordinate at hB
    linarith
  have hcommon : Real.exp (x / 2) * 2 * Real.pi * Real.exp x ^ 2 ≠ 0 := by
    positivity
  have hexp :
      Real.exp (-(Real.pi * Real.exp x ^ 2) * (n : ℝ) ^ 2) =
        Real.exp (-(Real.pi * Real.exp x ^ 2) * thetaCuspLikelihoodGap n) *
          Real.exp (-(Real.pi * Real.exp x ^ 2)) := by
    rw [← Real.exp_add]
    unfold thetaCuspLikelihoodGap
    congr 1
    ring
  rw [thetaCuspAtomLikelihoodRatio, thetaCuspSourceTerm_eq_scaleForm,
    thetaCuspSourceTerm_eq_scaleForm, hexp]
  norm_num
  field_simp [hcommon, hden, Real.exp_ne_zero]

/-- **Exact atom spectral law.**  In the canonical `B` coordinate, a theta-atom likelihood ratio
is an exponential atom plus an exponential ray transform. -/

theorem thetaCuspAtomLikelihoodRatio_eq_spectralTerm
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    thetaCuspAtomLikelihoodRatio n x =
      thetaCuspAtomLikelihoodSpectralTerm n (thetaCuspLikelihoodCoordinate x) := by
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  have hden : 2 * (Real.pi * Real.exp x ^ 2) - 3 ≠ 0 := by
    unfold thetaCuspLikelihoodCoordinate at hB
    linarith
  have hcoeff :
      (n : ℝ) ^ 2 *
          (2 * (Real.pi * Real.exp x ^ 2) * (n : ℝ) ^ 2 - 3) /
            (2 * (Real.pi * Real.exp x ^ 2) - 3) =
        (n : ℝ) ^ 4 +
          (3 / 2 : ℝ) * (n : ℝ) ^ 2 * thetaCuspLikelihoodGap n /
            thetaCuspLikelihoodCoordinate x := by
    unfold thetaCuspLikelihoodGap thetaCuspLikelihoodCoordinate
    have hden' : -3 + Real.pi * Real.exp x ^ 2 * 2 ≠ 0 := by
      intro hz
      apply hden
      linarith
    have hcancel :
        (-3 + Real.pi * Real.exp x ^ 2 * 2) *
            (-3 + Real.pi * Real.exp x ^ 2 * 2)⁻¹ = 1 :=
      mul_inv_cancel₀ hden'
    have hhalf : -3 / 2 + Real.pi * Real.exp x ^ 2 ≠ 0 := by
      unfold thetaCuspLikelihoodCoordinate at hB
      linarith
    have hprod :
        (-3 / 2 + Real.pi * Real.exp x ^ 2) *
            (2 * (-3 + Real.pi * Real.exp x ^ 2 * 2)⁻¹) = 1 := by
      calc
        _ = (-3 + Real.pi * Real.exp x ^ 2 * 2) *
            (-3 + Real.pi * Real.exp x ^ 2 * 2)⁻¹ := by ring
        _ = 1 := hcancel
    have hinv :
        (-3 / 2 + Real.pi * Real.exp x ^ 2)⁻¹ =
          2 * (-3 + Real.pi * Real.exp x ^ 2 * 2)⁻¹ := by
      apply mul_left_cancel₀ hhalf
      rw [mul_inv_cancel₀ hhalf]
      exact hprod.symm
    simp only [div_eq_mul_inv]
    rw [show (2 * (Real.pi * Real.exp x ^ 2) - 3)⁻¹ =
        (-3 + Real.pi * Real.exp x ^ 2 * 2)⁻¹ by congr 1 <;> ring]
    rw [show (Real.pi * Real.exp x ^ 2 - 3 * (2 : ℝ)⁻¹)⁻¹ =
        (-3 / 2 + Real.pi * Real.exp x ^ 2)⁻¹ by
      congr 1
      norm_num
      ring]
    rw [hinv]
    linear_combination (n : ℝ) ^ 4 * hcancel
  have hexp :
      Real.exp (-(Real.pi * Real.exp x ^ 2) * thetaCuspLikelihoodGap n) =
        Real.exp (-(3 / 2 : ℝ) * thetaCuspLikelihoodGap n) *
          Real.exp (-thetaCuspLikelihoodCoordinate x * thetaCuspLikelihoodGap n) := by
    rw [← Real.exp_add]
    unfold thetaCuspLikelihoodCoordinate
    congr 1
    ring
  rw [thetaCuspAtomLikelihoodRatio_eq_scaleForm hn hx, hcoeff, hexp]
  unfold thetaCuspAtomLikelihoodSpectralTerm
  ring

/-! ### The exact mixed spectral measure -/

/-- Pure-point coefficient in the spectral measure of one normalized theta atom. -/
def thetaCuspLikelihoodAtomWeight (n : ℕ) : ℝ :=
  Real.exp (-(3 / 2 : ℝ) * thetaCuspLikelihoodGap n) * (n : ℝ) ^ 4

/-- Lebesgue-ray coefficient in the spectral measure of one normalized theta atom. -/
def thetaCuspLikelihoodRayWeight (n : ℕ) : ℝ :=
  Real.exp (-(3 / 2 : ℝ) * thetaCuspLikelihoodGap n) *
    (3 / 2 : ℝ) * (n : ℝ) ^ 2 * thetaCuspLikelihoodGap n

theorem thetaCuspLikelihoodAtomWeight_pos {n : ℕ} (hn : 0 < n) :
    0 < thetaCuspLikelihoodAtomWeight n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold thetaCuspLikelihoodAtomWeight
  positivity

theorem thetaCuspLikelihoodRayWeight_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < thetaCuspLikelihoodRayWeight n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hn)
  have hd := thetaCuspLikelihoodGap_pos hn
  unfold thetaCuspLikelihoodRayWeight
  positivity

/-- The positive spectral measure carried by one higher normalized theta atom: one Dirac mass at
the square gap and one constant-density Lebesgue ray starting at the same gap. -/
def thetaCuspAtomLikelihoodSpectralMeasure (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (thetaCuspLikelihoodAtomWeight n) •
      Measure.dirac (thetaCuspLikelihoodGap n) +
    ENNReal.ofReal (thetaCuspLikelihoodRayWeight n) •
      volume.restrict (Ioi (thetaCuspLikelihoodGap n))

/-- The canonical positive spectral measure of the complete normalized higher theta tail. -/
def thetaCuspHigherLikelihoodSpectralMeasure : Measure ℝ :=
  Measure.sum fun k : ℕ => thetaCuspAtomLikelihoodSpectralMeasure (k + 2)

private theorem integrable_exp_neg_mul_atomSpectralMeasure
    {n : ℕ} {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => Real.exp (-B * t))
      (thetaCuspAtomLikelihoodSpectralMeasure n) := by
  have hdirac : Integrable (fun t : ℝ => Real.exp (-B * t))
      (Measure.dirac (thetaCuspLikelihoodGap n)) := integrable_dirac (by simp)
  have hray : Integrable (fun t : ℝ => Real.exp (-B * t))
      (volume.restrict (Ioi (thetaCuspLikelihoodGap n))) := by
    simpa only [neg_mul] using
      (integrableOn_exp_mul_Ioi (a := -B) (neg_neg_iff_pos.mpr hB)
        (thetaCuspLikelihoodGap n))
  exact (hdirac.smul_measure (by simp)).add_measure (hray.smul_measure (by simp))

/-- **One-atom Laplace law.**  Integration against the mixed positive measure is exactly the
transformed theta-atom likelihood ratio. -/
theorem integral_exp_neg_mul_thetaCuspAtomLikelihoodSpectralMeasure
    {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, Real.exp (-B * t) ∂thetaCuspAtomLikelihoodSpectralMeasure n) =
      thetaCuspAtomLikelihoodSpectralTerm n B := by
  have hAtomNonneg := (thetaCuspLikelihoodAtomWeight_pos
    (lt_of_lt_of_le (by omega) hn)).le
  have hRayNonneg := (thetaCuspLikelihoodRayWeight_pos hn).le
  have hdirac : Integrable (fun t : ℝ => Real.exp (-B * t))
      (ENNReal.ofReal (thetaCuspLikelihoodAtomWeight n) •
        Measure.dirac (thetaCuspLikelihoodGap n)) :=
    (integrable_dirac (by simp)).smul_measure (by simp)
  have hray : Integrable (fun t : ℝ => Real.exp (-B * t))
      (ENNReal.ofReal (thetaCuspLikelihoodRayWeight n) •
        volume.restrict (Ioi (thetaCuspLikelihoodGap n))) := by
    have hbase : Integrable (fun t : ℝ => Real.exp (-B * t))
        (volume.restrict (Ioi (thetaCuspLikelihoodGap n))) := by
      simpa only [neg_mul] using
        (integrableOn_exp_mul_Ioi (a := -B) (neg_neg_iff_pos.mpr hB)
          (thetaCuspLikelihoodGap n))
    exact hbase.smul_measure (by simp)
  rw [thetaCuspAtomLikelihoodSpectralMeasure,
    integral_add_measure hdirac hray,
    integral_smul_measure, integral_dirac,
    integral_smul_measure]
  change ENNReal.toReal (ENNReal.ofReal (thetaCuspLikelihoodAtomWeight n)) *
        Real.exp (-B * thetaCuspLikelihoodGap n) +
      ENNReal.toReal (ENNReal.ofReal (thetaCuspLikelihoodRayWeight n)) *
        (∫ t : ℝ in Ioi (thetaCuspLikelihoodGap n), Real.exp (-B * t)) = _
  rw [ENNReal.toReal_ofReal hAtomNonneg, ENNReal.toReal_ofReal hRayNonneg]
  rw [show (∫ t : ℝ in Ioi (thetaCuspLikelihoodGap n), Real.exp (-B * t)) =
      Real.exp (-B * thetaCuspLikelihoodGap n) / B by
    rw [show (fun t : ℝ => Real.exp (-B * t)) =
        fun t : ℝ => Real.exp ((-B) * t) by funext t; ring]
    rw [integral_exp_mul_Ioi (show -B < 0 by linarith)]
    ring]
  unfold thetaCuspLikelihoodAtomWeight thetaCuspLikelihoodRayWeight
    thetaCuspAtomLikelihoodSpectralTerm
  ring

/-! ### The complete theta-tail Laplace law -/

/-- The Laplace response of the complete normalized higher theta tail in its intrinsic spectral
coordinate. -/
def thetaCuspHigherLikelihoodSpectralResponse (B : ℝ) : ℝ :=
  ∑' k : ℕ, thetaCuspAtomLikelihoodSpectralTerm (k + 2) B

theorem summable_thetaCuspAtomLikelihoodSpectralTerm
    {B : ℝ} (hB : 0 < B) :
    Summable (fun k : ℕ => thetaCuspAtomLikelihoodSpectralTerm (k + 2) B) := by
  let c : ℝ := B + 3 / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have h4 : Summable (fun k : ℕ =>
      ((k + 2 : ℕ) : ℝ) ^ 4 *
        Real.exp (-c * (((k + 2 : ℕ) : ℝ) ^ 2))) :=
    (summable_pow_mul_exp_neg_nat_sq 4 hc).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have h2 : Summable (fun k : ℕ =>
      ((k + 2 : ℕ) : ℝ) ^ 2 *
        Real.exp (-c * (((k + 2 : ℕ) : ℝ) ^ 2))) :=
    (summable_pow_mul_exp_neg_nat_sq 2 hc).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hsum :=
    (h4.mul_left (Real.exp c * (1 + (3 / 2 : ℝ) / B))).add
      (h2.mul_left (-(Real.exp c * ((3 / 2 : ℝ) / B))))
  convert hsum using 1
  funext k
  let n : ℕ := k + 2
  have hexp :
      Real.exp (-(3 / 2 : ℝ) * thetaCuspLikelihoodGap n) *
          Real.exp (-B * thetaCuspLikelihoodGap n) =
        Real.exp c * Real.exp (-c * (n : ℝ) ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    unfold thetaCuspLikelihoodGap
    dsimp [c]
    congr 1
    ring
  change thetaCuspAtomLikelihoodSpectralTerm n B = _
  unfold thetaCuspAtomLikelihoodSpectralTerm
  calc
    Real.exp (-(3 / 2 : ℝ) * thetaCuspLikelihoodGap n) *
          ((n : ℝ) ^ 4 * Real.exp (-B * thetaCuspLikelihoodGap n) +
            (3 / 2 : ℝ) * (n : ℝ) ^ 2 * thetaCuspLikelihoodGap n *
              Real.exp (-B * thetaCuspLikelihoodGap n) / B) =
        (Real.exp (-(3 / 2 : ℝ) * thetaCuspLikelihoodGap n) *
          Real.exp (-B * thetaCuspLikelihoodGap n)) *
          ((n : ℝ) ^ 4 +
            (3 / 2 : ℝ) * (n : ℝ) ^ 2 * thetaCuspLikelihoodGap n / B) := by ring
    _ = (Real.exp c * Real.exp (-c * (n : ℝ) ^ 2)) *
          ((n : ℝ) ^ 4 +
            (3 / 2 : ℝ) * (n : ℝ) ^ 2 * thetaCuspLikelihoodGap n / B) := by
      rw [hexp]
    _ = _ := by
      unfold thetaCuspLikelihoodGap
      dsimp [c]
      ring

private theorem integral_norm_exp_neg_mul_atomSpectralMeasure
    {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, ‖Real.exp (-B * t)‖ ∂thetaCuspAtomLikelihoodSpectralMeasure n) =
      thetaCuspAtomLikelihoodSpectralTerm n B := by
  rw [show (fun t : ℝ => ‖Real.exp (-B * t)‖) =
      fun t : ℝ => Real.exp (-B * t) by
    funext t
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]]
  exact integral_exp_neg_mul_thetaCuspAtomLikelihoodSpectralMeasure hn hB

theorem integrable_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure
    {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => Real.exp (-B * t))
      thetaCuspHigherLikelihoodSpectralMeasure := by
  rw [thetaCuspHigherLikelihoodSpectralMeasure]
  apply integrable_sum_measure
  · intro k
    exact integrable_exp_neg_mul_atomSpectralMeasure hB
  · convert summable_thetaCuspAtomLikelihoodSpectralTerm hB using 1
    funext k
    exact integral_norm_exp_neg_mul_atomSpectralMeasure (by omega) hB

/-- **Complete spectral-measure law.**  The full intrinsic response is exactly the Laplace
transform of one fixed positive measure, independent of the spectral coordinate. -/
theorem integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure
    {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, Real.exp (-B * t) ∂thetaCuspHigherLikelihoodSpectralMeasure) =
      thetaCuspHigherLikelihoodSpectralResponse B := by
  rw [thetaCuspHigherLikelihoodSpectralMeasure,
    integral_sum_measure
      (integrable_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB)]
  unfold thetaCuspHigherLikelihoodSpectralResponse
  refine tsum_congr fun k => ?_
  exact integral_exp_neg_mul_thetaCuspAtomLikelihoodSpectralMeasure (by omega) hB

/-- The abstract spectral response is the actual higher-to-first Riemann-theta likelihood ratio
at every positive logarithmic source point. -/
theorem thetaCuspHigherLikelihoodSpectralResponse_coordinate
    {x : ℝ} (hx : 0 < x) :
    thetaCuspHigherLikelihoodSpectralResponse (thetaCuspLikelihoodCoordinate x) =
      thetaCuspHigherToFirstAtomLikelihoodRatio x := by
  rw [thetaCuspHigherToFirstAtomLikelihoodRatio_eq_tsum]
  unfold thetaCuspHigherLikelihoodSpectralResponse
  refine tsum_congr fun k => ?_
  exact (thetaCuspAtomLikelihoodRatio_eq_spectralTerm (by omega) hx).symm

/-- **Riemann-theta source factorization.**  The complete cusp source is the first atom multiplied
by one plus the Laplace transform of the canonical higher-tail spectral measure. -/
theorem thetaCuspFullSource_eq_first_mul_one_add_spectralIntegral
    {x : ℝ} (hx : 0 < x) :
    thetaCuspFullSource x = thetaCuspSourceTerm x 1 *
      (1 + ∫ t : ℝ, Real.exp (-thetaCuspLikelihoodCoordinate x * t)
        ∂thetaCuspHigherLikelihoodSpectralMeasure) := by
  have hfirst := thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    (n := 1) hx (by norm_num)
  rw [integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure
    (thetaCuspLikelihoodCoordinate_pos hx.le),
    thetaCuspHigherLikelihoodSpectralResponse_coordinate hx]
  unfold thetaCuspHigherToFirstAtomLikelihoodRatio
  field_simp [hfirst.ne']
  ring

/-! ### All-order tilted moments and the strict Hankel hierarchy -/

theorem ae_nonneg_thetaCuspAtomLikelihoodSpectralMeasure
    {n : ℕ} (hn : 2 ≤ n) :
    ∀ᵐ t ∂thetaCuspAtomLikelihoodSpectralMeasure n, 0 ≤ t := by
  rw [thetaCuspAtomLikelihoodSpectralMeasure, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    rw [ae_dirac_iff measurableSet_Ici]
    exact (thetaCuspLikelihoodGap_pos hn).le
  · apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (thetaCuspLikelihoodGap_pos hn).le.trans ht.le

theorem ae_nonneg_thetaCuspHigherLikelihoodSpectralMeasure :
    ∀ᵐ t ∂thetaCuspHigherLikelihoodSpectralMeasure, 0 ≤ t := by
  rw [thetaCuspHigherLikelihoodSpectralMeasure, Measure.ae_sum_iff]
  intro k
  exact ae_nonneg_thetaCuspAtomLikelihoodSpectralMeasure (by omega)

theorem integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure
    (m : ℕ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => t ^ m * Real.exp (-B * t))
      thetaCuspHigherLikelihoodSpectralMeasure := by
  let C : ℝ := (2 / B) ^ m * (m.factorial : ℝ)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbase : Integrable (fun t : ℝ => C * Real.exp (-(B / 2) * t))
      thetaCuspHigherLikelihoodSpectralMeasure :=
    (integrable_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure
      (show 0 < B / 2 by positivity)).const_mul C
  refine Integrable.mono' hbase (by fun_prop) ?_
  filter_upwards [ae_nonneg_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
  have hy : 0 ≤ (B / 2) * t := mul_nonneg (by positivity) ht
  have hpow := pow_le_factorial_mul_exp hy m
  have htScale : t = (2 / B) * ((B / 2) * t) := by
    field_simp [hB.ne']
  have hscale :
      t ^ m = (2 / B) ^ m * (((B / 2) * t) ^ m) := by
    calc
      t ^ m = ((2 / B) * ((B / 2) * t)) ^ m :=
        congrArg (fun u : ℝ => u ^ m) htScale
      _ = (2 / B) ^ m * (((B / 2) * t) ^ m) := by rw [mul_pow]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (pow_nonneg ht m) (Real.exp_pos _).le), hscale]
  calc
    (2 / B) ^ m * ((B / 2 * t) ^ m) * Real.exp (-B * t)
        = (2 / B) ^ m *
            (((B / 2 * t) ^ m) * Real.exp (-B * t)) := by ring
    _ ≤ (2 / B) ^ m *
          (((m.factorial : ℝ) * Real.exp ((B / 2) * t)) *
            Real.exp (-B * t)) := by
      gcongr
    _ = C * Real.exp (-(B / 2) * t) := by
      dsimp [C]
      have hexp : Real.exp ((B / 2) * t) * Real.exp (-B * t) =
          Real.exp (-(B / 2) * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        (2 / B) ^ m *
            ((m.factorial : ℝ) * Real.exp ((B / 2) * t) * Real.exp (-B * t)) =
          (2 / B) ^ m * (m.factorial : ℝ) *
            (Real.exp ((B / 2) * t) * Real.exp (-B * t)) := by ring
        _ = (2 / B) ^ m * (m.factorial : ℝ) *
            Real.exp (-(B / 2) * t) := by rw [hexp]

/-- Positive Gibbs density which tilts the fixed higher-tail spectral measure at coordinate `B`. -/
def thetaCuspHigherLikelihoodTiltDensity (B t : ℝ) : NNReal :=
  Real.toNNReal (Real.exp (-B * t))

theorem measurable_thetaCuspHigherLikelihoodTiltDensity (B : ℝ) :
    Measurable (thetaCuspHigherLikelihoodTiltDensity B) := by
  apply Measurable.real_toNNReal
  fun_prop

/-- Exponentially tilted spectral measure at coordinate `B`. -/
def thetaCuspHigherLikelihoodTiltedMeasure (B : ℝ) : Measure ℝ :=
  thetaCuspHigherLikelihoodSpectralMeasure.withDensity
    (fun t => ((thetaCuspHigherLikelihoodTiltDensity B t : NNReal) : ENNReal))

theorem integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure
    (m : ℕ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => t ^ m) (thetaCuspHigherLikelihoodTiltedMeasure B) := by
  rw [thetaCuspHigherLikelihoodTiltedMeasure,
    integrable_withDensity_iff_integrable_smul
      (measurable_thetaCuspHigherLikelihoodTiltDensity B)]
  convert integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure m hB using 1
  funext t
  rw [NNReal.smul_def]
  change (thetaCuspHigherLikelihoodTiltDensity B t : ℝ) * t ^ m =
    t ^ m * Real.exp (-B * t)
  rw [thetaCuspHigherLikelihoodTiltDensity,
    Real.coe_toNNReal _ (Real.exp_pos _).le]
  ring

/-- The `m`th moment of the intrinsic tilted higher-tail spectral measure. -/
def thetaCuspHigherLikelihoodSpectralMoment (B : ℝ) (m : ℕ) : ℝ :=
  ∫ t : ℝ, t ^ m ∂thetaCuspHigherLikelihoodTiltedMeasure B

theorem thetaCuspHigherLikelihoodSpectralMoment_eq_integral
    (B : ℝ) (m : ℕ) :
    thetaCuspHigherLikelihoodSpectralMoment B m =
      ∫ t : ℝ, t ^ m * Real.exp (-B * t)
        ∂thetaCuspHigherLikelihoodSpectralMeasure := by
  unfold thetaCuspHigherLikelihoodSpectralMoment
    thetaCuspHigherLikelihoodTiltedMeasure
  rw [integral_withDensity_eq_integral_smul
    (measurable_thetaCuspHigherLikelihoodTiltDensity B)]
  apply integral_congr_ae
  filter_upwards with t
  rw [NNReal.smul_def]
  change (thetaCuspHigherLikelihoodTiltDensity B t : ℝ) * t ^ m = _
  rw [thetaCuspHigherLikelihoodTiltDensity,
    Real.coe_toNNReal _ (Real.exp_pos _).le]
  ring

private theorem thetaCuspLikelihoodGap_shift_injective :
    Function.Injective (fun k : ℕ => thetaCuspLikelihoodGap (k + 2)) := by
  intro k l hkl
  have hk : (0 : ℝ) ≤ (k + 2 : ℕ) := by positivity
  have hl : (0 : ℝ) ≤ (l + 2 : ℕ) := by positivity
  unfold thetaCuspLikelihoodGap at hkl
  have hcast : ((k + 2 : ℕ) : ℝ) = (l + 2 : ℕ) := by
    nlinarith
  exact Nat.add_right_cancel (by exact_mod_cast hcast)

private theorem thetaCuspHigherLikelihoodSpectralMeasure_cofinite_pos
    (F : Finset ℝ) :
    0 < thetaCuspHigherLikelihoodSpectralMeasure {t : ℝ | t ∉ F} := by
  classical
  have hexists : ∃ k : ℕ, thetaCuspLikelihoodGap (k + 2) ∉ F := by
    by_contra h
    push Not at h
    have hsub : Set.range (fun k : ℕ => thetaCuspLikelihoodGap (k + 2)) ⊆ (F : Set ℝ) := by
      rintro _ ⟨k, rfl⟩
      exact h k
    exact (Set.infinite_range_of_injective thetaCuspLikelihoodGap_shift_injective)
      (F.finite_toSet.subset hsub)
  obtain ⟨k, hk⟩ := hexists
  let atom : Measure ℝ :=
    ENNReal.ofReal (thetaCuspLikelihoodAtomWeight (k + 2)) •
      Measure.dirac (thetaCuspLikelihoodGap (k + 2))
  have hatomLe : atom ≤ thetaCuspAtomLikelihoodSpectralMeasure (k + 2) := by
    unfold atom thetaCuspAtomLikelihoodSpectralMeasure
    exact Measure.le_add_right (le_refl _)
  have htotalLe : atom ≤ thetaCuspHigherLikelihoodSpectralMeasure := by
    exact hatomLe.trans (Measure.le_sum
      (fun j : ℕ => thetaCuspAtomLikelihoodSpectralMeasure (j + 2)) k)
  have hweight := thetaCuspLikelihoodAtomWeight_pos
    (n := k + 2) (by omega)
  have hmass : 0 < atom {t : ℝ | t ∉ F} := by
    unfold atom
    simp [hk, ENNReal.ofReal_pos.mpr hweight]
  exact hmass.trans_le (htotalLe {t : ℝ | t ∉ F})

private theorem thetaCuspHigherLikelihoodTiltedMeasure_cofinite_pos
    {B : ℝ} (F : Finset ℝ) :
    0 < thetaCuspHigherLikelihoodTiltedMeasure B {t : ℝ | t ∉ F} := by
  rw [pos_iff_ne_zero]
  intro hzero
  unfold thetaCuspHigherLikelihoodTiltedMeasure at hzero
  have hmeas : Measurable (fun t : ℝ =>
      ((thetaCuspHigherLikelihoodTiltDensity B t : NNReal) : ENNReal)) :=
    (measurable_thetaCuspHigherLikelihoodTiltDensity B).coe_nnreal_ennreal
  have hbaseZero := (withDensity_apply_eq_zero hmeas).mp hzero
  have hset : {t : ℝ |
      ((thetaCuspHigherLikelihoodTiltDensity B t : NNReal) : ENNReal) ≠ 0} = Set.univ := by
    ext t
    simp [thetaCuspHigherLikelihoodTiltDensity, ENNReal.coe_ne_zero,
      Real.toNNReal_eq_zero, not_le, Real.exp_pos]
  rw [hset, Set.univ_inter] at hbaseZero
  exact (ne_of_gt (thetaCuspHigherLikelihoodSpectralMeasure_cofinite_pos F)) hbaseZero

/-- **All-order strict spectral Hankel law.**  Every finite moment block of the normalized higher
Riemann-theta tail is positive definite at every positive spectral coordinate. -/
theorem thetaCuspHigherLikelihoodSpectralMoment_hankel_posDef
    {B : ℝ} (hB : 0 < B) (q : ℕ) :
    (HTGeometry.momentHankelMatrix
      (thetaCuspHigherLikelihoodSpectralMoment B) q).PosDef := by
  apply HTGeometry.momentHankelMatrix_posDef_of_infiniteSupport
    (thetaCuspHigherLikelihoodSpectralMoment B)
  · intro m
    rfl
  · intro m
    exact integrable_pow_thetaCuspHigherLikelihoodTiltedMeasure m hB
  · exact thetaCuspHigherLikelihoodTiltedMeasure_cofinite_pos

theorem det_thetaCuspHigherLikelihoodSpectralMoment_hankel_pos
    {B : ℝ} (hB : 0 < B) (q : ℕ) :
    0 < (HTGeometry.momentHankelMatrix
      (thetaCuspHigherLikelihoodSpectralMoment B) q).det :=
  (thetaCuspHigherLikelihoodSpectralMoment_hankel_posDef hB q).det_pos

/-- **Master spectral-carrier law.**  One fixed positive measure simultaneously gives the exact
normalized theta-tail response at every positive coordinate and a strictly positive Hankel moment
tower of every finite order. -/
theorem thetaCuspHigherLikelihoodSpectralMasterLaw
    {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ, Real.exp (-B * t) ∂thetaCuspHigherLikelihoodSpectralMeasure) =
        thetaCuspHigherLikelihoodSpectralResponse B ∧
      ∀ q : ℕ, (HTGeometry.momentHankelMatrix
        (thetaCuspHigherLikelihoodSpectralMoment B) q).PosDef := by
  exact ⟨integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB,
    thetaCuspHigherLikelihoodSpectralMoment_hankel_posDef hB⟩

end

end RHTower
