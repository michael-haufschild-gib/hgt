import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesSubcriticalPassiveResponse
import GaloisForLFunctions.RHTower.CompletedSeamCompactMarkovGermCapstone
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Reflected compact carrier of the Gamma-sewn Stokes response

The one-sided P-G69 response is passive but cannot equal the centered Xi trace: the latter is odd.
Kummer reflection forces a second pole at the negative Stokes gap.  The reflected pair remains
anti-Herglotz, is exactly odd, and its counterterms cancel.  Writing the reciprocal gap as
`x=1/g` and reflected weight as `w=b/g` gives the exact compact Markov form

`I/(z-g)+I/(z+g) = -z w ((1-xz)⁻¹+(1+xz)⁻¹)`.

P-G69 summability makes the symmetric reciprocal-gap atomic carrier finite and positive.  Its
support lies in the fixed compact interval `[-1/log 2,1/log 2]`, and near zero its Markov
transform is exactly the reflected Stokes response divided by `-z`.  This constructs a literal
source-native compact positive carrier in the functional class of Route P.  Missing gate is now
moment/germ equality with the completed prime--Gamma source, not carrier existence.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators Distributions FourierTransform

noncomputable section
namespace RHTower

def gammaSewnMobiusApertureStokesReflectedWeight (s : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk /
    gammaSewnMobiusApertureStokesGap s pk

def gammaSewnMobiusApertureStokesReciprocalGapNode (s : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  (gammaSewnMobiusApertureStokesGap s pk)⁻¹

theorem gammaSewnMobiusApertureStokesReflectedWeight_pos {s : ℝ} (hs : 0 < s) (pk : Nat.Primes × ℕ) :
    0 < gammaSewnMobiusApertureStokesReflectedWeight s pk := by
  rw [gammaSewnMobiusApertureStokesReflectedWeight, div_pos_iff]
  left
  constructor
  · have hr0 := xiMobiusContinuousApertureDiskNode_pos s pk.1
    have hr1 := xiMobiusContinuousApertureDiskNode_lt_one hs pk.1
    have hq0 := xiTransversePrimeApertureDiskNode_pos 1 pk.1
    have hc0 := gammaSewnMobiusValuationContractionMultiplier_pos s pk.1
    rw [gammaSewnMobiusApertureStokesDualFeatureCoefficient,
      gammaSewnMobiusContinuousApertureFeature,
      xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
    positivity
  · exact gammaSewnMobiusApertureStokesGap_pos hs pk

theorem gammaSewnMobiusApertureStokesReciprocalGapNode_pos {s : ℝ} (hs : 0 < s) (pk : Nat.Primes × ℕ) :
    0 < gammaSewnMobiusApertureStokesReciprocalGapNode s pk := by
  exact inv_pos.mpr (gammaSewnMobiusApertureStokesGap_pos hs pk)

theorem gammaSewnMobiusApertureStokesReciprocalGapNode_le {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesReciprocalGapNode s pk ≤ (Real.log 2)⁻¹ := by
  have hp : (1 : ℝ) ≤ (pk.1 : ℝ) := by
    exact_mod_cast pk.1.2.one_lt.le
  have hexp : 0 ≤ 1 - s := by linarith
  have hrpow : 1 ≤ (pk.1 : ℝ) ^ (1 - s) := by
    exact Real.one_le_rpow hp hexp
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgap : Real.log 2 ≤ gammaSewnMobiusApertureStokesGap s pk := by
    calc
      Real.log 2 ≤ Real.log 2 * (pk.1 : ℝ) ^ (1 - s) := by
        nlinarith
      _ ≤ gammaSewnMobiusApertureStokesGap s pk := by
        rw [gammaSewnMobiusApertureStokesGap]
        calc
          Real.log 2 * (pk.1 : ℝ) ^ (1 - s) ≤
              1 * gammaSewnMobiusApertureStokesInverseTilt s pk.1 := by
            simpa using gammaSewnMobiusApertureStokesInverseTilt_lower hs pk.1
          _ ≤ (pk.2 + 1 : ℝ) *
              gammaSewnMobiusApertureStokesInverseTilt s pk.1 := by
            exact mul_le_mul_of_nonneg_right (by norm_num)
              (gammaSewnMobiusApertureStokesInverseTilt_pos hs pk.1).le
  rw [gammaSewnMobiusApertureStokesReciprocalGapNode]
  exact (inv_le_inv₀ (lt_of_lt_of_le hlog hgap) hlog).2 hgap

def gammaSewnMobiusApertureStokesReflectedAtom (s : ℝ) (z : ℂ) (pk : Nat.Primes × ℕ) : ℂ :=
  let I := gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk *
    gammaSewnMobiusApertureStokesGap s pk
  (I : ℂ) / (z - (gammaSewnMobiusApertureStokesGap s pk : ℂ)) +
    (I : ℂ) / (z + (gammaSewnMobiusApertureStokesGap s pk : ℂ))

private theorem norm_ofReal_mul_div_sub_le
    {b t : ℝ} (hb : 0 ≤ b) (ht : t ≠ 0)
    {z : ℂ} (hz : 0 < z.im) :
    ‖(b : ℂ) * z / (z - (t : ℂ))‖ ≤
      ‖z‖ * (1 + ‖z‖ / z.im) * (b / |t|) := by
  let a := |t|
  let d := ‖z - (t : ℂ)‖
  have ha : 0 < a := abs_pos.mpr ht
  have himabs : |(z - (t : ℂ)).im| ≤ d := Complex.abs_im_le_norm _
  have him : z.im ≤ d := by simpa [d, abs_of_pos hz] using himabs
  have hd : 0 < d := lt_of_lt_of_le hz him
  have htri0 := norm_sub_le z (z - (t : ℂ))
  have htri : a ≤ d + ‖z‖ := by
    simpa [a, d, Complex.norm_real, Real.norm_eq_abs, add_comm] using htri0
  have hzscale : ‖z‖ ≤ (‖z‖ / z.im) * d := by
    calc
      ‖z‖ = (‖z‖ / z.im) * z.im := by field_simp
      _ ≤ (‖z‖ / z.im) * d := by
        exact mul_le_mul_of_nonneg_left him (div_nonneg (norm_nonneg _) hz.le)
  have hatscale : a ≤ (1 + ‖z‖ / z.im) * d := by nlinarith
  have hrecip : 1 / d ≤ (1 + ‖z‖ / z.im) / a := by
    rw [div_le_div_iff₀ hd ha]
    simpa using hatscale
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hb]
  change b * ‖z‖ / d ≤ ‖z‖ * (1 + ‖z‖ / z.im) * (b / a)
  calc
    b * ‖z‖ / d = (b * ‖z‖) * (1 / d) := by ring
    _ ≤ (b * ‖z‖) * ((1 + ‖z‖ / z.im) / a) := by
      exact mul_le_mul_of_nonneg_left hrecip (mul_nonneg hb (norm_nonneg _))
    _ = ‖z‖ * (1 + ‖z‖ / z.im) * (b / a) := by ring

theorem gammaSewnMobiusApertureStokesReflectedAtom_eq_subtracted_difference
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im)
    (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesReflectedAtom s z pk =
      gammaSewnMobiusApertureStokesOneSubtractedAtom s z pk -
        (gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk : ℂ) * z /
          (z + (gammaSewnMobiusApertureStokesGap s pk : ℂ)) := by
  let b := gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk
  let g := gammaSewnMobiusApertureStokesGap s pk
  have hg : (g : ℂ) ≠ 0 := by
    exact_mod_cast (gammaSewnMobiusApertureStokesGap_pos hs pk).ne'
  have hminus : z - (g : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hplus : z + (g : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  rw [gammaSewnMobiusApertureStokesReflectedAtom,
    gammaSewnMobiusApertureStokesOneSubtractedAtom]
  change (((b * g : ℝ) : ℂ)) / (z - (g : ℂ)) +
      (((b * g : ℝ) : ℂ)) / (z + (g : ℂ)) =
    (b : ℂ) * z / (z - (g : ℂ)) -
      (b : ℂ) * z / (z + (g : ℂ))
  push_cast
  field_simp [hg, hminus, hplus]
  ring

theorem summable_gammaSewnMobiusApertureStokesReflectedAtom
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz : 0 < z.im) :
    Summable (gammaSewnMobiusApertureStokesReflectedAtom s z) := by
  have hpos := summable_gammaSewnMobiusApertureStokesOneSubtractedAtom hs hs1 hz
  have hneg : Summable (fun pk : Nat.Primes × ℕ =>
      (gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk : ℂ) * z /
        (z + (gammaSewnMobiusApertureStokesGap s pk : ℂ))) := by
    apply Summable.of_norm_bounded
      ((summable_gammaSewnMobiusApertureStokesDualFeatureCoefficient_div_gap hs hs1).mul_left
        (‖z‖ * (1 + ‖z‖ / z.im)))
    intro pk
    have hb :=
      (gammaSewnMobiusApertureStokesDualFeatureCoefficient_mem_unit hs pk).1
    have hg := (gammaSewnMobiusApertureStokesGap_pos hs pk).ne'
    have h := norm_ofReal_mul_div_sub_le hb (neg_ne_zero.mpr hg) hz
    simpa [abs_of_pos (gammaSewnMobiusApertureStokesGap_pos hs pk), gammaSewnMobiusApertureStokesReflectedWeight,
      sub_eq_add_neg] using h
  exact (hpos.sub hneg).congr
    (fun pk => (gammaSewnMobiusApertureStokesReflectedAtom_eq_subtracted_difference hs hz pk).symm)

theorem gammaSewnMobiusApertureStokesReflectedAtom_im_nonpos
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im)
    (pk : Nat.Primes × ℕ) :
    (gammaSewnMobiusApertureStokesReflectedAtom s z pk).im ≤ 0 := by
  let I := gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk *
    gammaSewnMobiusApertureStokesGap s pk
  let g := gammaSewnMobiusApertureStokesGap s pk
  have hI : 0 ≤ I := mul_nonneg
    (gammaSewnMobiusApertureStokesDualFeatureCoefficient_mem_unit hs pk).1
    (gammaSewnMobiusApertureStokesGap_pos hs pk).le
  change (((I : ℂ) / (z - (g : ℂ)) + (I : ℂ) / (z + (g : ℂ))).im) ≤ 0
  rw [Complex.add_im]
  rw [HTGeometry.im_ofReal_div_sub_ofReal I g z]
  rw [show z + (g : ℂ) = z - ((-g : ℝ) : ℂ) by push_cast; ring]
  rw [HTGeometry.im_ofReal_div_sub_ofReal I (-g) z]
  exact add_nonpos
    (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_nonneg hI hz.le)) (Complex.normSq_nonneg _))
    (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_nonneg hI hz.le)) (Complex.normSq_nonneg _))

theorem gammaSewnMobiusApertureStokesReflectedAtom_neg (s : ℝ) (z : ℂ) (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesReflectedAtom s (-z) pk = -gammaSewnMobiusApertureStokesReflectedAtom s z pk := by
  let I := gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk *
    gammaSewnMobiusApertureStokesGap s pk
  let g := gammaSewnMobiusApertureStokesGap s pk
  change (I : ℂ) / (-z - (g : ℂ)) + (I : ℂ) / (-z + (g : ℂ)) =
    -((I : ℂ) / (z - (g : ℂ)) + (I : ℂ) / (z + (g : ℂ)))
  rw [show -z - (g : ℂ) = -(z + (g : ℂ)) by ring,
    show -z + (g : ℂ) = -(z - (g : ℂ)) by ring]
  simp only [div_neg]
  ring

theorem gammaSewnMobiusApertureStokesReflectedAtom_eq_compactMarkov
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im)
    (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesReflectedAtom s z pk =
      -2 * (gammaSewnMobiusApertureStokesReflectedWeight s pk : ℂ) * z /
        (1 - ((gammaSewnMobiusApertureStokesReciprocalGapNode s pk : ℂ) * z) ^ 2) := by
  let b := gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk
  let g := gammaSewnMobiusApertureStokesGap s pk
  have hg : (g : ℂ) ≠ 0 := by
    exact_mod_cast (gammaSewnMobiusApertureStokesGap_pos hs pk).ne'
  have hminus : z - (g : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hplus : z + (g : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hquadne : -z ^ 2 + (g : ℂ) ^ 2 ≠ 0 := by
    rw [show -z ^ 2 + (g : ℂ) ^ 2 =
      -(z - (g : ℂ)) * (z + (g : ℂ)) by ring]
    exact mul_ne_zero (neg_ne_zero.mpr hminus) hplus
  rw [gammaSewnMobiusApertureStokesReflectedAtom, gammaSewnMobiusApertureStokesReflectedWeight, gammaSewnMobiusApertureStokesReciprocalGapNode]
  change (((b * g : ℝ) : ℂ)) / (z - (g : ℂ)) +
      (((b * g : ℝ) : ℂ)) / (z + (g : ℂ)) =
    -2 * ((b / g : ℝ) : ℂ) * z /
      (1 - ((((g⁻¹ : ℝ) : ℂ)) * z) ^ 2)
  push_cast
  rw [show 1 - ((g : ℂ)⁻¹ * z) ^ 2 =
      (-z ^ 2 + (g : ℂ) ^ 2) / (g : ℂ) ^ 2 by
    field_simp [hg]
    ring]
  field_simp [hg, hminus, hplus, hquadne]
  ring

def gammaSewnMobiusApertureStokesReflectedResponse (s : ℝ) (z : ℂ) : ℂ :=
  ∑' pk : Nat.Primes × ℕ, gammaSewnMobiusApertureStokesReflectedAtom s z pk

theorem gammaSewnMobiusApertureStokesReflectedResponse_im_nonpos
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz : 0 < z.im) :
    (gammaSewnMobiusApertureStokesReflectedResponse s z).im ≤ 0 := by
  rw [gammaSewnMobiusApertureStokesReflectedResponse, Complex.im_tsum (summable_gammaSewnMobiusApertureStokesReflectedAtom hs hs1 hz)]
  exact tsum_nonpos (gammaSewnMobiusApertureStokesReflectedAtom_im_nonpos hs hz)

theorem gammaSewnMobiusApertureStokesReflectedResponse_neg
    (s : ℝ) (z : ℂ) :
    gammaSewnMobiusApertureStokesReflectedResponse s (-z) = -gammaSewnMobiusApertureStokesReflectedResponse s z := by
  rw [gammaSewnMobiusApertureStokesReflectedResponse, gammaSewnMobiusApertureStokesReflectedResponse]
  rw [tsum_congr (gammaSewnMobiusApertureStokesReflectedAtom_neg s z)]
  rw [tsum_neg]

abbrev GammaSewnMobiusApertureStokesSignedPrimePowerIndex :=
  (Nat.Primes × ℕ) ⊕ (Nat.Primes × ℕ)

def gammaSewnMobiusApertureStokesSignedWeight (s : ℝ) : GammaSewnMobiusApertureStokesSignedPrimePowerIndex → ℝ
  | Sum.inl pk => gammaSewnMobiusApertureStokesReflectedWeight s pk
  | Sum.inr pk => gammaSewnMobiusApertureStokesReflectedWeight s pk

def gammaSewnMobiusApertureStokesSignedReciprocalGapNode (s : ℝ) : GammaSewnMobiusApertureStokesSignedPrimePowerIndex → ℝ
  | Sum.inl pk => gammaSewnMobiusApertureStokesReciprocalGapNode s pk
  | Sum.inr pk => -gammaSewnMobiusApertureStokesReciprocalGapNode s pk

theorem gammaSewnMobiusApertureStokesSignedWeight_pos {s : ℝ} (hs : 0 < s)
    (i : GammaSewnMobiusApertureStokesSignedPrimePowerIndex) :
    0 < gammaSewnMobiusApertureStokesSignedWeight s i := by
  cases i <;> exact gammaSewnMobiusApertureStokesReflectedWeight_pos hs _

theorem gammaSewnMobiusApertureStokesSignedReciprocalGapNode_abs_le {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (i : GammaSewnMobiusApertureStokesSignedPrimePowerIndex) :
    |gammaSewnMobiusApertureStokesSignedReciprocalGapNode s i| ≤ (Real.log 2)⁻¹ := by
  cases i <;>
    simp only [gammaSewnMobiusApertureStokesSignedReciprocalGapNode, abs_neg, abs_of_pos (gammaSewnMobiusApertureStokesReciprocalGapNode_pos hs _)] <;>
    exact gammaSewnMobiusApertureStokesReciprocalGapNode_le hs hs1 _

theorem summable_gammaSewnMobiusApertureStokesSignedWeight {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Summable (gammaSewnMobiusApertureStokesSignedWeight s) := by
  let h := summable_gammaSewnMobiusApertureStokesDualFeatureCoefficient_div_gap
    hs hs1
  apply Summable.sum (gammaSewnMobiusApertureStokesSignedWeight s)
  · change Summable (fun pk : Nat.Primes × ℕ => gammaSewnMobiusApertureStokesReflectedWeight s pk)
    simpa [gammaSewnMobiusApertureStokesReflectedWeight] using h
  · change Summable (fun pk : Nat.Primes × ℕ => gammaSewnMobiusApertureStokesReflectedWeight s pk)
    simpa [gammaSewnMobiusApertureStokesReflectedWeight] using h

/-- Finite positive symmetric reciprocal-gap carrier forced by Stokes reflection. -/
def gammaSewnMobiusApertureStokesReflectedCompactCarrier (s : ℝ) : Measure ℝ :=
  Measure.sum fun i : GammaSewnMobiusApertureStokesSignedPrimePowerIndex =>
    ENNReal.ofReal (gammaSewnMobiusApertureStokesSignedWeight s i) • Measure.dirac (gammaSewnMobiusApertureStokesSignedReciprocalGapNode s i)

theorem integrable_one_gammaSewnMobiusApertureStokesReflectedCompactCarrier
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Integrable (fun _ : ℝ => (1 : ℝ)) (gammaSewnMobiusApertureStokesReflectedCompactCarrier s) := by
  rw [gammaSewnMobiusApertureStokesReflectedCompactCarrier]
  apply integrable_sum_dirac (fun i => by simp [ENNReal.ofReal_ne_top])
  apply (summable_gammaSewnMobiusApertureStokesSignedWeight hs hs1).congr
  intro i
  rw [ENNReal.toReal_ofReal (gammaSewnMobiusApertureStokesSignedWeight_pos hs i).le]
  simp

theorem gammaSewnMobiusApertureStokesReflectedCompactCarrier_finite
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    IsFiniteMeasure (gammaSewnMobiusApertureStokesReflectedCompactCarrier s) := by
  exact (integrable_const_iff_isFiniteMeasure one_ne_zero).mp
    (integrable_one_gammaSewnMobiusApertureStokesReflectedCompactCarrier hs hs1)

theorem ae_gammaSewnMobiusApertureStokesReflectedCompactCarrier_mem_compact
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∀ᵐ x : ℝ ∂gammaSewnMobiusApertureStokesReflectedCompactCarrier s, |x| ≤ (Real.log 2)⁻¹ := by
  rw [gammaSewnMobiusApertureStokesReflectedCompactCarrier, Measure.ae_sum_iff]
  intro i
  apply Measure.ae_smul_measure
  exact (ae_dirac_iff
    (measurableSet_le measurable_id.abs measurable_const)).2
      (gammaSewnMobiusApertureStokesSignedReciprocalGapNode_abs_le hs hs1 i)

private theorem summable_gammaSewnMobiusApertureStokesReflectedMarkovBranch
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz : ‖z‖ < 1 / (2 * (Real.log 2)⁻¹))
    (sign : Bool) :
    Summable (fun pk : Nat.Primes × ℕ =>
      (gammaSewnMobiusApertureStokesReflectedWeight s pk : ℂ) *
        (1 - ((if sign then gammaSewnMobiusApertureStokesReciprocalGapNode s pk else -gammaSewnMobiusApertureStokesReciprocalGapNode s pk : ℝ) : ℂ) * z)⁻¹) := by
  have hB : 0 < (Real.log 2)⁻¹ := inv_pos.mpr (Real.log_pos (by norm_num))
  have hw := summable_gammaSewnMobiusApertureStokesDualFeatureCoefficient_div_gap hs hs1
  apply Summable.of_norm_bounded (hw.mul_left 2)
  intro pk
  have hnode : |if sign then gammaSewnMobiusApertureStokesReciprocalGapNode s pk else -gammaSewnMobiusApertureStokesReciprocalGapNode s pk| ≤
      (Real.log 2)⁻¹ := by
    split_ifs <;> simpa [abs_of_pos (gammaSewnMobiusApertureStokesReciprocalGapNode_pos hs pk)] using gammaSewnMobiusApertureStokesReciprocalGapNode_le hs hs1 pk
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gammaSewnMobiusApertureStokesReflectedWeight_pos hs pk).le]
  simpa [gammaSewnMobiusApertureStokesReflectedWeight, mul_comm] using mul_le_mul_of_nonneg_left
    (norm_inv_one_sub_real_mul_le_two hB hnode hz)
    (gammaSewnMobiusApertureStokesReflectedWeight_pos hs pk).le

set_option maxHeartbeats 800000 in
theorem gammaSewnMobiusApertureStokesReflectedCompactCarrier_markov_eq_tsum
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz : ‖z‖ < 1 / (2 * (Real.log 2)⁻¹)) :
    compactMarkovTransform (gammaSewnMobiusApertureStokesReflectedCompactCarrier s) z =
      ∑' pk : Nat.Primes × ℕ,
        (gammaSewnMobiusApertureStokesReflectedWeight s pk : ℂ) *
          ((1 - (gammaSewnMobiusApertureStokesReciprocalGapNode s pk : ℂ) * z)⁻¹ +
            (1 + (gammaSewnMobiusApertureStokesReciprocalGapNode s pk : ℂ) * z)⁻¹) := by
  letI : IsFiniteMeasure (gammaSewnMobiusApertureStokesReflectedCompactCarrier s) :=
    gammaSewnMobiusApertureStokesReflectedCompactCarrier_finite hs hs1
  rw [compactMarkovTransform, compactMarkovKernelMoment, gammaSewnMobiusApertureStokesReflectedCompactCarrier]
  rw [integral_sum_dirac (fun i => by simp [ENNReal.ofReal_ne_top])]
  rw [tsum_congr (fun i => by
    rw [ENNReal.toReal_ofReal (gammaSewnMobiusApertureStokesSignedWeight_pos hs i).le])]
  simp only [pow_zero, one_mul, Nat.zero_add, pow_one]
  change (∑' i : GammaSewnMobiusApertureStokesSignedPrimePowerIndex,
      (gammaSewnMobiusApertureStokesSignedWeight s i : ℂ) *
        (1 - (gammaSewnMobiusApertureStokesSignedReciprocalGapNode s i : ℂ) * z)⁻¹) = _
  have hleft := summable_gammaSewnMobiusApertureStokesReflectedMarkovBranch hs hs1 hz true
  have hright := summable_gammaSewnMobiusApertureStokesReflectedMarkovBranch hs hs1 hz false
  have hleft' : Summable
      ((fun i : GammaSewnMobiusApertureStokesSignedPrimePowerIndex =>
        (gammaSewnMobiusApertureStokesSignedWeight s i : ℂ) *
          (1 - (gammaSewnMobiusApertureStokesSignedReciprocalGapNode s i : ℂ) * z)⁻¹) ∘ Sum.inl) := by
    change Summable (fun pk : Nat.Primes × ℕ =>
      (gammaSewnMobiusApertureStokesReflectedWeight s pk : ℂ) * (1 - (gammaSewnMobiusApertureStokesReciprocalGapNode s pk : ℂ) * z)⁻¹)
    simpa using hleft
  have hright' : Summable
      ((fun i : GammaSewnMobiusApertureStokesSignedPrimePowerIndex =>
        (gammaSewnMobiusApertureStokesSignedWeight s i : ℂ) *
          (1 - (gammaSewnMobiusApertureStokesSignedReciprocalGapNode s i : ℂ) * z)⁻¹) ∘ Sum.inr) := by
    change Summable (fun pk : Nat.Primes × ℕ =>
      (gammaSewnMobiusApertureStokesReflectedWeight s pk : ℂ) * (1 - ((-gammaSewnMobiusApertureStokesReciprocalGapNode s pk : ℝ) : ℂ) * z)⁻¹)
    simpa using hright
  rw [hleft'.tsum_sum hright']
  simp only [gammaSewnMobiusApertureStokesSignedWeight,
    gammaSewnMobiusApertureStokesSignedReciprocalGapNode]
  have hlcanon : Summable (fun pk : Nat.Primes × ℕ =>
      (gammaSewnMobiusApertureStokesReflectedWeight s pk : ℂ) * (1 - (gammaSewnMobiusApertureStokesReciprocalGapNode s pk : ℂ) * z)⁻¹) := by
    simpa using hleft
  have hrcanon : Summable (fun pk : Nat.Primes × ℕ =>
      (gammaSewnMobiusApertureStokesReflectedWeight s pk : ℂ) * (1 - ((-gammaSewnMobiusApertureStokesReciprocalGapNode s pk : ℝ) : ℂ) * z)⁻¹) := by
    simpa using hright
  rw [← hlcanon.tsum_add hrcanon]
  apply tsum_congr
  intro pk
  simp only [Complex.ofReal_neg]
  ring_nf

theorem gammaSewnMobiusApertureStokesReflectedResponse_eq_neg_mul_compactMarkov
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hzIm : 0 < z.im)
    (hz : ‖z‖ < 1 / (2 * (Real.log 2)⁻¹)) :
    gammaSewnMobiusApertureStokesReflectedResponse s z =
      -z * compactMarkovTransform (gammaSewnMobiusApertureStokesReflectedCompactCarrier s) z := by
  rw [gammaSewnMobiusApertureStokesReflectedResponse, gammaSewnMobiusApertureStokesReflectedCompactCarrier_markov_eq_tsum hs hs1 hz]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro pk
  rw [gammaSewnMobiusApertureStokesReflectedAtom_eq_compactMarkov hs hzIm]
  let x : ℂ := (gammaSewnMobiusApertureStokesReciprocalGapNode s pk : ℂ) * z
  have hminus : 1 - x ≠ 0 := by
    intro h
    have habs := congrArg Complex.im h
    simp [x] at habs
    have hnpos := gammaSewnMobiusApertureStokesReciprocalGapNode_pos hs pk
    have hz0 : z.im ≠ 0 := hzIm.ne'
    rcases habs with hzero | hzero
    · exact hnpos.ne' hzero
    · exact hz0 hzero
  have hplus : 1 + x ≠ 0 := by
    intro h
    have habs := congrArg Complex.im h
    simp [x] at habs
    have hnpos := gammaSewnMobiusApertureStokesReciprocalGapNode_pos hs pk
    rcases habs with hzero | hzero
    · exact hnpos.ne' hzero
    · exact hzIm.ne' hzero
  have hquad : 1 - x ^ 2 ≠ 0 := by
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
    exact mul_ne_zero hminus hplus
  change -2 * (gammaSewnMobiusApertureStokesReflectedWeight s pk : ℂ) * z / (1 - x ^ 2) =
    -z * ((gammaSewnMobiusApertureStokesReflectedWeight s pk : ℂ) * ((1 - x)⁻¹ + (1 + x)⁻¹))
  field_simp [hminus, hplus, hquad]
  ring

end RHTower
