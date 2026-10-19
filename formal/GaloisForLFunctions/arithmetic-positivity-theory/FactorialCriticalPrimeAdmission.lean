import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialPhaseBohrCoercivityAndTailIndependence
import GaloisForLFunctions.«arithmetic-positivity-theory».EnvelopeCriticalPrimeTransitionAndDilationGain
/-! Critical prime admission for exact factorial tails.

Reweighting the corrected tails by `exp (-x)` gives the critical envelope.
Their existing bounded lattice primitives and right derivatives yield one extra
dilation power in every fixed finite source correlation. The constant retains
coefficient and scale moments. Absolute convergence applies to the series of
integrated prime atoms.
-/


open MeasureTheory Set Filter
open scoped BigOperators Topology
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory
noncomputable section
set_option autoImplicit false

private theorem critical_weight_integrable :
    IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi 1) := by
  exact integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)

private theorem critical_weight_integral :
    (∫ v : ℝ in Ioi 1, v ^ (-2 : ℝ)) = 1 := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)]
  norm_num

private theorem critical_correlation_bound
    {F D Q : ℝ → ℝ} {A L P r : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hP : 0 ≤ P) (hr : 1 ≤ r)
    (hFc : Continuous F) (hQd : ∀ v, 0 < v → HasDerivAt Q (F v) v)
    (hFd : ∀ v, HasDerivWithinAt F (D v) (Ioi v) v)
    (hFb : ∀ v, |F v| ≤ A) (hDb : ∀ v, |D v| ≤ L)
    (hQb : ∀ v, |Q v| ≤ P) :
    |∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * F v * F (r * v)| ≤
      P * (4 * A + L) / r := by
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let W : ℝ → ℝ := fun v => v ^ (-2 : ℝ)
  let f : ℝ → ℝ := fun v => W v * F v * F (r * v)
  let H : ℝ → ℝ := fun v => W v * F v * (Q (r * v) / r)
  let E : ℝ → ℝ := fun v =>
    ((-2 * v ^ (-3 : ℝ)) * F v + W v * D v) * (Q (r * v) / r)
  let C : ℝ := P * (2 * A + L) / r
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hWn' {v : ℝ} (hv : 1 ≤ v) : 0 ≤ W v :=
    Real.rpow_nonneg (by linarith) _
  have hWle {v : ℝ} (hv : 1 ≤ v) : W v ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hv (by norm_num)
  have hWd {v : ℝ} (hv : 0 < v) : HasDerivAt W (-2 * v ^ (-3 : ℝ)) v := by
    simpa only [show (-2 : ℝ) - 1 = -3 by norm_num] using
      Real.hasDerivAt_rpow_const (p := (-2 : ℝ)) (Or.inl (ne_of_gt hv))
  have hfc : ContinuousOn f (Ici 1) := by
    intro v hv
    exact (((hWd (lt_of_lt_of_le zero_lt_one hv)).continuousAt.mul hFc.continuousAt).mul
      (hFc.continuousAt.comp (continuous_const.mul continuous_id).continuousAt)).continuousWithinAt
  have hfi : IntegrableOn f (Ioi 1) := by
    refine Integrable.mono' (critical_weight_integrable.const_mul (A * A))
      (hfc.mono Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    dsimp [f, W]
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_trans zero_le_one hv.le) _)]
    nlinarith [mul_le_mul (hFb v) (hFb (r * v)) (abs_nonneg _) hA,
      mul_nonneg (show 0 ≤ v ^ (-2 : ℝ) from hWn' hv.le)
        (sub_nonneg.mpr (mul_le_mul (hFb v) (hFb (r * v)) (abs_nonneg _) hA))]
  have hQrb (v : ℝ) : |Q (r * v) / r| ≤ P / r := by
    rw [abs_div, abs_of_pos hrp]
    exact div_le_div_of_nonneg_right (hQb _) hrp.le
  have hEb {v : ℝ} (hv : 1 ≤ v) : |E v| ≤ C * W v := by
    have hvp : 0 < v := by linarith
    have hW3 : v ^ (-3 : ℝ) ≤ W v :=
      Real.rpow_le_rpow_of_exponent_le hv (by norm_num)
    have hW3n : 0 ≤ v ^ (-3 : ℝ) := Real.rpow_nonneg hvp.le _
    have hinside : |(-2 * v ^ (-3 : ℝ)) * F v + W v * D v| ≤
        (2 * A + L) * W v := by
      calc
        _ ≤ |(-2 * v ^ (-3 : ℝ)) * F v| + |W v * D v| := abs_add_le _ _
        _ = 2 * v ^ (-3 : ℝ) * |F v| + W v * |D v| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hW3n, abs_of_nonneg (hWn' hv)]
          norm_num
        _ ≤ 2 * W v * A + W v * L := by
          exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hW3 (by norm_num))
            (hFb v) (abs_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left (hDb v) (hWn' hv))
        _ = _ := by ring
    dsimp [E]
    rw [abs_mul]
    have := mul_le_mul hinside (hQrb v) (abs_nonneg _) (by positivity)
    exact this.trans_eq (by dsimp [C]; ring)
  have hHb {v : ℝ} (hv : 1 ≤ v) : |H v| ≤ A * P / r := by
    dsimp [H]
    rw [abs_mul, abs_mul, abs_of_nonneg (hWn' hv)]
    have h1 : W v * |F v| ≤ A := by
      exact (mul_le_mul (hWle hv) (hFb v) (abs_nonneg _) (by norm_num)).trans_eq (one_mul A)
    exact (mul_le_mul h1 (hQrb v) (abs_nonneg _) hA).trans_eq (by ring)
  have hfin (T : ℝ) (hT : 1 ≤ T) : |∫ v in (1 : ℝ)..T, f v| ≤ P * (4 * A + L) / r := by
    have hWc : ContinuousOn W (Icc 1 T) := fun v hv =>
      (hWd (lt_of_lt_of_le zero_lt_one hv.1)).continuousAt.continuousWithinAt
    have hHc : ContinuousOn H (Icc 1 T) := by
      intro v hv
      have hvp := lt_of_lt_of_le zero_lt_one hv.1
      have hqd := hQd (r * v) (mul_pos hrp hvp)
      exact (((hWd hvp).continuousAt.mul hFc.continuousAt).mul
        ((hqd.continuousAt.comp (continuous_const.mul continuous_id).continuousAt).div_const r)).continuousWithinAt
    have hHd : ∀ v ∈ Ioo 1 T, HasDerivWithinAt H (f v + E v) (Ioi v) v := by
      intro v hv
      have hvp := zero_lt_one.trans hv.1
      have hqd := ((hQd (r * v) (mul_pos hrp hvp)).comp v
        ((hasDerivAt_id v).const_mul r)).div_const r
      have hqd' : HasDerivAt (fun y => Q (r * y) / r) (F (r * v)) v := by
        convert hqd using 1 <;> try rfl
        field_simp
      convert (((hWd hvp).hasDerivWithinAt.mul (hFd v)).mul
        hqd'.hasDerivWithinAt) using 1 <;> try rfl
      dsimp [f, E]
      ring
    have hfiT : IntervalIntegrable f volume 1 T :=
      (hfc.mono (fun _ h => h.1)).intervalIntegrable_of_Icc hT
    have hWiT : IntervalIntegrable W volume 1 T := hWc.intervalIntegrable_of_Icc hT
    have hupper := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
      (φ := fun v => f v + C * W v) hT hHc hHd
      (((hfc.mono (fun _ h => h.1)).add (continuousOn_const.mul hWc)).integrableOn_Icc)
      (fun v hv => by linarith [(abs_le.mp (hEb hv.1.le)).2])
    have hlower := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le
      (φ := fun v => f v - C * W v) hT hHc hHd
      (((hfc.mono (fun _ h => h.1)).sub (continuousOn_const.mul hWc)).integrableOn_Icc)
      (fun v hv => by linarith [(abs_le.mp (hEb hv.1.le)).1])
    have hweight : (∫ v in (1 : ℝ)..T, W v) ≤ 1 := by
      rw [intervalIntegral.integral_of_le hT]
      have hm := setIntegral_mono_set (s := Ioc 1 T) (t := Ioi 1) critical_weight_integrable
        (ae_restrict_of_forall_mem measurableSet_Ioi (fun v hv => hWn' hv.le))
        (Eventually.of_forall (fun v hv => hv.1))
      exact hm.trans_eq critical_weight_integral
    rw [intervalIntegral.integral_add hfiT (hWiT.const_mul C),
      intervalIntegral.integral_const_mul] at hupper
    rw [intervalIntegral.integral_sub hfiT (hWiT.const_mul C),
      intervalIntegral.integral_const_mul] at hlower
    have hCT := mul_le_mul_of_nonneg_left hweight hC
    have hH1 := abs_le.mp (hHb (v := 1) le_rfl)
    have hHT := abs_le.mp (hHb hT)
    have hbudget : P * (4 * A + L) / r = 2 * (A * P / r) + C := by
      dsimp [C]
      ring
    rw [hbudget]
    rw [abs_le]
    constructor <;> linarith only [hupper, hlower, hCT, hH1.1, hH1.2, hHT.1, hHT.2]
  have hlim := intervalIntegral_tendsto_integral_Ioi (μ := volume) (1 : ℝ) hfi tendsto_id
  exact le_of_tendsto hlim.abs (eventually_atTop.mpr ⟨1, hfin⟩)

private def filterRightSlope (u : ℝ) : ℝ :=
  (1 / 2 - Int.fract (4 * u)) - 4 * (1 / 2 - Int.fract (2 * u)) +
    4 * (1 / 2 - Int.fract u)

private theorem clamped_mul_right {a : ℝ} (ha : 0 < a) (v : ℝ) :
    HasDerivWithinAt (fun u => periodicClampedKernel (a * u))
      (a * (1 / 2 - Int.fract (a * v))) (Ioi v) v := by
  have hd := (RHTower.DeletionMixedRefinement.bernoulliPeriodic_hasDerivWithinAt_right (a * v)).neg
  have hc := hd.comp v ((hasDerivAt_id v).const_mul a).hasDerivWithinAt
    (show MapsTo (fun u : ℝ => a * u) (Ioi v) (Ici (a * v)) from
      fun u hu => mul_le_mul_of_nonneg_left hu.le ha.le)
  convert hc using 1 <;> first | rfl | ring

private theorem filter_right (v : ℝ) :
    HasDerivWithinAt dyadicBernoulliFilter (filterRightSlope v) (Ioi v) v := by
  have h4 := clamped_mul_right (a := 4) (by norm_num) v
  have h2 := clamped_mul_right (a := 2) (by norm_num) v
  have h1 := clamped_mul_right (a := 1) (by norm_num) v
  convert ((h4.div_const 4).sub (h2.const_mul 2)).add (h1.const_mul 4) using 1 <;>
    first
    | rfl
    | (funext u; simp only [dyadicBernoulliFilter, Pi.add_apply, Pi.sub_apply, one_mul])
    | (dsimp [filterRightSlope]; simp only [one_mul]; ring)

private theorem filter_slope_bound (v : ℝ) : |filterRightSlope v| ≤ 9 / 2 := by
  have h (u : ℝ) : |1 / 2 - Int.fract u| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [Int.fract_nonneg u, Int.fract_lt_one u]
  dsimp [filterRightSlope]
  calc
    _ ≤ |(1 / 2 - Int.fract (4 * v)) - 4 * (1 / 2 - Int.fract (2 * v))| +
        |4 * (1 / 2 - Int.fract v)| := abs_add_le _ _
    _ ≤ |1 / 2 - Int.fract (4 * v)| + |4 * (1 / 2 - Int.fract (2 * v))| +
        |4 * (1 / 2 - Int.fract v)| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ 9 / 2 := by
      rw [abs_mul, abs_mul]
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      linarith [h (4 * v), h (2 * v), h v]

private def phaseRightSlope (n : ℕ) (v : ℝ) : ℝ :=
  factorialShiftedFreq (n + 1) * filterRightSlope (factorialShiftedFreq (n + 1) * v) -
    ((n + 1 : ℕ) : ℝ) * filterRightSlope (((n + 1 : ℕ) : ℝ) * v)

private theorem phase_right (n : ℕ) (v : ℝ) :
    HasDerivWithinAt (factorialPhaseProfile (n + 1)) (phaseRightSlope n v) (Ioi v) v := by
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hLam := factorialShiftedFreq_pos (N := n + 1) (by omega)
  have hc (a : ℝ) (ha : 0 < a) := (filter_right (a * v)).comp v
    ((hasDerivAt_id v).const_mul a).hasDerivWithinAt
    (show MapsTo (fun u : ℝ => a * u) (Ioi v) (Ioi (a * v)) from
      fun u hu => mul_lt_mul_of_pos_left hu ha)
  convert (hc _ hLam).sub (hc _ hN) using 1 <;>
    first | rfl | (dsimp [phaseRightSlope]; ring)

private theorem phase_slope_bound (n : ℕ) (v : ℝ) :
    |phaseRightSlope n v| ≤ 14 * ((n + 1 : ℕ) : ℝ) := by
  have hN : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hLam := factorialShiftedFreq_pos (N := n + 1) (by omega)
  have hδ := (factorialShiftedFreq_sub_self_bounds (N := n + 1) (by omega)).2
  dsimp [phaseRightSlope]
  calc
    _ ≤ |factorialShiftedFreq (n + 1) * filterRightSlope (factorialShiftedFreq (n + 1) * v)| +
        |((n + 1 : ℕ) : ℝ) * filterRightSlope (((n + 1 : ℕ) : ℝ) * v)| := abs_sub _ _
    _ ≤ factorialShiftedFreq (n + 1) * (9 / 2) + ((n + 1 : ℕ) : ℝ) * (9 / 2) := by
      rw [abs_mul, abs_mul, abs_of_pos hLam, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))]
      exact add_le_add (mul_le_mul_of_nonneg_left (filter_slope_bound _) hLam.le)
        (mul_le_mul_of_nonneg_left (filter_slope_bound _) (by positivity))
    _ ≤ _ := by linarith

private def realPhase (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) : ℝ :=
  ∑ n ∈ S, b n * factorialPhaseProfile (n + 1) v

private def phasePrimitive (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) : ℝ :=
  ∑ n ∈ S, b n * (factorialMuntzTailLatticePrimitive n (((n + 1 : ℕ) : ℝ) * v) /
    ((n + 1 : ℕ) : ℝ))

private theorem realPhase_eq_re (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    realPhase S b v = (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re := by
  simp [realPhase, factorialPhaseCombination]

private theorem realPhase_continuous (S : Finset ℕ) (b : ℕ → ℝ) :
    Continuous (realPhase S b) := by
  exact continuous_finsetSum S fun n _ => continuous_const.mul (continuous_factorialPhaseProfile _)

private theorem realPhase_bound (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    |realPhase S b v| ≤ 2 * ∑ n ∈ S, |b n| := by
  dsimp [realPhase]
  calc
    _ ≤ ∑ n ∈ S, |b n * factorialPhaseProfile (n + 1) v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ S, |b n| * 2 := Finset.sum_le_sum fun n _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_factorialPhaseProfile_le _ _) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

private theorem realPhase_right (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    HasDerivWithinAt (realPhase S b) (∑ n ∈ S, b n * phaseRightSlope n v) (Ioi v) v :=
  HasDerivWithinAt.fun_sum fun n _ => (phase_right n v).const_mul (b n)

private theorem realPhase_slope_bound (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    |∑ n ∈ S, b n * phaseRightSlope n v| ≤ 14 * ∑ n ∈ S, ((n + 1 : ℕ) : ℝ) * |b n| := by
  calc
    _ ≤ ∑ n ∈ S, |b n * phaseRightSlope n v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ S, |b n| * (14 * ((n + 1 : ℕ) : ℝ)) := Finset.sum_le_sum fun n _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (phase_slope_bound _ _) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

private theorem phasePrimitive_bound (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    |phasePrimitive S b v| ≤ 12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) := by
  dsimp [phasePrimitive]
  calc
    _ ≤ ∑ n ∈ S, |b n * (factorialMuntzTailLatticePrimitive n (((n + 1 : ℕ) : ℝ) * v) /
        ((n + 1 : ℕ) : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ S, |b n| * (12 / ((n + 1 : ℕ) : ℝ)) := Finset.sum_le_sum fun n _ => by
      rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (factorialMuntzTailLatticePrimitive_abs_le _ _) (by positivity)) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

private theorem phasePrimitive_deriv (S : Finset ℕ) (b : ℕ → ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (phasePrimitive S b) (realPhase S b v) v := by
  apply HasDerivAt.fun_sum
  intro n _
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hd := ((factorialMuntzTailLatticePrimitive_hasDerivAt n (y := ((n + 1 : ℕ) : ℝ) * v)
    (by positivity)).comp v ((hasDerivAt_id v).const_mul ((n + 1 : ℕ) : ℝ))).div_const ((n + 1 : ℕ) : ℝ)
  have hd' : HasDerivAt (fun u => factorialMuntzTailLatticePrimitive n (((n + 1 : ℕ) : ℝ) * u) /
      ((n + 1 : ℕ) : ℝ)) (factorialPhaseProfile (n + 1) v) v := by
    convert hd using 1 <;> try rfl
    rw [factorialPhaseProfile_eq_tailRemainder n hv.le]
    field_simp
  exact hd'.const_mul (b n)

/-- The scale moments retained by critical prime admission. -/
def criticalFactorialPrimeConstant (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  (12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) *
    (8 * ∑ n ∈ S, |b n| + 14 * ∑ n ∈ S, ((n + 1 : ℕ) : ℝ) * |b n|)

/-- Actual critical physical correlations gain one dilation power for each fixed finite source. -/
theorem critical_factorial_physical_correlation_bound (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) :
    |∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) *
      (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re *
      (factorialPhaseCombination S (fun n => (b n : ℂ)) (((k + 1 : ℕ) : ℝ) * v)).re| ≤
      criticalFactorialPrimeConstant S b / ((k + 1 : ℕ) : ℝ) := by
  have h := critical_correlation_bound (F := realPhase S b)
    (D := fun v => ∑ n ∈ S, b n * phaseRightSlope n v) (Q := phasePrimitive S b)
    (A := 2 * ∑ n ∈ S, |b n|) (L := 14 * ∑ n ∈ S, ((n + 1 : ℕ) : ℝ) * |b n|)
    (P := 12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ))
    (r := ((k + 1 : ℕ) : ℝ)) (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
    (realPhase_continuous S b) (fun v hv => phasePrimitive_deriv S b hv)
    (realPhase_right S b) (realPhase_bound S b) (realPhase_slope_bound S b) (phasePrimitive_bound S b)
  simp only [realPhase_eq_re] at h
  convert h using 1
  unfold criticalFactorialPrimeConstant
  ring

/-- The exact factorial phase span with critical half-line envelope. -/
def criticalFactorialSource (S : Finset ℕ) (b : ℕ → ℝ) : ℝ → ℝ :=
  (Iic (0 : ℝ)).indicator (fun x => Real.exp (x / 2) *
    (factorialPhaseCombination S (fun n => (b n : ℂ)) (Real.exp (-x))).re)

private theorem critical_source_eq (S : Finset ℕ) (b : ℕ → ℝ) :
    criticalFactorialSource S b = (Iic (0 : ℝ)).indicator
      (fun x => Real.exp (x / 2) * realPhase S b (Real.exp (-x))) := by
  simp only [criticalFactorialSource, realPhase_eq_re]

/-- Critical reweighting is taken from the literal corrected sources. -/
theorem criticalFactorialSource_eq_correctedTail (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) :
    criticalFactorialSource S b x = ∑ n ∈ S,
      (b n / factorialTailAmplitude n) * Real.exp (-x) * factorialMuntzCorrectedTail n x := by
  rw [critical_source_eq]
  by_cases hx : x ≤ 0
  · rw [indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx)]
    dsimp [realPhase]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [factorialMuntzCorrectedTail_eq_factorialPhaseProfile,
      indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx)]
    have ha := (factorialTailAmplitude_pos n).ne'
    have he : Real.exp (-x) * Real.exp (3 * x / 2) = Real.exp (x / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = b n * (Real.exp (-x) * Real.exp (3 * x / 2)) *
          factorialPhaseProfile (n + 1) (Real.exp (-x)) := by rw [he]; ring
      _ = _ := by field_simp
  · rw [indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx)]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro n _
    rw [factorialMuntzCorrectedTail_eq_factorialPhaseProfile,
      indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx), mul_zero]

private theorem critical_log_product (S : Finset ℕ) (b : ℕ → ℝ) {r : ℝ} (hr : 1 ≤ r) :
    (fun x => criticalFactorialSource S b x * criticalFactorialSource S b (x - Real.log r)) =
      (Iic (0 : ℝ)).indicator (fun x => Real.exp (-(Real.log r) / 2) *
        (Real.exp x * (realPhase S b (Real.exp (-x)) * realPhase S b (r * Real.exp (-x))))) := by
  funext x
  have hrp : 0 < r := zero_lt_one.trans_le hr
  rw [critical_source_eq]
  by_cases hx : x ≤ 0
  · have hx' : x - Real.log r ≤ 0 := by linarith [Real.log_nonneg hr]
    rw [indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx),
      indicator_of_mem (show x - Real.log r ∈ Iic (0 : ℝ) from hx'),
      indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx)]
    have he : Real.exp (-(x - Real.log r)) = r * Real.exp (-x) := by
      rw [show -(x - Real.log r) = Real.log r + -x by ring, Real.exp_add, Real.exp_log hrp]
    have hexp : Real.exp (x / 2) * Real.exp ((x - Real.log r) / 2) =
        Real.exp (-(Real.log r) / 2) * Real.exp x := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [he]
    linear_combination realPhase S b (Real.exp (-x)) * realPhase S b (r * Real.exp (-x)) * hexp
  · rw [indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx), zero_mul,
      indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx)]

private theorem critical_exp_change_variables (F : ℝ → ℝ) :
    (∫ x in Iic (0 : ℝ), Real.exp x * F (Real.exp (-x))) =
      ∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * F v := by
  have h1 := integral_comp_neg_Iic (0 : ℝ) (fun y : ℝ => Real.exp (-y) * F (Real.exp y))
  simp only [neg_zero, neg_neg] at h1
  have h2 := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) (f := Real.exp)
    (f' := Real.exp) measurableSet_Ioi (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    Real.exp_injective.injOn (fun v => v ^ (-2 : ℝ) * F v)
  rw [Real.image_exp_Ioi, Real.exp_zero] at h2
  rw [h1, h2]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  dsimp only
  rw [abs_of_pos (Real.exp_pos y), smul_eq_mul, ← Real.exp_mul, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem critical_source_product_integrable (S : Finset ℕ) (b : ℕ → ℝ)
    {r : ℝ} (hr : 1 ≤ r) :
    Integrable (fun x => criticalFactorialSource S b x *
      criticalFactorialSource S b (x - Real.log r)) := by
  rw [critical_log_product S b hr]
  apply IntegrableOn.integrable_indicator
  · let A := 2 * ∑ n ∈ S, |b n|
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hc : Continuous (fun x => Real.exp (-(Real.log r) / 2) *
        (Real.exp x * (realPhase S b (Real.exp (-x)) * realPhase S b (r * Real.exp (-x))))) := by
      have hF := realPhase_continuous S b
      fun_prop
    refine Integrable.mono' ((integrableOn_exp_Iic 0).const_mul
      (Real.exp (-(Real.log r) / 2) * (A * A)))
      hc.aestronglyMeasurable.restrict ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have hm := mul_le_mul (realPhase_bound S b (Real.exp (-x)))
      (realPhase_bound S b (r * Real.exp (-x))) (abs_nonneg _) hA
    have h := mul_le_mul_of_nonneg_left hm
      (show 0 ≤ Real.exp (-(Real.log r) / 2) * Real.exp x by positivity)
    dsimp [A] at *
    nlinarith only [h]
  · exact measurableSet_Iic

private theorem critical_source_correlation_eq (S : Finset ℕ) (b : ℕ → ℝ)
    {r : ℝ} (hr : 1 ≤ r) :
    (∫ x : ℝ, criticalFactorialSource S b x * criticalFactorialSource S b (x - Real.log r)) =
      (Real.sqrt r)⁻¹ * (∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) * realPhase S b v * realPhase S b (r * v)) := by
  rw [critical_log_product S b hr, integral_indicator measurableSet_Iic, integral_const_mul,
    critical_exp_change_variables (fun v => realPhase S b v * realPhase S b (r * v))]
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have he : Real.exp (-(Real.log r) / 2) = (Real.sqrt r)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hrp, ← Real.exp_neg]
    congr 1
    ring
  rw [he]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  ring

/-- The actual critical source has an absolutely convergent von Mangoldt prime channel. -/
theorem summable_criticalFactorialSource_prime (S : Finset ℕ) (b : ℕ → ℝ) :
    Summable (fun r : ℕ => |(if 2 ≤ r then
      (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ) else 0) *
      ∫ x : ℝ, criticalFactorialSource S b x * criticalFactorialSource S b (x - Real.log (r : ℝ))|) := by
  have hK : 0 ≤ criticalFactorialPrimeConstant S b := by unfold criticalFactorialPrimeConstant; positivity
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _
    (summable_canonicalPrimeMajorant.mul_left (criticalFactorialPrimeConstant S b))
  intro r
  by_cases hr : 2 ≤ r
  · have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    have hrs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hrp
    have hcorr := critical_factorial_physical_correlation_bound S b (r - 1)
    rw [Nat.sub_add_cancel (show 1 ≤ r by omega)] at hcorr
    simp only [← realPhase_eq_re] at hcorr
    rw [if_pos hr, critical_source_correlation_eq S b hr1, abs_mul,
      abs_mul, abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hrs.le),
      abs_of_pos (inv_pos.mpr hrs)]
    have h := mul_le_mul_of_nonneg_left hcorr (show 0 ≤
      ((ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ)) * (Real.sqrt (r : ℝ))⁻¹ by positivity)
    have hs := Real.sq_sqrt hrp.le
    have he : ((ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ)) *
        (Real.sqrt (r : ℝ))⁻¹ * (criticalFactorialPrimeConstant S b / (r : ℝ)) =
        criticalFactorialPrimeConstant S b * envelopePrimeMajorant (3 / 2) r := by
      unfold envelopePrimeMajorant
      rw [if_pos hr]
      norm_num only [show (3 / 2 : ℝ) + 1 / 2 = 2 by norm_num, Real.rpow_two]
      field_simp
      rw [hs]
      ring
    calc
      _ ≤ ((ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ)) *
          (Real.sqrt (r : ℝ))⁻¹ * (criticalFactorialPrimeConstant S b / (r : ℝ)) := by
        simpa only [mul_assoc] using h
      _ = _ := he
  · simp [hr, envelopePrimeMajorant]

/-- The autocorrelations in the prime series are genuine Lebesgue integrals. -/
theorem integrable_criticalFactorialSource_product (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) :
    Integrable (fun x => criticalFactorialSource S b x *
      criticalFactorialSource S b (x - Real.log ((k + 1 : ℕ) : ℝ))) :=
  critical_source_product_integrable S b (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))


end
end GaloisForLFunctions.ArithmeticPositivityTheory
