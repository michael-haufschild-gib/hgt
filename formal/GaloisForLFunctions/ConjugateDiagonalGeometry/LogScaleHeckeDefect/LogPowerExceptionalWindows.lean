import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.HalfGateClosureAndDensityEquivalence
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.PSeries

/-!
# Logarithmic-power exceptions for unit-window corridors

For `b>1` and `0<η<b−1`, the corridor of width `b log log T / log T` fails
on a set of measure `O(U/(log U)^η)` in `[U,2U]`. For `b>2`, rescaling these
bounds makes the exceptions summable along geometric shells, giving eventual
control on almost every ray.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory Topology
open scoped BigOperators Real

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

/-- Starting heights in `[U,2U]` of unit windows containing a zero outside the strict corridor. -/
def badLogLogWindows (b U : ℝ) : Set ℝ :=
  {T ∈ Icc U (2 * U) | ∃ ρ ∈ xiUnitWindowZeros T,
    b * Real.log (Real.log T) / Real.log T ≤ |ρ.re - 1 / 2|}

/-- One offending zero pays an exponential depth charge. -/
private theorem logPower_le_depthCharge_add_two {b c η U T : ℝ}
    (hb : 0 < b) (hη : 0 < η) (hcb : 2 * c * b = 1 + η)
    (hlogU : 1 ≤ Real.log U) (hU : 0 < U) (hTU : U ≤ T)
    (hbad : ∃ ρ ∈ xiUnitWindowZeros T,
      b * Real.log (Real.log T) / Real.log T ≤ |ρ.re - 1 / 2|) :
    (Real.log U) ^ (1 + η) ≤ unitWindowDepthCharge T (c * Real.log T) + 2 := by
  obtain ⟨ρ, hρ, hd⟩ := hbad
  have hlogUT : Real.log U ≤ Real.log T := Real.log_le_log hU hTU
  have hlogT : 0 < Real.log T := lt_of_lt_of_le (by linarith only [hlogU]) hlogUT
  have hll : 0 ≤ Real.log (Real.log T) := Real.log_nonneg (hlogU.trans hlogUT)
  have hwidth : 0 ≤ b * Real.log (Real.log T) / Real.log T := by positivity
  have hmono := depthKernel_mono_depth (c * Real.log T)
    (d := b * Real.log (Real.log T) / Real.log T) (e := ρ.re - 1 / 2)
    (by simpa only [abs_of_nonneg hwidth] using hd)
  have harg : 2 * (b * Real.log (Real.log T) / Real.log T) * (c * Real.log T) =
      (1 + η) * Real.log (Real.log T) := by
    calc _ = (2 * c * b) * Real.log (Real.log T) := by field_simp [hlogT.ne']
         _ = _ := by rw [hcb]
  have hkernel : Real.exp ((1 + η) * Real.log (Real.log T)) ≤
      depthKernel (c * Real.log T) (ρ.re - 1 / 2) + 2 := by
    dsimp only [depthKernel]
    unfold depthKernel at hmono
    rw [harg, Real.cosh_eq] at hmono
    have hpos := Real.exp_pos (-((1 + η) * Real.log (Real.log T)))
    linarith only [hmono, hpos]
  calc (Real.log U) ^ (1 + η)
      ≤ (Real.log T) ^ (1 + η) :=
        Real.rpow_le_rpow (by linarith only [hlogU]) hlogUT (by linarith only [hη])
    _ = Real.exp ((1 + η) * Real.log (Real.log T)) := by
      rw [Real.rpow_def_of_pos hlogT, mul_comm]
    _ ≤ depthKernel (c * Real.log T) (ρ.re - 1 / 2) + 2 := hkernel
    _ ≤ unitWindowDepthCharge T (c * Real.log T) + 2 := by
      linarith only [depthKernel_le_unitWindowDepthCharge (L := c * Real.log T) hρ]

/-- The corridor coefficient `b>1` gives every logarithmic exceptional-set exponent below `b−1`. -/
theorem eventually_volume_badLogLogWindows_le_logPower {b η : ℝ}
    (hb : 1 < b) (hη : 0 < η) (hηb : η < b - 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      volume (badLogLogWindows b U) ≤ ENNReal.ofReal (C * U / (Real.log U) ^ η) := by
  let c : ℝ := (1 + η) / (2 * b)
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hc : c < 1 / 2 := by
    dsimp [c]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * b)).2
    linarith only [hηb]
  have hcb : 2 * c * b = 1 + η := by dsimp [c]; field_simp [hb0.ne']
  obtain ⟨_, _, hmean⟩ := exists_dyadicMean_corridor_and_polynomialTheta_le_log_up_to_half
  obtain ⟨K, hK, _, hmean⟩ := hmean c hc0 hc
  refine ⟨2 * K, by positivity, ?_⟩
  have hpow : Tendsto (fun U : ℝ => (Real.log U) ^ (1 + η)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith only [hη])).comp Real.tendsto_log_atTop
  filter_upwards [hmean, hpow.eventually_ge_atTop 4,
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_gt_atTop (0 : ℝ)]
    with U hmean hfour hlogU hU
  have hlog : 0 < Real.log U := by linarith only [hlogU]
  have hp : 0 < (Real.log U) ^ η := Real.rpow_pos_of_pos hlog _
  have hpadd : (Real.log U) ^ (1 + η) = Real.log U * (Real.log U) ^ η := by
    rw [Real.rpow_add hlog, Real.rpow_one]
  let μ := volume.restrict (Icc U (2 * U))
  let E : Set ℝ := {T | (Real.log U) ^ (1 + η) / 2 ≤
    unitWindowDepthCharge T (c * Real.log T)}
  have hsub : volume (badLogLogWindows b U) ≤ μ E := by
    rw [Measure.restrict_apply' measurableSet_Icc]
    apply measure_mono
    rintro T ⟨hT, hbad⟩
    refine ⟨?_, hT⟩
    have hh := logPower_le_depthCharge_add_two hb0 hη hcb hlogU hU hT.1 hbad
    change (Real.log U) ^ (1 + η) / 2 ≤ _
    linarith only [hh, hfour]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (Filter.Eventually.of_forall fun T => unitWindowDepthCharge_nonneg T (c * Real.log T))
    (integrableOn_unitWindowDepthCharge_log_Icc hU c) ((Real.log U) ^ (1 + η) / 2)
  have hmean' : (∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T)) ≤
      K * Real.log U * U := by
    apply (div_le_iff₀ hU).mp
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using hmean.1
  have hmarkov' : (Real.log U * (Real.log U) ^ η / 2) * μ.real E ≤
      ∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T) := by
    calc _ = (Real.log U) ^ (1 + η) / 2 * μ.real E := by rw [hpadd]
         _ ≤ _ := hmarkov
  have hreal : μ.real E ≤ 2 * K * U / (Real.log U) ^ η := by
    apply (le_div_iff₀ hp).2
    have hm : Real.log U * ((Real.log U) ^ η / 2 * μ.real E) ≤
        Real.log U * (K * U) := by
      nlinarith only [hmarkov', hmean']
    have hm' := (mul_le_mul_iff_right₀ hlog).mp hm
    linarith only [hm']
  calc volume (badLogLogWindows b U) ≤ μ E := hsub
    _ = ENNReal.ofReal (μ.real E) := (ENNReal.ofReal_toReal (measure_ne_top μ E)).symm
    _ ≤ ENNReal.ofReal (2 * K * U / (Real.log U) ^ η) := ENNReal.ofReal_le_ofReal hreal

/-- On almost every geometric ray, every sufficiently late unit window lies strictly
inside the double-log corridor. The coefficient `b>2` makes the exceptions summable. -/
theorem ae_eventually_geometric_unitWindow_corridor {b : ℝ} (hb : 2 < b) :
    ∀ᵐ x : ℝ, x ∈ Icc (1 : ℝ) 2 → ∀ᶠ n : ℕ in atTop,
      ∀ ρ ∈ xiUnitWindowZeros (Real.exp n * x),
        |ρ.re - 1 / 2| <
          b * Real.log (Real.log (Real.exp n * x)) / Real.log (Real.exp n * x) := by
  let η : ℝ := b / 2
  have hη : 1 < η := by dsimp [η]; linarith only [hb]
  obtain ⟨C, hC, hbound⟩ := eventually_volume_badLogLogWindows_le_logPower
    (b := b) (η := η) (by linarith only [hb]) (by linarith only [hη])
    (by dsimp [η]; linarith only [hb])
  let E : ℕ → Set ℝ := fun n =>
    (fun x : ℝ => Real.exp n * x) ⁻¹' badLogLogWindows b (Real.exp n)
  have hEsub (n : ℕ) : E n ⊆ Icc (1 : ℝ) 2 := by
    intro x hx
    have hx' := hx.1
    constructor
    · apply (mul_le_mul_iff_right₀ (Real.exp_pos (n : ℝ))).mp
      simpa only [mul_one] using hx'.1
    · apply (mul_le_mul_iff_right₀ (Real.exp_pos (n : ℝ))).mp
      simpa only [mul_comm] using hx'.2
  have hfinite (n : ℕ) : volume (E n) ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_mono (hEsub n)).trans_lt (by simp)
  have hexp : Tendsto (fun n : ℕ => Real.exp (n : ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  have hEbound : ∀ᶠ n : ℕ in atTop,
      volume (E n) ≤ ENNReal.ofReal (C / (n : ℝ) ^ η) := by
    filter_upwards [hexp.eventually hbound] with n hn
    dsimp only [E]
    rw [Real.volume_preimage_mul_left (Real.exp_pos (n : ℝ)).ne',
      abs_of_pos (inv_pos.mpr (Real.exp_pos (n : ℝ)))]
    calc ENNReal.ofReal ((Real.exp (n : ℝ))⁻¹) * volume (badLogLogWindows b (Real.exp n))
        ≤ ENNReal.ofReal ((Real.exp (n : ℝ))⁻¹) *
            ENNReal.ofReal (C * Real.exp n / (Real.log (Real.exp n)) ^ η) :=
          _root_.mul_le_mul_left' hn _
      _ = ENNReal.ofReal (C / (n : ℝ) ^ η) := by
        rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr (Real.exp_pos (n : ℝ)))), Real.log_exp]
        congr 1
        calc _ = ((Real.exp (n : ℝ))⁻¹ * Real.exp n) * C / (n : ℝ) ^ η := by ring
             _ = _ := by rw [inv_mul_cancel₀ (Real.exp_pos (n : ℝ)).ne', one_mul]
  have hseries : Summable (fun n : ℕ => C / (n : ℝ) ^ η) := by
    simpa only [div_eq_mul_inv] using (Real.summable_nat_rpow_inv.mpr hη).mul_left C
  have hrealSeries : Summable (fun n : ℕ => (volume (E n)).toReal) := by
    apply hseries.of_norm_bounded_eventually_nat
    filter_upwards [hEbound] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hn).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hsum : (∑' n : ℕ, volume (E n)) ≠ ⊤ := by
    have hh := hrealSeries.tsum_ofReal_ne_top
    have heq : (fun n : ℕ => ENNReal.ofReal ((volume (E n)).toReal)) =
        (fun n => volume (E n)) :=
      funext fun n => ENNReal.ofReal_toReal (hfinite n)
    rw [heq] at hh
    exact hh
  filter_upwards [ae_eventually_notMem hsum] with x hx
  intro hxI
  filter_upwards [hx] with n hn
  intro ρ hρ
  apply lt_of_not_ge
  intro hbad
  apply hn
  refine ⟨⟨?_, ?_⟩, ρ, hρ, hbad⟩
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hxI.1 (Real.exp_pos (n : ℝ)).le
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hxI.2 (Real.exp_pos (n : ℝ)).le

#print axioms eventually_volume_badLogLogWindows_le_logPower
#print axioms ae_eventually_geometric_unitWindow_corridor

end GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect
