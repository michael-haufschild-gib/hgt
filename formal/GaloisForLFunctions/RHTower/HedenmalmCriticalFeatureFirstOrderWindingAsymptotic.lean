import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureFirstOrderWindingReduction
import GaloisForLFunctions.RHTower.GammaVerticalPhaseAsymptotic
import GaloisForLFunctions.RHTower.GammaJumpMultiplierBounds
import GaloisForLFunctions.HTGeometry.PolynomialPowerDegreeSeparation

open Complex Filter Topology Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

def criticalFeatureFirstOrderPoleGammaPositiveWinding (T : ℝ) : ℝ :=
  2 * ∫ t : ℝ in (0 : ℝ)..T,
    (logDeriv archFactor (criticalFeatureEulerVMArchPoint t)).re

def criticalFeatureFirstOrderPoleGammaWindingError (t : ℝ) : ℝ :=
  2 * (logDeriv archFactor (criticalFeatureEulerVMArchPoint t)).re -
    (Complex.digamma ((3 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re

theorem criticalFeatureFirstOrderPoleGammaWindingError_eq (t : ℝ) :
    criticalFeatureFirstOrderPoleGammaWindingError t =
      2 * (1 / criticalFeatureEulerVMArchPoint t).re +
      2 * (1 / (criticalFeatureEulerVMArchPoint t - 1)).re - Real.log Real.pi := by
  have hs : 0 < (criticalFeatureEulerVMArchPoint t).re := by simp
  have hs0 : criticalFeatureEulerVMArchPoint t ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
  have hs1 : criticalFeatureEulerVMArchPoint t ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    norm_num at h'
  rw [criticalFeatureFirstOrderPoleGammaWindingError,
    logDeriv_archFactor_closed hs hs0 hs1]
  have hconn :
      (GaloisForLFunctions.gammaRealLogConnection
        (criticalFeatureEulerVMArchPoint t)).re =
      -Real.log Real.pi / 2 +
        (Complex.digamma (criticalFeatureEulerVMArchPoint t / 2)).re / 2 := by
    rw [GaloisForLFunctions.gammaRealLogConnection]
    norm_num [Complex.normSq_apply]
    ring
  rw [add_re, add_re, hconn]
  have hsHalf : criticalFeatureEulerVMArchPoint t / 2 =
      (3 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    simp [criticalFeatureEulerVMArchPoint]
    ring
  rw [hsHalf]
  ring

theorem abs_criticalFeatureFirstOrderPoleGammaWindingError_le (t : ℝ) :
    |criticalFeatureFirstOrderPoleGammaWindingError t| ≤
      16 / 3 + |Real.log Real.pi| := by
  rw [criticalFeatureFirstOrderPoleGammaWindingError_eq]
  have hsNorm : (3 / 2 : ℝ) ≤ ‖criticalFeatureEulerVMArchPoint t‖ := by
    calc
      (3 / 2 : ℝ) = |(criticalFeatureEulerVMArchPoint t).re| := by
        rw [criticalFeatureEulerVMArchPoint_re]
        norm_num
      _ ≤ _ := Complex.abs_re_le_norm _
  have hsSubNorm : (1 / 2 : ℝ) ≤ ‖criticalFeatureEulerVMArchPoint t - 1‖ := by
    calc
      (1 / 2 : ℝ) = |(criticalFeatureEulerVMArchPoint t - 1).re| := by
        norm_num [abs_of_nonneg]
      _ ≤ _ := Complex.abs_re_le_norm _
  have hs0 : criticalFeatureEulerVMArchPoint t ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
  have hs1 : criticalFeatureEulerVMArchPoint t - 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    norm_num at h'
  have hfirst : |(1 / criticalFeatureEulerVMArchPoint t).re| ≤ 2 / 3 := by
    calc
      |(1 / criticalFeatureEulerVMArchPoint t).re| ≤
          ‖1 / criticalFeatureEulerVMArchPoint t‖ := Complex.abs_re_le_norm _
      _ = 1 / ‖criticalFeatureEulerVMArchPoint t‖ := by
        rw [norm_div, norm_one]
      _ ≤ 2 / 3 := by
        rw [div_le_iff₀ (norm_pos_iff.mpr hs0)]
        nlinarith
  have hsecond : |(1 / (criticalFeatureEulerVMArchPoint t - 1)).re| ≤ 2 := by
    calc
      |(1 / (criticalFeatureEulerVMArchPoint t - 1)).re| ≤
          ‖1 / (criticalFeatureEulerVMArchPoint t - 1)‖ := Complex.abs_re_le_norm _
      _ = 1 / ‖criticalFeatureEulerVMArchPoint t - 1‖ := by
        rw [norm_div, norm_one]
      _ ≤ 2 := by
        rw [div_le_iff₀ (norm_pos_iff.mpr hs1)]
        nlinarith
  calc
    |2 * (1 / criticalFeatureEulerVMArchPoint t).re +
        2 * (1 / (criticalFeatureEulerVMArchPoint t - 1)).re - Real.log Real.pi| ≤
      2 * |(1 / criticalFeatureEulerVMArchPoint t).re| +
        2 * |(1 / (criticalFeatureEulerVMArchPoint t - 1)).re| +
          |Real.log Real.pi| := by
      calc
        |_ - Real.log Real.pi| ≤
            |2 * (1 / criticalFeatureEulerVMArchPoint t).re +
              2 * (1 / (criticalFeatureEulerVMArchPoint t - 1)).re| +
                |Real.log Real.pi| := abs_sub _ _
        _ ≤ (|2 * (1 / criticalFeatureEulerVMArchPoint t).re| +
              |2 * (1 / (criticalFeatureEulerVMArchPoint t - 1)).re|) +
                |Real.log Real.pi| := by
                  have h := abs_add_le
                    (2 * (1 / criticalFeatureEulerVMArchPoint t).re)
                    (2 * (1 / (criticalFeatureEulerVMArchPoint t - 1)).re)
                  linarith
        _ = _ := by rw [abs_mul, abs_mul]; norm_num
    _ ≤ 16 / 3 + |Real.log Real.pi| := by nlinarith

theorem criticalFeatureFirstOrderPoleGammaPositiveWinding_sub_gammaPhase (T : ℝ) :
    criticalFeatureFirstOrderPoleGammaPositiveWinding T -
      2 * gammaVerticalPhase (3 / 4) (T / 2) =
      ∫ t : ℝ in (0 : ℝ)..T,
        criticalFeatureFirstOrderPoleGammaWindingError t := by
  have hscale := intervalIntegral.integral_comp_div
    (fun u : ℝ =>
      (Complex.digamma ((3 / 4 : ℂ) + (u : ℂ) * I)).re)
    (by norm_num : (2 : ℝ) ≠ 0) (a := (0 : ℝ)) (b := T)
  unfold criticalFeatureFirstOrderPoleGammaPositiveWinding
  unfold criticalFeatureFirstOrderPoleGammaWindingError
  unfold gammaVerticalPhase
  have hlogInt : IntervalIntegrable
      (fun t : ℝ =>
        (logDeriv archFactor (criticalFeatureEulerVMArchPoint t)).re)
      volume 0 T :=
    continuous_re_logDeriv_archFactor_eulerVMArchPoint.intervalIntegrable 0 T
  have hdigCont : Continuous (fun t : ℝ =>
      (Complex.digamma ((3 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re) := by
    have h := continuous_digammaVerticalRe (by norm_num : (0 : ℝ) < 3 / 4)
    simpa [Function.comp_def, Complex.ofReal_div] using
      h.comp (continuous_id.div_const 2)
  have hdigInt : IntervalIntegrable (fun t : ℝ =>
      (Complex.digamma ((3 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re)
      volume 0 T := hdigCont.intervalIntegrable 0 T
  rw [intervalIntegral.integral_sub (hlogInt.const_mul 2)
    hdigInt]
  rw [intervalIntegral.integral_const_mul]
  have hscale' :
      (∫ t : ℝ in (0 : ℝ)..T,
        (Complex.digamma ((3 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re) =
        2 * gammaVerticalPhase (3 / 4) (T / 2) := by
    simpa [gammaVerticalPhase, smul_eq_mul] using hscale
  rw [hscale']
  congr 2

theorem continuous_criticalFeatureFirstOrderPoleGammaWindingError :
    Continuous criticalFeatureFirstOrderPoleGammaWindingError := by
  unfold criticalFeatureFirstOrderPoleGammaWindingError
  have hdig := continuous_digammaVerticalRe (by norm_num : (0 : ℝ) < 3 / 4)
  have hdig' : Continuous (fun t : ℝ =>
      (Complex.digamma ((3 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re) := by
    simpa [Function.comp_def, Complex.ofReal_div] using
      hdig.comp (continuous_id.div_const 2)
  exact continuous_re_logDeriv_archFactor_eulerVMArchPoint.const_mul 2 |>.sub hdig'

theorem abs_integral_criticalFeatureFirstOrderPoleGammaWindingError_le
    {T : ℝ} (hT : 0 ≤ T) :
    |∫ t : ℝ in (0 : ℝ)..T,
        criticalFeatureFirstOrderPoleGammaWindingError t| ≤
      (16 / 3 + |Real.log Real.pi|) * T := by
  have hconstInt : IntervalIntegrable
      (fun _t : ℝ => 16 / 3 + |Real.log Real.pi|) volume 0 T :=
    intervalIntegrable_const
  have h := intervalIntegral.norm_integral_le_of_norm_le hT
    (f := criticalFeatureFirstOrderPoleGammaWindingError)
    (g := fun _t : ℝ => 16 / 3 + |Real.log Real.pi|)
    (Filter.Eventually.of_forall fun t _ht => by
      rw [Real.norm_eq_abs]
      exact abs_criticalFeatureFirstOrderPoleGammaWindingError_le t)
    hconstInt
  simp only [Real.norm_eq_abs, intervalIntegral.integral_const, smul_eq_mul] at h
  calc
    |∫ t : ℝ in (0 : ℝ)..T,
        criticalFeatureFirstOrderPoleGammaWindingError t| ≤
        (T - 0) * (16 / 3 + |Real.log Real.pi|) := h
    _ = (16 / 3 + |Real.log Real.pi|) * T := by ring

theorem tendsto_criticalFeatureFirstOrderPoleGammaPositiveWinding_error_ratio :
    Tendsto (fun T : ℝ =>
      (criticalFeatureFirstOrderPoleGammaPositiveWinding T -
        2 * gammaVerticalPhase (3 / 4) (T / 2)) /
          (T * Real.log T)) atTop (𝓝 0) := by
  let C : ℝ := 16 / 3 + |Real.log Real.pi|
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hmajor : Tendsto (fun T : ℝ => C / Real.log T) atTop (𝓝 0) :=
    hlog.const_div_atTop C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun T => norm_nonneg _) ?_ hmajor
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 < Real.log T := Real.log_pos hT
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hT0 hlog0)]
  rw [criticalFeatureFirstOrderPoleGammaPositiveWinding_sub_gammaPhase]
  have herr := abs_integral_criticalFeatureFirstOrderPoleGammaWindingError_le hT0.le
  change |∫ t : ℝ in (0 : ℝ)..T,
      criticalFeatureFirstOrderPoleGammaWindingError t| / (T * Real.log T) ≤
        C / Real.log T
  rw [div_le_div_iff₀ (mul_pos hT0 hlog0) hlog0]
  dsimp only [C] at herr ⊢
  nlinarith

theorem tendsto_two_mul_gammaVerticalPhase_threeQuarter_half_ratio :
    Tendsto (fun T : ℝ =>
      2 * gammaVerticalPhase (3 / 4) (T / 2) / (T * Real.log T))
      atTop (𝓝 1) := by
  have hhalf : Tendsto (fun T : ℝ => T / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hphase : Tendsto (fun T : ℝ =>
      gammaVerticalPhase (3 / 4) (T / 2) /
        ((T / 2) * Real.log (T / 2))) atTop (𝓝 1) := by
    simpa [Function.comp_def] using
      (tendsto_gammaVerticalPhase_ratio (by norm_num : (0 : ℝ) < 3 / 4)).comp hhalf
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hsmall : Tendsto (fun T : ℝ => Real.log 2 / Real.log T) atTop (𝓝 0) :=
    hlog.const_div_atTop (Real.log 2)
  have hlogRatio : Tendsto (fun T : ℝ =>
      Real.log (T / 2) / Real.log T) atTop (𝓝 1) := by
    have hlim : Tendsto (fun T : ℝ => 1 - Real.log 2 / Real.log T)
        atTop (𝓝 1) := by simpa using tendsto_const_nhds.sub hsmall
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (1 : ℝ)] with T hT hT1
    rw [Real.log_div (ne_of_gt hT) (by norm_num : (2 : ℝ) ≠ 0)]
    have hlogNe : Real.log T ≠ 0 := (Real.log_pos hT1).ne'
    field_simp
  have hprod := hphase.mul hlogRatio
  simp only [one_mul] at hprod
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with T hT
  have hT0 : T ≠ 0 := ne_of_gt (by linarith)
  have hhalf0 : T / 2 ≠ 0 := div_ne_zero hT0 (by norm_num)
  have hlogT : Real.log T ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hlogHalf : Real.log (T / 2) ≠ 0 :=
    (Real.log_pos (by linarith)).ne'
  field_simp

theorem tendsto_criticalFeatureFirstOrderPoleGammaPositiveWinding_ratio :
    Tendsto (fun T : ℝ =>
      criticalFeatureFirstOrderPoleGammaPositiveWinding T /
        (T * Real.log T)) atTop (𝓝 1) := by
  have hsum :=
    tendsto_criticalFeatureFirstOrderPoleGammaPositiveWinding_error_ratio.add
      tendsto_two_mul_gammaVerticalPhase_threeQuarter_half_ratio
  simpa only [zero_add] using hsum.congr' (by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hden : T * Real.log T ≠ 0 :=
      mul_ne_zero (ne_of_gt (by linarith)) (Real.log_pos hT).ne'
    field_simp
    ring)

theorem criticalFeatureFirstOrderPoleGammaWindingError_neg (t : ℝ) :
    criticalFeatureFirstOrderPoleGammaWindingError (-t) =
      criticalFeatureFirstOrderPoleGammaWindingError t := by
  rw [criticalFeatureFirstOrderPoleGammaWindingError_eq,
    criticalFeatureFirstOrderPoleGammaWindingError_eq]
  simp [criticalFeatureEulerVMArchPoint, Complex.normSq_apply]

theorem even_re_logDeriv_archFactor_criticalFeatureEulerVMArchPoint :
    Function.Even (fun t : ℝ =>
      (logDeriv archFactor (criticalFeatureEulerVMArchPoint t)).re) := by
  intro t
  have herr := criticalFeatureFirstOrderPoleGammaWindingError_neg t
  have hdig := GaloisForLFunctions.RHTower.re_digamma_vertical_even
    (by norm_num : (0 : ℝ) < 3 / 4) (t / 2)
  have hdig' :
      (Complex.digamma ((3 / 4 : ℂ) + ((-(t / 2) : ℝ) : ℂ) * I)).re =
        (Complex.digamma ((3 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)).re := by
    convert hdig using 1 <;> norm_num
  unfold criticalFeatureFirstOrderPoleGammaWindingError at herr
  rw [show (-t) / 2 = -(t / 2) by ring] at herr
  rw [hdig'] at herr
  linarith

theorem criticalFeatureCanonicalFirstOrderPoleGammaWinding_eq_interval (n : ℕ) :
    criticalFeatureCanonicalFirstOrderPoleGammaWinding n =
      2 * ∫ t : ℝ in (-((n : ℝ) + 2))..((n : ℝ) + 1),
        (logDeriv archFactor (criticalFeatureEulerVMArchPoint t)).re := by
  let L : ℝ → ℝ := fun t =>
    (logDeriv archFactor (criticalFeatureEulerVMArchPoint t)).re
  have hL : Continuous L := continuous_re_logDeriv_archFactor_eulerVMArchPoint
  let D : ℤ → ℝ := fun k => ∫ t : ℝ in (0 : ℝ)..(k : ℝ), L t
  have hcell (k : ℤ) :
      (∫ t : ℝ in ((k : ℝ) - 1)..(k : ℝ), L t) = D k - D (k - 1) := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hL.intervalIntegrable (μ := volume) (0 : ℝ) ((k : ℝ) - 1))
      (hL.intervalIntegrable (μ := volume) ((k : ℝ) - 1) (k : ℝ))
    dsimp only [D]
    push_cast
    linarith
  rw [criticalFeatureCanonicalFirstOrderPoleGammaWinding]
  have hsum :
      (∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
        ∫ t : ℝ in ((k : ℝ) - 1)..(k : ℝ), L t) =
      D ((n : ℤ) + 1) - D (-((n : ℤ) + 2)) := by
    rw [Finset.sum_congr rfl fun k _hk => hcell k]
    exact sum_criticalFeatureCanonicalLatticeWindow_increment D n
  rw [hsum]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hL.intervalIntegrable (μ := volume) (-((n : ℝ) + 2)) 0)
    (hL.intervalIntegrable (μ := volume) 0 ((n : ℝ) + 1))
  have hsymm := intervalIntegral.integral_symm
    (μ := volume) (f := L) (a := (-((n : ℝ) + 2))) (b := 0)
  dsimp only [D, L]
  push_cast
  congr 1
  calc
    (∫ t : ℝ in (0 : ℝ)..((n : ℝ) + 1),
        (logDeriv archFactor (criticalFeatureEulerVMArchPoint t)).re) -
        ∫ t : ℝ in (0 : ℝ)..(-((n : ℝ) + 2)),
          (logDeriv archFactor (criticalFeatureEulerVMArchPoint t)).re =
      -(∫ t : ℝ in (0 : ℝ)..(-((n : ℝ) + 2)),
        (logDeriv archFactor (criticalFeatureEulerVMArchPoint t)).re) +
        ∫ t : ℝ in (0 : ℝ)..((n : ℝ) + 1),
          (logDeriv archFactor (criticalFeatureEulerVMArchPoint t)).re := by ring
    _ =
      (∫ t : ℝ in (-((n : ℝ) + 2))..0,
        (logDeriv archFactor (criticalFeatureEulerVMArchPoint t)).re) +
        ∫ t : ℝ in (0 : ℝ)..((n : ℝ) + 1),
          (logDeriv archFactor (criticalFeatureEulerVMArchPoint t)).re := by
            rw [hsymm]
            ring
    _ = _ := hadd

theorem criticalFeatureCanonicalFirstOrderPoleGammaWinding_eq_positive (n : ℕ) :
    criticalFeatureCanonicalFirstOrderPoleGammaWinding n =
      criticalFeatureFirstOrderPoleGammaPositiveWinding ((n : ℝ) + 2) +
        criticalFeatureFirstOrderPoleGammaPositiveWinding ((n : ℝ) + 1) := by
  rw [criticalFeatureCanonicalFirstOrderPoleGammaWinding_eq_interval]
  let L : ℝ → ℝ := fun t =>
    (logDeriv archFactor (criticalFeatureEulerVMArchPoint t)).re
  have hL : Continuous L := continuous_re_logDeriv_archFactor_eulerVMArchPoint
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hL.intervalIntegrable (μ := volume) (-((n : ℝ) + 2)) 0)
    (hL.intervalIntegrable (μ := volume) 0 ((n : ℝ) + 1))
  have hneg := intervalIntegral.integral_comp_neg
    (a := (0 : ℝ)) (b := ((n : ℝ) + 2)) L
  rw [show (fun t : ℝ => L (-t)) = L from
    funext even_re_logDeriv_archFactor_criticalFeatureEulerVMArchPoint] at hneg
  simp only [neg_zero] at hneg
  rw [← hsplit, ← hneg]
  unfold criticalFeatureFirstOrderPoleGammaPositiveWinding
  dsimp only [L]
  ring

theorem tendsto_log_natCast_add_div_log_natCast (c : ℕ) :
    Tendsto (fun n : ℕ =>
      Real.log ((n + c : ℕ) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 1) := by
  have hbase := GaloisForLFunctions.tendsto_natCast_add_div_natCast c
  have hlogBase : Tendsto (fun n : ℕ =>
      Real.log ((((n + c : ℕ) : ℝ) / (n : ℝ)))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hbase
  have hlogTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hquot : Tendsto (fun n : ℕ =>
      Real.log ((((n + c : ℕ) : ℝ) / (n : ℝ))) /
        Real.log (n : ℝ)) atTop (𝓝 0) := hlogBase.div_atTop hlogTop
  have hlim : Tendsto (fun n : ℕ =>
      1 + Real.log ((((n + c : ℕ) : ℝ) / (n : ℝ))) /
        Real.log (n : ℝ)) atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hquot
  have heq : ∀ᶠ n : ℕ in atTop,
      1 + Real.log ((((n + c : ℕ) : ℝ) / (n : ℝ))) / Real.log (n : ℝ) =
        Real.log ((n + c : ℕ) : ℝ) / Real.log (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hnc0 : ((n + c : ℕ) : ℝ) ≠ 0 := by positivity
    have hlog0 : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hn)).ne'
    rw [Real.log_div hnc0 hn0]
    field_simp
    ring
  have hres : Tendsto (fun n : ℕ =>
      Real.log ((n + c : ℕ) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (1 + 0)) := hlim.congr' heq
  norm_num at hres ⊢
  exact hres

theorem tendsto_natCast_add_mul_log_div_natCast_mul_log (c : ℕ) :
    Tendsto (fun n : ℕ =>
      (((n + c : ℕ) : ℝ) * Real.log ((n + c : ℕ) : ℝ)) /
        ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 1) := by
  have hprod := (GaloisForLFunctions.tendsto_natCast_add_div_natCast c).mul
    (tendsto_log_natCast_add_div_log_natCast c)
  simpa only [one_mul] using hprod.congr' (by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hlog0 : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hn)).ne'
    field_simp)

theorem tendsto_criticalFeatureFirstOrderPoleGammaPositiveWinding_nat_add_ratio
    (c : ℕ) :
    Tendsto (fun n : ℕ =>
      criticalFeatureFirstOrderPoleGammaPositiveWinding ((n + c : ℕ) : ℝ) /
        ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 1) := by
  have hshiftTop : Tendsto (fun n : ℕ => ((n : ℝ) + (c : ℝ))) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (c : ℝ)
      tendsto_natCast_atTop_atTop
  have hmain : Tendsto (fun n : ℕ =>
      criticalFeatureFirstOrderPoleGammaPositiveWinding ((n + c : ℕ) : ℝ) /
        (((n + c : ℕ) : ℝ) * Real.log ((n + c : ℕ) : ℝ)))
      atTop (𝓝 1) := by
    simpa [Function.comp_def] using
      tendsto_criticalFeatureFirstOrderPoleGammaPositiveWinding_ratio.comp hshiftTop
  have hprod := hmain.mul (tendsto_natCast_add_mul_log_div_natCast_mul_log c)
  simpa only [one_mul] using hprod.congr' (by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hlogn0 : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hn)).ne'
    have hnc0 : ((n + c : ℕ) : ℝ) ≠ 0 := by positivity
    have hlognc0 : Real.log ((n + c : ℕ) : ℝ) ≠ 0 :=
      (Real.log_pos (by
        exact_mod_cast (show 1 < n + c by omega))).ne'
    field_simp)

theorem tendsto_criticalFeatureCanonicalFirstOrderPoleGammaWinding_natLog_ratio :
    Tendsto (fun n : ℕ =>
      criticalFeatureCanonicalFirstOrderPoleGammaWinding n /
        ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 2) := by
  have htwo :=
    (tendsto_criticalFeatureFirstOrderPoleGammaPositiveWinding_nat_add_ratio 2).add
      (tendsto_criticalFeatureFirstOrderPoleGammaPositiveWinding_nat_add_ratio 1)
  have heq : ∀ᶠ n : ℕ in atTop,
      criticalFeatureCanonicalFirstOrderPoleGammaWinding n /
          ((n : ℝ) * Real.log (n : ℝ)) =
        criticalFeatureFirstOrderPoleGammaPositiveWinding ((n + 2 : ℕ) : ℝ) /
            ((n : ℝ) * Real.log (n : ℝ)) +
          criticalFeatureFirstOrderPoleGammaPositiveWinding ((n + 1 : ℕ) : ℝ) /
            ((n : ℝ) * Real.log (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    rw [criticalFeatureCanonicalFirstOrderPoleGammaWinding_eq_positive]
    push_cast
    ring
  have hres := htwo.congr' (heq.mono fun _ h => h.symm)
  norm_num at hres ⊢
  exact hres

theorem tendsto_criticalFeatureCanonicalZeroCount_natLog_ratio :
    Tendsto (fun n : ℕ =>
      criticalFeatureCanonicalZeroCount n /
        ((n : ℝ) * Real.log (n : ℝ))) atTop
      (𝓝 (1 / (2 * Real.pi))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T₀, _hT₀, hclose⟩ :=
    exists_xiZeroCount_close (ε / 2) (by linarith)
  refine ⟨max ⌈T₀⌉₊ 2, fun n hn => ?_⟩
  have hnT : ⌈T₀⌉₊ ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hT : T₀ ≤ (n : ℝ) :=
    (Nat.le_ceil T₀).trans (by exact_mod_cast hnT)
  have hcloseN := hclose (n : ℝ) hT
  have hnpos : (0 : ℝ) < n := by positivity
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn2)
  have hscale : 0 < (n : ℝ) * Real.log (n : ℝ) := mul_pos hnpos hlogpos
  rw [Real.dist_eq]
  have heq :
      criticalFeatureCanonicalZeroCount n / ((n : ℝ) * Real.log (n : ℝ)) -
          1 / (2 * Real.pi) =
        (criticalFeatureCanonicalZeroCount n -
            (1 / (2 * Real.pi)) * ((n : ℝ) * Real.log (n : ℝ))) /
          ((n : ℝ) * Real.log (n : ℝ)) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hscale]
  exact lt_of_le_of_lt (div_le_iff₀ hscale |>.2 hcloseN) (by linarith)

theorem tendsto_criticalFeatureCanonicalFirstOrderPoleGammaWinding_div_zeroCount :
    Tendsto (fun n : ℕ =>
      criticalFeatureCanonicalFirstOrderPoleGammaWinding n /
        criticalFeatureCanonicalZeroCount n) atTop (𝓝 (4 * Real.pi)) := by
  have hquot :=
    tendsto_criticalFeatureCanonicalFirstOrderPoleGammaWinding_natLog_ratio.div
      tendsto_criticalFeatureCanonicalZeroCount_natLog_ratio
      (by positivity : (1 / (2 * Real.pi) : ℝ) ≠ 0)
  have heq : ∀ᶠ n : ℕ in atTop,
      (criticalFeatureCanonicalFirstOrderPoleGammaWinding n /
          ((n : ℝ) * Real.log (n : ℝ))) /
          (criticalFeatureCanonicalZeroCount n /
            ((n : ℝ) * Real.log (n : ℝ))) =
        criticalFeatureCanonicalFirstOrderPoleGammaWinding n /
          criticalFeatureCanonicalZeroCount n := by
    filter_upwards [eventually_ge_atTop 2,
      eventually_criticalFeatureCanonicalZeroCount_pos] with n hn hN
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hlog0 : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hn)).ne'
    have hN0 : criticalFeatureCanonicalZeroCount n ≠ 0 := ne_of_gt hN
    field_simp
  have hres := hquot.congr' heq
  have hconst : (2 : ℝ) / (1 / (2 * Real.pi)) = 4 * Real.pi := by
    field_simp
    norm_num
  rw [hconst] at hres
  exact hres

/-- Conservation law at zero-count scale: source covariance plus compact source boundary carries
exactly the universal `4π` archimedean mass. -/
theorem tendsto_criticalFeaturePhaseCovariance_add_boundary_div_zeroCount :
    Tendsto (fun n : ℕ =>
      (criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n +
        criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n) /
          criticalFeatureCanonicalZeroCount n) atTop (𝓝 (4 * Real.pi)) := by
  have hsum :=
    tendsto_criticalFeaturePhaseCovariance_sub_firstOrderWindingBoundary_div.add
      tendsto_criticalFeatureCanonicalFirstOrderPoleGammaWinding_div_zeroCount
  have heq : ∀ᶠ n : ℕ in atTop,
      (criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n -
          (criticalFeatureCanonicalFirstOrderPoleGammaWinding n -
            criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n)) /
            criticalFeatureCanonicalZeroCount n +
        criticalFeatureCanonicalFirstOrderPoleGammaWinding n /
          criticalFeatureCanonicalZeroCount n =
      (criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n +
        criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n) /
          criticalFeatureCanonicalZeroCount n := by
    filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos] with n hN
    have hN0 : criticalFeatureCanonicalZeroCount n ≠ 0 := ne_of_gt hN
    field_simp
    ring
  have hres := hsum.congr' heq
  simpa only [zero_add] using hres

/-- `B(n) ≥ c N(n) - o(N(n))`, encoded without choosing a remainder sequence. -/
def CriticalFeatureCanonicalAsymptoticLower (B : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (c - ε) * criticalFeatureCanonicalZeroCount n ≤ B n

/-- Sharp reformulation of every covariance ceiling as a source-boundary floor. -/
theorem criticalFeaturePhaseCovariance_upper_iff_sourceBoundary_lower (c : ℝ) :
    CriticalFeatureCanonicalAsymptoticUpper
        criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage c ↔
      CriticalFeatureCanonicalAsymptoticLower
        criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage
          (4 * Real.pi - c) := by
  constructor
  · intro hupper ε hε
    have hcov := hupper (ε / 2) (by linarith)
    have hsum :=
      tendsto_criticalFeaturePhaseCovariance_add_boundary_div_zeroCount.eventually_const_lt
        (by linarith : 4 * Real.pi - ε / 2 < 4 * Real.pi)
    filter_upwards [hcov, hsum, eventually_criticalFeatureCanonicalZeroCount_pos] with
        n hcovN hsumN hN
    rw [lt_div_iff₀ hN] at hsumN
    nlinarith
  · intro hlower ε hε
    have hboundary := hlower (ε / 2) (by linarith)
    have hsum :=
      tendsto_criticalFeaturePhaseCovariance_add_boundary_div_zeroCount.eventually_lt_const
        (by linarith : 4 * Real.pi < 4 * Real.pi + ε / 2)
    filter_upwards [hboundary, hsum, eventually_criticalFeatureCanonicalZeroCount_pos] with
        n hboundaryN hsumN hN
    rw [div_lt_iff₀ hN] at hsumN
    nlinarith

theorem criticalFeaturePhaseCovariance_fourTwentyFifths_upper_iff_sourceBoundary_lower :
    CriticalFeatureCanonicalAsymptoticUpper
        criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage (4 / 25) ↔
      CriticalFeatureCanonicalAsymptoticLower
        criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage
          (4 * Real.pi - 4 / 25) :=
  criticalFeaturePhaseCovariance_upper_iff_sourceBoundary_lower (4 / 25)

theorem integral_criticalFeatureTranslatedLatticeBoundaryCutoffWeight_le_two_pi
    (thetaWindow : Finset ℤ) (cutoff : ℕ) (x : ℝ) :
    (∫ theta : ℝ in (0 : ℝ)..1,
      criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta thetaWindow cutoff x) ≤
        2 * Real.pi := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  simp_rw [criticalFeatureTranslatedLatticeBoundaryCutoffWeight_eq_finite_mul_cutoff]
  rw [MeasureTheory.integral_mul_const]
  have hbase :=
    integral_Ioc_criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight_le_two_pi
      thetaWindow x
  have hcut0 := SchwartzMap.realCompactIntervalCutoff_nonnegative (cutoff : ℝ) x
  have hcut1 := SchwartzMap.realCompactIntervalCutoff_le_one (cutoff : ℝ) x
  nlinarith [Real.pi_pos]

/-- The source-boundary phase average has no mass beyond the multiplicity of the real `XiC`
packet exposed by its Plemelj representation. -/
theorem exists_criticalFeatureSourceBoundaryPhaseAverage_le_realZeroMultiplicity (n : ℕ) :
    ∃ Gamma : Finset ℝ,
      (∀ gamma : ℝ, gamma ∈ Gamma ↔
        ((gamma : ℂ) ∈ Metric.ball (0 : ℂ) ((n : ℝ) + 4) ∧
          XiC (gamma : ℂ) = 0)) ∧
      criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n ≤
        2 * Real.pi *
          ∑ gamma ∈ Gamma, ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) := by
  obtain ⟨Gamma, hGamma, hformula⟩ :=
    exists_criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseFamily_eq_realZeroSums n
  refine ⟨Gamma, hGamma, ?_⟩
  rw [criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage]
  simp_rw [hformula]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun gamma hgamma => by
      rw [intervalIntegral.integral_const_mul]
      have hm : (0 : ℝ) ≤ ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) :=
        Nat.cast_nonneg _
      calc
        ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            (∫ theta : ℝ in (0 : ℝ)..1,
              criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta
                (criticalFeatureCanonicalLatticeWindow n) n gamma) ≤
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) * (2 * Real.pi) :=
            mul_le_mul_of_nonneg_left
              (integral_criticalFeatureTranslatedLatticeBoundaryCutoffWeight_le_two_pi
                (criticalFeatureCanonicalLatticeWindow n) n gamma) hm
        _ = 2 * Real.pi * ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) := by ring
  · intro gamma hgamma
    exact (continuous_const.mul
      (continuous_criticalFeatureTranslatedLatticeBoundaryCutoffWeight_phase
        (criticalFeatureCanonicalLatticeWindow n) n gamma)).intervalIntegrable 0 1

end

end RHTower
