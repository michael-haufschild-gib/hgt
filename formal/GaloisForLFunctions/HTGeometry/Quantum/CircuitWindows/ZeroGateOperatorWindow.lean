import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateCriticalLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Critical window in operator norm

The chord tolerance is stationary at the full turn. The critical angular
window therefore maps to an operator-norm window of width proportional to
`log D / D^2`, centered at the tolerance for complementary length `log D / D`.
-/

open Filter MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev windowDimension (n : ℕ) : ℝ := 2 ^ n

private theorem windowDimension_pos (n : ℕ) : 0 < windowDimension n :=
  pow_pos (by norm_num) _

private theorem tendsto_log_windowDimension : Tendsto (fun n => Real.log (windowDimension n)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

/-- Operator-norm tolerance at complementary angular length `(log D + y) / D`. -/
def zeroGateCriticalOperatorTolerance (y : ℝ) (n : ℕ) : ℝ :=
  zeroGateArcTolerance (zeroGateCriticalArcRadius y n)

/-- Width of the critical window in units of operator-norm tolerance. -/
def zeroGateOperatorWindowWidth (n : ℕ) : ℝ :=
  (Real.pi ^ 2 / 2) * Real.log (windowDimension n) / windowDimension n ^ 2

private theorem zeroGateOperatorWindowWidth_nonneg (n : ℕ) : 0 ≤ zeroGateOperatorWindowWidth n :=
  div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (one_le_pow₀ (by norm_num)))) (sq_nonneg _)

/-- Every fixed multiple of the inverse squared dimension is eventually
smaller than any positive fraction of the operator-window width. -/
theorem eventually_div_dimension_sq_le_zeroGateOperatorWindowWidth (c : ℝ) (η : Ioi (0 : ℝ)) :
    ∀ᶠ n in atTop, c / ((2 : ℝ) ^ n) ^ 2 ≤ (η : ℝ) * zeroGateOperatorWindowWidth n := by
  let a := (η : ℝ) * (Real.pi ^ 2 / 2)
  have ha : 0 < a := mul_pos η.2 (by positivity)
  filter_upwards [(tendsto_atTop.mp tendsto_log_windowDimension) (c / a)] with n hn
  have hc := (div_le_iff₀ ha).mp hn
  have hd : 0 ≤ (windowDimension n) ^ 2 := sq_nonneg _
  change c / (windowDimension n) ^ 2 ≤ (η : ℝ) * zeroGateOperatorWindowWidth n
  rw [zeroGateOperatorWindowWidth, ← mul_div_assoc, ← mul_assoc]
  exact div_le_div_of_nonneg_right (show c ≤ a * Real.log (windowDimension n) by
    rw [mul_comm a]
    exact hc) hd

private def gapAngle (y : ℝ) (n : ℕ) : ℝ := Real.pi * (1 - (zeroGateCriticalArcRadius y n : ℝ)) / 2

private theorem tendsto_gapAngle (y : ℝ) : Tendsto (gapAngle y) atTop (𝓝 0) := by
  change Tendsto (fun n => Real.pi * (1 - (zeroGateCriticalArcRadius y n : ℝ)) / 2) atTop (𝓝 0)
  simpa only [mul_zero, zero_div] using
    ((tendsto_zeroGateCriticalGap y).const_mul Real.pi).div_const 2

private theorem zeroGateCriticalOperatorTolerance_eq_cos (y : ℝ) (n : ℕ) :
    zeroGateCriticalOperatorTolerance y n = 2 * Real.cos (gapAngle y n) := by
  have hangle : Real.pi * (zeroGateCriticalArcRadius y n : ℝ) / 2 = Real.pi / 2 - gapAngle y n := by
    unfold gapAngle
    ring
  rw [zeroGateCriticalOperatorTolerance, zeroGateArcTolerance, hangle, Real.sin_pi_div_two_sub]

private theorem sin_eq_mul_sinc (x : ℝ) : Real.sin x = x * Real.sinc x := by
  by_cases h : x = 0
  · simp [h]
  · rw [Real.sinc_of_ne_zero h, ← mul_div_assoc, mul_comm x, mul_div_cancel_right₀ _ h]

private theorem tendsto_sinc_of_tendsto_zero {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun n => Real.sinc (f n)) atTop (𝓝 1) := by
  have h := (Real.continuous_sinc.continuousAt (x := (0 : ℝ))).tendsto.comp hf
  change Tendsto (fun n => Real.sinc (f n)) atTop (𝓝 (Real.sinc 0)) at h
  rwa [Real.sinc_zero] at h

/-- Measured from the central tolerance, one angular critical offset changes
the operator tolerance by one window width in the limit. -/
theorem tendsto_zeroGateCriticalOperatorTolerance_shift (y : ℝ) :
    Tendsto (fun n => (zeroGateCriticalOperatorTolerance 0 n - zeroGateCriticalOperatorTolerance y n) /
      zeroGateOperatorWindowWidth n) atTop (𝓝 y) := by
  let u (n : ℕ) := (gapAngle y n + gapAngle 0 n) / 2
  let v (n : ℕ) := (gapAngle y n - gapAngle 0 n) / 2
  let p (n : ℕ) := y + y ^ 2 / 2 * (Real.log (windowDimension n))⁻¹
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa only [u, add_zero, zero_div] using ((tendsto_gapAngle y).add (tendsto_gapAngle 0)).div_const 2
  have hv : Tendsto v atTop (𝓝 0) := by
    simpa only [v, sub_zero, zero_div] using ((tendsto_gapAngle y).sub (tendsto_gapAngle 0)).div_const 2
  have hinv : Tendsto (fun n => (Real.log (windowDimension n))⁻¹) atTop (𝓝 0) :=
    tendsto_log_windowDimension.inv_tendsto_atTop
  have hp : Tendsto p atTop (𝓝 y) := by
    simpa only [p, mul_zero, add_zero] using (hinv.const_mul (y ^ 2 / 2)).const_add y
  have h := hp.mul ((tendsto_sinc_of_tendsto_zero hu).mul (tendsto_sinc_of_tendsto_zero hv))
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_zeroGateCriticalGap_eq y, eventually_zeroGateCriticalGap_eq 0,
    (tendsto_atTop.mp tendsto_log_windowDimension) 1] with n hy h0 hlog
  have h0angle : gapAngle 0 n = u n - v n := by
    dsimp only [u, v]
    ring
  have hyangle : gapAngle y n = u n + v n := by
    dsimp only [u, v]
    ring
  have hdiff : zeroGateCriticalOperatorTolerance 0 n - zeroGateCriticalOperatorTolerance y n =
      4 * Real.sin (u n) * Real.sin (v n) := by
    rw [zeroGateCriticalOperatorTolerance_eq_cos 0 n, zeroGateCriticalOperatorTolerance_eq_cos y n,
      h0angle, hyangle, Real.cos_sub, Real.cos_add]
    ring
  have heu : u n = Real.pi * (2 * Real.log (windowDimension n) + y) / (4 * windowDimension n) := by
    dsimp only [u, gapAngle]
    rw [hy, h0]
    ring
  have hev : v n = Real.pi * y / (4 * windowDimension n) := by
    dsimp only [v, gapAngle]
    rw [hy, h0]
    ring
  have hlog0 : Real.log (windowDimension n) ≠ 0 := (zero_lt_one.trans_le hlog).ne'
  have hcoeff : 4 * u n * v n / zeroGateOperatorWindowWidth n = p n := by
    rw [heu, hev]
    dsimp only [p, zeroGateOperatorWindowWidth]
    field_simp [(windowDimension_pos n).ne', hlog0, Real.pi_ne_zero]
    ring
  rw [hdiff, sin_eq_mul_sinc (u n), sin_eq_mul_sinc (v n), ← hcoeff, div_mul_eq_mul_div]
  ring

/-- The chord tolerance increases strictly throughout the full turn. -/
theorem strictMonoOn_zeroGateArcTolerance_full : StrictMonoOn zeroGateArcTolerance (Icc 0 1) := by
  have hangle (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      Real.pi * x / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    have h0 : 0 ≤ Real.pi * x / 2 := div_nonneg (mul_nonneg Real.pi_pos.le hx.1) (by norm_num)
    have h1 := mul_le_mul_of_nonneg_left hx.2 Real.pi_pos.le
    constructor <;> linarith only [Real.pi_pos, h0, h1]
  intro r hr s hs hrs
  have h := Real.strictMonoOn_sin (hangle r hr) (hangle s hs)
    (div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hrs Real.pi_pos) (by norm_num))
  exact mul_lt_mul_of_pos_left h (by norm_num : (0 : ℝ) < 2)

private theorem zeroGateCriticalOperatorTolerance_mem (y : ℝ) (n : ℕ) :
    zeroGateCriticalOperatorTolerance y n ∈ Icc (0 : ℝ) 2 := by
  have h := strictMonoOn_zeroGateArcTolerance_full.monotoneOn
  refine ⟨?_, ?_⟩
  · simpa only [zeroGateCriticalOperatorTolerance, zeroGateArcTolerance, mul_zero, zero_div, Real.sin_zero] using
      h ⟨le_rfl, zero_le_one⟩ (zeroGateCriticalArcRadius y n).2 (zeroGateCriticalArcRadius y n).2.1
  · simpa only [zeroGateCriticalOperatorTolerance, zeroGateArcTolerance, mul_one, Real.sin_pi_div_two] using
      h (zeroGateCriticalArcRadius y n).2 ⟨zero_le_one, le_rfl⟩ (zeroGateCriticalArcRadius y n).2.2

/-- A tolerance obtained by shifting the center by `-y` window widths. -/
def zeroGateAffineOperatorTolerance (y : ℝ) (n : ℕ) : Icc (0 : ℝ) 2 :=
  ⟨max 0 (min 2 (zeroGateCriticalOperatorTolerance 0 n - y * zeroGateOperatorWindowWidth n)),
    le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- The affine tolerance lies between nearby true critical tolerances with
a positive fraction of a window width to spare on either side. -/
theorem eventually_zeroGateAffineOperatorTolerance_bracket (y : ℝ) (η : Ioi (0 : ℝ)) :
    ∀ᶠ n in atTop,
      zeroGateCriticalOperatorTolerance (y + (η : ℝ)) n + (η : ℝ) / 2 * zeroGateOperatorWindowWidth n ≤
        (zeroGateAffineOperatorTolerance y n : ℝ) ∧
      (zeroGateAffineOperatorTolerance y n : ℝ) + (η : ℝ) / 2 * zeroGateOperatorWindowWidth n ≤
        zeroGateCriticalOperatorTolerance (y - (η : ℝ)) n := by
  have hη : 0 < (η : ℝ) := η.2
  have hlo : y + (η : ℝ) / 2 < y + (η : ℝ) := by linarith only [hη]
  have hhi : y - (η : ℝ) < y - (η : ℝ) / 2 := by linarith only [hη]
  filter_upwards [(tendsto_order.mp (tendsto_zeroGateCriticalOperatorTolerance_shift _)).1 _ hlo,
    (tendsto_order.mp (tendsto_zeroGateCriticalOperatorTolerance_shift _)).2 _ hhi,
    (tendsto_atTop.mp tendsto_log_windowDimension) 1] with n hl hu hlog
  have hw : 0 < zeroGateOperatorWindowWidth n :=
    div_pos (mul_pos (by positivity) (zero_lt_one.trans_le hlog)) (pow_pos (windowDimension_pos n) _)
  have hleft := (lt_div_iff₀ hw).mp hl
  have hright := (div_lt_iff₀ hw).mp hu
  let c := zeroGateCriticalOperatorTolerance 0 n - (y : ℝ) * zeroGateOperatorWindowWidth n
  let d := (η : ℝ) / 2 * zeroGateOperatorWindowWidth n
  have hd : 0 ≤ d := mul_nonneg (div_nonneg hη.le (by norm_num)) hw.le
  have hlc : zeroGateCriticalOperatorTolerance (y + (η : ℝ)) n + d ≤ c := by
    dsimp only [c, d]
    linarith only [hleft]
  have hcu : c + d ≤ zeroGateCriticalOperatorTolerance (y - (η : ℝ)) n := by
    dsimp only [c, d]
    linarith only [hright]
  have hc0 := (zeroGateCriticalOperatorTolerance_mem (y + (η : ℝ)) n).1.trans
    ((le_add_of_nonneg_right hd).trans hlc)
  have hc2 := ((le_add_of_nonneg_right hd).trans hcu).trans
    (zeroGateCriticalOperatorTolerance_mem (y - (η : ℝ)) n).2
  change _ + d ≤ max 0 (min 2 c) ∧ max 0 (min 2 c) + d ≤ _
  rw [min_eq_right hc2, max_eq_right hc0]
  exact ⟨hlc, hcu⟩

/-- The arc threshold for affine operator tolerances. -/
def zeroGateOperatorWindowRadius (y : ℝ) (n : ℕ) : Icc (0 : ℝ) 1 := by
  let x := (zeroGateAffineOperatorTolerance y n : ℝ) / 2
  have hx : 0 ≤ x := div_nonneg (zeroGateAffineOperatorTolerance y n).2.1 (by norm_num)
  refine ⟨2 * Real.arcsin x / Real.pi,
    div_nonneg (mul_nonneg (by norm_num) (Real.arcsin_nonneg.mpr hx)) Real.pi_pos.le, ?_⟩
  apply (div_le_iff₀ Real.pi_pos).mpr
  linarith only [Real.arcsin_le_pi_div_two x]

/-- The inverse chord map realizes the affine threshold exactly. -/
theorem zeroGateArcTolerance_operatorWindowRadius (y : ℝ) (n : ℕ) :
    zeroGateArcTolerance (zeroGateOperatorWindowRadius y n) = (zeroGateAffineOperatorTolerance y n : ℝ) := by
  let x := (zeroGateAffineOperatorTolerance y n : ℝ) / 2
  have hx0 : -1 ≤ x := by
    have h := (zeroGateAffineOperatorTolerance y n).2.1
    dsimp only [x]
    linarith only [h]
  have hx1 : x ≤ 1 := by
    have h := (zeroGateAffineOperatorTolerance y n).2.2
    dsimp only [x]
    linarith only [h]
  have hangle : Real.pi * (2 * Real.arcsin x / Real.pi) / 2 = Real.arcsin x := by
    field_simp [Real.pi_ne_zero]
  change 2 * Real.sin (Real.pi * (2 * Real.arcsin x / Real.pi) / 2) = _
  rw [hangle, Real.sin_arcsin hx0 hx1]
  dsimp only [x]
  ring

private theorem eventually_zeroGateOperatorWindowRadius_between (y : ℝ) (η : Ioi (0 : ℝ)) :
    ∀ᶠ n in atTop, (zeroGateCriticalArcRadius (y + (η : ℝ)) n : ℝ) ≤ zeroGateOperatorWindowRadius y n ∧
      (zeroGateOperatorWindowRadius y n : ℝ) ≤ zeroGateCriticalArcRadius (y - (η : ℝ)) n := by
  filter_upwards [eventually_zeroGateAffineOperatorTolerance_bracket y η] with n hn
  have hd : 0 ≤ (η : ℝ) / 2 * zeroGateOperatorWindowWidth n :=
    mul_nonneg (div_nonneg η.2.le (by norm_num)) (zeroGateOperatorWindowWidth_nonneg n)
  constructor
  · apply (strictMonoOn_zeroGateArcTolerance_full.le_iff_le (zeroGateCriticalArcRadius _ n).2
      (zeroGateOperatorWindowRadius y n).2).mp
    rw [zeroGateArcTolerance_operatorWindowRadius]
    exact (le_add_of_nonneg_right hd).trans hn.1
  · apply (strictMonoOn_zeroGateArcTolerance_full.le_iff_le (zeroGateOperatorWindowRadius y n).2
      (zeroGateCriticalArcRadius _ n).2).mp
    rw [zeroGateArcTolerance_operatorWindowRadius]
    exact (le_add_of_nonneg_right hd).trans hn.2

/-- Two nearby critical arc thresholds give lower and upper occupation
bounds within any prescribed error of the limiting probability. -/
theorem eventually_zeroGateCriticalArcMass_bracket (y : ℝ) (ε : Ioi (0 : ℝ)) :
    ∃ η : Ioi (0 : ℝ), ∀ᶠ n in atTop,
      (1 - Real.exp (-Real.exp (-y))) - (ε : ℝ) <
        zeroGateFullArcMass n (zeroGateCriticalArcRadius (y + (η : ℝ)) n) ∧
      zeroGateFullArcMass n (zeroGateCriticalArcRadius (y - (η : ℝ)) n) <
        (1 - Real.exp (-Real.exp (-y))) + (ε : ℝ) := by
  let F (t : ℝ) := 1 - Real.exp (-Real.exp (-t))
  have hF : Continuous F :=
    continuous_const.sub (Real.continuous_exp.comp (Real.continuous_exp.comp continuous_neg).neg)
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp (hF.continuousAt (x := y)) ε ε.2
  let η : Ioi (0 : ℝ) := ⟨δ / 2, half_pos hδ⟩
  have hplus : dist (y + (η : ℝ)) y < δ := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg η.2.le]
    exact half_lt_self hδ
  have hminus : dist (y - (η : ℝ)) y < δ := by
    rw [Real.dist_eq, show y - (η : ℝ) - y = -(η : ℝ) by ring, abs_neg, abs_of_nonneg η.2.le]
    exact half_lt_self hδ
  have hl := (abs_lt.mp (by
    simpa only [Real.dist_eq] using hclose hplus :
      |F (y + (η : ℝ)) - F y| < (ε : ℝ))).1
  have hu := (abs_lt.mp (by
    simpa only [Real.dist_eq] using hclose hminus :
      |F (y - (η : ℝ)) - F y| < (ε : ℝ))).2
  have hlow : F y - (ε : ℝ) < F (y + (η : ℝ)) := by linarith only [hl]
  have hhigh : F (y - (η : ℝ)) < F y + (ε : ℝ) := by linarith only [hu]
  refine ⟨η, ?_⟩
  filter_upwards [(tendsto_order.mp (tendsto_zeroGateCriticalArcMass (y + (η : ℝ)))).1 _ hlow,
    (tendsto_order.mp (tendsto_zeroGateCriticalArcMass (y - (η : ℝ)))).2 _ hhigh] with n hn hm
  exact ⟨hn, hm⟩

/-- The Gumbel occupation profile survives linear normalization of the
physical operator-norm threshold. -/
theorem tendsto_zeroGateOperatorWindowMass (y : ℝ) :
    Tendsto (fun n => zeroGateFullArcMass n (zeroGateOperatorWindowRadius y n)) atTop
      (𝓝 (1 - Real.exp (-Real.exp (-y)))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη⟩ := eventually_zeroGateCriticalArcMass_bracket y ⟨ε, hε⟩
  filter_upwards [eventually_zeroGateOperatorWindowRadius_between y η, hη] with n hn hmass
  have hlo := (relativeUnitArcMass_mono (fun _ : Fin n => false)) hn.1
  have hhi := (relativeUnitArcMass_mono (fun _ : Fin n => false)) hn.2
  change zeroGateFullArcMass n (zeroGateCriticalArcRadius (y + (η : ℝ)) n) ≤
    zeroGateFullArcMass n (zeroGateOperatorWindowRadius y n) at hlo
  change zeroGateFullArcMass n (zeroGateOperatorWindowRadius y n) ≤
    zeroGateFullArcMass n (zeroGateCriticalArcRadius (y - (η : ℝ)) n) at hhi
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith only [hlo, hmass.1], by linarith only [hhi, hmass.2]⟩

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- On almost every Gaussian chain, physical time fractions at the affine
operator threshold have the Gumbel tail as the prefix size grows. -/
theorem gaussian_path_zeroGateOperatorWindowOccupation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ y a : ℝ,
      (∀ k : ℕ,
        let u := pathPauliDisorderShell ω (k + 1)
        let H : selfAdjoint (Reg (k + 3)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
        Tendsto (fun T => volume.real
          ({t | orbitCircuitDistance H 0 t ≤ zeroGateAffineOperatorTolerance y (k + 3)} ∩ Icc a T) /
            (T - a)) atTop
          (𝓝 (zeroGateFullArcMass (k + 3) (zeroGateOperatorWindowRadius y (k + 3))))) ∧
      Tendsto (fun k : ℕ => zeroGateFullArcMass (k + 3) (zeroGateOperatorWindowRadius y (k + 3))) atTop
        (𝓝 (1 - Real.exp (-Real.exp (-y)))) := by
  filter_upwards [gaussian_path_zeroGateFullOccupation_from_start] with ω hω
  intro y a
  refine ⟨fun k => ?_, (tendsto_zeroGateOperatorWindowMass y).comp (tendsto_add_atTop_nat 3)⟩
  simpa only [zeroGateReturnSet, zeroGateArcTolerance_operatorWindowRadius] using
    hω k (zeroGateOperatorWindowRadius y (k + 3)) a

#print axioms tendsto_zeroGateCriticalOperatorTolerance_shift
#print axioms eventually_div_dimension_sq_le_zeroGateOperatorWindowWidth
#print axioms eventually_zeroGateAffineOperatorTolerance_bracket
#print axioms eventually_zeroGateCriticalArcMass_bracket
#print axioms tendsto_zeroGateOperatorWindowMass
#print axioms gaussian_path_zeroGateOperatorWindowOccupation

end

end GaloisForLFunctions.HTGeometry
