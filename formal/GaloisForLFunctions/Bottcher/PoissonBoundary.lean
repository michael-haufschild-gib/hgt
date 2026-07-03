/-
# Poisson kernel: positivity, continuity, unit mass (toward Dirichlet ingredient 3/3)

Foundational facts about the Poisson kernel on the circle, for the harmonic Schwarz reflection
principle.  These feed the approximate-identity argument that the Poisson integral attains its
continuous boundary values (the last Dirichlet ingredient).

* `poissonKernel_continuousOn_sphere` — `z ↦ poissonKernel c w z` is continuous on `sphere c R`
  (denominator `‖z - w‖² ≠ 0` there, `w` interior);
* `poissonKernel_nonneg` — the kernel is `≥ 0` (mathlib's lower bound `le_re_herglotzRieszKernel`);
* `poissonKernel_circleAverage_eq_one` — the kernel has unit mass (the reproducing property
  `DiffContOnCl.circleAverage_poissonKernel_smul` applied to the constant `1`);
* `poissonKernel_le_concentration` — the concentration bound `poissonKernel c w z ≤ 2R‖w-ζ‖/(δ/2)²`
  for `z` at distance `≥ δ` from a boundary point `ζ` and `w` within `δ/2` of `ζ`: the kernel → 0
  away from `ζ` as `w → ζ` (the analytic heart of the approximate identity).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib

open Complex Set Metric MeasureTheory Filter Topology

namespace Bottcher

theorem poissonKernel_continuousOn_sphere {c w : ℂ} {R : ℝ}
    (hw : w ∈ ball c R) : ContinuousOn (poissonKernel c w) (sphere c R) := by
  have hzw : ∀ z ∈ sphere c R, (z - c) - (w - c) ≠ 0 := by
    intro z hz
    rw [show (z - c) - (w - c) = z - w by ring, sub_ne_zero]
    intro h; subst h
    rw [mem_sphere, dist_comm] at hz; rw [mem_ball, dist_comm] at hw
    rw [hz] at hw; exact lt_irrefl R hw
  have hrw : poissonKernel c w = fun z => (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2 := by
    funext z; exact poissonKernel_def c w z
  rw [hrw]
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro z hz
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hzw z hz))

theorem poissonKernel_nonneg {c w z : ℂ} {R : ℝ} (hz : z ∈ sphere c R) (hw : w ∈ ball c R) :
    0 ≤ poissonKernel c w z := by
  have hwc : ‖w - c‖ < R := by rw [mem_ball, dist_eq_norm] at hw; exact hw
  have hbound := le_re_herglotzRieszKernel hz hw
  have hpk : poissonKernel c w z = ((z - c + (w - c)) / ((z - c) - (w - c))).re := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]; rfl
  rw [hpk]
  refine le_trans ?_ hbound
  apply div_nonneg <;> [linarith; linarith [norm_nonneg (w - c)]]

theorem poissonKernel_circleAverage_eq_one {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) :
    Real.circleAverage (poissonKernel c w) c R = 1 := by
  have hdc : DiffContOnCl ℂ (fun _ : ℂ => (1 : ℂ)) (ball c R) :=
    ⟨differentiableOn_const 1, continuousOn_const⟩
  have h := DiffContOnCl.circleAverage_poissonKernel_smul hdc hw
  have hfun : (poissonKernel c w • fun _ : ℂ => (1 : ℂ)) = (fun z => ((poissonKernel c w z : ℝ) : ℂ)) := by
    funext z; simp
  rw [hfun] at h
  have hR : 0 < R := dist_nonneg.trans_lt (mem_ball.mp hw)
  have hci : CircleIntegrable (poissonKernel c w) c R :=
    (show ContinuousOn (poissonKernel c w) (sphere c |R|) by
      rw [abs_of_pos hR]; exact poissonKernel_continuousOn_sphere hw).circleIntegrable'
  have hcomm := ContinuousLinearMap.circleAverage_comp_comm Complex.ofRealCLM hci
  have hfun2 : (⇑Complex.ofRealCLM ∘ poissonKernel c w) = (fun z => ((poissonKernel c w z : ℝ) : ℂ)) := rfl
  rw [hfun2, h] at hcomm
  have h1 : ((Real.circleAverage (poissonKernel c w) c R : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofRealCLM_apply]; exact hcomm.symm
  exact_mod_cast h1

/-- **Concentration bound.**  For `z` on the sphere at distance `≥ δ` from a boundary point `ζ`, and
`w` within `δ/2` of `ζ`, the Poisson kernel is bounded by `2R‖w-ζ‖/(δ/2)²`.  As `w → ζ`, the bound
`→ 0`, so the kernel concentrates near `ζ` — the analytic core of the approximate identity. -/
theorem poissonKernel_le_concentration {c w z ζ : ℂ} {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hz : z ∈ sphere c R) (hζ : ζ ∈ sphere c R) (hw : w ∈ ball c R)
    (hzζ : δ ≤ ‖z - ζ‖) (hwζ : ‖w - ζ‖ < δ / 2) :
    poissonKernel c w z ≤ 2 * R * ‖w - ζ‖ / (δ / 2) ^ 2 := by
  have hzc : ‖z - c‖ = R := by rw [mem_sphere, dist_eq_norm] at hz; exact hz
  have hζc : ‖ζ - c‖ = R := by rw [mem_sphere, dist_eq_norm] at hζ; exact hζ
  have hwc : ‖w - c‖ < R := by rw [mem_ball, dist_eq_norm] at hw; exact hw
  have hden : δ / 2 ≤ ‖z - w‖ := by
    have h1 := norm_sub_norm_le (z - ζ) (w - ζ)
    rw [show (z - ζ) - (w - ζ) = z - w by ring] at h1
    linarith
  have hRwc : R - ‖w - c‖ ≤ ‖w - ζ‖ := by
    have h2 := norm_sub_norm_le (ζ - c) (w - c)
    rw [show (ζ - c) - (w - c) = ζ - w by ring, hζc, show ζ - w = -(w - ζ) by ring, norm_neg] at h2
    linarith
  have hnum : ‖z - c‖ ^ 2 - ‖w - c‖ ^ 2 ≤ 2 * R * ‖w - ζ‖ := by
    rw [hzc, show R ^ 2 - ‖w - c‖ ^ 2 = (R - ‖w - c‖) * (R + ‖w - c‖) by ring]
    calc (R - ‖w - c‖) * (R + ‖w - c‖) ≤ ‖w - ζ‖ * (2 * R) :=
          mul_le_mul hRwc (by linarith) (by linarith [norm_nonneg (w - c)]) (norm_nonneg _)
      _ = 2 * R * ‖w - ζ‖ := by ring
  have hnum0 : 0 ≤ ‖z - c‖ ^ 2 - ‖w - c‖ ^ 2 := by rw [hzc]; nlinarith [norm_nonneg (w - c)]
  rw [poissonKernel_def, show (z - c) - (w - c) = z - w by ring]
  have hd2 : (δ / 2) ^ 2 ≤ ‖z - w‖ ^ 2 := by gcongr
  calc (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖z - w‖ ^ 2
      ≤ (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / (δ / 2) ^ 2 := by gcongr
    _ ≤ 2 * R * ‖w - ζ‖ / (δ / 2) ^ 2 := by gcongr

/-- **Poisson integral attains continuous boundary values (Dirichlet ingredient 3/3).**  For `g`
continuous on `sphere c R` and a boundary point `ζ`, the Poisson integral tends to `g ζ` as `w → ζ`
from inside the disc.  Approximate identity: `poissonInt(w) - g ζ = circleAverage(kernel·(g - g ζ))`
(unit mass); bounded pointwise by `ε/2·kernel + C` with `C = 16RM‖w-ζ‖/δ₁²` constant in `z` (continuity
near `ζ`, concentration far), integrating to `ε/2 + C → ε`. -/
theorem poissonInt_tendsto_boundary {c : ℂ} {R : ℝ} (hR : 0 < R) {g : ℂ → ℝ}
    (hg : ContinuousOn g (sphere c R)) {ζ : ℂ} (hζ : ζ ∈ sphere c R) :
    Tendsto (fun w => Real.circleAverage (poissonKernel c w • g) c R)
      (𝓝[ball c R] ζ) (𝓝 (g ζ)) := by
  have habsR : |R| = R := abs_of_pos hR
  obtain ⟨M, hM0, hMg⟩ : ∃ M, 0 ≤ M ∧ ∀ z ∈ sphere c R, |g z| ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hg
    exact ⟨max M 0, le_max_right _ _,
      fun z hz => (Real.norm_eq_abs (g z) ▸ hM z hz).trans (le_max_left _ _)⟩
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hδ₁g⟩ := (Metric.continuousWithinAt_iff).mp (hg ζ hζ) (ε / 2) (by linarith)
  set K : ℝ := 16 * R * M / δ₁ ^ 2 with hK
  refine ⟨min (δ₁ / 2) (ε / 2 / (K + 1)), by positivity, ?_⟩
  intro w hwball hwζ
  have hwζ1 : ‖w - ζ‖ < δ₁ / 2 := by
    rw [Complex.dist_eq] at hwζ; exact lt_of_lt_of_le hwζ (min_le_left _ _)
  have hwζ2 : ‖w - ζ‖ < ε / 2 / (K + 1) := by
    rw [Complex.dist_eq] at hwζ; exact lt_of_lt_of_le hwζ (min_le_right _ _)
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set C : ℝ := K * ‖w - ζ‖ with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; exact mul_nonneg hK0 (norm_nonneg _)
  have hpkg : (poissonKernel c w • g) = (fun z => poissonKernel c w z * g z) := by
    funext z; simp [smul_eq_mul]
  have hpkCI : CircleIntegrable (poissonKernel c w) c R :=
    (show ContinuousOn (poissonKernel c w) (sphere c |R|) by
      rw [habsR]; exact poissonKernel_continuousOn_sphere hwball).circleIntegrable'
  have hmass := poissonKernel_circleAverage_eq_one hwball
  -- reduction to the difference integrand
  have hkey : Real.circleAverage (fun z => poissonKernel c w z * (g z - g ζ)) c R
      = Real.circleAverage (poissonKernel c w • g) c R - g ζ := by
    have he : (fun z => poissonKernel c w z * g ζ) = (g ζ • poissonKernel c w) := by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]; ring
    have hCIgζ : CircleIntegrable (fun z => poissonKernel c w z * g ζ) c R := by
      rw [he]; exact hpkCI.smul (g ζ)
    have hCIpg : CircleIntegrable (fun z => poissonKernel c w z * g z) c R := by
      rw [← hpkg]
      exact (show ContinuousOn (poissonKernel c w • g) (sphere c |R|) by
        rw [habsR]; exact (poissonKernel_continuousOn_sphere hwball).smul hg).circleIntegrable'
    have hgζval : Real.circleAverage (fun z => poissonKernel c w z * g ζ) c R = g ζ := by
      rw [he, Real.circleAverage_smul, hmass, smul_eq_mul, mul_one]
    have hint : (fun z => poissonKernel c w z * (g z - g ζ))
        = (fun z => poissonKernel c w z * g z - poissonKernel c w z * g ζ) := by funext z; ring
    rw [hint, Real.circleAverage_fun_sub hCIpg hCIgζ, hgζval, ← hpkg]
  rw [Real.dist_eq, ← hkey]
  have hbound : ∀ z ∈ sphere c |R|,
      |poissonKernel c w z * (g z - g ζ)| ≤ ε / 2 * poissonKernel c w z + C := by
    intro z hz
    rw [habsR] at hz
    have hpk0 : 0 ≤ poissonKernel c w z := poissonKernel_nonneg hz hwball
    rw [abs_mul, abs_of_nonneg hpk0]
    by_cases hnear : ‖z - ζ‖ < δ₁
    · have hgz : |g z - g ζ| < ε / 2 := by
        have := hδ₁g (x := z) hz (by rw [Complex.dist_eq]; exact hnear)
        rwa [Real.dist_eq] at this
      nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hgz) hpk0]
    · rw [not_lt] at hnear
      have hconc := poissonKernel_le_concentration hR hδ₁ hz hζ hwball hnear hwζ1
      have hgd : |g z - g ζ| ≤ 2 * M := by
        calc |g z - g ζ| ≤ |g z| + |g ζ| := abs_sub _ _
          _ ≤ 2 * M := by linarith [hMg z hz, hMg ζ hζ]
      have hCbound : poissonKernel c w z * |g z - g ζ| ≤ C := by
        calc poissonKernel c w z * |g z - g ζ|
            ≤ (2 * R * ‖w - ζ‖ / (δ₁ / 2) ^ 2) * (2 * M) :=
              mul_le_mul hconc hgd (abs_nonneg _) (by positivity)
          _ = C := by rw [hCdef, hK]; ring
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ε / 2) hpk0]
  have hstep : |Real.circleAverage (fun z => poissonKernel c w z * (g z - g ζ)) c R| ≤ ε / 2 + C := by
    have hCImaj : CircleIntegrable (fun z => ε / 2 * poissonKernel c w z + C) c R :=
      (show ContinuousOn (fun z => ε / 2 * poissonKernel c w z + C) (sphere c |R|) by
        rw [habsR]
        exact (continuousOn_const.mul (poissonKernel_continuousOn_sphere hwball)).add
          continuousOn_const).circleIntegrable'
    have hCIabs : CircleIntegrable (fun z => |poissonKernel c w z * (g z - g ζ)|) c R :=
      (show ContinuousOn (fun z => |poissonKernel c w z * (g z - g ζ)|) (sphere c |R|) by
        rw [habsR]
        exact ((poissonKernel_continuousOn_sphere hwball).mul
          (hg.sub continuousOn_const)).abs).circleIntegrable'
    have hCIepk : CircleIntegrable (fun z => ε / 2 * poissonKernel c w z) c R :=
      (show ContinuousOn (fun z => ε / 2 * poissonKernel c w z) (sphere c |R|) by
        rw [habsR]; exact continuousOn_const.mul (poissonKernel_continuousOn_sphere hwball)).circleIntegrable'
    have hCIc : CircleIntegrable (fun _ : ℂ => C) c R := continuousOn_const.circleIntegrable'
    calc |Real.circleAverage (fun z => poissonKernel c w z * (g z - g ζ)) c R|
        ≤ Real.circleAverage (fun z => |poissonKernel c w z * (g z - g ζ)|) c R :=
          Real.abs_circleAverage_le_circleAverage_abs
      _ ≤ Real.circleAverage (fun z => ε / 2 * poissonKernel c w z + C) c R :=
          Real.circleAverage_mono hCIabs hCImaj hbound
      _ = ε / 2 + C := by
          rw [Real.circleAverage_fun_add hCIepk hCIc, Real.circleAverage_const]
          congr 1
          rw [show (fun z => ε / 2 * poissonKernel c w z) = ((ε / 2) • poissonKernel c w) from by
                funext z; simp [smul_eq_mul],
            Real.circleAverage_smul, hmass, smul_eq_mul, mul_one]
  -- C < ε/2 from δ choice
  have hCsmall : C < ε / 2 := by
    rw [hCdef]
    have hKpos : 0 < K + 1 := by positivity
    calc K * ‖w - ζ‖ ≤ (K + 1) * ‖w - ζ‖ := by nlinarith [norm_nonneg (w - ζ)]
      _ < (K + 1) * (ε / 2 / (K + 1)) := by
          apply mul_lt_mul_of_pos_left hwζ2 hKpos
      _ = ε / 2 := by field_simp
  linarith [hstep]

end Bottcher
