import GaloisForLFunctions.RHTower.PowerLatticeResidue
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The Lambert sum is holomorphic near the origin

On a disc small enough that every Lambert variable stays in `‖u_n‖ ≤ 1/2`, the terms are rational
functions with nonvanishing denominators, dominated by a summable `p`-series.  The sum is therefore
holomorphic there.

This is the analytic half of the transform's description: the series is not merely convergent, it
defines a holomorphic function on a neighbourhood of the origin — the object whose poles and
residues the lattice law describes.

* `GaloisForLFunctions.RHTower.norm_lambertVar_le_of_mem_ball`;
* `GaloisForLFunctions.RHTower.differentiableOn_lambertSum`.
-/

open Complex Metric

namespace GaloisForLFunctions.RHTower

/-- On a ball of radius `M` the Lambert variable is bounded by `M/(2π)^s` divided by a power. -/
theorem norm_lambertVar_le_of_mem_ball {s : ℝ} (_hs : 0 < s) {M : ℝ} {ξ : ℂ} (hξ : ‖ξ‖ ≤ M)
    (n : ℕ) : ‖lambertVar s ξ n‖ ≤ (M / (2 * Real.pi) ^ s) / ((n : ℝ) + 1) ^ s := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsplit : ((2 * Real.pi * ((n : ℝ) + 1)) ^ s : ℝ)
      = (2 * Real.pi) ^ s * ((n : ℝ) + 1) ^ s := Real.mul_rpow hpi.le hN.le
  have hden : (0 : ℝ) < (2 * Real.pi * ((n : ℝ) + 1)) ^ s :=
    Real.rpow_pos_of_pos (by positivity) s
  have hpis : (0 : ℝ) < (2 * Real.pi) ^ s := Real.rpow_pos_of_pos hpi s
  have hNs : (0 : ℝ) < ((n : ℝ) + 1) ^ s := Real.rpow_pos_of_pos hN s
  have hcancel : M / (2 * Real.pi) ^ s * (2 * Real.pi) ^ s = M :=
    div_mul_cancel₀ _ (ne_of_gt hpis)
  rw [lambertVar, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden, hsplit,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hcancel]

/-- **The Lambert sum is holomorphic on a disc where every variable is small.** -/
theorem differentiableOn_lambertSum {s : ℝ} (hs : 0 < s) (α : ℝ) {M : ℝ} (hM0 : 0 < M)
    (hM : M ≤ (2 * Real.pi) ^ s / 2) :
    DifferentiableOn ℂ (fun ξ : ℂ => ∑' n : ℕ, (1 / ((n : ℂ) + 1)) *
        (lambertVar s ξ n * (Real.sin α : ℂ)
          / (1 + 2 * lambertVar s ξ n * (Real.cos α : ℂ) + (lambertVar s ξ n) ^ 2)))
      (ball (0 : ℂ) M) := by
  classical
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpis : (0 : ℝ) < (2 * Real.pi) ^ s := Real.rpow_pos_of_pos hpi s
  set C : ℝ := M / (2 * Real.pi) ^ s with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hNpow : ∀ n : ℕ, (1 : ℝ) ≤ ((n : ℝ) + 1) ^ s := by
    intro n
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    simpa using Real.one_le_rpow h1 hs.le
  -- every variable is small on the ball
  have hsmall : ∀ (n : ℕ) (ξ : ℂ), ξ ∈ ball (0 : ℂ) M → ‖lambertVar s ξ n‖ ≤ 1 / 2 := by
    intro n ξ hξ
    have hξM : ‖ξ‖ ≤ M := le_of_lt (by simpa using mem_ball_zero_iff.1 hξ)
    have hb := norm_lambertVar_le_of_mem_ball hs hξM n
    have hNs := hNpow n
    have hCle : C ≤ 1 / 2 := by
      rw [hCdef, div_le_iff₀ hpis]
      linarith
    have hstep : C / ((n : ℝ) + 1) ^ s ≤ C := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith [le_trans hb hstep]
  -- the quadratic is bounded below on the ball
  have hquad : ∀ (n : ℕ) (ξ : ℂ), ξ ∈ ball (0 : ℂ) M →
      (1 : ℝ) / 4 ≤ ‖1 + 2 * lambertVar s ξ n * (Real.cos α : ℂ) + (lambertVar s ξ n) ^ 2‖ := by
    intro n ξ hξ
    have hsm := hsmall n ξ hξ
    have hle1 : ‖lambertVar s ξ n‖ ≤ 1 := by linarith
    have hbase := norm_lambertQuadratic_ge α hle1
    nlinarith [norm_nonneg (lambertVar s ξ n)]
  -- termwise domination
  have hbound : ∀ (n : ℕ) (ξ : ℂ), ξ ∈ ball (0 : ℂ) M →
      ‖(1 / ((n : ℂ) + 1)) * (lambertVar s ξ n * (Real.sin α : ℂ)
        / (1 + 2 * lambertVar s ξ n * (Real.cos α : ℂ) + (lambertVar s ξ n) ^ 2))‖
        ≤ 4 * C / ((n : ℝ) + 1) ^ (1 + s) := by
    intro n ξ hξ
    have hξM : ‖ξ‖ ≤ M := le_of_lt (by simpa using mem_ball_zero_iff.1 hξ)
    have hb := norm_lambertVar_le_of_mem_ball hs hξM n
    have hq := hquad n ξ hξ
    have hqpos : (0 : ℝ) < ‖1 + 2 * lambertVar s ξ n * (Real.cos α : ℂ)
        + (lambertVar s ξ n) ^ 2‖ := by linarith
    have hsinle : ‖(Real.sin α : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_sin_le_one _
    have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hnormn : ‖(1 : ℂ) / ((n : ℂ) + 1)‖ = 1 / ((n : ℝ) + 1) := by
      have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [norm_div, norm_one, hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNpos]
    have hnum : ‖lambertVar s ξ n * (Real.sin α : ℂ)‖ ≤ C / ((n : ℝ) + 1) ^ s := by
      calc ‖lambertVar s ξ n * (Real.sin α : ℂ)‖
          = ‖lambertVar s ξ n‖ * ‖(Real.sin α : ℂ)‖ := norm_mul _ _
        _ ≤ (C / ((n : ℝ) + 1) ^ s) * 1 :=
            mul_le_mul hb hsinle (norm_nonneg _) (by positivity)
        _ = C / ((n : ℝ) + 1) ^ s := by ring
    have hfrac : ‖lambertVar s ξ n * (Real.sin α : ℂ)
        / (1 + 2 * lambertVar s ξ n * (Real.cos α : ℂ) + (lambertVar s ξ n) ^ 2)‖
        ≤ 4 * (C / ((n : ℝ) + 1) ^ s) := by
      rw [norm_div, div_le_iff₀ hqpos]
      nlinarith [norm_nonneg (lambertVar s ξ n * (Real.sin α : ℂ))]
    have hNs : (0 : ℝ) < ((n : ℝ) + 1) ^ s := Real.rpow_pos_of_pos hNpos s
    calc ‖(1 / ((n : ℂ) + 1)) * (lambertVar s ξ n * (Real.sin α : ℂ)
          / (1 + 2 * lambertVar s ξ n * (Real.cos α : ℂ) + (lambertVar s ξ n) ^ 2))‖
        = ‖(1 : ℂ) / ((n : ℂ) + 1)‖ * ‖lambertVar s ξ n * (Real.sin α : ℂ)
            / (1 + 2 * lambertVar s ξ n * (Real.cos α : ℂ) + (lambertVar s ξ n) ^ 2)‖ := by
          rw [norm_mul]
      _ ≤ (1 / ((n : ℝ) + 1)) * (4 * (C / ((n : ℝ) + 1) ^ s)) := by
          rw [hnormn]
          exact mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = 4 * C / ((n : ℝ) + 1) ^ (1 + s) := by
          rw [Real.rpow_add hNpos, Real.rpow_one]
          field_simp
  -- each term is holomorphic on the ball
  have hterm : ∀ n : ℕ, DifferentiableOn ℂ (fun ξ : ℂ => (1 / ((n : ℂ) + 1)) *
      (lambertVar s ξ n * (Real.sin α : ℂ)
        / (1 + 2 * lambertVar s ξ n * (Real.cos α : ℂ) + (lambertVar s ξ n) ^ 2)))
      (ball (0 : ℂ) M) := by
    intro n
    have hvar : DifferentiableOn ℂ (fun ξ : ℂ => lambertVar s ξ n) (ball (0 : ℂ) M) := by
      unfold lambertVar
      fun_prop
    refine DifferentiableOn.const_mul ?_ _
    refine DifferentiableOn.div (hvar.mul_const _) ?_ ?_
    · exact ((differentiableOn_const 1).add ((hvar.const_mul 2).mul_const _)).add (hvar.pow 2)
    · intro ξ hξ
      have := hquad n ξ hξ
      intro hcon
      rw [hcon, norm_zero] at this
      linarith
  -- the dominating series
  have hu : Summable fun n : ℕ => 4 * C / ((n : ℝ) + 1) ^ (1 + s) := by
    have hbase : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ (1 + s) :=
      summable_one_div_nat_add_one_rpow (by linarith)
    have hmul := hbase.mul_left (4 * C)
    refine hmul.congr fun n => ?_
    rw [mul_one_div]
  exact differentiableOn_tsum_of_summable_norm hu hterm isOpen_ball
    (fun n w hw => hbound n w hw)

end GaloisForLFunctions.RHTower
