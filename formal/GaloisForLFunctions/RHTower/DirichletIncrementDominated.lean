import GaloisForLFunctions.RHTower.HurwitzZetaSmallShift
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Dominated convergence for Dirichlet increments at the pole

The increment `x^{-s} - (x+1)^{-s}` is at most `s x^{-s-1}`, so on `1 < s ≤ 2` it is uniformly at
most `2/x²`.  A summable weight against that majorant therefore lets the limit `s → 1⁺` pass
inside the sum, turning each increment into `1/x - 1/(x+1)`.
-/

open Filter Topology Complex

namespace RHTower

noncomputable section

theorem tendsto_cpow_neg_ofReal {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s : ℝ => ((x : ℝ) : ℂ) ^ (-(s : ℂ))) (𝓝[>] 1) (𝓝 (((x : ℝ) : ℂ)⁻¹)) := by
  have hne : ((x : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hx
  have hexp : Tendsto (fun s : ℝ => (-(s : ℂ))) (𝓝[>] (1 : ℝ)) (𝓝 (-(1 : ℂ))) := by
    have hc : Tendsto (fun s : ℝ => ((s : ℝ) : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (((1 : ℝ) : ℂ))) :=
      Complex.continuous_ofReal.tendsto 1
    have hw : Tendsto (fun s : ℝ => ((s : ℝ) : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (((1 : ℝ) : ℂ))) :=
      hc.mono_left nhdsWithin_le_nhds
    simpa using hw.neg
  have hlim := hexp.const_cpow (a := ((x : ℝ) : ℂ)) (Or.inl hne)
  rw [Complex.cpow_neg, Complex.cpow_one] at hlim
  exact hlim

/-- **The uniform increment bound on `1 ≤ s ≤ 2`.** -/
theorem norm_cpow_increment_le (k : ℕ) {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    ‖(((k : ℝ) + 1 : ℝ) : ℂ) ^ (-(s : ℂ)) - (((k : ℝ) + 2 : ℝ) : ℂ) ^ (-(s : ℂ))‖
      ≤ 2 / ((k : ℝ) + 1) ^ 2 := by
  have hx : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hx1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hw : (0 : ℝ) < ((s : ℂ)).re := by
    simpa using lt_of_lt_of_le zero_lt_one hs1
  have hbase := norm_cpow_shift_sub_le_of_nonneg (x := (k : ℝ) + 1) (b := 1) hx zero_le_one
    (w := (s : ℂ)) hw
  have hcast : ((k : ℝ) + 1 + 1 : ℝ) = ((k : ℝ) + 2 : ℝ) := by ring
  rw [hcast] at hbase
  have hnormw : ‖((s : ℝ) : ℂ)‖ = s := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hre : ((s : ℝ) : ℂ).re = s := Complex.ofReal_re s
  rw [hnormw, hre, mul_one] at hbase
  have hmono : ((k : ℝ) + 1) ^ (-s - 1) ≤ ((k : ℝ) + 1) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hval : ((k : ℝ) + 1) ^ (-2 : ℝ) = 1 / ((k : ℝ) + 1) ^ 2 := by
    rw [Real.rpow_neg hx.le, one_div]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [norm_sub_rev]
  refine hbase.trans ?_
  rw [hval] at hmono
  have hspos : (0 : ℝ) < s := by linarith
  have hinv : (0 : ℝ) < 1 / ((k : ℝ) + 1) ^ 2 := by positivity
  calc s * ((k : ℝ) + 1) ^ (-s - 1)
      ≤ s * (1 / ((k : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left hmono hspos.le
    _ ≤ 2 * (1 / ((k : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_right hs2 hinv.le
    _ = 2 / ((k : ℝ) + 1) ^ 2 := by ring

/-- **Dominated convergence for a weighted Dirichlet increment series.** -/
theorem tendsto_tsum_cpow_increment {E : ℕ → ℂ} {bound : ℕ → ℝ} (hsum : Summable bound)
    (hb : ∀ k, ‖E k‖ * (2 / ((k : ℝ) + 1) ^ 2) ≤ bound k) :
    Tendsto (fun s : ℝ => ∑' k : ℕ, E k * ((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-(s : ℂ))
        - (((k : ℝ) + 2 : ℝ) : ℂ) ^ (-(s : ℂ))))
      (𝓝[>] 1) (𝓝 (∑' k : ℕ, E k * ((((k : ℝ) + 1 : ℝ) : ℂ)⁻¹
        - (((k : ℝ) + 2 : ℝ) : ℂ)⁻¹))) := by
  refine tendsto_tsum_of_dominated_convergence hsum (fun k => ?_) ?_
  · have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    exact (((tendsto_cpow_neg_ofReal h1).sub (tendsto_cpow_neg_ofReal h2)).const_mul (E k))
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))] with s hs hslt k
    have hs1 : (1 : ℝ) ≤ s := le_of_lt hs
    have hs2 : s ≤ 2 := le_of_lt hslt
    rw [norm_mul]
    refine le_trans ?_ (hb k)
    exact mul_le_mul_of_nonneg_left (norm_cpow_increment_le k hs1 hs2) (norm_nonneg _)

end

end RHTower
