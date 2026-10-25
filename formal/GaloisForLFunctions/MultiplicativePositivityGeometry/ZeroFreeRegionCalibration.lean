import GaloisForLFunctions.MultiplicativePositivityGeometry.GrowthToForcing
import GaloisForLFunctions.RHTower.ZeroFreeRegionFromFour

/-!
# Calibration: the de la Vallée Poussin region as an instance of the growth law

For a zero `β + iγ` with `γ ≥ 4`, the corpus inequality `RHTower.dlvp_half` gives, for every
`1 < σ ≤ 2`,
`4/(σ − β) ≤ 3/(σ − 1) + G_γ`, where `G_γ = (5/2) log γ + C` and `C = dlvpHalfConstant 1`.
This is the input `(A, B, G) = (3, 4, G_γ)` of the growth-to-forcing law. The optimal witness
`δ* = √(3η/G_γ)` lies in `(0, 1]`, so the law yields the region `β ≤ 1 − (2 − √3)²/G_γ`
(`xiZero_re_le_dlvp`).

The region is the best this input can give: for `η ≥ (2 − √3)²/G` the inequality holds at every
`δ > 0` (`dlvp_input_consistent`).
-/

open Real

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

private theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- **dlVP from the growth law.** Every Xi zero `β + iγ` with `γ ≥ 4` has
`β ≤ 1 − (2 − √3)² / ((5/2) log γ + C)`. -/
theorem xiZero_re_le_dlvp (q₀ : RHTower.XiZeroCopy) (hγ : 4 ≤ (q₀.1 : ℂ).im) :
    (q₀.1 : ℂ).re ≤ 1 - (2 - Real.sqrt 3) ^ 2 /
      (5 / 2 * Real.log ((q₀.1 : ℂ).im) + RHTower.dlvpHalfConstant 1) := by
  set β := (q₀.1 : ℂ).re with hβdef
  set G := 5 / 2 * Real.log ((q₀.1 : ℂ).im) + RHTower.dlvpHalfConstant 1 with hGdef
  have hlog : 0 < Real.log ((q₀.1 : ℂ).im) := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hG2 : 2 < G := by
    rw [hGdef]
    unfold RHTower.dlvpHalfConstant
    linarith
  have hG : 0 < G := by linarith
  have hβ1 : β < 1 := RHTower.xiZeroCopy_re_lt_one q₀
  have hη : 0 < 1 - β := by linarith
  have hs3 : 1 < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs3' : Real.sqrt 3 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  by_contra hcon
  push Not at hcon
  have hw : 1 - β < (2 - Real.sqrt 3) ^ 2 / G := by linarith
  have hGη : Real.sqrt (G * (1 - β)) < 2 - Real.sqrt 3 := by
    rw [Real.sqrt_lt' (by linarith)]
    rw [lt_div_iff₀ hG] at hw
    linarith
  have hexcl : Real.sqrt 3 + Real.sqrt (G * (1 - β)) < Real.sqrt 4 := by
    rw [sqrt_four]
    linarith
  have hδ := exclusion_at_geometric_mean (A := 3) (B := 4) (by norm_num) (by norm_num) hG hη hexcl
  set δ := Real.sqrt 3 * Real.sqrt (G * (1 - β)) / G with hδdef
  have hδ0 : 0 < δ := by
    have : 0 < Real.sqrt (G * (1 - β)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  -- The optimal witness lies in `(0, 1]`, inside the range of `dlvp_half`.
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one hG]
    have h1 : Real.sqrt (G * (1 - β)) < 1 := by linarith
    nlinarith [Real.sqrt_nonneg (G * (1 - β))]
  have hd := RHTower.dlvp_half (fun _ h1 h2 => RHTower.neg_re_logDeriv_riemannZeta_real_le h1 h2)
    (σ := 1 + δ) (by linarith) (by linarith) q₀ hγ
  rw [show 1 + δ - (q₀.1 : ℂ).re = δ + (1 - β) by rw [hβdef]; ring,
    show 1 + δ - 1 = δ by ring] at hd
  linarith

/-- **The input is used optimally.** For `η ≥ (2 − √3)²/G` the input inequality
`4/(δ + η) ≤ 3/δ + G` holds at every `δ > 0`, so `(A, B, G) = (3, 4, G)` cannot exclude a zero at
that distance. -/
theorem dlvp_input_consistent {G η : ℝ} (hG : 0 < G) (hη : 0 < η)
    (hw : (2 - Real.sqrt 3) ^ 2 / G ≤ η) (δ : ℝ) (hδ : 0 < δ) :
    4 / (δ + η) ≤ 3 / δ + G := by
  by_contra hcon
  push Not at hcon
  have := (exclusion_iff_lt_width (A := 3) (B := 4) (by norm_num) (by norm_num) hG hη).mp
    ⟨δ, hδ, hcon⟩
  rw [sqrt_four] at this
  linarith [this.2]

end GaloisForLFunctions.MultiplicativePositivityGeometry
