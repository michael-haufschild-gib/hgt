import GaloisForLFunctions.RHTower.XiCosineShiftAlmostEveryHeight
import GaloisForLFunctions.RHTower.XiLogDerivVinogradovKorobovPositive

/-!
# The Vinogradov–Korobov lossless window of the cosine producer

A non-real zero `z` of `cos(hD)Ξ` needs a zero `ρ` of `ζ` with `Re ρ − ½ > h` and
`|Im ρ − Re z| < ½` (`exists_zetaZero_of_cosineShift_nonreal`). The Vinogradov–Korobov region bounds
`|Re ρ − ½| ≤ ½ − w(|Im ρ|)` above a height `γ₁`, where
`w(T) = (log T)^{−2/3}(log log T)^{−5/3}/10⁸` (`abs_re_sub_half_le_vinogradovKorobov`), and `w`
decreases (`vkHadamardWidth_antitoneOn`). Hence:

* `cosineShift_zero_real_of_vinogradovKorobov`: for every `h > 0`, every zero `z` of `cos(hD)Ξ` with
  `|Re z| ≥ γ₁ + ½` and `½ − h ≤ w(|Re z| + ½)` is real.

So at height `X` the producer is lossless for every depth `h ≥ ½ − w(X + ½)`. Equivalently, at depth
`h` it is lossless up to the height where `w` falls below `½ − h`, a window of size
`exp(c(½ − h)^{−3/2 + o(1)})` instead of the de la Vallée Poussin size `exp(c/(½ − h))`.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- The Vinogradov–Korobov width decreases above `e^e`. -/
theorem vkHadamardWidth_antitoneOn : AntitoneOn vkHadamardWidth (Ici (Real.exp (Real.exp 1))) := by
  intro S hS T hT hST
  simp only [mem_Ici] at hS hT
  have he1 : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hS0 : 0 < S := lt_of_lt_of_le (Real.exp_pos _) hS
  have hlogS : Real.exp 1 ≤ Real.log S := by
    rw [Real.le_log_iff_exp_le hS0]; exact hS
  have hlogST : Real.log S ≤ Real.log T := Real.log_le_log hS0 hST
  have hLS : 0 < Real.log S := lt_of_lt_of_le (Real.exp_pos _) hlogS
  have hllS : 1 ≤ Real.log (Real.log S) := by
    rw [Real.le_log_iff_exp_le hLS]; exact hlogS
  have hllST : Real.log (Real.log S) ≤ Real.log (Real.log T) := Real.log_le_log hLS hlogST
  unfold vkHadamardWidth
  have h1 : Real.log T ^ (-(2 : ℝ) / 3) ≤ Real.log S ^ (-(2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hLS hlogST (by norm_num)
  have h2 : Real.log (Real.log T) ^ (-(5 : ℝ) / 3) ≤ Real.log (Real.log S) ^ (-(5 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hllST (by norm_num)
  have h3 : 0 ≤ Real.log (Real.log T) ^ (-(5 : ℝ) / 3) :=
    Real.rpow_nonneg (by linarith) _
  have h4 : 0 ≤ Real.log S ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg hLS.le _
  have := mul_le_mul h1 h2 h3 h4
  exact div_le_div_of_nonneg_right this (by norm_num)

/-- **Vinogradov–Korobov lossless window.** -/
theorem cosineShift_zero_real_of_vinogradovKorobov :
    ∃ γ₁ : ℝ, Real.exp (Real.exp 1) ≤ γ₁ ∧ ∀ h : ℝ, 0 < h → ∀ z : ℂ,
      (XiC (z + h * I) + XiC (z - h * I)) / 2 = 0 → γ₁ + 1 / 2 ≤ |z.re| →
        1 / 2 - h ≤ vkHadamardWidth (|z.re| + 1 / 2) → z.im = 0 := by
  obtain ⟨γ₁, hγ₁, hvk⟩ := abs_re_sub_half_le_vinogradovKorobov
  refine ⟨γ₁, hγ₁, fun h hh z h0 hre hw => ?_⟩
  by_contra hz
  obtain ⟨ρ, hζ, hlo, hρ1, hclose⟩ := exists_zetaZero_of_cosineShift_nonreal hh hz h0
  have hρ0 : 0 < ρ.re := by linarith
  have hγ : γ₁ ≤ |ρ.im| := by
    have := abs_sub_abs_le_abs_sub z.re ρ.im
    rw [abs_sub_comm] at hclose
    linarith
  have hdisp := hvk ρ hρ0 hρ1 hζ hγ
  have hdeep : h < |ρ.re - 1 / 2| := by rw [abs_of_pos (by linarith)]; linarith
  have hupper : |ρ.im| ≤ |z.re| + 1 / 2 := by
    have := abs_sub_abs_le_abs_sub ρ.im z.re
    linarith
  have hanti := vkHadamardWidth_antitoneOn (show |ρ.im| ∈ Ici (Real.exp (Real.exp 1)) from
    le_trans hγ₁ hγ) (show |z.re| + 1 / 2 ∈ Ici (Real.exp (Real.exp 1)) by
      simp only [mem_Ici]; linarith) hupper
  linarith

end

end RHTower
