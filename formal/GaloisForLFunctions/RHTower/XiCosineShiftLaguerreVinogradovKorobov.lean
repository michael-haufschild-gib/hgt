import GaloisForLFunctions.RHTower.XiCosineShiftLaguerreTraces
import GaloisForLFunctions.RHTower.XiCosineShiftVinogradovKorobovWindow

/-!
# The Laguerre criterion in the Vinogradov–Korobov region

`Q(s) = (Im ξ'(s))² + Re ξ(s) · Re ξ''(s)`, and RH is `Q > 0` on `½ < Re s < 1`
(`riemannHypothesis_iff_strict_laguerre_strip`).

**Theorem** (`exists_laguerre_nonneg_vinogradovKorobov`). There is `T₀` such that `Q(s) ≥ 0` for
every `s` with `|Im s| ≥ T₀` and `Re s ≥ 1 − w(|Im s| + 1)`. Here `w(T) =
(log T)^{−2/3}(log log T)^{−5/3}/10⁸` is the Vinogradov–Korobov width.

This is the first-Laguerre analogue of the Hadamard positivity `Re(ξ'/ξ) ≥ 0` in the same region
(`exists_re_logDeriv_xi_nonneg_vinogradovKorobov`).

**Proof.** Put `h = Re s − ½` and `x = Im s`. By the trace law (`laguerre_nonneg_of_trace`) it
suffices that every zero `w` of `Ξ` with `(Im w)² > h²` has `4((Im w)² − h²) ≤ (x − Re w)²`. A zero
at horizontal distance at least `1` satisfies this because `(Im w)² ≤ ¼`. A nearby zero has
ordinate within `1` of `x`, so the Vinogradov–Korobov displacement bound gives
`|Im w| ≤ ½ − w(|Re w|) ≤ ½ − w(|x| + 1) ≤ h`, and no such zero exists.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

theorem vkHadamardWidth_le_quarter {T : ℝ} (hT : Real.exp (Real.exp 1) ≤ T) :
    vkHadamardWidth T ≤ 1 / 4 := by
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  have hL : Real.exp 1 ≤ Real.log T := by
    rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hT
  have hL1 : 1 ≤ Real.log T := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hL
  have hLL : 1 ≤ Real.log (Real.log T) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hL
  have h1 : Real.log T ^ (-(2 : ℝ) / 3) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have h2 : Real.log (Real.log T) ^ (-(5 : ℝ) / 3) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hLL (by norm_num)
  have h1' : 0 ≤ Real.log T ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  have h2' : 0 ≤ Real.log (Real.log T) ^ (-(5 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  unfold vkHadamardWidth
  have : Real.log T ^ (-(2 : ℝ) / 3) * Real.log (Real.log T) ^ (-(5 : ℝ) / 3) ≤ 1 :=
    mul_le_one₀ h1 h2' h2
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- **`Q ≥ 0` in the Vinogradov–Korobov region.** -/
theorem exists_laguerre_nonneg_vinogradovKorobov :
    ∃ T₀ : ℝ, ∀ s : ℂ, T₀ ≤ |s.im| → 1 - vkHadamardWidth (|s.im| + 1) ≤ s.re →
      0 ≤ (deriv xi s).im ^ 2 + (xi s).re * (deriv (deriv xi) s).re := by
  obtain ⟨γ₁, hγ₁e, hdisp⟩ := abs_re_sub_half_le_vinogradovKorobov
  refine ⟨γ₁ + 1, fun s hs hσ => ?_⟩
  set h : ℝ := s.re - 1 / 2 with hh
  set x : ℝ := s.im with hx
  have hγ₁0 : 0 < γ₁ := lt_of_lt_of_le (Real.exp_pos _) hγ₁e
  have hx1 : Real.exp (Real.exp 1) ≤ |x| + 1 := by linarith
  have hwhalf := vkHadamardWidth_le_quarter hx1
  have hwpos := vkHadamardWidth_pos hx1
  have hhpos : 0 < h := by rw [hh]; linarith
  have hhalf : 1 / 2 - vkHadamardWidth (|x| + 1) ≤ h := by rw [hh]; linarith
  have key := laguerre_nonneg_of_trace (h := h) (x := x) hhpos (fun w hw hwh => ?_)
  · have hs' : (((1 / 2 + h : ℝ) : ℂ) + (x : ℂ) * I) = s := by
      apply Complex.ext <;> simp [hh, hx]
    simp only [foldF, foldFx, foldFxx, hs'] at key
    linarith
  -- the trace condition
  have him2 : w.im ^ 2 ≤ 1 / 4 := by
    have h0 : DeBruijn.cosTransform riemannKernelReal w = 0 := by
      rw [DeBruijn.cosTransform_riemannKernel_eq_XiC]; exact hw
    exact DeBruijn.riemannKernel_zeros_im_sq_le w h0
  by_cases hfar : 1 ≤ |x - w.re|
  · have : 1 ≤ (x - w.re) ^ 2 := by
      rw [← sq_abs]; nlinarith
    nlinarith [sq_nonneg h]
  · exfalso
    push Not at hfar
    -- the zero `ρ = ½ + iw` of `ζ`
    set ρ : ℂ := 1 / 2 + I * w with hρ
    have hρ0 : xi ρ = 0 := by
      have e : XiC w = xi ρ := by rw [hρ, XiC, mul_comm]
      rw [← e]; exact hw
    have hρre : ρ.re = 1 / 2 - w.im := by simp [hρ]; ring
    have hρim : ρ.im = w.re := by simp [hρ]
    have habs : |w.im| ≤ 1 / 2 := by
      rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
    have hρpos : 0 < ρ.re := by
      rw [hρre]
      have hlt : |w.im| < 1 / 2 := by
        have := abs_im_lt_half_of_XiC_eq_zero hw
        exact this
      linarith [le_abs_self w.im]
    have hρlt : ρ.re < 1 := by
      rw [hρre]
      have hlt : |w.im| < 1 / 2 := abs_im_lt_half_of_XiC_eq_zero hw
      linarith [neg_abs_le w.im]
    have hρ1 : ρ ≠ 1 := fun e => by rw [e] at hρlt; simp at hρlt
    have hζ : riemannZeta ρ = 0 := (xi_eq_zero_iff hρpos hρ1).mp hρ0
    have hfar' := abs_lt.mp hfar
    have hγ : γ₁ ≤ |ρ.im| := by
      rw [hρim]
      have : |x| - 1 ≤ |w.re| := by
        have := abs_sub_abs_le_abs_sub x w.re
        linarith [hfar'.1, hfar'.2, abs_lt.mpr hfar']
      linarith
    have hd := hdisp ρ hρpos hρlt hζ hγ
    rw [hρre, hρim, show (1 / 2 - w.im - 1 / 2 : ℝ) = -w.im by ring, abs_neg] at hd
    -- monotonicity of the width
    have hle : |w.re| ≤ |x| + 1 := by
      have := abs_sub_abs_le_abs_sub w.re x
      rw [abs_sub_comm w.re x] at this
      linarith [abs_lt.mpr hfar']
    have hwre : γ₁ ≤ |w.re| := by rw [← hρim]; exact hγ
    have hmono : vkHadamardWidth (|x| + 1) ≤ vkHadamardWidth |w.re| :=
      vkHadamardWidth_antitoneOn (by simp only [mem_Ici]; linarith)
        (by simp only [mem_Ici]; linarith) hle
    have : |w.im| ≤ h := by linarith
    have hsq : w.im ^ 2 ≤ h ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    linarith

end

end RHTower
