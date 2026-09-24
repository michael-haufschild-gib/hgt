import GaloisForLFunctions.RHTower.EstermannMellinNumerator
import GaloisForLFunctions.HTGeometry.RectangleDerivativeFormula

/-!
# The rectangle identity for the Estermann Mellin integrand

On the rectangle `[½, 2] × [-T, T]` the smoothed Perron integrand `x^{-s} Γ(s) D(s, a/q)` agrees
with `N(s)/(s-1)²` for the holomorphic numerator `N` of `EstermannMellinNumerator`, and `s = 1` is
strictly inside.  Cauchy's derivative formula on a rectangle therefore evaluates the boundary
integral exactly:

```text
∮_{∂[½,2]×[-T,T]} x^{-s} Γ(s) D(s, a/q) ds = 2πi · N'(1) = 2πi (γ - log x - 2 log q)/(q x).
```

Letting `T → ∞` and discarding the horizontal edges — which decay like `T^N e^{-π T/2}` because
the Gamma factor beats the convexity bound for `D` — turns this into the contour shift.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The smoothed Perron integrand. -/
def estermannMellinIntegrand (q : ℕ) [NeZero q] (a : ZMod q) (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ (-s) * Complex.Gamma s * estermannZeta q a s

/-- **The exact rectangle identity.** -/
theorem rectIntegral_estermannMellinIntegrand (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) {x T : ℝ}
    (hx : 0 < x) (hT : 0 < T) :
    rectIntegral (estermannMellinIntegrand q ((a : ZMod q)) x)
        ((1 / 2 : ℂ) - (T : ℂ) * I) ((2 : ℂ) + (T : ℂ) * I)
      = 2 * Real.pi * I * deriv (estermannMellinNumerator q ((a : ZMod q)) x) 1 := by
  set z₁ : ℂ := (1 / 2 : ℂ) - (T : ℂ) * I with hz₁
  set z₂ : ℂ := (2 : ℂ) + (T : ℂ) * I with hz₂
  have hz₁re : z₁.re = 1 / 2 := by rw [hz₁]; simp
  have hz₁im : z₁.im = -T := by rw [hz₁]; simp
  have hz₂re : z₂.re = 2 := by rw [hz₂]; simp
  have hz₂im : z₂.im = T := by rw [hz₂]; simp
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ {z : ℂ | 0 < z.re} := by
    intro z hz
    have hre : z.re ∈ uIcc z₁.re z₂.re := (Complex.mem_reProdIm.mp hz).1
    rw [hz₁re, hz₂re, Set.uIcc_of_le (by norm_num : (1 : ℝ) / 2 ≤ 2)] at hre
    exact lt_of_lt_of_le (by norm_num) hre.1
  have hbot : ∀ u ∈ uIcc z₁.re z₂.re, ((u : ℂ) + z₁.im * I) ∈ {z : ℂ | z ≠ 1} := by
    intro u _ heq
    have him := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_add, mul_one, Complex.one_im] at him
    rw [hz₁im] at him
    linarith
  have htop : ∀ u ∈ uIcc z₁.re z₂.re, ((u : ℂ) + z₂.im * I) ∈ {z : ℂ | z ≠ 1} := by
    intro u _ heq
    have him := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_add, mul_one, Complex.one_im] at him
    rw [hz₂im] at him
    linarith
  have hright : ∀ v ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + v * I) ∈ {z : ℂ | z ≠ 1} := by
    intro v _ heq
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, Complex.one_re] at hre
    rw [hz₂re] at hre
    norm_num at hre
  have hleft : ∀ v ∈ uIcc z₁.im z₂.im, ((z₁.re : ℂ) + v * I) ∈ {z : ℂ | z ≠ 1} := by
    intro v _ heq
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, Complex.one_re] at hre
    rw [hz₁re] at hre
    norm_num at hre
  have hcongr : rectIntegral (estermannMellinIntegrand q ((a : ZMod q)) x) z₁ z₂
      = rectIntegral
          (fun s => estermannMellinNumerator q ((a : ZMod q)) x s / (s - 1) ^ 2) z₁ z₂ := by
    refine rectIntegral_congr (S := {z : ℂ | z ≠ 1}) (fun z hz => ?_) hbot htop hright hleft
    exact (estermannMellinNumerator_div q a x hz).symm
  rw [hcongr]
  refine rectIntegral_div_sub_sq_eq_deriv hU
    (differentiableOn_estermannMellinNumerator q a hx) (by simp)
    hsub ?_ ?_ ?_ ?_
  · rw [hz₁re]; norm_num
  · rw [hz₂re]; norm_num
  · rw [hz₁im]; simp; linarith
  · rw [hz₂im]; simp; linarith

end

end RHTower
