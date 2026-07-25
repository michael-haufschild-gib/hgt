import GaloisForLFunctions.RHTower.RectangleResidue

/-!
# A two-pole rectangle residue theorem

If a function agrees on the punctured plane with two scalar Cauchy kernels plus an entire
remainder, its positively oriented rectangle integral is `2πi` times the sum of the two scalar
residues whenever both poles lie strictly inside.
-/

noncomputable section

namespace RHTower

open Complex intervalIntegral Set

theorem rectIntegral_eq_two_pole_residues
    {F R : ℂ → ℂ} {p q rp rq z₁ z₂ : ℂ}
    (hp1 : z₁.re < p.re) (hp2 : p.re < z₂.re)
    (hp3 : z₁.im < p.im) (hp4 : p.im < z₂.im)
    (hq1 : z₁.re < q.re) (hq2 : q.re < z₂.re)
    (hq3 : z₁.im < q.im) (hq4 : q.im < z₂.im)
    (hR : Differentiable ℂ R)
    (hdecomp : ∀ z, z ≠ p → z ≠ q →
      F z = rp * (z - p)⁻¹ + (rq * (z - q)⁻¹ + R z)) :
    rectIntegral F z₁ z₂ = 2 * Real.pi * I * (rp + rq) := by
  let S : Set ℂ := {z | z ≠ p ∧ z ≠ q}
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      ((x : ℂ) + z₁.im * I) ∈ S := by
    intro x hx
    constructor
    · intro heq
      have him := congrArg Complex.im heq
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
      linarith
    · intro heq
      have him := congrArg Complex.im heq
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
      linarith
  have htop : ∀ x ∈ uIcc z₁.re z₂.re,
      ((x : ℂ) + z₂.im * I) ∈ S := by
    intro x hx
    constructor
    · intro heq
      have him := congrArg Complex.im heq
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
      linarith
    · intro heq
      have him := congrArg Complex.im heq
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
      linarith
  have hright : ∀ y ∈ uIcc z₁.im z₂.im,
      ((z₂.re : ℂ) + y * I) ∈ S := by
    intro y hy
    constructor
    · intro heq
      have hre := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
      linarith
    · intro heq
      have hre := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
      linarith
  have hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      ((z₁.re : ℂ) + y * I) ∈ S := by
    intro y hy
    constructor
    · intro heq
      have hre := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
      linarith
    · intro heq
      have hre := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
      linarith
  have hkernel : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt →
      ∀ (c pole : ℂ), (∀ t ∈ uIcc a b, pt t ≠ pole) →
        IntervalIntegrable (fun t => c * (pt t - pole)⁻¹)
          MeasureTheory.volume a b := by
    intro a b pt hpt c pole hne
    exact (continuousOn_const.mul
      ((hpt.continuousOn.sub continuousOn_const).inv₀
        (fun t ht => sub_ne_zero.mpr (hne t ht)))).intervalIntegrable
  have hregular : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt →
      IntervalIntegrable (fun t => R (pt t)) MeasureTheory.volume a b := by
    intro a b pt hpt
    exact (hR.continuous.comp hpt).intervalIntegrable a b
  rw [rectIntegral_congr
    (fun z hz => hdecomp z hz.1 hz.2) hbot htop hright hleft,
    rectIntegral_add
      (hkernel _ (by fun_prop) rp p (fun x hx => (hbot x hx).1))
      ((hkernel _ (by fun_prop) rq q (fun x hx => (hbot x hx).2)).add
        (hregular _ (by fun_prop)))
      (hkernel _ (by fun_prop) rp p (fun x hx => (htop x hx).1))
      ((hkernel _ (by fun_prop) rq q (fun x hx => (htop x hx).2)).add
        (hregular _ (by fun_prop)))
      (hkernel _ (by fun_prop) rp p (fun y hy => (hright y hy).1))
      ((hkernel _ (by fun_prop) rq q (fun y hy => (hright y hy).2)).add
        (hregular _ (by fun_prop)))
      (hkernel _ (by fun_prop) rp p (fun y hy => (hleft y hy).1))
      ((hkernel _ (by fun_prop) rq q (fun y hy => (hleft y hy).2)).add
        (hregular _ (by fun_prop))),
    rectIntegral_add
      (hkernel _ (by fun_prop) rq q (fun x hx => (hbot x hx).2))
      (hregular _ (by fun_prop))
      (hkernel _ (by fun_prop) rq q (fun x hx => (htop x hx).2))
      (hregular _ (by fun_prop))
      (hkernel _ (by fun_prop) rq q (fun y hy => (hright y hy).2))
      (hregular _ (by fun_prop))
      (hkernel _ (by fun_prop) rq q (fun y hy => (hleft y hy).2))
      (hregular _ (by fun_prop)),
    rectIntegral_const_mul, rectIntegral_cauchyKernel hp1 hp2 hp3 hp4,
    rectIntegral_const_mul, rectIntegral_cauchyKernel hq1 hq2 hq3 hq4,
    rectIntegral_eq_zero_of_analyticOnNhd
      (U := Set.univ) (fun _ _ => Set.mem_univ _)
      (hR.differentiableOn.analyticOnNhd isOpen_univ)]
  ring

end RHTower
