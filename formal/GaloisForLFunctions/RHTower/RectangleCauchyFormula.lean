import GaloisForLFunctions.RHTower.RectangleResidue
import GaloisForLFunctions.RHTower.CarrierSlope

/-!
# Cauchy's integral formula on a rectangle

The rectangle residue infrastructure evaluates the bare Cauchy kernel and annihilates functions
analytic on a neighbourhood of the closed rectangle.  This module combines those two facts with
the removable divided difference `dslope g p`.  For an entire function `g`, its value at an
interior point `p` is therefore recovered exactly from the rectangle boundary integral of
`g(z)/(z-p)`.
-/

open Complex intervalIntegral Set

namespace RHTower

noncomputable section

private theorem edgePoint_re (x c : ℝ) :
    ((x : ℂ) + (c : ℂ) * I).re = x := by simp

private theorem edgePoint_im (x c : ℝ) :
    ((x : ℂ) + (c : ℂ) * I).im = c := by simp

/-- **Cauchy's integral formula on a rectangle.**  If `g` is entire and `p` lies strictly inside
the rectangle with opposite corners `z₁,z₂`, then the positively oriented boundary integral of
`g(z)/(z-p)` is `2πi g(p)`.

The proof writes `g z = g p + (z-p) dslope g p z`.  The divided difference is entire, including
at `p`, so its rectangle integral vanishes; the remaining bare Cauchy kernel has winding one. -/
theorem rectIntegral_cauchyFormula_entire
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    {p z₁ z₂ : ℂ}
    (hre₁ : z₁.re < p.re) (hre₂ : p.re < z₂.re)
    (him₁ : z₁.im < p.im) (him₂ : p.im < z₂.im) :
    rectIntegral (fun z => g z * (z - p)⁻¹) z₁ z₂ =
      2 * Real.pi * I * g p := by
  let q : ℂ → ℂ := dslope g p
  have hq : AnalyticOnNhd ℂ q Set.univ := by
    intro z hz
    exact analyticAt_dslope_of_analyticAt (hg p (Set.mem_univ p))
      (hg z (Set.mem_univ z))
  have hqzero : rectIntegral q z₁ z₂ = 0 :=
    rectIntegral_eq_zero_of_analyticOnNhd (U := Set.univ) (by simp) hq
  have hqcont : Continuous q := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (hq z (Set.mem_univ z)).continuousAt
  have hbot_ne : ∀ x : ℝ, ((x : ℂ) + z₁.im * I) - p ≠ 0 := by
    intro x hzero
    have him := congrArg Complex.im (sub_eq_zero.mp hzero)
    rw [edgePoint_im] at him
    linarith
  have htop_ne : ∀ x : ℝ, ((x : ℂ) + z₂.im * I) - p ≠ 0 := by
    intro x hzero
    have him := congrArg Complex.im (sub_eq_zero.mp hzero)
    rw [edgePoint_im] at him
    linarith
  have hright_ne : ∀ y : ℝ, ((z₂.re : ℂ) + y * I) - p ≠ 0 := by
    intro y hzero
    have hre := congrArg Complex.re (sub_eq_zero.mp hzero)
    rw [edgePoint_re] at hre
    linarith
  have hleft_ne : ∀ y : ℝ, ((z₁.re : ℂ) + y * I) - p ≠ 0 := by
    intro y hzero
    have hre := congrArg Complex.re (sub_eq_zero.mp hzero)
    rw [edgePoint_re] at hre
    linarith
  have hkb : IntervalIntegrable
      (fun x : ℝ => (((x : ℂ) + z₁.im * I) - p)⁻¹)
      MeasureTheory.volume z₁.re z₂.re := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous fun x : ℝ =>
      ((x : ℂ) + z₁.im * I) - p).inv₀ hbot_ne
  have hkt : IntervalIntegrable
      (fun x : ℝ => (((x : ℂ) + z₂.im * I) - p)⁻¹)
      MeasureTheory.volume z₁.re z₂.re := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous fun x : ℝ =>
      ((x : ℂ) + z₂.im * I) - p).inv₀ htop_ne
  have hkr : IntervalIntegrable
      (fun y : ℝ => (((z₂.re : ℂ) + y * I) - p)⁻¹)
      MeasureTheory.volume z₁.im z₂.im := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous fun y : ℝ =>
      ((z₂.re : ℂ) + y * I) - p).inv₀ hright_ne
  have hkl : IntervalIntegrable
      (fun y : ℝ => (((z₁.re : ℂ) + y * I) - p)⁻¹)
      MeasureTheory.volume z₁.im z₂.im := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous fun y : ℝ =>
      ((z₁.re : ℂ) + y * I) - p).inv₀ hleft_ne
  have hqb : IntervalIntegrable
      (fun x : ℝ => q ((x : ℂ) + z₁.im * I))
      MeasureTheory.volume z₁.re z₂.re :=
    (hqcont.comp (by fun_prop)).intervalIntegrable _ _
  have hqt : IntervalIntegrable
      (fun x : ℝ => q ((x : ℂ) + z₂.im * I))
      MeasureTheory.volume z₁.re z₂.re :=
    (hqcont.comp (by fun_prop)).intervalIntegrable _ _
  have hqr : IntervalIntegrable
      (fun y : ℝ => q ((z₂.re : ℂ) + y * I))
      MeasureTheory.volume z₁.im z₂.im :=
    (hqcont.comp (by fun_prop)).intervalIntegrable _ _
  have hql : IntervalIntegrable
      (fun y : ℝ => q ((z₁.re : ℂ) + y * I))
      MeasureTheory.volume z₁.im z₂.im :=
    (hqcont.comp (by fun_prop)).intervalIntegrable _ _
  have hsum := rectIntegral_add
    (g₁ := fun z => g p * (z - p)⁻¹) (g₂ := q)
    (z₁ := z₁) (z₂ := z₂)
    (hkb.const_mul (g p)) hqb (hkt.const_mul (g p)) hqt
    (hkr.const_mul (g p)) hqr (hkl.const_mul (g p)) hql
  have hcongr :
      rectIntegral (fun z => g z * (z - p)⁻¹) z₁ z₂ =
        rectIntegral (fun z => g p * (z - p)⁻¹ + q z) z₁ z₂ := by
    apply rectIntegral_congr (S := {z : ℂ | z ≠ p})
    · intro z hz
      have hne : z ≠ p := hz
      have hslope := sub_smul_dslope g p z
      simp only [smul_eq_mul] at hslope
      dsimp only [q]
      calc
        g z * (z - p)⁻¹ =
            (g p + (z - p) * dslope g p z) * (z - p)⁻¹ := by
          rw [hslope]
          ring
        _ = g p * (z - p)⁻¹ + dslope g p z := by
          field_simp [sub_ne_zero.mpr hne]
    · intro x hx
      simp only [Set.mem_setOf_eq]
      exact sub_ne_zero.mp (hbot_ne x)
    · intro x hx
      simp only [Set.mem_setOf_eq]
      exact sub_ne_zero.mp (htop_ne x)
    · intro y hy
      simp only [Set.mem_setOf_eq]
      exact sub_ne_zero.mp (hright_ne y)
    · intro y hy
      simp only [Set.mem_setOf_eq]
      exact sub_ne_zero.mp (hleft_ne y)
  rw [hcongr, hsum, rectIntegral_const_mul,
    rectIntegral_cauchyKernel hre₁ hre₂ him₁ him₂, hqzero]
  ring

end

end RHTower
