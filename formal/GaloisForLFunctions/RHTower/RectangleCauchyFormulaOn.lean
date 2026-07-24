import GaloisForLFunctions.RHTower.RectangleCauchyFormula

/-!
# Cauchy's integral formula on a rectangle, relative form

`rectIntegral_cauchyFormula_entire` generalized from entire `g` to `g`
analytic on any set containing the closed rectangle: the boundary
integral of `g(z)/(z-p)` is `2πi·g(p)` for `p` strictly inside.  The
divided difference `dslope g p` is analytic on the same set, so its
boundary integral vanishes and only the winding of the bare kernel
remains.
-/

noncomputable section

namespace RHTower

open Complex Set

/-- **Cauchy's integral formula on a rectangle, relative form.** -/
theorem rectIntegral_cauchyFormula_analyticOnNhd
    {g : ℂ → ℂ} {U : Set ℂ} {p z₁ z₂ : ℂ}
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hg : AnalyticOnNhd ℂ g U)
    (hre₁ : z₁.re < p.re) (hre₂ : p.re < z₂.re)
    (him₁ : z₁.im < p.im) (him₂ : p.im < z₂.im) :
    rectIntegral (fun z => g z * (z - p)⁻¹) z₁ z₂ =
      2 * Real.pi * I * g p := by
  have hedge_re : ∀ x y : ℝ, ((x : ℂ) + (y : ℂ) * I).re = x := by
    intro x y
    simp
  have hedge_im : ∀ x y : ℝ, ((x : ℂ) + (y : ℂ) * I).im = y := by
    intro x y
    simp
  have hpU : p ∈ U := by
    apply hsub
    rw [Complex.mem_reProdIm, uIcc_of_le (by linarith : z₁.re ≤ z₂.re),
      uIcc_of_le (by linarith : z₁.im ≤ z₂.im)]
    exact ⟨⟨hre₁.le, hre₂.le⟩, ⟨him₁.le, him₂.le⟩⟩
  -- membership of the four edges in `U`
  have hmemb : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₁.im * I) ∈ U := by
    intro x hx
    exact hsub (Complex.mem_reProdIm.2
      ⟨by rw [hedge_re]; exact hx, by rw [hedge_im]; exact left_mem_uIcc⟩)
  have hmemt : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₂.im * I) ∈ U := by
    intro x hx
    exact hsub (Complex.mem_reProdIm.2
      ⟨by rw [hedge_re]; exact hx, by rw [hedge_im]; exact right_mem_uIcc⟩)
  have hmemr : ∀ y ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + y * I) ∈ U := by
    intro y hy
    exact hsub (Complex.mem_reProdIm.2
      ⟨by rw [hedge_re]; exact right_mem_uIcc, by rw [hedge_im]; exact hy⟩)
  have hmeml : ∀ y ∈ uIcc z₁.im z₂.im, ((z₁.re : ℂ) + y * I) ∈ U := by
    intro y hy
    exact hsub (Complex.mem_reProdIm.2
      ⟨by rw [hedge_re]; exact left_mem_uIcc, by rw [hedge_im]; exact hy⟩)
  set q : ℂ → ℂ := dslope g p with hqdef
  have hq : AnalyticOnNhd ℂ q U := fun z hz =>
    analyticAt_dslope_of_analyticAt (hg p hpU) (hg z hz)
  have hqzero : rectIntegral q z₁ z₂ = 0 :=
    rectIntegral_eq_zero_of_analyticOnNhd hsub hq
  -- the four edge points avoid `p`
  have hbot_ne : ∀ x : ℝ, ((x : ℂ) + z₁.im * I) - p ≠ 0 := by
    intro x hzero
    have him := congrArg Complex.im (sub_eq_zero.mp hzero)
    rw [hedge_im] at him
    linarith
  have htop_ne : ∀ x : ℝ, ((x : ℂ) + z₂.im * I) - p ≠ 0 := by
    intro x hzero
    have him := congrArg Complex.im (sub_eq_zero.mp hzero)
    rw [hedge_im] at him
    linarith
  have hright_ne : ∀ y : ℝ, ((z₂.re : ℂ) + y * I) - p ≠ 0 := by
    intro y hzero
    have hre := congrArg Complex.re (sub_eq_zero.mp hzero)
    rw [hedge_re] at hre
    linarith
  have hleft_ne : ∀ y : ℝ, ((z₁.re : ℂ) + y * I) - p ≠ 0 := by
    intro y hzero
    have hre := congrArg Complex.re (sub_eq_zero.mp hzero)
    rw [hedge_re] at hre
    linarith
  -- kernel edge integrability
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
  -- dslope edge integrability, via analyticity on `U`
  have hqb : IntervalIntegrable
      (fun x : ℝ => q ((x : ℂ) + z₁.im * I))
      MeasureTheory.volume z₁.re z₂.re := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact (ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + z₁.im * I)
      (x := x) ((hq _ (hmemb x hx)).continuousAt)
      ((by fun_prop : Continuous fun x : ℝ =>
        (x : ℂ) + z₁.im * I).continuousAt)).continuousWithinAt
  have hqt : IntervalIntegrable
      (fun x : ℝ => q ((x : ℂ) + z₂.im * I))
      MeasureTheory.volume z₁.re z₂.re := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact (ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + z₂.im * I)
      (x := x) ((hq _ (hmemt x hx)).continuousAt)
      ((by fun_prop : Continuous fun x : ℝ =>
        (x : ℂ) + z₂.im * I).continuousAt)).continuousWithinAt
  have hqr : IntervalIntegrable
      (fun y : ℝ => q ((z₂.re : ℂ) + y * I))
      MeasureTheory.volume z₁.im z₂.im := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    exact (ContinuousAt.comp (f := fun y : ℝ => (z₂.re : ℂ) + y * I)
      (x := y) ((hq _ (hmemr y hy)).continuousAt)
      ((by fun_prop : Continuous fun y : ℝ =>
        (z₂.re : ℂ) + y * I).continuousAt)).continuousWithinAt
  have hql : IntervalIntegrable
      (fun y : ℝ => q ((z₁.re : ℂ) + y * I))
      MeasureTheory.volume z₁.im z₂.im := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    exact (ContinuousAt.comp (f := fun y : ℝ => (z₁.re : ℂ) + y * I)
      (x := y) ((hq _ (hmeml y hy)).continuousAt)
      ((by fun_prop : Continuous fun y : ℝ =>
        (z₁.re : ℂ) + y * I).continuousAt)).continuousWithinAt
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
      rw [hqdef]
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

end RHTower
