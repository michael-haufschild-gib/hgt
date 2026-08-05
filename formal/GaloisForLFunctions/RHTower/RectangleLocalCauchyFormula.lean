import GaloisForLFunctions.RHTower.RectangleCauchyFormula

/-!
# Local Cauchy formula on a rectangle

`RectangleCauchyFormula` states the weighted rectangle formula for entire functions.  Mass-root
tests are holomorphic only on their natural branch strip.  The theorem below records the exact
local form: holomorphy on any neighbourhood containing the closed rectangle is sufficient.
-/

open Complex intervalIntegral Set

namespace RHTower

noncomputable section

private theorem localEdgePoint_re (x c : ℝ) :
    ((x : ℂ) + (c : ℂ) * I).re = x := by simp

private theorem localEdgePoint_im (x c : ℝ) :
    ((x : ℂ) + (c : ℂ) * I).im = c := by simp

/-- **Local Cauchy formula on a rectangle.**  Analyticity on a neighbourhood of the closed
rectangle, rather than on all of `ℂ`, recovers the value at every strict interior point. -/
theorem rectIntegral_cauchyFormula_of_analyticOnNhd
    {g : ℂ → ℂ} {p z₁ z₂ : ℂ} {U : Set ℂ}
    (hg : AnalyticOnNhd ℂ g U)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hre₁ : z₁.re < p.re) (hre₂ : p.re < z₂.re)
    (him₁ : z₁.im < p.im) (him₂ : p.im < z₂.im) :
    rectIntegral (fun z => g z * (z - p)⁻¹) z₁ z₂ =
      2 * Real.pi * I * g p := by
  have hp : p ∈ U := hsub (Complex.mem_reProdIm.mpr
    ⟨by rw [uIcc_of_le (hre₁.trans hre₂).le]; exact ⟨hre₁.le, hre₂.le⟩,
      by rw [uIcc_of_le (him₁.trans him₂).le]; exact ⟨him₁.le, him₂.le⟩⟩)
  let q : ℂ → ℂ := dslope g p
  have hq : AnalyticOnNhd ℂ q U := by
    intro z hz
    exact analyticAt_dslope_of_analyticAt (hg p hp) (hg z hz)
  have hqzero : rectIntegral q z₁ z₂ = 0 :=
    rectIntegral_eq_zero_of_analyticOnNhd hsub hq
  have hbot_mem : ∀ x ∈ uIcc z₁.re z₂.re,
      ((x : ℂ) + z₁.im * I) ∈ U := by
    intro x hx
    exact hsub (Complex.mem_reProdIm.mpr
      ⟨by rw [localEdgePoint_re]; exact hx,
        by rw [localEdgePoint_im]; exact left_mem_uIcc⟩)
  have htop_mem : ∀ x ∈ uIcc z₁.re z₂.re,
      ((x : ℂ) + z₂.im * I) ∈ U := by
    intro x hx
    exact hsub (Complex.mem_reProdIm.mpr
      ⟨by rw [localEdgePoint_re]; exact hx,
        by rw [localEdgePoint_im]; exact right_mem_uIcc⟩)
  have hright_mem : ∀ y ∈ uIcc z₁.im z₂.im,
      ((z₂.re : ℂ) + y * I) ∈ U := by
    intro y hy
    exact hsub (Complex.mem_reProdIm.mpr
      ⟨by rw [localEdgePoint_re]; exact right_mem_uIcc,
        by rw [localEdgePoint_im]; exact hy⟩)
  have hleft_mem : ∀ y ∈ uIcc z₁.im z₂.im,
      ((z₁.re : ℂ) + y * I) ∈ U := by
    intro y hy
    exact hsub (Complex.mem_reProdIm.mpr
      ⟨by rw [localEdgePoint_re]; exact left_mem_uIcc,
        by rw [localEdgePoint_im]; exact hy⟩)
  have hbot_ne : ∀ x : ℝ, ((x : ℂ) + z₁.im * I) - p ≠ 0 := by
    intro x hzero
    have him := congrArg Complex.im (sub_eq_zero.mp hzero)
    rw [localEdgePoint_im] at him
    linarith
  have htop_ne : ∀ x : ℝ, ((x : ℂ) + z₂.im * I) - p ≠ 0 := by
    intro x hzero
    have him := congrArg Complex.im (sub_eq_zero.mp hzero)
    rw [localEdgePoint_im] at him
    linarith
  have hright_ne : ∀ y : ℝ, ((z₂.re : ℂ) + y * I) - p ≠ 0 := by
    intro y hzero
    have hre := congrArg Complex.re (sub_eq_zero.mp hzero)
    rw [localEdgePoint_re] at hre
    linarith
  have hleft_ne : ∀ y : ℝ, ((z₁.re : ℂ) + y * I) - p ≠ 0 := by
    intro y hzero
    have hre := congrArg Complex.re (sub_eq_zero.mp hzero)
    rw [localEdgePoint_re] at hre
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
    (hq.continuousOn.comp (by fun_prop : ContinuousOn
      (fun x : ℝ => (x : ℂ) + z₁.im * I) (uIcc z₁.re z₂.re)) hbot_mem).intervalIntegrable
  have hqt : IntervalIntegrable
      (fun x : ℝ => q ((x : ℂ) + z₂.im * I))
      MeasureTheory.volume z₁.re z₂.re :=
    (hq.continuousOn.comp (by fun_prop : ContinuousOn
      (fun x : ℝ => (x : ℂ) + z₂.im * I) (uIcc z₁.re z₂.re)) htop_mem).intervalIntegrable
  have hqr : IntervalIntegrable
      (fun y : ℝ => q ((z₂.re : ℂ) + y * I))
      MeasureTheory.volume z₁.im z₂.im :=
    (hq.continuousOn.comp (by fun_prop : ContinuousOn
      (fun y : ℝ => (z₂.re : ℂ) + y * I) (uIcc z₁.im z₂.im)) hright_mem).intervalIntegrable
  have hql : IntervalIntegrable
      (fun y : ℝ => q ((z₁.re : ℂ) + y * I))
      MeasureTheory.volume z₁.im z₂.im :=
    (hq.continuousOn.comp (by fun_prop : ContinuousOn
      (fun y : ℝ => (z₁.re : ℂ) + y * I) (uIcc z₁.im z₂.im)) hleft_mem).intervalIntegrable
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
      have hslope := sub_smul_dslope g p z
      simp only [smul_eq_mul] at hslope
      dsimp only [q]
      calc
        g z * (z - p)⁻¹ =
            (g p + (z - p) * dslope g p z) * (z - p)⁻¹ := by
          rw [hslope]
          ring
        _ = g p * (z - p)⁻¹ + dslope g p z := by
          field_simp [sub_ne_zero.mpr hz]
    · intro x _
      exact sub_ne_zero.mp (hbot_ne x)
    · intro x _
      exact sub_ne_zero.mp (htop_ne x)
    · intro y _
      exact sub_ne_zero.mp (hright_ne y)
    · intro y _
      exact sub_ne_zero.mp (hleft_ne y)
  rw [hcongr, hsum, rectIntegral_const_mul,
    rectIntegral_cauchyKernel hre₁ hre₂ him₁ him₂, hqzero]
  ring

end

end RHTower
