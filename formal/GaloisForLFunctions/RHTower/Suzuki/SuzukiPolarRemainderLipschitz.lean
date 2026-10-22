import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilRemainderRegularity
import GaloisForLFunctions.HTGeometry.ExponentialDividedDifference

/-!
# Lipschitz regularity of Suzuki's polar remainder

Suzuki's restricted-Weil source contains the second derivative of the non-prime remainder,

`r''(t) = -2 cosh (t/2) + exp (|t|/2) / (2 sinh |t|) - 1/(2|t|)`,

whose apparent pole at the origin is removable with value `-7/4`.  Continuity of `r''` alone
leaves the boundary modulus of the polar convolution uncontrolled.  This module proves the sharp
regularity: writing the polar block through the two exponential divided differences

`h(s) = (expDivTwo (-2s) - expDivOne (-s/2) / 4) / expDivOne (-2s)`

exhibits it as a quotient of Lipschitz functions with a denominator bounded away from zero, so
`r''` is Lipschitz on every compact interval.  The even `|t|` argument cannot destroy this because
`|·|` is a contraction.
-/

open Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The pole-free form of Suzuki's polar block `exp (s/2)/(2 sinh s) - 1/(2s)`. -/
def suzukiPolarCore (s : ℝ) : ℝ :=
  (expDivTwo (-(2 * s)) - expDivOne (-(s / 2)) / 4) / expDivOne (-(2 * s))

theorem suzukiPolarCore_zero : suzukiPolarCore 0 = 1 / 4 := by
  norm_num [suzukiPolarCore, expDivOne_zero, expDivTwo_zero]

private theorem polarCore_algebra {a s : ℝ} (ha : 0 < a) (ha1 : a < 1) (hs : 0 < s) :
    ((a * a * (a * a) - 1 - (-(2 * s))) / (-(2 * s)) ^ (2 : ℕ)
        - ((a - 1) / (-(s / 2))) / 4) / ((a * a * (a * a) - 1) / (-(2 * s)))
      = a⁻¹ / (2 * (((a * a)⁻¹ - a * a) / 2)) - 1 / (2 * s) := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hsne : s ≠ 0 := ne_of_gt hs
  have hsq : a * a < 1 := by nlinarith
  have h4 : a * a * (a * a) < 1 := by nlinarith [mul_pos ha ha]
  have hne1 : a * a * (a * a) - 1 ≠ 0 := by
    intro h
    have := sub_eq_zero.mp h
    linarith
  have hne1' : 1 - a * a * (a * a) ≠ 0 := by
    intro h
    have := sub_eq_zero.mp h
    linarith
  have hne2 : a * a - 1 ≠ 0 := by
    intro h
    have := sub_eq_zero.mp h
    linarith
  have hne2' : 1 - a * a ≠ 0 := by
    intro h
    have := sub_eq_zero.mp h
    linarith
  have hpow4 : a ^ (4 : ℕ) = a * a * (a * a) := by ring
  have hne4 : (1 : ℝ) - a ^ (4 : ℕ) ≠ 0 := by
    rw [hpow4]
    exact hne1'
  have hne4' : a ^ (4 : ℕ) - 1 ≠ 0 := by
    rw [hpow4]
    exact hne1
  have hne5 : (-1 : ℝ) + a ^ (4 : ℕ) ≠ 0 := by
    intro h
    exact hne4' (by linarith)
  field_simp
  ring

/-- On the open half line the pole-free form is Suzuki's literal polar block. -/
theorem suzukiPolarCore_eq_of_pos {s : ℝ} (hs : 0 < s) :
    suzukiPolarCore s = Real.exp (s / 2) / (2 * Real.sinh s) - 1 / (2 * s) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have h2s : (-(2 * s)) ≠ 0 := by
    intro h
    exact hs0 (by linarith [neg_eq_zero.mp h])
  have hs2 : (-(s / 2)) ≠ 0 := by
    intro h
    exact hs0 (by linarith [neg_eq_zero.mp h])
  have hapos : 0 < Real.exp (-(s / 2)) := Real.exp_pos _
  have ha1 : Real.exp (-(s / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hmul2 : Real.exp (-(s / 2)) * Real.exp (-(s / 2)) = Real.exp (-s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmul4 : Real.exp (-s) * Real.exp (-s) = Real.exp (-(2 * s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hD : Real.exp (-(2 * s))
      = Real.exp (-(s / 2)) * Real.exp (-(s / 2))
        * (Real.exp (-(s / 2)) * Real.exp (-(s / 2))) := by
    rw [hmul2, hmul4]
  have hC : Real.exp (-s) = Real.exp (-(s / 2)) * Real.exp (-(s / 2)) := hmul2.symm
  have hA : Real.exp (s / 2) = (Real.exp (-(s / 2)))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hB : Real.exp s = (Real.exp (-(s / 2)) * Real.exp (-(s / 2)))⁻¹ := by
    rw [hmul2, ← Real.exp_neg]
    simp
  rw [suzukiPolarCore, expDivTwo_eq_of_ne h2s, expDivOne_eq_of_ne hs2, expDivOne_eq_of_ne h2s,
    Real.sinh_eq, hD, hC, hB, hA]
  exact polarCore_algebra hapos ha1 hs

/-- Suzuki's even source kernel is the smooth `cosh` block plus the pole-free polar core. -/
theorem suzukiWeilRemainderKernel_eq (t : ℝ) :
    suzukiWeilRemainderKernel t = -2 * Real.cosh (t / 2) + suzukiPolarCore |t| := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [show |(0 : ℝ)| = 0 by norm_num, suzukiPolarCore_zero]
    have h0 : suzukiWeilRemainderKernel 0 = -7 / 4 := by
      simp [suzukiWeilRemainderKernel, suzukiWeilRemainderSecondDerivativeContinuous]
    rw [h0]
    norm_num
  · have habs : 0 < |t| := abs_pos.mpr ht
    have hcosh : Real.cosh (|t| / 2) = Real.cosh (t / 2) := by
      rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
      · rw [h, show -t / 2 = -(t / 2) by ring, Real.cosh_neg]
    rw [suzukiWeilRemainderKernel_eq_source_of_ne ht, suzukiPolarCore_eq_of_pos habs,
      suzukiWeilRemainderSecondDerivative, hcosh]
    ring

/-- The numerator of the polar core is bounded on the closed positive half line. -/
theorem abs_suzukiPolarNum_le {s : ℝ} (hs : 0 ≤ s) :
    |expDivTwo (-(2 * s)) - expDivOne (-(s / 2)) / 4| ≤ 3 / 4 := by
  have h1 : (-(2 * s)) ≤ 0 := by linarith
  have h2 : (-(s / 2)) ≤ 0 := by linarith
  have hA := expDivTwo_le_half h1
  have hA' := (expDivTwo_pos h1).le
  have hB := expDivOne_le_one h2
  have hB' := (expDivOne_pos h2).le
  rw [abs_le]
  constructor <;> linarith

/-- The denominator of the polar core is bounded below on `[0, T]`. -/
theorem exp_le_suzukiPolarDen {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    Real.exp (-(2 * T)) ≤ expDivOne (-(2 * s)) := by
  have h1 : (-(2 * s)) ≤ 0 := by linarith
  exact le_trans (Real.exp_le_exp.mpr (by linarith)) (exp_le_expDivOne h1)

/-- Lipschitz bound for the numerator of the polar core on the positive half line. -/
theorem abs_suzukiPolarNum_sub_le {s₁ s₂ : ℝ} (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂) :
    |(expDivTwo (-(2 * s₁)) - expDivOne (-(s₁ / 2)) / 4) -
        (expDivTwo (-(2 * s₂)) - expDivOne (-(s₂ / 2)) / 4)| ≤ 3 * |s₁ - s₂| := by
  have hA := abs_expDivTwo_sub_le (x := -(2 * s₁)) (y := -(2 * s₂)) (by linarith) (by linarith)
  have hB := abs_expDivOne_sub_le (x := -(s₁ / 2)) (y := -(s₂ / 2)) (by linarith) (by linarith)
  have hA' : |(-(2 * s₁)) - (-(2 * s₂))| = 2 * |s₁ - s₂| := by
    rw [show (-(2 * s₁)) - (-(2 * s₂)) = 2 * (s₂ - s₁) by ring, abs_mul, abs_sub_comm s₂ s₁]
    norm_num
  have hB' : |(-(s₁ / 2)) - (-(s₂ / 2))| = |s₁ - s₂| / 2 := by
    rw [show (-(s₁ / 2)) - (-(s₂ / 2)) = (s₂ - s₁) / 2 by ring, abs_div, abs_sub_comm s₂ s₁]
    norm_num
  rw [hA'] at hA
  rw [hB'] at hB
  have hsplit :
      (expDivTwo (-(2 * s₁)) - expDivOne (-(s₁ / 2)) / 4) -
          (expDivTwo (-(2 * s₂)) - expDivOne (-(s₂ / 2)) / 4)
        = (expDivTwo (-(2 * s₁)) - expDivTwo (-(2 * s₂)))
            - (expDivOne (-(s₁ / 2)) - expDivOne (-(s₂ / 2))) / 4 := by ring
  rw [hsplit]
  have hsub := abs_sub (expDivTwo (-(2 * s₁)) - expDivTwo (-(2 * s₂)))
    ((expDivOne (-(s₁ / 2)) - expDivOne (-(s₂ / 2))) / 4)
  have hdiv : |(expDivOne (-(s₁ / 2)) - expDivOne (-(s₂ / 2))) / 4|
      = |expDivOne (-(s₁ / 2)) - expDivOne (-(s₂ / 2))| / 4 := by
    rw [abs_div]
    norm_num
  rw [hdiv] at hsub
  linarith [abs_nonneg (s₁ - s₂)]

/-- Lipschitz bound for the denominator of the polar core on the positive half line. -/
theorem abs_suzukiPolarDen_sub_le {s₁ s₂ : ℝ} (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂) :
    |expDivOne (-(2 * s₁)) - expDivOne (-(2 * s₂))| ≤ 2 * |s₁ - s₂| := by
  have hA := abs_expDivOne_sub_le (x := -(2 * s₁)) (y := -(2 * s₂)) (by linarith) (by linarith)
  have hA' : |(-(2 * s₁)) - (-(2 * s₂))| = 2 * |s₁ - s₂| := by
    rw [show (-(2 * s₁)) - (-(2 * s₂)) = 2 * (s₂ - s₁) by ring, abs_mul, abs_sub_comm s₂ s₁]
    norm_num
  rw [hA'] at hA
  exact hA

/-- **The polar core is Lipschitz on every bounded piece of the closed positive half line.** -/
theorem abs_suzukiPolarCore_sub_le {T s₁ s₂ : ℝ} (h₁ : s₁ ∈ Icc 0 T) (h₂ : s₂ ∈ Icc 0 T) :
    |suzukiPolarCore s₁ - suzukiPolarCore s₂| ≤ 5 * Real.exp (4 * T) * |s₁ - s₂| := by
  obtain ⟨hs₁, hs₁T⟩ := h₁
  obtain ⟨hs₂, hs₂T⟩ := h₂
  set N₁ := expDivTwo (-(2 * s₁)) - expDivOne (-(s₁ / 2)) / 4 with hN₁
  set N₂ := expDivTwo (-(2 * s₂)) - expDivOne (-(s₂ / 2)) / 4 with hN₂
  set D₁ := expDivOne (-(2 * s₁)) with hD₁
  set D₂ := expDivOne (-(2 * s₂)) with hD₂
  have hd : Real.exp (-(2 * T)) ≤ D₁ := exp_le_suzukiPolarDen hs₁ hs₁T
  have hd' : Real.exp (-(2 * T)) ≤ D₂ := exp_le_suzukiPolarDen hs₂ hs₂T
  have hdpos : 0 < Real.exp (-(2 * T)) := Real.exp_pos _
  have hD₁pos : 0 < D₁ := lt_of_lt_of_le hdpos hd
  have hD₂pos : 0 < D₂ := lt_of_lt_of_le hdpos hd'
  have hD₂le : D₂ ≤ 1 := expDivOne_le_one (by linarith)
  have hN₂le : |N₂| ≤ 3 / 4 := abs_suzukiPolarNum_le hs₂
  have hNsub : |N₁ - N₂| ≤ 3 * |s₁ - s₂| := abs_suzukiPolarNum_sub_le hs₁ hs₂
  have hDsub : |D₁ - D₂| ≤ 2 * |s₁ - s₂| := abs_suzukiPolarDen_sub_le hs₁ hs₂
  have hquot : suzukiPolarCore s₁ - suzukiPolarCore s₂
      = ((N₁ - N₂) * D₂ - N₂ * (D₁ - D₂)) / (D₁ * D₂) := by
    rw [suzukiPolarCore, suzukiPolarCore, ← hN₁, ← hN₂, ← hD₁, ← hD₂]
    field_simp
    ring
  rw [hquot, abs_div, abs_of_pos (by positivity : (0:ℝ) < D₁ * D₂)]
  have hnum : |(N₁ - N₂) * D₂ - N₂ * (D₁ - D₂)| ≤ 5 * |s₁ - s₂| := by
    have hsub := abs_sub ((N₁ - N₂) * D₂) (N₂ * (D₁ - D₂))
    have e1 : |(N₁ - N₂) * D₂| = |N₁ - N₂| * |D₂| := abs_mul _ _
    have e2 : |N₂ * (D₁ - D₂)| = |N₂| * |D₁ - D₂| := abs_mul _ _
    have hD₂abs : |D₂| ≤ 1 := by rw [abs_of_pos hD₂pos]; exact hD₂le
    have h1 : |N₁ - N₂| * |D₂| ≤ 3 * |s₁ - s₂| * 1 :=
      mul_le_mul hNsub hD₂abs (abs_nonneg _) (by positivity)
    have h2 : |N₂| * |D₁ - D₂| ≤ (3 / 4) * (2 * |s₁ - s₂|) :=
      mul_le_mul hN₂le hDsub (abs_nonneg _) (by norm_num)
    rw [e1, e2] at hsub
    linarith [abs_nonneg (s₁ - s₂)]
  have hden : Real.exp (-(4 * T)) ≤ D₁ * D₂ := by
    have hprod : Real.exp (-(2 * T)) * Real.exp (-(2 * T)) ≤ D₁ * D₂ :=
      mul_le_mul hd hd' hdpos.le hD₁pos.le
    have hsq : Real.exp (-(2 * T)) * Real.exp (-(2 * T)) = Real.exp (-(4 * T)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    linarith [hsq.symm.le, hsq.le]
  rw [div_le_iff₀ (show (0:ℝ) < D₁ * D₂ by positivity)]
  have hE : Real.exp (4 * T) * Real.exp (-(4 * T)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hfac : 0 ≤ 5 * Real.exp (4 * T) * |s₁ - s₂| := by positivity
  have hstep : 5 * Real.exp (4 * T) * |s₁ - s₂| * Real.exp (-(4 * T))
      ≤ 5 * Real.exp (4 * T) * |s₁ - s₂| * (D₁ * D₂) :=
    mul_le_mul_of_nonneg_left hden hfac
  have heq : 5 * Real.exp (4 * T) * |s₁ - s₂| * Real.exp (-(4 * T)) = 5 * |s₁ - s₂| := by
    calc 5 * Real.exp (4 * T) * |s₁ - s₂| * Real.exp (-(4 * T))
        = 5 * |s₁ - s₂| * (Real.exp (4 * T) * Real.exp (-(4 * T))) := by ring
      _ = 5 * |s₁ - s₂| := by rw [hE]; ring
  linarith [hnum, hstep, heq.le, heq.ge]

end

end RHTower

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The polar core is bounded on `[0, T]`. -/
theorem abs_suzukiPolarCore_le {T s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    |suzukiPolarCore s| ≤ 3 / 4 * Real.exp (2 * T) := by
  have hd : Real.exp (-(2 * T)) ≤ expDivOne (-(2 * s)) := exp_le_suzukiPolarDen hs hsT
  have hdpos : 0 < Real.exp (-(2 * T)) := Real.exp_pos _
  have hDpos : 0 < expDivOne (-(2 * s)) := lt_of_lt_of_le hdpos hd
  have hN : |expDivTwo (-(2 * s)) - expDivOne (-(s / 2)) / 4| ≤ 3 / 4 := abs_suzukiPolarNum_le hs
  rw [suzukiPolarCore, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
  have hE : Real.exp (-(2 * T)) * Real.exp (2 * T) = 1 := by
    rw [← Real.exp_add]
    simp
  have hstep : 3 / 4 * Real.exp (2 * T) * Real.exp (-(2 * T))
      ≤ 3 / 4 * Real.exp (2 * T) * expDivOne (-(2 * s)) := by
    apply mul_le_mul_of_nonneg_left hd
    positivity
  have heq : 3 / 4 * Real.exp (2 * T) * Real.exp (-(2 * T)) = 3 / 4 := by
    calc 3 / 4 * Real.exp (2 * T) * Real.exp (-(2 * T))
        = 3 / 4 * (Real.exp (-(2 * T)) * Real.exp (2 * T)) := by ring
      _ = 3 / 4 := by rw [hE]; ring
  linarith

/-- Suzuki's source kernel is bounded on every finite aperture, with an explicit constant. -/
theorem abs_suzukiWeilRemainderKernel_le {T t : ℝ} (ht : |t| ≤ T) :
    |suzukiWeilRemainderKernel t| ≤ 2 * Real.exp (T / 2) + 3 / 4 * Real.exp (2 * T) := by
  have hT : 0 ≤ T := le_trans (abs_nonneg t) ht
  have hbounds := abs_le.mp ht
  have hcore : |suzukiPolarCore (|t|)| ≤ 3 / 4 * Real.exp (2 * T) :=
    abs_suzukiPolarCore_le (abs_nonneg t) ht
  have hcosh : |(-2 : ℝ) * Real.cosh (t / 2)| ≤ 2 * Real.exp (T / 2) := by
    rw [abs_mul, abs_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0),
      abs_of_pos (Real.cosh_pos (t / 2)), Real.cosh_eq]
    have h1 : Real.exp (t / 2) ≤ Real.exp (T / 2) :=
      Real.exp_le_exp.mpr (by linarith [hbounds.2])
    have h2 : Real.exp (-(t / 2)) ≤ Real.exp (T / 2) :=
      Real.exp_le_exp.mpr (by linarith [hbounds.1])
    linarith
  rw [suzukiWeilRemainderKernel_eq t]
  calc |(-2 : ℝ) * Real.cosh (t / 2) + suzukiPolarCore (|t|)|
      ≤ |(-2 : ℝ) * Real.cosh (t / 2)| + |suzukiPolarCore (|t|)| := abs_add_le _ _
    _ ≤ 2 * Real.exp (T / 2) + 3 / 4 * Real.exp (2 * T) := by linarith

/-- **`r''` is Lipschitz on every compact interval** — the sharp regularity of Suzuki's polar
remainder, beyond the continuity supplied by the removable singularity. -/
theorem abs_suzukiWeilRemainderKernel_sub_le {T x y : ℝ} (hx : |x| ≤ T) (hy : |y| ≤ T) :
    |suzukiWeilRemainderKernel x - suzukiWeilRemainderKernel y|
      ≤ (Real.exp (T / 2) + 5 * Real.exp (4 * T)) * |x - y| := by
  have hT : 0 ≤ T := le_trans (abs_nonneg x) hx
  have hxm : x / 2 ≤ T / 2 := by
    have := abs_le.mp hx
    linarith [this.2]
  have hym : y / 2 ≤ T / 2 := by
    have := abs_le.mp hy
    linarith [this.2]
  have hxm' : -(x / 2) ≤ T / 2 := by
    have := abs_le.mp hx
    linarith [this.1]
  have hym' : -(y / 2) ≤ T / 2 := by
    have := abs_le.mp hy
    linarith [this.1]
  have hcosh : |Real.cosh (x / 2) - Real.cosh (y / 2)| ≤ Real.exp (T / 2) * |x - y| / 2 := by
    have hsplit : Real.cosh (x / 2) - Real.cosh (y / 2)
        = ((Real.exp (x / 2) - Real.exp (y / 2)) + (Real.exp (-(x / 2)) - Real.exp (-(y / 2)))) / 2 := by
      rw [Real.cosh_eq, Real.cosh_eq]
      ring
    have h1 := abs_exp_sub_exp_le hxm hym
    have h2 := abs_exp_sub_exp_le hxm' hym'
    have e1 : |x / 2 - y / 2| = |x - y| / 2 := by
      rw [show x / 2 - y / 2 = (x - y) / 2 by ring, abs_div]
      norm_num
    have e2 : |(-(x / 2)) - (-(y / 2))| = |x - y| / 2 := by
      rw [show (-(x / 2)) - (-(y / 2)) = (y - x) / 2 by ring, abs_div, abs_sub_comm y x]
      norm_num
    rw [e1] at h1
    rw [e2] at h2
    rw [hsplit, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have := abs_add_le (Real.exp (x / 2) - Real.exp (y / 2)) (Real.exp (-(x / 2)) - Real.exp (-(y / 2)))
    linarith
  have hcore : abs (suzukiPolarCore |x| - suzukiPolarCore |y|)
      ≤ 5 * Real.exp (4 * T) * |x - y| := by
    have hmem₁ : |x| ∈ Icc (0:ℝ) T := ⟨abs_nonneg x, hx⟩
    have hmem₂ : |y| ∈ Icc (0:ℝ) T := ⟨abs_nonneg y, hy⟩
    have hbase := abs_suzukiPolarCore_sub_le hmem₁ hmem₂
    have habs : abs (|x| - |y|) ≤ |x - y| := abs_abs_sub_abs_le_abs_sub x y
    have hpos : (0:ℝ) ≤ 5 * Real.exp (4 * T) := by positivity
    calc abs (suzukiPolarCore |x| - suzukiPolarCore |y|)
        ≤ 5 * Real.exp (4 * T) * abs (|x| - |y|) := hbase
      _ ≤ 5 * Real.exp (4 * T) * |x - y| := mul_le_mul_of_nonneg_left habs hpos
  rw [suzukiWeilRemainderKernel_eq x, suzukiWeilRemainderKernel_eq y]
  have hsplit : (-2 * Real.cosh (x / 2) + suzukiPolarCore (|x|))
      - (-2 * Real.cosh (y / 2) + suzukiPolarCore (|y|))
      = -2 * (Real.cosh (x / 2) - Real.cosh (y / 2))
        + (suzukiPolarCore (|x|) - suzukiPolarCore (|y|)) := by ring
  rw [hsplit]
  have hadd := abs_add_le (-2 * (Real.cosh (x / 2) - Real.cosh (y / 2)))
    (suzukiPolarCore (|x|) - suzukiPolarCore (|y|))
  have hmul : |(-2 : ℝ) * (Real.cosh (x / 2) - Real.cosh (y / 2))|
      = 2 * |Real.cosh (x / 2) - Real.cosh (y / 2)| := by
    rw [abs_mul]
    norm_num
  rw [hmul] at hadd
  linarith

end

end RHTower
