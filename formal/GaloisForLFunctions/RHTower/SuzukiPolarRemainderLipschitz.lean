import GaloisForLFunctions.RHTower.SuzukiWeilRemainderRegularity
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
  simp [suzukiPolarCore, expDivOne_zero, expDivTwo_zero]
  norm_num

/-- On the open half line the pole-free form is Suzuki's literal polar block. -/
theorem suzukiPolarCore_eq_of_pos {s : ℝ} (hs : 0 < s) :
    suzukiPolarCore s = Real.exp (s / 2) / (2 * Real.sinh s) - 1 / (2 * s) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have h2s : (-(2 * s)) ≠ 0 := by
    intro h
    apply hs0
    linarith [neg_eq_zero.mp h]
  have hs2 : (-(s / 2)) ≠ 0 := by
    intro h
    apply hs0
    have := neg_eq_zero.mp h
    linarith
  set u : ℝ := Real.exp (s / 2) with hu
  have hupos : 0 < u := Real.exp_pos _
  have hu1 : 1 < u := by
    rw [hu]
    exact Real.one_lt_exp_iff_of_pos (by linarith) |>.mpr (by linarith)
  have huu : u * u = Real.exp s := by
    rw [hu, ← Real.exp_add]
    congr 1
    ring
  have hneg_half : Real.exp (-(s / 2)) = u⁻¹ := by
    rw [hu, ← Real.exp_neg]
  have hneg_two : Real.exp (-(2 * s)) = (u * u * (u * u))⁻¹ := by
    rw [huu, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have hnegs : Real.exp (-s) = (u * u)⁻¹ := by
    rw [huu, ← Real.exp_neg]
  have hsinh : Real.sinh s = (u * u - (u * u)⁻¹) / 2 := by
    rw [Real.sinh_eq, huu, hnegs]
  have hu4 : (u * u * (u * u)) ≠ 0 := by positivity
  have hone_sub : 1 - (u * u * (u * u))⁻¹ ≠ 0 := by
    have h1 : 1 < u * u * (u * u) := by nlinarith
    have h2 : (u * u * (u * u))⁻¹ < 1 := by
      rw [inv_lt_one₀ (by positivity)]
      exact h1
    intro h
    linarith [sub_eq_zero.mp h]
  have hsinh_ne : Real.sinh s ≠ 0 := Real.sinh_ne_zero.mpr hs0
  rw [suzukiPolarCore, expDivTwo_eq_of_ne h2s, expDivOne_eq_of_ne hs2, expDivOne_eq_of_ne h2s,
    hneg_half, hneg_two, hsinh]
  have hupow : u ≠ 0 := ne_of_gt hupos
  field_simp
  ring

/-- Suzuki's even source kernel is the smooth `cosh` block plus the pole-free polar core. -/
theorem suzukiWeilRemainderKernel_eq (t : ℝ) :
    suzukiWeilRemainderKernel t = -2 * Real.cosh (t / 2) + suzukiPolarCore |t| := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [suzukiWeilRemainderKernel, suzukiWeilRemainderSecondDerivativeContinuous,
      suzukiPolarCore_zero]
    norm_num
  · have habs : 0 < |t| := abs_pos.mpr ht
    rw [suzukiWeilRemainderKernel_eq_source_of_ne ht, suzukiPolarCore_eq_of_pos habs,
      suzukiWeilRemainderSecondDerivative]
    have : Real.cosh (|t| / 2) = Real.cosh (t / 2) := by
      rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
      · rw [h]
        rw [show -t / 2 = -(t / 2) by ring, Real.cosh_neg]
    rw [this]

/-- The polar core is bounded on the closed positive half line. -/
theorem abs_suzukiPolarCore_num_le (s : ℝ) (hs : 0 ≤ s) :
    |expDivTwo (-(2 * s)) - expDivOne (-(s / 2)) / 4| ≤ 3 / 4 := by
  have h1 : (-(2 * s)) ≤ 0 := by linarith
  have h2 : (-(s / 2)) ≤ 0 := by linarith
  have hA := expDivTwo_le_half h1
  have hA' := (expDivTwo_pos h1).le
  have hB := expDivOne_le_one h2
  have hB' := (expDivOne_pos h2).le
  rw [abs_le]
  constructor <;> linarith

/-- The polar core's denominator is bounded below on `[0, T]`. -/
theorem exp_le_suzukiPolarDen {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    Real.exp (-(2 * T)) ≤ expDivOne (-(2 * s)) := by
  have h1 : (-(2 * s)) ≤ 0 := by linarith
  refine le_trans ?_ (exp_le_expDivOne h1)
  exact Real.exp_le_exp.mpr (by linarith)

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
  calc |(expDivTwo (-(2 * s₁)) - expDivTwo (-(2 * s₂)))
          - (expDivOne (-(s₁ / 2)) - expDivOne (-(s₂ / 2))) / 4|
      ≤ |expDivTwo (-(2 * s₁)) - expDivTwo (-(2 * s₂))|
          + |(expDivOne (-(s₁ / 2)) - expDivOne (-(s₂ / 2))) / 4| := abs_sub _ _
    _ ≤ 2 * |s₁ - s₂| + (|s₁ - s₂| / 2) / 4 := by
        rw [abs_div]
        have : |(4 : ℝ)| = 4 := by norm_num
        rw [this]
        have := hB
        constructor <;> linarith
    _ ≤ 3 * |s₁ - s₂| := by linarith [abs_nonneg (s₁ - s₂)]

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
  have hN₂le : |N₂| ≤ 3 / 4 := abs_suzukiPolarCore_num_le s₂ hs₂
  have hNsub : |N₁ - N₂| ≤ 3 * |s₁ - s₂| := abs_suzukiPolarNum_sub_le hs₁ hs₂
  have hDsub : |D₁ - D₂| ≤ 2 * |s₁ - s₂| := abs_suzukiPolarDen_sub_le hs₁ hs₂
  have hquot : suzukiPolarCore s₁ - suzukiPolarCore s₂
      = ((N₁ - N₂) * D₂ - N₂ * (D₁ - D₂)) / (D₁ * D₂) := by
    rw [suzukiPolarCore, suzukiPolarCore, ← hN₁, ← hN₂, ← hD₁, ← hD₂]
    field_simp
    ring
  rw [hquot, abs_div, abs_of_pos (by positivity : (0:ℝ) < D₁ * D₂)]
  have hnum : |(N₁ - N₂) * D₂ - N₂ * (D₁ - D₂)| ≤ 4.5 * |s₁ - s₂| := by
    calc |(N₁ - N₂) * D₂ - N₂ * (D₁ - D₂)|
        ≤ |(N₁ - N₂) * D₂| + |N₂ * (D₁ - D₂)| := abs_sub _ _
      _ = |N₁ - N₂| * |D₂| + |N₂| * |D₁ - D₂| := by rw [abs_mul, abs_mul]
      _ ≤ 3 * |s₁ - s₂| * 1 + (3 / 4) * (2 * |s₁ - s₂|) := by
          have hD₂abs : |D₂| ≤ 1 := by rw [abs_of_pos hD₂pos]; exact hD₂le
          have h1 : |N₁ - N₂| * |D₂| ≤ 3 * |s₁ - s₂| * 1 :=
            mul_le_mul hNsub hD₂abs (abs_nonneg _) (by positivity)
          have h2 : |N₂| * |D₁ - D₂| ≤ (3 / 4) * (2 * |s₁ - s₂|) :=
            mul_le_mul hN₂le hDsub (abs_nonneg _) (by norm_num)
          linarith
      _ = 4.5 * |s₁ - s₂| := by norm_num; ring
  have hden : Real.exp (-(2 * T)) * Real.exp (-(2 * T)) ≤ D₁ * D₂ :=
    mul_le_mul hd hd' hdpos.le hD₁pos.le
  have hdensq : Real.exp (-(2 * T)) * Real.exp (-(2 * T)) = Real.exp (-(4 * T)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hdensq] at hden
  have hkey : |(N₁ - N₂) * D₂ - N₂ * (D₁ - D₂)| / (D₁ * D₂)
      ≤ (4.5 * |s₁ - s₂|) / Real.exp (-(4 * T)) := by
    apply div_le_div_of_nonneg_of_le_of_pos hnum hden (Real.exp_pos _)
  refine hkey.trans ?_
  have hinv : (Real.exp (-(4 * T)))⁻¹ = Real.exp (4 * T) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [div_eq_mul_inv, hinv]
  have : (4.5 : ℝ) * |s₁ - s₂| * Real.exp (4 * T) ≤ 5 * Real.exp (4 * T) * |s₁ - s₂| := by
    nlinarith [abs_nonneg (s₁ - s₂), Real.exp_pos (4 * T)]
  exact this

end

end RHTower
