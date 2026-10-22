import GaloisForLFunctions.RHTower.XiHorizontalRatioSelection
import GaloisForLFunctions.RHTower.ThetaThresholdXiDivisibleUniqueness

/-! # An unconditional exhaustion by zero-free Xi contours

Good horizontal ratios and the exterior Gamma floor produce a spaced contour
exhaustion. No location, separation or multiplicity of an individual zero is
chosen or assumed.
-/

open Complex Set Filter Topology

namespace RHTower
noncomputable section

structure DeningerMeyerXiContourSchedule where
  exponent : ℕ
  offset : ℝ
  offset_ge : 10 ≤ offset
  height : ℕ → ℝ
  lower : ∀ n : ℕ, offset+4*(n : ℝ) ≤ height n
  upper : ∀ n : ℕ, height n ≤ offset+4*(n : ℝ)+1
  floor_pos : ∀ (n : ℕ) (σ : ℝ), -1 ≤ σ → σ ≤ 2 →
    Real.exp (-(Real.pi*height n/4))/(3*Real.pi) ≤
      (height n)^exponent*‖xi ((σ : ℂ)+(height n : ℂ)*I)‖
  floor_neg : ∀ (n : ℕ) (σ : ℝ), -1 ≤ σ → σ ≤ 2 →
    Real.exp (-(Real.pi*height n/4))/(3*Real.pi) ≤
      (height n)^exponent*‖xi ((σ : ℂ)-(height n : ℂ)*I)‖

/-- A literal schedule selected from the unconditional good-height theorem. -/
def deningerMeyerXiContourSchedule : DeningerMeyerXiContourSchedule := by
  classical
  apply Classical.choice
  obtain ⟨M, n₀, hsel⟩ := exists_xi_horizontal_ratio_nat_bound
  let N := max n₀ 10
  have hN : 10 ≤ N := le_max_right _ _
  have hinput := fun n : ℕ => hsel (N+4*(n : ℝ))
    (by dsimp [N]; linarith [le_max_left n₀ 10, Nat.cast_nonneg (α := ℝ) n])
  choose T hL hU hratio using hinput
  refine ⟨⟨M, N, hN, T, hL, hU, ?_, ?_⟩⟩
  · intro n σ hσ₁ hσ₂
    have hT : 0 ≤ T n := by linarith [hL n, Nat.cast_nonneg (α := ℝ) n]
    calc
      Real.exp (-(Real.pi*T n/4))/(3*Real.pi) ≤ ‖xi (2+(T n : ℂ)*I)‖ := by
        simpa only [abs_of_nonneg hT] using xi_floor_two (T n)
      _ ≤ (T n)^M*‖xi ((σ : ℂ)+(T n : ℂ)*I)‖ :=
        (hratio n 2 σ (by norm_num) le_rfl hσ₁ hσ₂).1
  · intro n σ hσ₁ hσ₂
    have hT : 0 ≤ T n := by linarith [hL n, Nat.cast_nonneg (α := ℝ) n]
    calc
      Real.exp (-(Real.pi*T n/4))/(3*Real.pi) ≤ ‖xi (2-(T n : ℂ)*I)‖ := by
        simpa [abs_of_nonneg hT, sub_eq_add_neg] using xi_floor_two (-T n)
      _ ≤ (T n)^M*‖xi ((σ : ℂ)-(T n : ℂ)*I)‖ :=
        (hratio n 2 σ (by norm_num) le_rfl hσ₁ hσ₂).2

namespace DeningerMeyerXiContourSchedule

variable (S : DeningerMeyerXiContourSchedule)

theorem height_ge (n : ℕ) : 10+4*(n : ℝ) ≤ S.height n := by
  linarith [S.offset_ge, S.lower n]

theorem height_pos (n : ℕ) : 0 < S.height n := by
  linarith [S.height_ge n, Nat.cast_nonneg (α := ℝ) n]

theorem height_next_gap (n : ℕ) :
    3 ≤ S.height (n+1)-S.height n ∧ S.height (n+1)-S.height n ≤ 5 := by
  have h₁ := S.lower n
  have h₂ := S.upper n
  have h₃ := S.lower (n+1)
  have h₄ := S.upper (n+1)
  push_cast at h₃ h₄
  constructor <;> linarith

theorem floor_abs (n : ℕ) {z : ℂ} (hz₁ : -1 ≤ z.re) (hz₂ : z.re ≤ 2)
    (hz : |z.im| = S.height n) :
    Real.exp (-(Real.pi*S.height n/4))/(3*Real.pi) ≤
      (S.height n)^S.exponent*‖xi z‖ := by
  by_cases h : 0 ≤ z.im
  · have hi : z.im = S.height n := by simpa only [abs_of_nonneg h] using hz
    have he : z = (z.re : ℂ)+(S.height n : ℂ)*I := by
      apply Complex.ext <;> simp [hi]
    simpa only [← he] using S.floor_pos n z.re hz₁ hz₂
  · have hi : z.im = -S.height n := by
      rw [abs_of_neg (lt_of_not_ge h)] at hz
      linarith
    have he : z = (z.re : ℂ)-(S.height n : ℂ)*I := by
      apply Complex.ext <;> simp [hi]
    simpa only [← he] using S.floor_neg n z.re hz₁ hz₂

theorem horizontal_ne_zero (n : ℕ) {z : ℂ}
    (hz₁ : -1 ≤ z.re) (hz₂ : z.re ≤ 2) (hz : |z.im| = S.height n) : xi z ≠ 0 := by
  intro hzero
  have h := S.floor_abs n hz₁ hz₂ hz
  rw [hzero, norm_zero, mul_zero] at h
  have hp : 0 < Real.exp (-(Real.pi*S.height n/4))/(3*Real.pi) := by positivity
  linarith

end DeningerMeyerXiContourSchedule

theorem deningerXiContour_edge_floor (s : ℂ) (hs : s.re = -1 ∨ s.re = 2) :
    Real.exp (-(Real.pi*|s.im|/4))/(3*Real.pi) ≤ ‖xi s‖ := by
  rcases hs with hs | hs
  · have he : 1-s = 2+((-s.im : ℝ) : ℂ)*I := by
      apply Complex.ext <;> norm_num [hs]
    have h := xi_floor_two (-s.im)
    rw [← he, xi_one_sub] at h
    simpa only [abs_neg] using h
  · have he : s = 2+(s.im : ℂ)*I := by
      apply Complex.ext <;> simp [hs]
    simpa only [← he] using xi_floor_two s.im

theorem deningerXiContour_inverse_of_floor {z : ℂ} {P t : ℝ}
    (h : Real.exp (-(Real.pi*t/4))/(3*Real.pi) ≤ P*‖xi z‖) :
    xi z ≠ 0 ∧ ‖(xi z)⁻¹‖ ≤ 3*Real.pi*P*Real.exp (Real.pi*t/4) := by
  have hp : 0 < Real.exp (-(Real.pi*t/4))/(3*Real.pi) := by positivity
  have hnz : xi z ≠ 0 := by
    intro hz
    rw [hz, norm_zero, mul_zero] at h
    linarith
  refine ⟨hnz, ?_⟩
  have hd : 1/‖xi z‖ ≤ P/(Real.exp (-(Real.pi*t/4))/(3*Real.pi)) :=
    (div_le_div_iff₀ (norm_pos_iff.mpr hnz) hp).mpr (by simpa only [one_mul] using h)
  rw [norm_inv, inv_eq_one_div]
  calc
    1/‖xi z‖ ≤ P/(Real.exp (-(Real.pi*t/4))/(3*Real.pi)) := hd
    _ = 3*Real.pi*P*Real.exp (Real.pi*t/4) := by
      rw [div_div_eq_mul_div, Real.exp_neg, div_inv_eq_mul]
      ring

end
end RHTower
