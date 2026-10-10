import GaloisForLFunctions.HTGeometry.ReciprocalPositivityMinimumModulus
import GaloisForLFunctions.RHTower.XiEntireReal

/-!
# Reciprocal slice positivity puts the nearest zero on the critical line

At height `t` consider the horizontal pair product `h_t(σ) = Ξ(t+σ)·Ξ(t−σ)` with
`Ξ(z) = ξ(½ + z·i)` (`xiHorizontalPair`).  For complex `σ` its zeros are the points `σ = ±(z − t)`
over the zeros `z` of `Ξ`, so `‖σ‖` ranges over the distances `‖ρ − (½ + it)‖` from `½ + it` to the
zeros `ρ` of `ξ`.

**Nearest-zero law** (`xi_critical_zero_at_nearest_distance_of_reciprocal_nonneg`).  If every
Taylor coefficient of `1/h_t` at `0` is a nonnegative real number (*reciprocal slice positivity* at
height `t`), then the distance from `½ + it` to the zero set of `ξ` is attained at a critical zero
`½ + i(t ± d)`.

This is the minimum-modulus form of Pringsheim's theorem
(`HTGeometry.apply_eq_zero_of_inv_taylor_nonneg`).  On each circle inside the zero-free disk,
`‖h_t‖` is smallest at the positive real point.  So a zero on the boundary circle forces a zero at
the positive real point `σ = d`, i.e. a zero of `Ξ` at the real point `t + d` or `t − d`.

**Critical shadowing** (`exists_critical_zero_shadowing_of_reciprocal_nonneg`).  If reciprocal
slice positivity holds at the height of a zero `ρ`, then some critical zero `½ + iγ` satisfies
`|γ − Im ρ| ≤ |Re ρ − ½|`.  An off-line zero closer to the critical line than to every critical zero
in height is therefore excluded by reciprocal positivity at a single height: its own.
-/

open Complex Metric
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The horizontal pair product `Ξ(t + σ)·Ξ(t − σ)` at height `t`. -/
def xiHorizontalPair (t : ℝ) (σ : ℂ) : ℂ := XiC (t + σ) * XiC (t - σ)

theorem differentiable_xiHorizontalPair (t : ℝ) : Differentiable ℂ (xiHorizontalPair t) := by
  unfold xiHorizontalPair
  have h1 : Differentiable ℂ (fun σ : ℂ => XiC (t + σ)) :=
    XiC_differentiable.comp (by fun_prop)
  have h2 : Differentiable ℂ (fun σ : ℂ => XiC (t - σ)) :=
    XiC_differentiable.comp (by fun_prop)
  exact h1.mul h2

/-- Reciprocal slice positivity at height `t`: every Taylor coefficient of `1/h_t` at `0` is a
nonnegative real number. -/
def XiReciprocalSlicePositive (t : ℝ) : Prop :=
  ∀ n : ℕ, 0 ≤ iteratedDeriv n (fun σ => (xiHorizontalPair t σ)⁻¹) 0

/-- A zero of `Ξ(t ± σ)` is a zero of `ξ` at distance `‖σ‖` from `½ + it`. -/
theorem norm_sub_eq_of_XiC (t : ℝ) (σ : ℂ) :
    ‖(1 / 2 + ((t : ℂ) + σ) * I) - (1 / 2 + t * I)‖ = ‖σ‖ ∧
      ‖(1 / 2 + ((t : ℂ) - σ) * I) - (1 / 2 + t * I)‖ = ‖σ‖ := by
  constructor
  · rw [show (1 / 2 + ((t : ℂ) + σ) * I) - (1 / 2 + t * I) = σ * I by ring, norm_mul,
      Complex.norm_I, mul_one]
  · rw [show (1 / 2 + ((t : ℂ) - σ) * I) - (1 / 2 + t * I) = -(σ * I) by ring, norm_neg,
      norm_mul, Complex.norm_I, mul_one]

/-- **Nearest-zero law.**  Under reciprocal slice positivity at height `t`, if `ρ` is a zero of `ξ`
with no zero strictly closer to `½ + it`, then `ξ` vanishes at `½ + i(t + d)` or `½ + i(t − d)`,
where `d = ‖ρ − (½ + it)‖`. -/
theorem xi_critical_zero_at_nearest_distance_of_reciprocal_nonneg {t : ℝ}
    (hpos : XiReciprocalSlicePositive t) {ρ : ℂ} (hρ : xi ρ = 0)
    (hmin : ∀ ρ' : ℂ, xi ρ' = 0 → ‖ρ - (1 / 2 + t * I)‖ ≤ ‖ρ' - (1 / 2 + t * I)‖) :
    xi (1 / 2 + ((t + ‖ρ - (1 / 2 + t * I)‖ : ℝ) : ℂ) * I) = 0 ∨
      xi (1 / 2 + ((t - ‖ρ - (1 / 2 + t * I)‖ : ℝ) : ℂ) * I) = 0 := by
  set c : ℂ := 1 / 2 + t * I with hc
  set d : ℝ := ‖ρ - c‖ with hd
  rcases (norm_nonneg (ρ - c)).eq_or_lt with hd0 | hdpos
  · have hρc : ρ = c := by
      rw [← sub_eq_zero, ← norm_eq_zero]
      exact hd0.symm
    left
    have hd' : d = 0 := by rw [hd]; exact hd0.symm
    have ht : (((t + d : ℝ)) : ℂ) = t := by rw [hd']; simp
    rw [ht, ← hc, ← hρc]
    exact hρ
  · have hne : ∀ σ : ℂ, ‖σ‖ < d → xiHorizontalPair t σ ≠ 0 := by
      intro σ hσ h0
      rcases mul_eq_zero.mp h0 with h | h
      · have := hmin _ h
        rw [(norm_sub_eq_of_XiC t σ).1] at this
        linarith
      · have := hmin _ h
        rw [(norm_sub_eq_of_XiC t σ).2] at this
        linarith
    set w : ℂ := -I * (ρ - c) with hw
    have hwn : ‖w‖ = d := by
      rw [hw, norm_mul, norm_neg, Complex.norm_I, one_mul]
    have hw0 : xiHorizontalPair t w = 0 := by
      unfold xiHorizontalPair XiC
      apply mul_eq_zero_of_left
      convert hρ using 2
      rw [hw, hc]
      linear_combination (-(ρ - (1 / 2 + (t : ℂ) * I))) * Complex.I_sq
    have h := apply_eq_zero_of_inv_taylor_nonneg (differentiable_xiHorizontalPair t) hdpos hne
      hpos hwn hw0
    unfold xiHorizontalPair XiC at h
    rcases mul_eq_zero.mp h with h | h
    · left
      convert h using 2
      push_cast
      ring
    · right
      convert h using 2
      push_cast
      ring

/-- **Reciprocal positivity bounds the distance to the critical zeros.**  Under reciprocal slice
positivity at height `t`, for every zero `ρ` of `ξ` there is a critical zero `½ + iγ` with
`|γ − t| ≤ ‖ρ − (½ + it)‖`. -/
theorem exists_critical_zero_within_of_reciprocal_nonneg {t : ℝ}
    (hpos : XiReciprocalSlicePositive t) {ρ : ℂ} (hρ : xi ρ = 0) :
    ∃ γ : ℝ, xi (1 / 2 + (γ : ℂ) * I) = 0 ∧ |γ - t| ≤ ‖ρ - (1 / 2 + t * I)‖ := by
  set c : ℂ := 1 / 2 + t * I with hc
  set S : Set ℂ := {z ∈ ball c (‖ρ - c‖ + 1) | xi z = 0} with hS
  have hfin : S.Finite := xi_zeros_finite_ball c _
  have hρS : ρ ∈ S := ⟨by rw [mem_ball, dist_eq_norm]; linarith, hρ⟩
  obtain ⟨ρ₀, hρ₀S, hρ₀min⟩ := Set.exists_min_image S (fun z => ‖z - c‖) hfin ⟨ρ, hρS⟩
  have hρ₀le : ‖ρ₀ - c‖ ≤ ‖ρ - c‖ := hρ₀min ρ hρS
  have hglob : ∀ ρ' : ℂ, xi ρ' = 0 → ‖ρ₀ - c‖ ≤ ‖ρ' - c‖ := by
    intro ρ' hρ'
    by_cases hin : ρ' ∈ S
    · exact hρ₀min ρ' hin
    · have hfar : ‖ρ - c‖ + 1 ≤ ‖ρ' - c‖ := by
        by_contra hlt
        push Not at hlt
        exact hin ⟨by rw [mem_ball, dist_eq_norm]; exact hlt, hρ'⟩
      linarith
  rcases xi_critical_zero_at_nearest_distance_of_reciprocal_nonneg hpos hρ₀S.2 hglob with h | h
  · refine ⟨t + ‖ρ₀ - c‖, h, ?_⟩
    rw [add_sub_cancel_left, abs_of_nonneg (norm_nonneg _)]
    exact hρ₀le
  · refine ⟨t - ‖ρ₀ - c‖, h, ?_⟩
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (norm_nonneg _)]
    exact hρ₀le

/-- **Critical shadowing.**  If reciprocal slice positivity holds at the height of a zero `ρ` of
`ξ`, then some critical zero `½ + iγ` satisfies `|γ − Im ρ| ≤ |Re ρ − ½|`. -/
theorem exists_critical_zero_shadowing_of_reciprocal_nonneg {ρ : ℂ} (hρ : xi ρ = 0)
    (hpos : XiReciprocalSlicePositive ρ.im) :
    ∃ γ : ℝ, xi (1 / 2 + (γ : ℂ) * I) = 0 ∧ |γ - ρ.im| ≤ |ρ.re - 1 / 2| := by
  obtain ⟨γ, hγ, hle⟩ := exists_critical_zero_within_of_reciprocal_nonneg hpos hρ
  refine ⟨γ, hγ, ?_⟩
  have hnorm : ‖ρ - (1 / 2 + (ρ.im : ℂ) * I)‖ = |ρ.re - 1 / 2| := by
    have : ρ - (1 / 2 + (ρ.im : ℂ) * I) = ((ρ.re - 1 / 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at hle
  exact hle

end

end RHTower
