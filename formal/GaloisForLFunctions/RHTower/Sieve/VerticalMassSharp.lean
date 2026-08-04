import GaloisForLFunctions.RHTower.Sieve.VerticalEdgeBound

/-!
# The vertical mass with a constant taken on the line itself

`exists_bound_integral_norm_mellin_line` bounds the vertical mass of the cutoff's transform on the
line `Re s = c` using a decay constant valid on the whole range `0 < Re s ≤ σmax`.  That constant
grows like `(N+H)^{σmax}`, whereas the mass on the line is of size `(N+H)^c`.  When `c < 1 < σmax`
the difference is a factor `(N+H)^{σmax-c}`, which in the application is
`exp( (9c₀/16)·log(N+H) / log⁹K )` — nine times the exponent of the saving the contour is bought
with, and hence fatal.

The remedy is to take the decay constant on the line itself.  Everything else in the proof is
unchanged; the constant is supplied as a hypothesis so that the caller can instantiate it at
`σmax = c`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set GaloisForLFunctions.HTGeometry

/-- **The vertical mass, with the decay constant taken on the line.**  Both terms are now of size
`(N+H)^c`: the near part by the trivial bound, the tails by the order-two decay at abscissa `c`. -/
theorem integral_norm_mellin_line_le {N H c T C : ℝ} (hN : 0 < N) (hH : 0 < H)
    (hc : 0 < c) (hT : 1 ≤ T)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ c →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) :
    ∫ y : ℝ in (-T)..T, ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
        ((c : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ 2 * ((N + H) ^ c / c) + 2 * C := by
  have hC : 0 ≤ C := by
    have h := hbd ((c : ℂ) + (1 : ℝ) * Complex.I) (by simp; exact hc) (by simp)
    refine le_trans ?_ h
    positivity
  set f : ℝ → ℝ := fun y => ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
    ((c : ℂ) + (y : ℝ) * Complex.I)‖ with hfdef
  have hre : ∀ y : ℝ, ((c : ℂ) + (y : ℝ) * Complex.I).re = c := fun y => by simp
  have hcont : Continuous f := (continuous_mellin_smoothWeight_line hH hc).norm
  have hii : ∀ a b : ℝ, IntervalIntegrable f volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have htriv : ∀ y : ℝ, f y ≤ (N + H) ^ c / c := by
    intro y
    have h := norm_mellin_smoothWeight_le_pow (N := N) (H := H) hN.le hH
      (s := (c : ℂ) + (y : ℝ) * Complex.I) (by rw [hre]; exact hc)
    rwa [hre] at h
  have htail : ∀ y : ℝ, 1 ≤ |y| → f y ≤ C * y ^ (-2 : ℤ) := fun y hy =>
    norm_mellin_smoothWeight_line_tail hc le_rfl hy hbd
  have hzi : ∀ a b : ℝ, (0 : ℝ) ∉ Set.uIcc a b →
      IntervalIntegrable (fun y : ℝ => C * y ^ (-2 : ℤ)) volume a b := fun a b h0 =>
    (intervalIntegral.intervalIntegrable_zpow (Or.inr h0)).const_mul C
  have hsplit : (∫ y : ℝ in (-T)..(-1), f y) + ((∫ y : ℝ in (-1 : ℝ)..1, f y)
      + (∫ y : ℝ in (1 : ℝ)..T, f y)) = ∫ y : ℝ in (-T)..T, f y := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hii (-1) 1) (hii 1 T),
      intervalIntegral.integral_add_adjacent_intervals (hii (-T) (-1)) (hii (-1) T)]
  have hmid : (∫ y : ℝ in (-1 : ℝ)..1, f y) ≤ 2 * ((N + H) ^ c / c) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (f := f)
      (g := fun _ => (N + H) ^ c / c) (by norm_num) (hii (-1) 1)
      intervalIntegrable_const (fun x _ => htriv x)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    calc (∫ y : ℝ in (-1 : ℝ)..1, f y) ≤ (1 - (-1)) * ((N + H) ^ c / c) := h
      _ = 2 * ((N + H) ^ c / c) := by ring
  have hTpos : (0 : ℝ) < T := by linarith
  have hTinv : (0 : ℝ) < T⁻¹ := by positivity
  have hright : (∫ y : ℝ in (1 : ℝ)..T, f y) ≤ C := by
    have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) T := by
      rw [Set.uIcc_of_le hT]
      intro hmem
      exact absurd hmem.1 (by norm_num)
    have h := intervalIntegral.integral_mono_on (μ := volume) (f := f)
      (g := fun y => C * y ^ (-2 : ℤ)) hT (hii 1 T) (hzi 1 T h0)
      (fun x hx => htail x (by rw [abs_of_pos (by linarith [hx.1] : (0 : ℝ) < x)]; exact hx.1))
    rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, h0⟩)] at h
    refine le_trans h ?_
    have hval : (T ^ ((-2 : ℤ) + 1) - (1 : ℝ) ^ ((-2 : ℤ) + 1)) / (((-2 : ℤ) : ℝ) + 1)
        = 1 - T⁻¹ := by
      rw [show (-2 : ℤ) + 1 = -1 from rfl, zpow_neg, zpow_neg, zpow_one, zpow_one, inv_one]
      push_cast
      ring
    rw [hval]
    nlinarith [hC, hTinv]
  have hleft : (∫ y : ℝ in (-T)..(-1 : ℝ), f y) ≤ C := by
    have h0 : (0 : ℝ) ∉ Set.uIcc (-T) (-1 : ℝ) := by
      rw [Set.uIcc_of_le (by linarith)]
      intro hmem
      exact absurd hmem.2 (by norm_num)
    have h := intervalIntegral.integral_mono_on (μ := volume) (f := f)
      (g := fun y => C * y ^ (-2 : ℤ)) (by linarith) (hii (-T) (-1)) (hzi (-T) (-1) h0)
      (fun x hx => htail x (by
        rw [abs_of_neg (by linarith [hx.2] : x < 0)]
        linarith [hx.2]))
    rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, h0⟩)] at h
    refine le_trans h ?_
    have hval : (((-1 : ℝ)) ^ ((-2 : ℤ) + 1) - (-T) ^ ((-2 : ℤ) + 1)) / (((-2 : ℤ) : ℝ) + 1)
        = 1 - T⁻¹ := by
      rw [show (-2 : ℤ) + 1 = -1 from rfl, zpow_neg, zpow_neg, zpow_one, zpow_one,
        show ((-1 : ℝ))⁻¹ = -1 by norm_num, inv_neg]
      push_cast
      ring
    rw [hval]
    nlinarith [hC, hTinv]
  rw [← hsplit]
  linarith

/-- **The left vertical edge, with the constant taken on the line.** -/
theorem norm_integral_vertical_edge_le {N H c T M C : ℝ} (hN : 0 < N) (hH : 0 < H)
    (hc : 0 < c) (hT : 1 ≤ T) (hM : 0 ≤ M)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ c →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C)
    {F : ℂ → ℂ}
    (hFcont : ContinuousOn (fun y : ℝ => F ((c : ℂ) + (y : ℝ) * Complex.I)) (Set.uIcc (-T) T))
    (hF : ∀ y ∈ Set.Icc (-T) T, ‖F ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ M) :
    ‖∫ y : ℝ in (-T)..T, F ((c : ℂ) + (y : ℝ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((c : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ M * (2 * ((N + H) ^ c / c) + 2 * C) := by
  set f : ℝ → ℝ := fun y => ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
    ((c : ℂ) + (y : ℝ) * Complex.I)‖ with hfdef
  have hWcont : Continuous fun y : ℝ =>
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I) :=
    continuous_mellin_smoothWeight_line hH hc
  have hii : IntervalIntegrable f volume (-T) T := hWcont.norm.intervalIntegrable _ _
  have hprodcont : ContinuousOn (fun y : ℝ => F ((c : ℂ) + (y : ℝ) * Complex.I)
      * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I))
      (Set.uIcc (-T) T) :=
    hFcont.mul hWcont.continuousOn
  have hTle : (-T : ℝ) ≤ T := by linarith
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hTle) ?_
  have hstep : (∫ y : ℝ in (-T)..T, ‖F ((c : ℂ) + (y : ℝ) * Complex.I)
      * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I)‖)
      ≤ ∫ y : ℝ in (-T)..T, M * f y := by
    refine intervalIntegral.integral_mono_on hTle
      hprodcont.norm.intervalIntegrable (hii.const_mul M) (fun y hy => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hF y hy) (norm_nonneg _)
  refine le_trans hstep ?_
  rw [intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_norm_mellin_line_le hN hH hc hT hbd) hM

end RHTower.Sieve
