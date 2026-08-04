import GaloisForLFunctions.RHTower.Sieve.HorizontalEdgeBound
import GaloisForLFunctions.HTGeometry.SmoothWeightInversion

/-!
# The left vertical edge of the truncated contour

The left edge of the truncated rectangle is where the saving lives: the cutoff's transform is at
most `(N+H)^c / c` on the line `re s = c`, so pushing `c` below `1` replaces the trivial size `N`
by `N^c`.  What must be paid for it is a bound on the other factor along that edge, and that is the
only place the zero-free region is genuinely used.

The mass of the transform on a vertical line is bounded *independently of the truncation height*:
near the real axis by the trivial bound `(N+H)^c / c`, and beyond height `1` by the order-`2` decay
of the cutoff, whose integral over the tails converges.  So the left edge costs `sup‖F‖` times a
constant, not times `T`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set GaloisForLFunctions.HTGeometry

/-- The order-two tail bound on a vertical line, in divided form. -/
theorem norm_mellin_smoothWeight_line_tail {N H : ℝ} {σmax C c y : ℝ} (hc : 0 < c)
    (hcmax : c ≤ σmax) (hy : 1 ≤ |y|)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ σmax →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) :
    ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
        ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ C * y ^ (-2 : ℤ) := by
  have hre : ((c : ℂ) + (y : ℝ) * Complex.I).re = c := by simp
  have him : ((c : ℂ) + (y : ℝ) * Complex.I).im = y := by simp
  have hy0 : y ≠ 0 := by
    intro h
    rw [h] at hy
    norm_num at hy
  have hy2 : (0 : ℝ) < y ^ 2 := by positivity
  have h := hbd ((c : ℂ) + (y : ℝ) * Complex.I) (by rw [hre]; exact hc) (by rw [hre]; exact hcmax)
  rw [him] at h
  have hsq : |y| ^ (1 + 1) = y ^ 2 := by
    norm_num [sq_abs]
  rw [hsq] at h
  have hy2' : (y : ℝ) ^ (2 : ℤ) = y ^ 2 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
  have hz : C * (y : ℝ) ^ (-2 : ℤ) = C / y ^ 2 := by
    rw [zpow_neg, hy2', div_eq_mul_inv]
  rw [hz, le_div_iff₀ hy2, mul_comm]
  exact h

/-- **The vertical mass of the cutoff's transform, uniformly in the truncation height.**  The
constant depends on the cutoff and on the abscissa range only; in particular the bound does not
grow with `T`. -/
theorem exists_bound_integral_norm_mellin_line {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (σmax : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c T : ℝ, 0 < c → c ≤ σmax → 1 ≤ T →
      ∫ y : ℝ in (-T)..T, ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
          ((c : ℂ) + (y : ℝ) * Complex.I)‖
        ≤ 2 * ((N + H) ^ c / c) + 2 * C := by
  obtain ⟨C, hC, hbd⟩ := exists_bound_mellin_smoothWeight_im_pow hN hH 1 σmax
  refine ⟨C, hC, fun c T hc hcmax hT => ?_⟩
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
    norm_mellin_smoothWeight_line_tail hc hcmax hy hbd
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

/-- **The left vertical edge of the truncated rectangle.**  A bound `M` on the other factor along
the edge turns into the bound `M · (2·(N+H)^c/c + 2C)` for the edge, with no dependence on the
truncation height. -/
theorem exists_vertical_edge_bound {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (σmax : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : ℂ → ℂ) (c T M : ℝ), 0 < c → c ≤ σmax → 1 ≤ T → 0 ≤ M →
      ContinuousOn (fun y : ℝ => F ((c : ℂ) + (y : ℝ) * Complex.I)) (Set.uIcc (-T) T) →
      (∀ y ∈ Set.Icc (-T) T, ‖F ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ M) →
      ‖∫ y : ℝ in (-T)..T, F ((c : ℂ) + (y : ℝ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((c : ℂ) + (y : ℝ) * Complex.I)‖
        ≤ M * (2 * ((N + H) ^ c / c) + 2 * C) := by
  obtain ⟨C, hC, hbd⟩ := exists_bound_integral_norm_mellin_line hN hH σmax
  refine ⟨C, hC, fun F c T M hc hcmax hT hM hFcont hF => ?_⟩
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
  exact mul_le_mul_of_nonneg_left (hbd c T hc hcmax hT) hM

end RHTower.Sieve
