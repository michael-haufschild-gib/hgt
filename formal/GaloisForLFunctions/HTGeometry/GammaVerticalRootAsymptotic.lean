/-
# The vertical line is invisible to the root

Along a vertical line the Gamma modulus is squeezed between a constant multiple of the real
Gamma value and that value itself.  The upper bound is the integral representation; the lower one
is the functional equation, since the ratio `Γ(x)/‖Γ(x+iy)‖` is multiplied by `x/‖x+iy‖ ≤ 1` at
each unit step and is therefore bounded by its values on `[1,2]`.  A constant factor is invisible
to the `k`-th root, so the root asymptotic of a Gamma value along a complex ray is the real one.

Main results:
* `gammaVerticalRatio_add_one_le` — the comparison ratio decreases along unit steps.
* `exists_const_Gamma_le_norm_Gamma_vertical` — **`Γ(x) ≤ C‖Γ(x+iy)‖` for all `x ≥ 1`**.
* `tendsto_const_rpow_inv` — a positive constant is invisible to the root.
* `tendsto_norm_Gamma_linear_rpow_inv` — **`‖Γ(cx+β)‖^{1/x}/x^c → (c/e)^c`**.
-/
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus
import GaloisForLFunctions.HTGeometry.GammaRootAsymptotic
import GaloisForLFunctions.HTGeometry.GammaWendelInequality

open Filter Topology Real Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The point `x + iy` of the vertical line at height `y`. -/
def verticalPoint (y x : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * Complex.I

theorem verticalPoint_re (y x : ℝ) : (verticalPoint y x).re = x := by
  simp [verticalPoint]

theorem verticalPoint_add_one (y x : ℝ) :
    verticalPoint y (x + 1) = verticalPoint y x + 1 := by
  simp only [verticalPoint, Complex.ofReal_add, Complex.ofReal_one]
  ring

theorem verticalPoint_add_nat (y x : ℝ) (n : ℕ) :
    verticalPoint y (x + n) = verticalPoint y x + (n : ℂ) := by
  simp only [verticalPoint, Complex.ofReal_add, Complex.ofReal_natCast]
  ring

theorem verticalPoint_ne_zero {y x : ℝ} (hx : 0 < x) : verticalPoint y x ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [verticalPoint_re] at this
  simp at this
  exact hx.ne' this

theorem norm_Gamma_verticalPoint_pos {y x : ℝ} (hx : 0 < x) :
    0 < ‖Complex.Gamma (verticalPoint y x)‖ := by
  refine norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos ?_)
  rw [verticalPoint_re]
  exact hx

theorem le_norm_verticalPoint (y x : ℝ) : x ≤ ‖verticalPoint y x‖ := by
  have h := Complex.abs_re_le_norm (verticalPoint y x)
  rw [verticalPoint_re] at h
  exact le_trans (le_abs_self x) h

/-- The comparison ratio between the real Gamma value and the modulus on the vertical line. -/
def gammaVerticalRatio (y x : ℝ) : ℝ :=
  Real.Gamma x / ‖Complex.Gamma (verticalPoint y x)‖

theorem gammaVerticalRatio_nonneg {y x : ℝ} (hx : 0 < x) : 0 ≤ gammaVerticalRatio y x :=
  div_nonneg (Real.Gamma_pos_of_pos hx).le (norm_nonneg _)

/-- **The comparison ratio decreases along a unit step.**  The functional equation multiplies it
by `x/‖x+iy‖ ≤ 1`. -/
theorem gammaVerticalRatio_add_one_le {y x : ℝ} (hx : 0 < x) :
    gammaVerticalRatio y (x + 1) ≤ gammaVerticalRatio y x := by
  have hGr : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hGc : 0 < ‖Complex.Gamma (verticalPoint y x)‖ := norm_Gamma_verticalPoint_pos hx
  have hstep : Complex.Gamma (verticalPoint y (x + 1))
      = verticalPoint y x * Complex.Gamma (verticalPoint y x) := by
    rw [verticalPoint_add_one]
    exact Complex.Gamma_add_one _ (verticalPoint_ne_zero hx)
  have hnorm : ‖Complex.Gamma (verticalPoint y (x + 1))‖
      = ‖verticalPoint y x‖ * ‖Complex.Gamma (verticalPoint y x)‖ := by
    rw [hstep, norm_mul]
  have hreal : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one hx.ne'
  have hge : x ≤ ‖verticalPoint y x‖ := le_norm_verticalPoint y x
  have hVpos : 0 < ‖verticalPoint y x‖ := lt_of_lt_of_le hx hge
  rw [gammaVerticalRatio, gammaVerticalRatio, hreal, hnorm,
    div_le_div_iff₀ (by positivity) hGc]
  have hmul := mul_le_mul_of_nonneg_left hge (mul_nonneg hGr.le hGc.le)
  linarith [hmul]

theorem gammaVerticalRatio_add_nat_le {y x : ℝ} (hx : 0 < x) (n : ℕ) :
    gammaVerticalRatio y (x + n) ≤ gammaVerticalRatio y x := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hxm : 0 < x + (m : ℝ) := by positivity
      have hcast : x + ((m + 1 : ℕ) : ℝ) = (x + (m : ℝ)) + 1 := by push_cast; ring
      rw [hcast]
      exact le_trans (gammaVerticalRatio_add_one_le hxm) ih

/-! ## The ratio is bounded on the whole ray -/

theorem Gamma_le_one_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) : Real.Gamma x ≤ 1 := by
  obtain ⟨h1, h2⟩ := hx
  have ha0 : (0 : ℝ) ≤ x - 1 := by linarith
  have ha1 : x - 1 ≤ 1 := by linarith
  have h := Gamma_add_le (x := 1) (a := x - 1) one_pos ha0 ha1
  rw [Real.Gamma_one, Real.one_rpow, one_mul] at h
  have hx' : (1 : ℝ) + (x - 1) = x := by ring
  rw [hx'] at h
  exact h

theorem continuous_verticalPoint (y : ℝ) : Continuous (verticalPoint y) := by
  unfold verticalPoint
  fun_prop

theorem verticalPoint_ne_neg_natCast {y x : ℝ} (hx : 0 < x) (m : ℕ) :
    verticalPoint y x ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  rw [verticalPoint_re] at hre
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem continuousAt_Gamma_verticalPoint {y x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun t : ℝ => Complex.Gamma (verticalPoint y t)) x := by
  have h1 : ContinuousAt Complex.Gamma (verticalPoint y x) :=
    (Complex.differentiableAt_Gamma _ (verticalPoint_ne_neg_natCast hx)).continuousAt
  exact h1.comp ((continuous_verticalPoint y).continuousAt)

theorem continuousOn_norm_Gamma_verticalPoint (y : ℝ) :
    ContinuousOn (fun x : ℝ => ‖Complex.Gamma (verticalPoint y x)‖) (Icc (1 : ℝ) 2) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx.1
  exact ((continuousAt_Gamma_verticalPoint hx0).norm).continuousWithinAt

theorem exists_pos_le_norm_Gamma_verticalPoint (y : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Icc (1 : ℝ) 2, M ≤ ‖Complex.Gamma (verticalPoint y x)‖ := by
  obtain ⟨x₀, hx₀mem, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (by norm_num : (1 : ℝ) ≤ 2))
    (continuousOn_norm_Gamma_verticalPoint y)
  refine ⟨‖Complex.Gamma (verticalPoint y x₀)‖, ?_, fun x hx => isMinOn_iff.mp hmin x hx⟩
  exact norm_Gamma_verticalPoint_pos (lt_of_lt_of_le one_pos hx₀mem.1)

/-- **A constant compares the real Gamma value with the modulus on any vertical line.** -/
theorem exists_const_Gamma_le_norm_Gamma_vertical (y : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      Real.Gamma x ≤ C * ‖Complex.Gamma (verticalPoint y x)‖ := by
  obtain ⟨M, hM, hMle⟩ := exists_pos_le_norm_Gamma_verticalPoint y
  refine ⟨1 / M, by positivity, ?_⟩
  intro x hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hfl : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  set n : ℕ := ⌊x⌋₊ - 1 with hn
  have hncast : (n : ℝ) = (⌊x⌋₊ : ℝ) - 1 := by
    rw [hn, Nat.cast_sub hfl, Nat.cast_one]
  have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hlt_floor : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  set x₀ : ℝ := x - (n : ℝ) with hx₀
  have hx₀1 : 1 ≤ x₀ := by rw [hx₀, hncast]; linarith
  have hx₀2 : x₀ ≤ 2 := by rw [hx₀, hncast]; linarith
  have hx₀pos : 0 < x₀ := lt_of_lt_of_le one_pos hx₀1
  have hsum : x₀ + (n : ℝ) = x := by rw [hx₀]; ring
  have hratio : gammaVerticalRatio y x ≤ gammaVerticalRatio y x₀ := by
    have := gammaVerticalRatio_add_nat_le (y := y) hx₀pos n
    rwa [hsum] at this
  have hx₀le : gammaVerticalRatio y x₀ ≤ 1 / M := by
    rw [gammaVerticalRatio, div_le_div_iff₀ (norm_Gamma_verticalPoint_pos hx₀pos) hM]
    have h1 := Gamma_le_one_of_mem_Icc ⟨hx₀1, hx₀2⟩
    have h2 := hMle x₀ ⟨hx₀1, hx₀2⟩
    nlinarith [Real.Gamma_pos_of_pos hx₀pos, (norm_Gamma_verticalPoint_pos (y := y) hx₀pos)]
  have hGc : 0 < ‖Complex.Gamma (verticalPoint y x)‖ := norm_Gamma_verticalPoint_pos hx0
  have hfin : Real.Gamma x / ‖Complex.Gamma (verticalPoint y x)‖ ≤ 1 / M :=
    le_trans hratio hx₀le
  rw [div_le_iff₀ hGc] at hfin
  exact hfin

/-! ## The root asymptotic along a complex ray -/

/-- A positive constant is invisible to the `x`-th root. -/
theorem tendsto_const_rpow_inv {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => a ^ (1 / x)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun x : ℝ => Real.log a / x) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop tendsto_id _
  have hexp := (Real.continuous_exp.tendsto _).comp hlog
  rw [Real.exp_zero] at hexp
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  show Real.exp (Real.log a / x) = a ^ (1 / x)
  rw [Real.rpow_def_of_pos ha]
  congr 1
  ring

theorem ofReal_add_eq_verticalPoint (t : ℝ) (β : ℂ) :
    ((t : ℝ) : ℂ) + β = verticalPoint β.im (t + β.re) := by
  simp [verticalPoint, Complex.ext_iff]

/-- **The root asymptotic of a Gamma value along a complex ray**:
`‖Γ(cx+β)‖^{1/x}/x^c → (c/e)^c`.  The imaginary part of `β` only changes the modulus by a bounded
factor, which the root cannot see. -/
theorem tendsto_norm_Gamma_linear_rpow_inv {c : ℝ} (hc : 0 < c) (β : ℂ) :
    Tendsto (fun x : ℝ => ‖Complex.Gamma (((c * x : ℝ) : ℂ) + β)‖ ^ (1 / x) / x ^ c) atTop
      (𝓝 ((c / Real.exp 1) ^ c)) := by
  obtain ⟨C, hC, hCle⟩ := exists_const_Gamma_le_norm_Gamma_vertical β.im
  have hreal := tendsto_Gamma_linear_rpow_inv hc β.re
  have hconst : Tendsto (fun x : ℝ => (1 / C) ^ (1 / x)) atTop (𝓝 1) :=
    tendsto_const_rpow_inv (by positivity)
  have hlow : Tendsto (fun x : ℝ =>
      Real.Gamma (c * x + β.re) ^ (1 / x) / x ^ c * (1 / C) ^ (1 / x)) atTop
      (𝓝 ((c / Real.exp 1) ^ c)) := by
    have h := hreal.mul hconst
    rwa [mul_one] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hreal ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop ((1 - β.re) / c)]
      with x hx hxb
    have h1 : (1 : ℝ) ≤ c * x + β.re := by
      have := (div_le_iff₀ hc).mp hxb
      linarith
    have hpos : (0 : ℝ) < c * x + β.re := by linarith
    have hxc : (0 : ℝ) < x ^ c := Real.rpow_pos_of_pos hx c
    have hinv : (0 : ℝ) < 1 / x := by positivity
    have hpt : ((c * x : ℝ) : ℂ) + β = verticalPoint β.im (c * x + β.re) :=
      ofReal_add_eq_verticalPoint _ _
    have hGnn : (0 : ℝ) ≤ Real.Gamma (c * x + β.re) := (Real.Gamma_pos_of_pos hpos).le
    have hcomp := hCle (c * x + β.re) h1
    have hL : Real.Gamma (c * x + β.re) ^ (1 / x) * (1 / C) ^ (1 / x)
        ≤ ‖Complex.Gamma (((c * x : ℝ) : ℂ) + β)‖ ^ (1 / x) := by
      rw [← Real.mul_rpow hGnn (by positivity), hpt]
      refine Real.rpow_le_rpow (by positivity) ?_ hinv.le
      rw [mul_one_div, div_le_iff₀ hC]
      linarith [hcomp]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hxc hxc]
    exact mul_le_mul_of_nonneg_right hL hxc.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop ((1 - β.re) / c)]
      with x hx hxb
    have h1 : (1 : ℝ) ≤ c * x + β.re := by
      have := (div_le_iff₀ hc).mp hxb
      linarith
    have hpos : (0 : ℝ) < c * x + β.re := by linarith
    have hxc : (0 : ℝ) < x ^ c := Real.rpow_pos_of_pos hx c
    have hinv : (0 : ℝ) < 1 / x := by positivity
    have hpt : ((c * x : ℝ) : ℂ) + β = verticalPoint β.im (c * x + β.re) :=
      ofReal_add_eq_verticalPoint _ _
    have hupper : ‖Complex.Gamma (((c * x : ℝ) : ℂ) + β)‖ ≤ Real.Gamma (c * x + β.re) := by
      rw [hpt]
      have := norm_Gamma_le_Gamma_re (s := verticalPoint β.im (c * x + β.re))
        (by rw [verticalPoint_re]; exact hpos)
      rwa [verticalPoint_re] at this
    have hpow : ‖Complex.Gamma (((c * x : ℝ) : ℂ) + β)‖ ^ (1 / x)
        ≤ Real.Gamma (c * x + β.re) ^ (1 / x) :=
      Real.rpow_le_rpow (norm_nonneg _) hupper hinv.le
    rw [div_le_div_iff₀ hxc hxc]
    exact mul_le_mul_of_nonneg_right hpow hxc.le

/-- The complex-ray root asymptotic along the natural numbers. -/
theorem tendsto_norm_Gamma_linear_rpow_inv_nat {c : ℝ} (hc : 0 < c) (β : ℂ) :
    Tendsto (fun k : ℕ => ‖Complex.Gamma (((c * (k : ℝ) : ℝ) : ℂ) + β)‖ ^ (1 / (k : ℝ))
      / (k : ℝ) ^ c) atTop (𝓝 ((c / Real.exp 1) ^ c)) :=
  (tendsto_norm_Gamma_linear_rpow_inv hc β).comp tendsto_natCast_atTop_atTop

end

end GaloisForLFunctions.HTGeometry
