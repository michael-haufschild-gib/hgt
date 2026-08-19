import GaloisForLFunctions.RHTower.PutnamKernel
import Mathlib.Topology.Algebra.Order.Floor

/-!
# One-sided limits of Putnam's kernel

On the whole line the kernel is

`C_a(x) = e^{(½-ia)x} - ⌊e^x⌋ e^{-(½+ia)x}` ,

because `⌊e^x⌋ = 0` for `x < 0`.  Its only discontinuities are therefore the jumps of `⌊e^x⌋`, which
occur exactly at `x = log m` for integers `m ≥ 1` and are downward of size `m^{-½-ia}`.  The kernel
is right-continuous everywhere and has a left limit everywhere.
-/

open Complex Filter Topology Set

noncomputable section

namespace RHTower

/-- The kernel, written with the integer part, valid on all of `ℝ`. -/
theorem putnamKernel_eq_floor (a x : ℝ) :
    putnamKernel a x
      = Complex.exp ((1 / 2 - (a : ℂ) * I) * x)
        - ((⌊Real.exp x⌋ : ℤ) : ℂ) * Complex.exp (-(1 / 2 + (a : ℂ) * I) * x) := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [putnamKernel_of_neg hx]
    have hlt : Real.exp x < 1 := by
      simpa using Real.exp_lt_one_iff.mpr hx
    have hge : (0 : ℝ) ≤ Real.exp x := (Real.exp_pos x).le
    have hfloor : ⌊Real.exp x⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]
      exact ⟨hge, hlt⟩
    rw [hfloor]
    simp
  · rw [putnamKernel_of_nonneg hx]
    have hfract : (Int.fract (Real.exp x) : ℝ) = Real.exp x - (⌊Real.exp x⌋ : ℤ) := rfl
    rw [hfract]
    push_cast
    rw [sub_mul, ← Complex.exp_add]
    congr 2
    ring

/-- The kernel is right-continuous. -/
theorem tendsto_putnamKernel_right (a y : ℝ) :
    Tendsto (putnamKernel a) (𝓝[>] y) (𝓝 (putnamKernel a y)) := by
  have hfloor : Tendsto (fun x : ℝ => ((⌊Real.exp x⌋ : ℤ) : ℂ)) (𝓝[>] y)
      (𝓝 (((⌊Real.exp y⌋ : ℤ) : ℂ))) := by
    have hexp : Tendsto Real.exp (𝓝[>] y) (𝓝[≥] (Real.exp y)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (Real.continuous_exp.continuousAt.continuousWithinAt) ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (Real.exp_le_exp.mpr (le_of_lt hx))
    have hfl := (tendsto_floor_right_pure_floor (α := ℝ) (Real.exp y)).comp hexp
    have := (tendsto_pure_nhds (fun n : ℤ => ((n : ℤ) : ℂ)) ⌊Real.exp y⌋).comp hfl
    exact this
  have hcont : Tendsto (fun x : ℝ => Complex.exp ((1 / 2 - (a : ℂ) * I) * x)
      - ((⌊Real.exp x⌋ : ℤ) : ℂ) * Complex.exp (-(1 / 2 + (a : ℂ) * I) * x)) (𝓝[>] y)
      (𝓝 (Complex.exp ((1 / 2 - (a : ℂ) * I) * y)
        - ((⌊Real.exp y⌋ : ℤ) : ℂ) * Complex.exp (-(1 / 2 + (a : ℂ) * I) * y))) := by
    refine Tendsto.sub ?_ (hfloor.mul ?_)
    · exact ((Complex.continuous_exp.comp
        (by fun_prop)).continuousAt.continuousWithinAt)
    · exact ((Complex.continuous_exp.comp
        (by fun_prop)).continuousAt.continuousWithinAt)
  have heq : putnamKernel a = fun x : ℝ => Complex.exp ((1 / 2 - (a : ℂ) * I) * x)
      - ((⌊Real.exp x⌋ : ℤ) : ℂ) * Complex.exp (-(1 / 2 + (a : ℂ) * I) * x) := by
    funext x
    exact putnamKernel_eq_floor a x
  rw [heq]
  exact hcont

/-- The kernel has a left limit everywhere, differing from its value by the jump of `⌊e^x⌋`. -/
theorem tendsto_putnamKernel_left (a y : ℝ) :
    Tendsto (putnamKernel a) (𝓝[<] y)
      (𝓝 (Complex.exp ((1 / 2 - (a : ℂ) * I) * y)
        - (((⌈Real.exp y⌉ - 1 : ℤ)) : ℂ) * Complex.exp (-(1 / 2 + (a : ℂ) * I) * y))) := by
  have hfloor : Tendsto (fun x : ℝ => ((⌊Real.exp x⌋ : ℤ) : ℂ)) (𝓝[<] y)
      (𝓝 (((⌈Real.exp y⌉ - 1 : ℤ) : ℂ))) := by
    have hexp : Tendsto Real.exp (𝓝[<] y) (𝓝[<] (Real.exp y)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (Real.continuous_exp.continuousAt.continuousWithinAt) ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact Real.exp_lt_exp.mpr hx
    have hfl := (tendsto_floor_left_pure_ceil_sub_one (α := ℝ) (Real.exp y)).comp hexp
    exact (tendsto_pure_nhds (fun n : ℤ => ((n : ℤ) : ℂ)) (⌈Real.exp y⌉ - 1)).comp hfl
  have hcont : Tendsto (fun x : ℝ => Complex.exp ((1 / 2 - (a : ℂ) * I) * x)
      - ((⌊Real.exp x⌋ : ℤ) : ℂ) * Complex.exp (-(1 / 2 + (a : ℂ) * I) * x)) (𝓝[<] y)
      (𝓝 (Complex.exp ((1 / 2 - (a : ℂ) * I) * y)
        - (((⌈Real.exp y⌉ - 1 : ℤ)) : ℂ) * Complex.exp (-(1 / 2 + (a : ℂ) * I) * y))) := by
    refine Tendsto.sub ?_ (hfloor.mul ?_)
    · exact ((Complex.continuous_exp.comp
        (by fun_prop)).continuousAt.continuousWithinAt)
    · exact ((Complex.continuous_exp.comp
        (by fun_prop)).continuousAt.continuousWithinAt)
  have heq : putnamKernel a = fun x : ℝ => Complex.exp ((1 / 2 - (a : ℂ) * I) * x)
      - ((⌊Real.exp x⌋ : ℤ) : ℂ) * Complex.exp (-(1 / 2 + (a : ℂ) * I) * x) := by
    funext x
    exact putnamKernel_eq_floor a x
  rw [heq]
  exact hcont

end RHTower

end
