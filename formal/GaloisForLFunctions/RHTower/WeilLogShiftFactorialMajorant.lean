import GaloisForLFunctions.RHTower.WeilLogShiftUniformBallGenericity
import Mathlib.Data.Nat.Factorial.Basic

/-!
# The algebraic class of finite factorial majorants

Allowing the order, exponential rate, prefactor, and cutoff to vary still
gives a class closed under addition, subtraction, and scalar multiplication.
For bounded recovery histories, membership at some real shift is equivalent
to membership at the origin. Summable factorial-normalized sequences belong
to this class before normalization.
-/

open Filter Topology Real
open scoped BoundedContinuousFunction

namespace RHTower

open WeilExcess

/-- An eventual majorant of some finite natural factorial order and real
exponential rate; all parameters are allowed to depend on the sequence. -/
def WeilLogShiftHasFactorialMajorant (f : ℕ → ℝ) : Prop :=
  ∃ (m : ℕ) (A D : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n →
    |f n| ≤ D * exp (A * n) * (n.factorial : ℝ) ^ m

theorem weilLogShiftHasFactorialMajorant_zero :
    WeilLogShiftHasFactorialMajorant (fun _ => 0) := by
  refine ⟨0, 0, 0, 0, fun n _ => ?_⟩
  simp

/-- Eventual absolute domination preserves finite factorial regularity. -/
theorem weilLogShiftHasFactorialMajorant_of_eventually_abs_le {f g : ℕ → ℝ}
    (hfg : ∀ᶠ n : ℕ in atTop, |f n| ≤ |g n|) (hg : WeilLogShiftHasFactorialMajorant g) :
    WeilLogShiftHasFactorialMajorant f := by
  obtain ⟨m, A, D, N, hg⟩ := hg
  obtain ⟨M, hM⟩ := eventually_atTop.mp hfg
  refine ⟨m, A, D, max N M, fun n hn => ?_⟩
  exact (hM n ((le_max_right _ _).trans hn)).trans (hg n ((le_max_left _ _).trans hn))

/-- Multiplying by any real scalar preserves the majorant class. -/
theorem weilLogShiftHasFactorialMajorant_mul (c : ℝ) {f : ℕ → ℝ}
    (hf : WeilLogShiftHasFactorialMajorant f) :
    WeilLogShiftHasFactorialMajorant (fun n => c * f n) := by
  obtain ⟨m, A, D, N, hf⟩ := hf
  refine ⟨m, A, |c| * D, N, fun n hn => ?_⟩
  rw [abs_mul]
  calc
    |c| * |f n| ≤ |c| * (D * exp (A * n) * (n.factorial : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left (hf n hn) (abs_nonneg c)
    _ = _ := by ring

private theorem factorial_majorant_enlarge (n m M : ℕ) (A B D : ℝ)
    (hm : m ≤ M) (hAB : A ≤ B) :
    D * exp (A * n) * (n.factorial : ℝ) ^ m ≤
      |D| * exp (B * n) * (n.factorial : ℝ) ^ M := by
  have hfac : (1 : ℝ) ≤ n.factorial := by
    exact_mod_cast (show 1 ≤ n.factorial by have h := Nat.factorial_pos n; omega)
  have hweight : exp (A * n) * (n.factorial : ℝ) ^ m ≤
      exp (B * n) * (n.factorial : ℝ) ^ M := by
    exact mul_le_mul
      (exp_le_exp.mpr (mul_le_mul_of_nonneg_right hAB (Nat.cast_nonneg (α := ℝ) n)))
      (pow_le_pow_right₀ hfac hm) (by positivity) (exp_pos _).le
  calc
    _ = D * (exp (A * n) * (n.factorial : ℝ) ^ m) := by ring
    _ ≤ |D| * (exp (A * n) * (n.factorial : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_right (le_abs_self D) (by positivity)
    _ ≤ |D| * (exp (B * n) * (n.factorial : ℝ) ^ M) :=
      mul_le_mul_of_nonneg_left hweight (abs_nonneg D)
    _ = _ := by ring

/-- Different factorial orders and rates can be merged into one common
majorant, so the class is closed under addition. -/
theorem weilLogShiftHasFactorialMajorant_add {f g : ℕ → ℝ}
    (hf : WeilLogShiftHasFactorialMajorant f) (hg : WeilLogShiftHasFactorialMajorant g) :
    WeilLogShiftHasFactorialMajorant (fun n => f n + g n) := by
  obtain ⟨mf, Af, Df, Nf, hf⟩ := hf
  obtain ⟨mg, Ag, Dg, Ng, hg⟩ := hg
  refine ⟨max mf mg, max Af Ag, |Df| + |Dg|, max Nf Ng, fun n hn => ?_⟩
  have hf' := (hf n ((le_max_left _ _).trans hn)).trans
    (factorial_majorant_enlarge n mf (max mf mg) Af (max Af Ag) Df
      (le_max_left _ _) (le_max_left _ _))
  have hg' := (hg n ((le_max_right _ _).trans hn)).trans
    (factorial_majorant_enlarge n mg (max mf mg) Ag (max Af Ag) Dg
      (le_max_right _ _) (le_max_right _ _))
  calc
    |f n + g n| ≤ |f n| + |g n| := abs_add_le _ _
    _ ≤ |Df| * exp (max Af Ag * n) * (n.factorial : ℝ) ^ max mf mg +
        |Dg| * exp (max Af Ag * n) * (n.factorial : ℝ) ^ max mf mg := add_le_add hf' hg'
    _ = _ := by ring

/-- The union of all finite factorial classes is closed under subtraction. -/
theorem weilLogShiftHasFactorialMajorant_sub {f g : ℕ → ℝ}
    (hf : WeilLogShiftHasFactorialMajorant f) (hg : WeilLogShiftHasFactorialMajorant g) :
    WeilLogShiftHasFactorialMajorant (fun n => f n - g n) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using
    weilLogShiftHasFactorialMajorant_add hf (weilLogShiftHasFactorialMajorant_mul (-1) hg)

/-- Nonzero scalar multiplication preserves membership in both directions. -/
theorem weilLogShiftHasFactorialMajorant_mul_iff (c : ℝ) (hc : c ≠ 0) (f : ℕ → ℝ) :
    WeilLogShiftHasFactorialMajorant (fun n => c * f n) ↔ WeilLogShiftHasFactorialMajorant f := by
  constructor
  · intro hf
    simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] using
      weilLogShiftHasFactorialMajorant_mul c⁻¹ hf
  · exact weilLogShiftHasFactorialMajorant_mul c

/-- Summability after any finite factorial and exponential normalization
forces an eventual majorant for the original sequence. -/
theorem weilLogShiftHasFactorialMajorant_of_summable_normalization
    (f : ℕ → ℝ) (m : ℕ) (A : ℝ)
    (hs : Summable (fun n : ℕ => exp (-(A * n)) * f n / (n.factorial : ℝ) ^ m)) :
    WeilLogShiftHasFactorialMajorant f := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp hs.norm.tendsto_atTop_zero).2 1 (by norm_num))
  refine ⟨m, A, 1, N, fun n hn => ?_⟩
  have hsmall := hN n hn
  have hfacpos : 0 < (n.factorial : ℝ) ^ m :=
    pow_pos (by exact_mod_cast Nat.factorial_pos n) m
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (exp_pos _), abs_of_pos hfacpos] at hsmall
  have hweighted := (div_le_iff₀ hfacpos).mp hsmall.le
  rw [one_mul] at hweighted
  have hscaled := mul_le_mul_of_nonneg_left hweighted (exp_pos (A * n)).le
  rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul] at hscaled
  simpa only [one_mul] using hscaled

/-- A factorial majorant at any real shift also bounds the origin moment
with the same order, rate, and prefactor after enlarging the cutoff. -/
theorem weilLogShiftHasFactorialMajorant_origin_of_shift (h : ℕ →ᵇ ℝ) (y : ℝ)
    (hy : WeilLogShiftHasFactorialMajorant (weilLogShiftRecoveryMoment y h)) :
    WeilLogShiftHasFactorialMajorant (weilLogShiftRecoveryMoment 0 h) := by
  by_cases hy0 : y = 0
  · subst y
    exact hy
  refine weilLogShiftHasFactorialMajorant_of_eventually_abs_le ?_ hy
  have h0y : |(0 : ℝ)| < |y| := by simpa only [abs_zero] using abs_pos.mpr hy0
  filter_upwards [eventually_mul_pairedLogKernel_le_of_abs_lt h0y 1] with n hn
  have hkernel : pairedLogKernel 0 n ≤ pairedLogKernel y n := by
    simpa only [one_mul] using hn
  simp only [weilLogShiftRecoveryMoment, abs_mul,
    abs_of_pos (pairedLogKernel_pos 0 n), abs_of_pos (pairedLogKernel_pos y n)]
  exact mul_le_mul_of_nonneg_left hkernel (abs_nonneg _)

/-- Existence of any factorial-regular shift is exactly origin regularity. -/
theorem weilLogShiftHasFactorialMajorant_some_shift_iff_origin (h : ℕ →ᵇ ℝ) :
    (∃ y : ℝ, WeilLogShiftHasFactorialMajorant (weilLogShiftRecoveryMoment y h)) ↔
      WeilLogShiftHasFactorialMajorant (weilLogShiftRecoveryMoment 0 h) := by
  constructor
  · rintro ⟨y, hy⟩
    exact weilLogShiftHasFactorialMajorant_origin_of_shift h y hy
  · intro hh
    exact ⟨0, hh⟩

end RHTower
