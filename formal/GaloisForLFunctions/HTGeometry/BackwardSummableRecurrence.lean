import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Uniqueness from the infinite boundary of a summable backward recurrence

An exponential weight turns a backward envelope into a nonnegative monotone
sequence. Its zero boundary value forces the entire sequence to vanish. This
supplies the infinite-boundary uniqueness needed for native tail realization.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology

theorem backward_exp_envelope_zero {q M : ℕ → ℝ} (c : ℝ) (hs : Summable q)
    (hM : ∀ n, 0 ≤ M n)
    (hstep : ∀ n, M n ≤ Real.exp (c * q n) * M (n + 1))
    (hlim : Tendsto M atTop (𝓝 0)) : ∀ n, M n = 0 := by
  let R (n : ℕ) := Real.exp (c * ∑ j ∈ Finset.range n, q j) * M n
  have hm : Monotone R := by
    apply monotone_nat_of_le_succ
    intro n
    calc
      R n ≤ Real.exp (c * ∑ j ∈ Finset.range n, q j) *
          (Real.exp (c * q n) * M (n + 1)) :=
        mul_le_mul_of_nonneg_left (hstep n) (Real.exp_pos _).le
      _ = R (n + 1) := by
        dsimp [R]
        rw [Finset.sum_range_succ, mul_add, Real.exp_add]
        ring
  have he := Real.continuous_exp.continuousAt.tendsto.comp
    (hs.hasSum.tendsto_sum_nat.const_mul c)
  have hr : Tendsto R atTop (𝓝 0) := by
    simpa only [R, Function.comp_def, mul_zero] using he.mul hlim
  intro n
  have hz : R n = 0 := le_antisymm (hm.ge_of_tendsto hr n)
    (mul_nonneg (Real.exp_pos _).le (hM n))
  exact (mul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero _)

theorem backward_genealogy_recurrence_zero {q δ : ℕ → ℝ}
    (hq : ∀ n, 0 ≤ q n) (hs : Summable q)
    (hrec : ∀ n, δ n = (1 + q n / 2) * δ (n + 1) - q n / 4 * δ (n + 2))
    (hlim : Tendsto δ atTop (𝓝 0)) : ∀ n, δ n = 0 := by
  let M (n : ℕ) := max |δ n| |δ (n + 1)|
  have hM (n : ℕ) : 0 ≤ M n := le_trans (abs_nonneg _) (le_max_left _ _)
  have hd (n : ℕ) : |δ n| ≤ (1 + 3 * q n / 4) * M (n + 1) := by
    have hq0 := hq n
    calc
      |δ n| = |(1 + q n / 2) * δ (n + 1) - q n / 4 * δ (n + 2)| := congrArg abs (hrec n)
      _ ≤ |(1 + q n / 2) * δ (n + 1)| + |q n / 4 * δ (n + 2)| := abs_sub _ _
      _ = (1 + q n / 2) * |δ (n + 1)| + q n / 4 * |δ (n + 2)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + q n / 2),
          abs_of_nonneg (by positivity : 0 ≤ q n / 4)]
      _ ≤ (1 + q n / 2) * M (n + 1) + q n / 4 * M (n + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
      _ = (1 + 3 * q n / 4) * M (n + 1) := by ring
  have hstep (n : ℕ) : M n ≤ Real.exp ((3 / 4 : ℝ) * q n) * M (n + 1) := by
    have hq0 := hq n
    have hpos := hM (n + 1)
    have he : 1 + 3 * q n / 4 ≤ Real.exp ((3 / 4 : ℝ) * q n) := by
      linarith [Real.add_one_le_exp ((3 / 4 : ℝ) * q n)]
    apply (max_le (hd n) ?_).trans (mul_le_mul_of_nonneg_right he hpos)
    have hle : |δ (n + 1)| ≤ M (n + 1) := le_max_left _ _
    nlinarith [mul_nonneg hq0 hpos]
  have hm : Tendsto M atTop (𝓝 0) := by
    simpa only [M, abs_zero, max_self] using
      hlim.abs.max ((tendsto_add_atTop_iff_nat 1).mpr hlim).abs
  have hz := backward_exp_envelope_zero (3 / 4) hs hM hstep hm
  intro n
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  have hle : |δ n| ≤ M n := le_max_left _ _
  simpa only [hz n] using hle

theorem backward_genealogy_recurrence_unique {q f g : ℕ → ℝ} {L : ℝ}
    (hq : ∀ n, 0 ≤ q n) (hs : Summable q)
    (hf : ∀ n, f n = f (n + 1) + q n / 4 * (2 * f (n + 1) - f (n + 2)))
    (hg : ∀ n, g n = g (n + 1) + q n / 4 * (2 * g (n + 1) - g (n + 2)))
    (hflim : Tendsto f atTop (𝓝 L)) (hglim : Tendsto g atTop (𝓝 L)) : f = g := by
  have hz := backward_genealogy_recurrence_zero (δ := fun n => f n - g n) hq hs
    (fun n => by rw [hf n, hg n]; ring)
    (by simpa only [sub_self] using hflim.sub hglim)
  exact funext fun n => sub_eq_zero.mp (hz n)

end
end GaloisForLFunctions.HTGeometry
