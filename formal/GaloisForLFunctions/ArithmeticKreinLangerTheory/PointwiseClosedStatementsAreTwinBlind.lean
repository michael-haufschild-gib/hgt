import GaloisForLFunctions.HTGeometry.PrimeTorusKroneckerDensity
import Mathlib.NumberTheory.ArithmeticFunction.Liouville

/-!
# Pointwise-closed statements are twin-blind

The battery requires a selective input to fail for the Liouville twin `n ↦ λ(n) a(n)` of the weights.
This module shows which statements cannot do that.

**The twin is a limit of vertical shifts** (`exists_shifts_tendsto_liouville`). The logarithms of the
primes are independent over `ℚ`, so Kronecker gives times `τ_m` with `p^{iτ_m} → −1` at every prime.
Both `n ↦ n^{iτ}` and `λ` are completely multiplicative, so `n^{iτ_m} → λ(n)` for every `n ≥ 1`.

**Twin-blindness** (`liouvilleTwin_mem_of_isClosed`). A set of weight sequences that is closed for
pointwise convergence and contains every vertical shift `n ↦ a(n) n^{iτ}` contains the twin. Hence
(`exists_shift_not_mem_of_selective`) a pointwise-closed statement that the twin fails is failed by
some vertical shift of `a`: a selective input is either not pointwise-closed or not invariant under
vertical shifts.

Weil positivity is pointwise-closed: for each compactly supported test it involves finitely many
weights. Its selectivity therefore lives in the terms that do not move with the weights under a
shift, the pole and the Gamma factor, where the index-one window carries its square.
-/

open Complex Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

/-- **The Liouville twin is a limit of vertical shifts.** There are times `τ_m` with
`n^{iτ_m} → λ(n)` for every `n ≥ 1`. -/
theorem exists_shifts_tendsto_liouville :
    ∃ τ : ℕ → ℝ, ∀ n : ℕ, n ≠ 0 →
      Tendsto (fun m => (n : ℂ) ^ ((τ m : ℂ) * I)) atTop
        (𝓝 (ArithmeticFunction.liouville n : ℂ)) := by
  have hK : ∀ m : ℕ, ∃ t : ℝ, ∀ p : primesLE m,
      ‖(((p : Nat.Primes) : ℕ) : ℂ) ^ ((t : ℂ) * I) - cexp ((π : ℝ) * I)‖ < 1 / (m + 1) :=
    fun m => primeTorus_cpow_dense m (fun _ => π) (by positivity)
  choose τ hτ using hK
  refine ⟨τ, fun n hn => ?_⟩
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => simp [ArithmeticFunction.liouville_apply_one]
  | prime p hp =>
    rw [ArithmeticFunction.liouville_apply hp.ne_zero, ArithmeticFunction.cardFactors_apply_prime hp]
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
    refine ⟨max M p, fun m hm => ?_⟩
    have h := hτ m ⟨⟨p, hp⟩, (mem_primesLE m _).mpr (le_of_max_le_right hm)⟩
    rw [exp_pi_mul_I, sub_neg_eq_add] at h
    have hmM : (1 : ℝ) / (m + 1) ≤ 1 / (M + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ (le_of_max_le_left hm))
    rw [dist_eq_norm]
    push_cast
    rw [sub_neg_eq_add]
    exact h.trans_le (hmM.trans hM.le)
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hn
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hn
    simp only [Nat.cast_mul, natCast_mul_natCast_cpow, ArithmeticFunction.liouville_apply_mul,
      Int.cast_mul]
    exact (ha ha0).mul (hb hb0)

/-- **Pointwise-closed statements are twin-blind.** A set of weight sequences, closed for pointwise
convergence, that contains every vertical shift `n ↦ a(n) n^{iτ}` of `a` contains its Liouville twin
`n ↦ λ(n) a(n)`. -/
theorem liouvilleTwin_mem_of_isClosed {S : Set (ℕ → ℂ)} (hS : IsClosed S) (a : ℕ → ℂ)
    (hshift : ∀ τ : ℝ, (fun n => a n * (n : ℂ) ^ ((τ : ℂ) * I)) ∈ S) :
    (fun n => (ArithmeticFunction.liouville n : ℂ) * a n) ∈ S := by
  obtain ⟨τ, hτ⟩ := exists_shifts_tendsto_liouville
  refine hS.mem_of_tendsto (b := atTop)
    (f := fun m => fun n => a n * (n : ℂ) ^ ((τ m : ℂ) * I)) (tendsto_pi_nhds.mpr fun n => ?_)
    (Eventually.of_forall fun m => hshift (τ m))
  rcases eq_or_ne n 0 with rfl | hn
  · -- the times are eventually nonzero, so the zeroth coordinate is eventually `0`
    have h2 := hτ 2 (by norm_num)
    have hne : ∀ᶠ m in atTop, τ m ≠ 0 := by
      obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp h2) 1 one_pos
      refine eventually_atTop.mpr ⟨M, fun m hm hτ0 => ?_⟩
      have := hM m hm
      rw [hτ0, ArithmeticFunction.liouville_apply two_ne_zero,
        ArithmeticFunction.cardFactors_apply_prime Nat.prime_two, dist_eq_norm] at this
      norm_num at this
    simp only [ArithmeticFunction.map_zero, Int.cast_zero, zero_mul, Nat.cast_zero]
    refine tendsto_const_nhds.congr' (hne.mono fun m hm => ?_)
    show (0 : ℂ) = a 0 * (0 : ℂ) ^ ((τ m : ℂ) * I)
    rw [zero_cpow (mul_ne_zero (ofReal_ne_zero.mpr hm) I_ne_zero), mul_zero]
  · simpa only [mul_comm (a n)] using (hτ n hn).mul_const (a n)

/-- **A selective closed statement is not shift-invariant.** If a pointwise-closed set of weights
excludes the Liouville twin of `a`, it excludes some vertical shift of `a`. -/
theorem exists_shift_not_mem_of_selective {S : Set (ℕ → ℂ)} (hS : IsClosed S) (a : ℕ → ℂ)
    (htwin : (fun n => (ArithmeticFunction.liouville n : ℂ) * a n) ∉ S) :
    ∃ τ : ℝ, (fun n => a n * (n : ℂ) ^ ((τ : ℂ) * I)) ∉ S := by
  by_contra h
  push Not at h
  exact htwin (liouvilleTwin_mem_of_isClosed hS a h)

end GaloisForLFunctions.ArithmeticKreinLangerTheory
