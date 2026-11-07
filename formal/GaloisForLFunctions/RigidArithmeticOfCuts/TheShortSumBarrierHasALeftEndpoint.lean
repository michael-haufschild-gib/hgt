import GaloisForLFunctions.RigidArithmeticOfCuts.EffectiveKroneckerAtArithmeticScale
import Mathlib.NumberTheory.Primorial

/-!
# The short-sum barrier has a left endpoint

Below a certain length, a prime polynomial at height `T` has no cancellation at all: at some height up to
`T`, every phase can be aligned at once in the weighted `ℓ¹` sense. Effective Kronecker gives the length.

For the primes up to `y`, any targets, and `D ≥ 5`, there is `t ∈ [0, T]` with

`Σ_{p≤y} a_p cos(t log p − θ_p) ≥ (1 − 5/(D+1)) Σ_{p≤y} a_p`,

as soon as `T ≥ 4 (D+1) 4^{(2D+1) y}`. So **no nontrivial sup bound for prime polynomials is possible below
length `c log T`**, and all signs of the phases are reachable. In particular at some height up to `T`, every
prime up to `y` has `p^{-it}` close to `−1` in the weighted sense: the Euler product at that height reads the
Liouville twin up to `y`.

The barrier runs up to the Vinogradov–Korobov length. This is its left endpoint, as a theorem.
-/

open Finset Complex

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The primes up to `y`. -/
def primesUpTo (y : ℕ) : Finset ℕ := (range (y + 1)).filter Nat.Prime

theorem prime_of_mem_primesUpTo {y p : ℕ} (hp : p ∈ primesUpTo y) : p.Prime := (mem_filter.mp hp).2

theorem radicalOf_primesUpTo (y : ℕ) : radicalOf (primesUpTo y) = primorial y := rfl

/-- **Alignment at height `T`.** -/
theorem exists_height_aligned (y D : ℕ) (θ a : ℕ → ℝ) (ha : ∀ p ∈ primesUpTo y, 0 ≤ a p) {T : ℝ}
    (hT : 4 * ((D : ℝ) + 1) * (4 : ℝ) ^ ((2 * D + 1) * y) ≤ T) :
    ∃ t ∈ Set.Icc (0 : ℝ) T,
      (1 - 5 / ((D : ℝ) + 1)) * ∑ p ∈ primesUpTo y, a p ≤
        ∑ p ∈ primesUpTo y, a p * Real.cos (t * Real.log p - θ p) := by
  have hP : ∀ p ∈ primesUpTo y, p.Prime := fun p hp => prime_of_mem_primesUpTo hp
  have hR : (radicalOf (primesUpTo y) : ℝ) ^ (2 * D + 1) ≤ (4 : ℝ) ^ ((2 * D + 1) * y) := by
    rw [radicalOf_primesUpTo, mul_comm (2 * D + 1) y, pow_mul]
    refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _
    exact_mod_cast primorial_le_four_pow y
  have hthreshold : 4 * ((D : ℝ) + 1) * (radicalOf (primesUpTo y) : ℝ) ^ (D + 1) *
      ((exponentBox (primesUpTo y) D).card : ℝ) ≤ T := by
    refine (threshold_le D hP).trans (le_trans ?_ hT)
    exact mul_le_mul_of_nonneg_left hR (by positivity)
  obtain ⟨t, ht, hbound⟩ := exists_height_phase_return D hP θ a ha hthreshold
  refine ⟨t, ht, ?_⟩
  have hexp : ∑ p ∈ primesUpTo y, a p * (1 - Real.cos (t * Real.log p - θ p)) =
      ∑ p ∈ primesUpTo y, a p - ∑ p ∈ primesUpTo y, a p * Real.cos (t * Real.log p - θ p) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun p _ => by ring
  rw [hexp] at hbound
  have hrw2 : 5 * (∑ p ∈ primesUpTo y, a p) / ((D : ℝ) + 1) =
      5 / ((D : ℝ) + 1) * ∑ p ∈ primesUpTo y, a p := by ring
  rw [hrw2] at hbound
  linarith

/-- The real part of a prime term. -/
theorem re_prime_cpow (σ t : ℝ) {p : ℕ} (hp : p.Prime) :
    (((p : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))).re = (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hne : ((p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hp0.le]
  have hsplit : ((Real.log p : ℝ) : ℂ) * (-((σ : ℂ) + (t : ℂ) * I)) =
      ((-(σ * Real.log p) : ℝ) : ℂ) + ((-(t * Real.log p) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  rw [Real.cos_neg, Real.rpow_def_of_pos hp0]
  have : Real.log p * -σ = -(σ * Real.log p) := by ring
  rw [this]
  ring

/-- **No cancellation below length `c log T`.** The prime polynomial of length `y` has size at least
`(1 − 5/(D+1)) Σ_{p≤y} p^{-σ}` at some height up to `T`, when `T ≥ 4 (D+1) 4^{(2D+1) y}`. -/
theorem exists_height_no_cancellation (y D : ℕ) (σ : ℝ) {T : ℝ}
    (hT : 4 * ((D : ℝ) + 1) * (4 : ℝ) ^ ((2 * D + 1) * y) ≤ T) :
    ∃ t ∈ Set.Icc (0 : ℝ) T,
      (1 - 5 / ((D : ℝ) + 1)) * ∑ p ∈ primesUpTo y, (p : ℝ) ^ (-σ) ≤
        (∑ p ∈ primesUpTo y, ((p : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))).re := by
  obtain ⟨t, ht, h⟩ := exists_height_aligned y D (fun _ => 0) (fun p => (p : ℝ) ^ (-σ))
    (fun p _ => by positivity) hT
  refine ⟨t, ht, h.trans (le_of_eq ?_)⟩
  rw [Complex.re_sum]
  refine sum_congr rfl fun p hp => ?_
  rw [re_prime_cpow σ t (prime_of_mem_primesUpTo hp), sub_zero]

/-- **Every sign is reachable.** At some height up to `T`, all primes up to `y` point the other way: the
prime polynomial has real part at most `−(1 − 5/(D+1)) Σ_{p≤y} p^{-σ}`. This is the Liouville alignment. -/
theorem exists_height_negative_alignment (y D : ℕ) (σ : ℝ) {T : ℝ}
    (hT : 4 * ((D : ℝ) + 1) * (4 : ℝ) ^ ((2 * D + 1) * y) ≤ T) :
    ∃ t ∈ Set.Icc (0 : ℝ) T,
      (∑ p ∈ primesUpTo y, ((p : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))).re ≤
        -((1 - 5 / ((D : ℝ) + 1)) * ∑ p ∈ primesUpTo y, (p : ℝ) ^ (-σ)) := by
  obtain ⟨t, ht, h⟩ := exists_height_aligned y D (fun _ => Real.pi) (fun p => (p : ℝ) ^ (-σ))
    (fun p _ => by positivity) hT
  refine ⟨t, ht, ?_⟩
  have hsum : (∑ p ∈ primesUpTo y, ((p : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))).re =
      -∑ p ∈ primesUpTo y, (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p - Real.pi) := by
    rw [Complex.re_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun p hp => ?_
    rw [re_prime_cpow σ t (prime_of_mem_primesUpTo hp), Real.cos_sub_pi]
    ring
  rw [hsum]
  linarith

end GaloisForLFunctions.RigidArithmeticOfCuts
