import Mathlib

/-!
# Supports with independent logarithms

A set `S ⊂ [1, x]` of integers whose logarithms are linearly independent over `ℚ` has at most
`π(x)` elements (`card_le_primesUpToFinset_of_linearIndependent_log`). The exponent vectors of its
elements are then linearly independent in `ℚ^{π(x)}`, because `log n = Σ_p v_p(n) log p`.

By Cauchy–Schwarz, a weight system on such a support satisfies
`(Σ λ)² ≤ π(x) Σ λ²` (`sq_sum_le_card_primesUpToFinset_mul_sum_sq`). Density-one systems on
independent supports therefore carry prime-level square mass `≳ x log x`. In the Weil positivity
problem for `ζ` this is the diagonal variance `≳ ¼ log² T` on the critical line, whose square root
equals the archimedean cap `½ log T`.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The primes up to `x`, as a finset. -/
def primesUpToFinset (x : ℕ) : Finset ℕ := (Finset.range (x + 1)).filter Nat.Prime

theorem log_eq_sum_primesUpToFinset {x n : ℕ} (hnx : n ≤ x) :
    Real.log n = ∑ p ∈ primesUpToFinset x, (n.factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    rw [Nat.support_factorization] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpn := Nat.le_of_mem_primeFactors hp
    rw [primesUpToFinset, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpp⟩
  · intro p _ hp
    rw [Finsupp.notMem_support_iff] at hp
    simp [hp]

/-- **Multiplicatively independent integers are at most as many as the primes.**  If the logarithms
of a finite set `S` of integers in `[1, x]` are linearly independent over `ℚ`, then
`|S| ≤ π(x)`: the exponent vectors of the elements of `S` are linearly independent in `ℚ^{π(x)}`. -/
theorem card_le_primesUpToFinset_of_linearIndependent_log {x : ℕ} {S : Finset ℕ}
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ x)
    (hind : LinearIndependent ℚ (fun n : S => Real.log (n : ℕ))) :
    S.card ≤ (primesUpToFinset x).card := by
  let v : S → (primesUpToFinset x → ℚ) := fun n p => ((n : ℕ).factorization p : ℚ)
  let L : (primesUpToFinset x → ℚ) →ₗ[ℚ] ℝ :=
    { toFun := fun f => ∑ p : primesUpToFinset x, (f p : ℝ) * Real.log (p : ℕ)
      map_add' := by
        intro f g
        simp only [Pi.add_apply, Rat.cast_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, RingHom.id_apply]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Rat.smul_def]
        ring }
  have hcomp : (L ∘ v) = fun n : S => Real.log (n : ℕ) := by
    funext n
    obtain ⟨_, hx⟩ := hS n n.2
    simp only [Function.comp_apply, L, v, LinearMap.coe_mk, AddHom.coe_mk, Rat.cast_natCast]
    rw [log_eq_sum_primesUpToFinset hx]
    exact (Finset.sum_coe_sort (primesUpToFinset x)
      (fun p => ((n : ℕ).factorization p : ℝ) * Real.log p))
  have hv : LinearIndependent ℚ v := by
    apply LinearIndependent.of_comp L
    rw [hcomp]
    exact hind
  have := hv.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe] at this
  exact this

/-- **Mass on an independent support costs square mass.**  If `S ⊂ [1, x]` has `ℚ`-linearly
independent logarithms, then `(Σ_{n∈S} λ(n))² ≤ π(x) · Σ_{n∈S} λ(n)²`. So a weight system of total
mass `≈ x` on such a support has square mass `≳ x²/π(x) ≈ x log x`. This is the source of the
prime-level diagonal variance `≳ ¼ log² T` of every density-one system on an independent support. -/
theorem sq_sum_le_card_primesUpToFinset_mul_sum_sq {x : ℕ} {S : Finset ℕ}
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ x)
    (hind : LinearIndependent ℚ (fun n : S => Real.log (n : ℕ))) (lam : ℕ → ℝ) :
    (∑ n ∈ S, lam n) ^ 2 ≤ ((primesUpToFinset x).card : ℝ) * ∑ n ∈ S, lam n ^ 2 := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := lam)
  have hcard : (S.card : ℝ) ≤ (primesUpToFinset x).card := by
    exact_mod_cast card_le_primesUpToFinset_of_linearIndependent_log hS hind
  have hnn : 0 ≤ ∑ n ∈ S, lam n ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  calc (∑ n ∈ S, lam n) ^ 2 ≤ S.card * ∑ n ∈ S, lam n ^ 2 := hcs
    _ ≤ (primesUpToFinset x).card * ∑ n ∈ S, lam n ^ 2 := mul_le_mul_of_nonneg_right hcard hnn

end RHTower
