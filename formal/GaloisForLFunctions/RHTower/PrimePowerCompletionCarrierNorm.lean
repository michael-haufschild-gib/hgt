import GaloisForLFunctions.HTGeometry.CenteredApertureCarrierNorm
import GaloisForLFunctions.RHTower.PrimePowerCompletionBudget

/-!
# Critical-norm stability of the prime-power completion carrier `(PFK16)/(PFK17)`

The von Mangoldt completion carrier is the coherent fusion of the proper-prime-power atoms
`p^r` (`r ≥ 2`), each an aperture feature at log-location `r log p` weighted by `log p / p^r`.  This
file bounds the `L²` norm of any finite truncation of that carrier by `√A` times the prime-power
arithmetic tail: for atoms all above `N₀ ≥ 3`,
`‖completion‖₂ ≤ √A · 2(log N₀+1)/N₀`  and  `‖completion‖₂² ≤ A · (2(log N₀+1)/N₀)²`.
This is the critical-norm stability `(PFK16)/(PFK17)`: it composes the base-general aggregate carrier
norm bound (`HTGeometry.CenteredApertureCarrierNorm`) with the arithmetic tail
(`sum_primes_primePowerTail_le`).
-/

open Real Filter
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The finite prime-power completion carrier norm is `√A` times its total weight. -/
theorem norm_primePowerCompletionCarrier_le {A : ℝ} (hA : 0 < A) (m k : ℝ)
    (S : Finset (Nat.Primes × ℕ)) :
    ‖∑ x ∈ S, (Real.log (x.1 : ℕ) / (x.1 : ℕ) ^ (2 + x.2)) •
        centeredApertureCarrierAt A m k ((2 + x.2 : ℕ) * Real.log (x.1 : ℕ))‖
      ≤ Real.sqrt A * ∑ x ∈ S, Real.log (x.1 : ℕ) / (x.1 : ℕ) ^ (2 + x.2) := by
  apply norm_aggregate_centeredApertureCarrierAt_le hA m k S
    (fun x => (2 + x.2 : ℕ) * Real.log (x.1 : ℕ))
    (fun x => Real.log (x.1 : ℕ) / (x.1 : ℕ) ^ (2 + x.2))
  intro x _
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast x.1.prop.one_lt.le)) (by positivity)

/-- Each prime's fiber sum of completion weights is bounded by its full power tail `∑'_r log p/p^(2+r)`. -/
theorem primePowerWeight_fiber_le_tsum (p : Nat.Primes) (S : Finset (Nat.Primes × ℕ)) :
    ∑ x ∈ S.filter (fun x => Prod.fst x = p), Real.log (x.1 : ℕ) / (x.1 : ℕ) ^ (2 + x.2)
      ≤ ∑' r : ℕ, Real.log (p : ℕ) / (p : ℕ) ^ (2 + r) := by
  set fib := S.filter (fun x => Prod.fst x = p) with hfib
  have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.two_le
  have hp0 : (0 : ℝ) < (p : ℕ) := by linarith
  have hsummable : Summable (fun r : ℕ => Real.log (p : ℕ) / (p : ℕ) ^ (2 + r)) := by
    have heq : (fun r : ℕ => Real.log (p : ℕ) / (p : ℕ) ^ (2 + r))
        = fun r : ℕ => (Real.log (p : ℕ) / (p : ℕ) ^ 2) * (1 / (p : ℕ)) ^ r := by
      funext r; rw [pow_add, one_div, inv_pow]; field_simp
    rw [heq]
    exact (summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one hp0]; linarith)).mul_left _
  have hinj : Set.InjOn Prod.snd (fib : Set (Nat.Primes × ℕ)) := by
    intro a ha b hb hab
    simp only [hfib, Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    exact Prod.ext (ha.2.trans hb.2.symm) hab
  have hnn : ∀ r : ℕ, 0 ≤ Real.log (p : ℕ) / (p : ℕ) ^ (2 + r) :=
    fun r => div_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)) (by positivity)
  have hkey : ∑ x ∈ fib, Real.log (x.1 : ℕ) / (x.1 : ℕ) ^ (2 + x.2)
      = ∑ r ∈ fib.image Prod.snd, Real.log (p : ℕ) / (p : ℕ) ^ (2 + r) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro x hx
    have : x.1 = p := by simp only [hfib, Finset.mem_filter] at hx; exact hx.2
    rw [this]
  rw [hkey]
  exact hsummable.sum_le_tsum _ (fun r _ => hnn r)

/-- The total completion weight over prime-power atoms above `N₀` is `≤ 2(log N₀+1)/N₀`
(fiberwise reduction to `sum_primes_primePowerTail_le`). -/
theorem sum_pairs_primePowerWeight_le_tail {N₀ : ℕ} (hN₀ : 3 ≤ N₀)
    (S : Finset (Nat.Primes × ℕ)) (hS : ∀ x ∈ S, N₀ < (x.1 : ℕ)) :
    ∑ x ∈ S, Real.log (x.1 : ℕ) / (x.1 : ℕ) ^ (2 + x.2)
      ≤ 2 * ((Real.log (N₀ : ℝ) + 1) / (N₀ : ℝ)) := by
  set P := S.image Prod.fst with hP_def
  have hmaps : ∀ x ∈ S, Prod.fst x ∈ P := fun x hx => Finset.mem_image_of_mem _ hx
  have hP_prime : ∀ p ∈ P, N₀ < (p : ℕ) := by
    intro p hp
    rw [hP_def, Finset.mem_image] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    exact hS x hx
  calc ∑ x ∈ S, Real.log (x.1 : ℕ) / (x.1 : ℕ) ^ (2 + x.2)
      = ∑ p ∈ P, ∑ x ∈ S.filter (fun x => Prod.fst x = p),
          Real.log (x.1 : ℕ) / (x.1 : ℕ) ^ (2 + x.2) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ p ∈ P, ∑' r : ℕ, Real.log (p : ℕ) / (p : ℕ) ^ (2 + r) :=
        Finset.sum_le_sum (fun p _ => primePowerWeight_fiber_le_tsum p S)
    _ ≤ 2 * ((Real.log (N₀ : ℝ) + 1) / (N₀ : ℝ)) := sum_primes_primePowerTail_le hN₀ P hP_prime

/-- **`(PFK16)` critical-norm stability.**  The von Mangoldt prime-power completion carrier (any finite
atom set above `N₀ ≥ 3`) has `L²` norm `≤ √A · 2(log N₀+1)/N₀`, of order `√A·log M/√M` for
`N₀ = ⌈√X⌉`.  Combines the base-general aggregate norm bound with the prime-power arithmetic tail. -/
theorem norm_primePowerCompletionCarrier_le_tail {A : ℝ} (hA : 0 < A) (m k : ℝ)
    {N₀ : ℕ} (hN₀ : 3 ≤ N₀) (S : Finset (Nat.Primes × ℕ)) (hS : ∀ x ∈ S, N₀ < (x.1 : ℕ)) :
    ‖∑ x ∈ S, (Real.log (x.1 : ℕ) / (x.1 : ℕ) ^ (2 + x.2)) •
        centeredApertureCarrierAt A m k ((2 + x.2 : ℕ) * Real.log (x.1 : ℕ))‖
      ≤ Real.sqrt A * (2 * ((Real.log (N₀ : ℝ) + 1) / (N₀ : ℝ))) :=
  le_trans (norm_primePowerCompletionCarrier_le hA m k S)
    (mul_le_mul_of_nonneg_left (sum_pairs_primePowerWeight_le_tail hN₀ S hS) (Real.sqrt_nonneg A))

/-- **`(PFK17)` squared critical-norm stability.**  Squaring `(PFK16)`:
`‖completion carrier‖² ≤ A·(2(log N₀+1)/N₀)²`, of order `A·log²M/M` for `N₀ = ⌈√X⌉`. -/
theorem normSq_primePowerCompletionCarrier_le_tail {A : ℝ} (hA : 0 < A) (m k : ℝ)
    {N₀ : ℕ} (hN₀ : 3 ≤ N₀) (S : Finset (Nat.Primes × ℕ)) (hS : ∀ x ∈ S, N₀ < (x.1 : ℕ)) :
    ‖∑ x ∈ S, (Real.log (x.1 : ℕ) / (x.1 : ℕ) ^ (2 + x.2)) •
        centeredApertureCarrierAt A m k ((2 + x.2 : ℕ) * Real.log (x.1 : ℕ))‖ ^ 2
      ≤ A * (2 * ((Real.log (N₀ : ℝ) + 1) / (N₀ : ℝ))) ^ 2 := by
  have h2 := pow_le_pow_left₀ (norm_nonneg _)
    (norm_primePowerCompletionCarrier_le_tail hA m k hN₀ S hS) 2
  rwa [mul_pow, Real.sq_sqrt hA.le] at h2

end RHTower
