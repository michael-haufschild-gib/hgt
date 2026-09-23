import GaloisForLFunctions.HTGeometry.LogLinearTailIntegral
import GaloisForLFunctions.HTGeometry.GeometricPrimePowerTail
import GaloisForLFunctions.HTGeometry.LogSquaredTailIntegral

/-!
# Prime-power completion budget: the `(PFK14)` `r=2` prime tail

The prime-power completion stability `(PFK14)` of
`xi-physical-prime-log-aperture-fusion-cross-kernel` is dominated by the `r = 2` band
`∑_{p, p^(2 : ℕ) > X} log p / p^(2 : ℕ)`.  This file provides the reusable prime→integer sub-sum comparison and
its specialization to that band: a finite set of primes all exceeding `N₀` has weight-sum bounded by
the natural-number tail controlled in `HTGeometry.LogLinearTailIntegral`, giving
`∑_p log p / p^(2 : ℕ) ≤ (log N₀ + 1)/N₀`.  With `N₀ = ⌈√X⌉` this is `≪ log X / √X`, the `(PFK14)` `r=2`
estimate.
-/

open Real Filter
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- General prime sub-sum vs shifted tail: for a nonnegative summable `f`, a finite set of primes all
exceeding `N₀` has `∑_{p∈P} f p ≤ ∑'_i f (N₀+1+i)`. -/
theorem sum_primes_le_tsum_shift {f : ℕ → ℝ} (hf : Summable f) (hf0 : ∀ n, 0 ≤ f n)
    {N₀ : ℕ} (P : Finset Nat.Primes) (hP : ∀ p ∈ P, N₀ < (p : ℕ)) :
    ∑ p ∈ P, f (p : ℕ) ≤ ∑' i : ℕ, f (N₀ + 1 + i) := by
  set φ : Nat.Primes → ℕ := fun p => (p : ℕ) - (N₀ + 1) with hφ_def
  have hshift_sum : Summable (fun i => f (N₀ + 1 + i)) := by
    have h := (summable_nat_add_iff (f := f) (N₀ + 1)).mpr hf
    refine h.congr ?_
    intro i; rw [Nat.add_comm]
  have hinj : Set.InjOn φ ↑P := by
    intro p hp q hq h
    have hpp := hP p (Finset.mem_coe.mp hp)
    have hqq := hP q (Finset.mem_coe.mp hq)
    have hpq : (p : ℕ) = (q : ℕ) := by rw [hφ_def] at h; simp only at h; omega
    exact Subtype.ext hpq
  have hpoint : ∀ p ∈ P, f (p : ℕ) = f (N₀ + 1 + φ p) := by
    intro p hp
    have hp_ge : N₀ + 1 ≤ (p : ℕ) := hP p hp
    congr 1
    simp only [hφ_def]
    omega
  calc ∑ p ∈ P, f (p : ℕ)
      = ∑ p ∈ P, f (N₀ + 1 + φ p) := Finset.sum_congr rfl hpoint
    _ = ∑ i ∈ P.image φ, f (N₀ + 1 + i) :=
        (Finset.sum_image (f := fun i => f (N₀ + 1 + i)) hinj).symm
    _ ≤ ∑' i, f (N₀ + 1 + i) := hshift_sum.sum_le_tsum _ (fun i _ => hf0 _)

/-- `(PFK14)` `r=2` prime estimate: for primes all exceeding `N₀ ≥ 3`,
`∑_p log p/p² ≤ (log N₀ + 1)/N₀`. -/
theorem sum_primes_logLin_div_sq_le_tail {N₀ : ℕ} (hN₀ : 3 ≤ N₀)
    (P : Finset Nat.Primes) (hP : ∀ p ∈ P, N₀ < (p : ℕ)) :
    ∑ p ∈ P, Real.log (p : ℕ) / (p : ℕ) ^ (2 : ℕ) ≤ (Real.log (N₀ : ℝ) + 1) / (N₀ : ℝ) := by
  have hexp : Real.exp 1 ≤ (N₀ : ℝ) := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h2 : (3 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀
    linarith
  have hf0 : ∀ n : ℕ, 0 ≤ Real.log n / n ^ (2 : ℕ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast h)) (by positivity)
  have hgen := sum_primes_le_tsum_shift (f := fun n => Real.log n / n ^ (2 : ℕ))
    summable_logLin_div_sq hf0 P hP
  refine le_trans hgen ?_
  have hcast : ∑' i : ℕ, Real.log ((N₀ + 1 + i : ℕ) : ℝ) / ((N₀ + 1 + i : ℕ) : ℝ) ^ (2 : ℕ)
      = ∑' i : ℕ, Real.log ((N₀ : ℝ) + ((i : ℝ) + 1)) / ((N₀ : ℝ) + ((i : ℝ) + 1)) ^ (2 : ℕ) := by
    apply tsum_congr
    intro i
    have hh : ((N₀ + 1 + i : ℕ) : ℝ) = (N₀ : ℝ) + ((i : ℝ) + 1) := by push_cast; ring
    rw [hh]
  rw [hcast]
  exact tsum_logLin_div_sq_le hexp

/-- **`(PFK14)` complete prime-power completion tail.**  For primes all `> N₀ ≥ 3`, the entire
proper-prime-power correction `∑_p ∑_{r≥2} log p/p^r` is bounded by `2(log N₀+1)/N₀`: the geometric
tail folds each inner `r ≥ 2` series into `2 log p/p²`, and the `r=2` prime tail bounds the rest. -/
theorem sum_primes_primePowerTail_le {N₀ : ℕ} (hN₀ : 3 ≤ N₀)
    (P : Finset Nat.Primes) (hP : ∀ p ∈ P, N₀ < (p : ℕ)) :
    ∑ p ∈ P, ∑' r : ℕ, Real.log (p : ℕ) / (p : ℕ) ^ (2 + r)
      ≤ 2 * ((Real.log (N₀ : ℝ) + 1) / (N₀ : ℝ)) := by
  have hinner : ∀ p ∈ P, ∑' r : ℕ, Real.log (p : ℕ) / (p : ℕ) ^ (2 + r)
      ≤ 2 * Real.log (p : ℕ) / (p : ℕ) ^ (2 : ℕ) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.two_le
    exact tsum_log_div_pow_shift_le hp2 2
  calc ∑ p ∈ P, ∑' r : ℕ, Real.log (p : ℕ) / (p : ℕ) ^ (2 + r)
      ≤ ∑ p ∈ P, 2 * Real.log (p : ℕ) / (p : ℕ) ^ (2 : ℕ) := Finset.sum_le_sum hinner
    _ = 2 * ∑ p ∈ P, Real.log (p : ℕ) / (p : ℕ) ^ (2 : ℕ) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    _ ≤ 2 * ((Real.log (N₀ : ℝ) + 1) / (N₀ : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_primes_logLin_div_sq_le_tail hN₀ P hP) (by norm_num)

end RHTower
