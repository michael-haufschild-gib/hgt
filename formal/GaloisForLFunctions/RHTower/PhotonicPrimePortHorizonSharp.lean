import GaloisForLFunctions.RHTower.PhotonicPrimePortHorizon
import GaloisForLFunctions.RHTower.PrimeZetaOneLineConvergence

/-!
# The prime-port horizon is exactly grade `½`

**Theorem** (`ptrEulerPartialProduct_converges_iff`). Let `Re s > ½` and `Im s ≠ 0`. The partial Euler
products `∏_{p ≤ N} (1 − p^{-s})^{-1}` converge to a nonzero limit if and only if `Re s ≥ 1`.

In PTR terms: at height `x ≠ 0` the prime-order port realises the producer grade `h` exactly when
`h ≥ ½`. The horizon `Re s = 1` is sharp. On the one-line the prime port still converges, by the
convergence of `Σ_p p^{-1-it}` (`exists_tendsto_primeCpowSum`, from the prime number theorem). Just
inside the strip it converges nowhere (`not_tendsto_ptrEulerPartialProduct`).

**Proof.** `log(1 − z)^{-1} = z + O(|z|²)` with `z = p^{-s}`. The remainders are summable for
`Re s > ½`. So the partial products converge to a nonzero limit iff the prime sums `Σ_{p ≤ N} p^{-s}`
converge. They converge absolutely for `Re s > 1`, conditionally on `Re s = 1` (`t ≠ 0`), and
nowhere in `Re s < 1`.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- The second-order remainder of the logarithm of the `n`-th Euler factor. -/
def ptrEulerRemainder (s : ℂ) (n : ℕ) : ℂ :=
  if (n + 1).Prime then -Complex.log (1 - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) -
    (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) else 0

theorem norm_cpow_neg_succ (s : ℂ) (n : ℕ) :
    ‖(((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)‖ = ((n : ℝ) + 1) ^ (-s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]

theorem norm_cpow_neg_succ_le {s : ℂ} (hσ : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖(((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ (2 : ℝ) ^ (-s.re) := by
  rw [norm_cpow_neg_succ]
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith) (by linarith)

/-- `log` of an Euler factor: first-order term plus remainder. -/
theorem log_ptrEulerFactor_eq {s : ℂ} (hσ : 0 < s.re) (n : ℕ) :
    Complex.log (ptrEulerFactor s n) =
      ((if (n + 1).Prime then (1 : ℝ) else 0 : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) +
        ptrEulerRemainder s n := by
  simp only [ptrEulerFactor, ptrEulerRemainder]
  split_ifs with hp
  · have hn : 1 ≤ n := by have := hp.two_le; omega
    set z := (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
    have hz := norm_cpow_neg_succ_le hσ hn
    have hq : (2 : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hre : 0 < (1 - z).re := by
      simp only [Complex.sub_re, Complex.one_re]
      have := Complex.abs_re_le_norm z
      linarith [le_abs_self z.re]
    have harg : (1 - z).arg ≠ Real.pi := by
      intro h
      have := Complex.arg_eq_pi_iff.mp h
      linarith [this.1]
    rw [Complex.log_inv _ harg]
    push_cast; ring
  · simp

theorem summable_ptrEulerRemainder {s : ℂ} (hσ : 1 / 2 < s.re) : Summable (ptrEulerRemainder s) := by
  have hσ0 : 0 < s.re := by linarith
  have hq : (2 : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hle : ∀ n, ‖ptrEulerRemainder s n‖ ≤
      (1 - (2 : ℝ) ^ (-s.re))⁻¹ / 2 * ((n : ℝ) + 1) ^ (-(2 * s.re)) := by
    intro n
    simp only [ptrEulerRemainder]
    split_ifs with hp
    · have hn : 1 ≤ n := by have := hp.two_le; omega
      set z := (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
      have hzn := norm_cpow_neg_succ_le hσ0 hn
      have hlt : ‖-z‖ < 1 := by rw [norm_neg]; linarith
      have h1 := Complex.norm_log_one_add_sub_self_le hlt
      rw [norm_neg] at h1
      have e : -Complex.log (1 - z) - z = -(Complex.log (1 + -z) - -z) := by
        rw [← sub_eq_add_neg]; ring
      rw [e, norm_neg]
      refine h1.trans ?_
      have hsq : ‖z‖ ^ 2 = ((n : ℝ) + 1) ^ (-(2 * s.re)) := by
        rw [norm_cpow_neg_succ, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1; push_cast; ring
      rw [hsq]
      have hinv : (1 - ‖z‖)⁻¹ ≤ (1 - (2 : ℝ) ^ (-s.re))⁻¹ := inv_anti₀ (by linarith) (by linarith)
      have hpos : 0 ≤ ((n : ℝ) + 1) ^ (-(2 * s.re)) := by positivity
      calc ((n : ℝ) + 1) ^ (-(2 * s.re)) * (1 - ‖z‖)⁻¹ / 2
          ≤ ((n : ℝ) + 1) ^ (-(2 * s.re)) * (1 - (2 : ℝ) ^ (-s.re))⁻¹ / 2 := by gcongr
        _ = _ := by ring
    · simp; positivity
  refine Summable.of_norm_bounded (g := fun n : ℕ =>
    (1 - (2 : ℝ) ^ (-s.re))⁻¹ / 2 * ((n : ℝ) + 1) ^ (-(2 * s.re))) ?_ hle
  refine Summable.mul_left _ ?_
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (2 * s.re))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  refine ((summable_nat_add_iff 1).mpr hbase).congr fun n => ?_
  push_cast
  rw [Real.rpow_neg (by positivity)]

theorem ptrEulerFactor_ne_zero {s : ℂ} (hσ : 0 < s.re) (n : ℕ) : ptrEulerFactor s n ≠ 0 := by
  unfold ptrEulerFactor
  split_ifs with hp
  · have hn : 1 ≤ n := by have := hp.two_le; omega
    refine inv_ne_zero fun h0 => ?_
    have hz := norm_cpow_neg_succ_le hσ hn
    have hq : (2 : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have : (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) = 1 := by linear_combination -h0
    rw [this, norm_one] at hz
    linarith
  · exact one_ne_zero

/-- The partial products are the exponentials of the partial logarithm sums. -/
theorem ptrEulerPartialProduct_eq_exp {s : ℂ} (hσ : 0 < s.re) (N : ℕ) :
    ptrEulerPartialProduct s N =
      Complex.exp (∑ n ∈ Finset.range N, Complex.log (ptrEulerFactor s n)) := by
  rw [Complex.exp_sum, ptrEulerPartialProduct]
  exact Finset.prod_congr rfl fun n _ => (Complex.exp_log (ptrEulerFactor_ne_zero hσ n)).symm

/-- The prime sum in Euler-factor indexing equals the sum over primes `k ≤ N`. -/
theorem sum_primeIndicator_eq (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((if (n + 1).Prime then (1 : ℝ) else 0 : ℝ) : ℂ) *
        (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) =
      ∑ k ∈ Finset.Icc 0 N with k.Prime, ((k : ℂ)) ^ (-s) := by
  classical
  rw [Finset.sum_filter]
  have h1 : ∑ k ∈ Finset.Icc 0 N, (if k.Prime then ((k : ℂ)) ^ (-s) else 0) =
      ∑ k ∈ Finset.range (N + 1), (if k.Prime then ((k : ℂ)) ^ (-s) else 0) := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext k; simp
  rw [h1, Finset.sum_range_succ']
  simp only [Nat.not_prime_zero, if_false, add_zero]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> push_cast <;> ring

/-- **Convergence on and beyond the one-line.** -/
theorem exists_tendsto_ptrEulerPartialProduct_of_one_le {s : ℂ} (h1 : 1 ≤ s.re) (ht : s.im ≠ 0) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (ptrEulerPartialProduct s) atTop (𝓝 L) := by
  have hσ : 1 / 2 < s.re := by linarith
  have hσ0 : 0 < s.re := by linarith
  -- the prime sums converge
  obtain ⟨Lp, hLp⟩ : ∃ Lp : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
      ((if (n + 1).Prime then (1 : ℝ) else 0 : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s))
      atTop (𝓝 Lp) := by
    rcases eq_or_lt_of_le h1 with heq | hgt
    · obtain ⟨L, hL⟩ := exists_tendsto_primeCpowSum (lam := s.im) ht
      have hs : -s = -1 - (s.im : ℂ) * I := by
        apply Complex.ext <;> simp [← heq]
      refine ⟨L, ?_⟩
      have hcomp := hL.comp tendsto_natCast_atTop_atTop
      refine hcomp.congr fun N => ?_
      simp only [Function.comp, Nat.floor_natCast]
      rw [sum_primeIndicator_eq, hs]
    · have hsum : Summable (fun n : ℕ => ((if (n + 1).Prime then (1 : ℝ) else 0 : ℝ) : ℂ) *
          (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) := by
        refine Summable.of_norm_bounded (g := fun n : ℕ => ((n : ℝ) + 1) ^ (-s.re)) ?_ fun n => ?_
        · have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ s.re)⁻¹) :=
            Real.summable_nat_rpow_inv.mpr hgt
          refine ((summable_nat_add_iff 1).mpr hbase).congr fun n => ?_
          push_cast
          rw [Real.rpow_neg (by positivity)]
        · rw [norm_mul, norm_cpow_neg_succ]
          split_ifs <;> simp
          positivity
      exact ⟨_, hsum.hasSum.tendsto_sum_nat⟩
  -- the logarithm sums converge, hence the products
  have hR := (summable_ptrEulerRemainder hσ).hasSum.tendsto_sum_nat
  have hlog : Tendsto (fun N => ∑ n ∈ Finset.range N, Complex.log (ptrEulerFactor s n)) atTop
      (𝓝 (Lp + ∑' n, ptrEulerRemainder s n)) := by
    have := hLp.add hR
    refine this.congr fun N => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => (log_ptrEulerFactor_eq hσ0 n).symm
  refine ⟨Complex.exp (Lp + ∑' n, ptrEulerRemainder s n), Complex.exp_ne_zero _, ?_⟩
  have := (Complex.continuous_exp.tendsto _).comp hlog
  refine this.congr fun N => ?_
  simp only [Function.comp]
  rw [ptrEulerPartialProduct_eq_exp hσ0]

/-- **The prime-port horizon is exactly `Re s = 1`.** -/
theorem ptrEulerPartialProduct_converges_iff {s : ℂ} (hs : 1 / 2 < s.re) (ht : s.im ≠ 0) :
    (∃ L : ℂ, L ≠ 0 ∧ Tendsto (ptrEulerPartialProduct s) atTop (𝓝 L)) ↔ 1 ≤ s.re := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    exact not_tendsto_ptrEulerPartialProduct hs hlt h
  · intro h1
    exact exists_tendsto_ptrEulerPartialProduct_of_one_le h1 ht

end

end RHTower
