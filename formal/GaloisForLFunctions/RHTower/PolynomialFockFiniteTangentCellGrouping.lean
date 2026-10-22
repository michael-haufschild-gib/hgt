import GaloisForLFunctions.RHTower.PolynomialFockFiniteTangentTrace

/-!
# Grouping critical primes by adapted cells

Each prime `p` is assigned the adapted cell index `I(p) = ⌊(log p)^(m/2)⌋`. For a finite set `T`
of primes with `log p ≥ 2`, the total critical weight `∑ (log p)² / p` of the primes in one fiber
`I(p) = n` is bounded by the scaled adapted cell mass `M_n`: the prime-log window mass centered at
`n^(2/m)` with radius `s_m ρ_m(n^(2/m))`, where `s_m = 2^(m/2 - 1) + 2` is the overlap cell scale.
Grouping by fibers then turns the weighted sum `∑_{p ∈ T} w_p M_{I(p)}^(q-1)` into a bound by
`∑_n M_n^q`.

## Main results

- `sum_criticalPrimeSamplingWeight_adaptedCellIndex_fiber_le_scaledCellMass`: the critical weight
  of a nonempty fiber of `I` on `T` is at most `M_n`.
- `sum_weight_mul_scaledCellMass_rpow_sub_one_le_tsum_rpow_scaledCellMass`:
  `∑_{p ∈ T} w_p M_{I(p)}^(q-1) ≤ ∑'_n M_n^q`.

## Hypotheses

The results assume `4 ≤ m` and that every prime of `T` satisfies `2 ≤ log p`. The second result
also assumes `1 < q` and takes as a hypothesis the summability of `n ↦ M_n^q`; its conclusion is
stated relative to that summability input.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Assuming `4 ≤ m` and `2 ≤ log p` on `T`, the primes of `T` in the adapted cell `n` (an index
attained on `T`) have total weight `∑ (log p)² / p` at most the scaled adapted cell mass `M_n`. -/
theorem sum_criticalPrimeSamplingWeight_adaptedCellIndex_fiber_le_scaledCellMass
    {m : ℝ} (hm : 4 ≤ m) (T : Finset Nat.Primes)
    (hT : ∀ p ∈ T, 2 ≤ Real.log (p : ℝ))
    {n : ℕ}
    (hn : n ∈ T.image (fun p : Nat.Primes =>
      criticalPrimeFockAdaptedCellIndex m (Real.log (p : ℝ)))) :
    (∑ p ∈ T.filter (fun p : Nat.Primes =>
      criticalPrimeFockAdaptedCellIndex m (Real.log (p : ℝ)) = n),
        criticalPrimeSamplingWeight p) ≤
      criticalPrimeFockScaledAdaptedCellMass m
        (criticalPrimeFockOverlapCellScale m) n := by
  classical
  obtain ⟨p, hpT, hpn⟩ := Finset.mem_image.mp hn
  let c : ℝ := criticalPrimeFockAdaptedCellCenter m n
  let R : ℝ := criticalPrimeFockOverlapCellScale m * criticalPrimeFockRadius m c
  let S : Finset Nat.Primes := T.filter (fun q =>
    criticalPrimeFockAdaptedCellIndex m (Real.log (q : ℝ)) = n)
  have hnpos : 0 < n := by
    rw [← hpn]
    exact criticalPrimeFockAdaptedCellIndex_pos (by linarith) (by linarith [hT p hpT])
  have hcpos : 0 < c := by
    dsimp [c, criticalPrimeFockAdaptedCellCenter]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hnpos) _
  have hRpos : 0 < R := mul_pos (criticalPrimeFockOverlapCellScale_pos m)
    (criticalPrimeFockRadius_pos hcpos)
  have hsub : S.image (fun q : Nat.Primes => (q : ℕ)) ⊆
      Finset.Ioc ⌊Real.exp (c - R)⌋₊ ⌊Real.exp (c + R)⌋₊ := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨q, hqS, rfl⟩ := hk
    have hqT : q ∈ T := (Finset.mem_filter.mp hqS).1
    have hqidx : criticalPrimeFockAdaptedCellIndex m (Real.log (q : ℝ)) = n :=
      (Finset.mem_filter.mp hqS).2
    apply mem_primeLogWindow_of_abs_log_sub_lt q.2
    have hcover := abs_sub_adaptedCellCenter_index_lt_radius
      (by linarith : 2 ≤ m) (by linarith [hT q hqT] : 1 ≤ Real.log (q : ℝ))
    rw [hqidx] at hcover
    have hrpos : 0 < criticalPrimeFockRadius m c := criticalPrimeFockRadius_pos hcpos
    have hscale : criticalPrimeFockRadius m c < R := by
      dsimp [R]
      have hs1 : 1 < criticalPrimeFockOverlapCellScale m := by
        unfold criticalPrimeFockOverlapCellScale
        have hpow : 0 < (2 : ℝ) ^ (m / 2 - 1) :=
          Real.rpow_pos_of_pos (by norm_num) _
        linarith
      nlinarith
    exact hcover.trans hscale
  change (∑ p ∈ S, criticalPrimeSamplingWeight p) ≤ primeLogWindowMass c R
  rw [primeLogWindowMass_eq_sum c hRpos.le]
  calc
    (∑ q ∈ S, criticalPrimeSamplingWeight q) =
        ∑ k ∈ S.image (fun q : Nat.Primes => (q : ℕ)), primeLogPowWeight 2 k := by
      symm
      calc
        (∑ k ∈ S.image (fun q : Nat.Primes => (q : ℕ)), primeLogPowWeight 2 k) =
            ∑ q ∈ S, primeLogPowWeight 2 (q : ℕ) :=
          Finset.sum_image (fun q _ r _ h => Subtype.ext h)
        _ = ∑ q ∈ S, criticalPrimeSamplingWeight q := by simp
    _ ≤ ∑ k ∈ Finset.Ioc ⌊Real.exp (c - R)⌋₊ ⌊Real.exp (c + R)⌋₊,
        primeLogPowWeight 2 k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun k _ _ => primeLogPowWeight_two_nonneg k)

/-- Assuming `4 ≤ m`, `1 < q`, `2 ≤ log p` on `T`, and summability of `n ↦ M_n^q`,
`∑_{p ∈ T} w_p M_{I(p)}^(q-1) ≤ ∑'_n M_n^q`, by grouping primes into adapted-cell fibers. -/
theorem sum_weight_mul_scaledCellMass_rpow_sub_one_le_tsum_rpow_scaledCellMass
    {m q : ℝ} (hm : 4 ≤ m) (hq : 1 < q)
    (T : Finset Nat.Primes)
    (hT : ∀ p ∈ T, 2 ≤ Real.log (p : ℝ))
    (hsum : Summable fun n : ℕ =>
      criticalPrimeFockScaledAdaptedCellMass m
        (criticalPrimeFockOverlapCellScale m) n ^ q) :
    (∑ p ∈ T, criticalPrimeSamplingWeight p *
      criticalPrimeFockScaledAdaptedCellMass m
        (criticalPrimeFockOverlapCellScale m)
        (criticalPrimeFockAdaptedCellIndex m (Real.log (p : ℝ))) ^ (q - 1)) ≤
      ∑' n : ℕ, criticalPrimeFockScaledAdaptedCellMass m
        (criticalPrimeFockOverlapCellScale m) n ^ q := by
  classical
  let I : Nat.Primes → ℕ := fun p =>
    criticalPrimeFockAdaptedCellIndex m (Real.log (p : ℝ))
  let M : ℕ → ℝ := fun n =>
    criticalPrimeFockScaledAdaptedCellMass m
      (criticalPrimeFockOverlapCellScale m) n
  have hM0 : ∀ n, 0 ≤ M n := fun n =>
    criticalPrimeFockScaledAdaptedCellMass_nonneg
      (criticalPrimeFockOverlapCellScale_pos m).le m n
  have hfiber : ∀ n ∈ T.image I,
      (∑ p ∈ T.filter (fun p => I p = n), criticalPrimeSamplingWeight p) ≤ M n := by
    intro n hn
    exact sum_criticalPrimeSamplingWeight_adaptedCellIndex_fiber_le_scaledCellMass
      hm T hT hn
  have hsplit :
      (∑ p ∈ T, criticalPrimeSamplingWeight p * M (I p) ^ (q - 1)) =
        ∑ n ∈ T.image I,
          (∑ p ∈ T.filter (fun p => I p = n), criticalPrimeSamplingWeight p) *
            M n ^ (q - 1) := by
    calc
      (∑ p ∈ T, criticalPrimeSamplingWeight p * M (I p) ^ (q - 1)) =
          ∑ n ∈ T.image I, ∑ p ∈ T.filter (fun p => I p = n),
            criticalPrimeSamplingWeight p * M (I p) ^ (q - 1) :=
        (Finset.sum_fiberwise_of_maps_to
          (fun p hp => Finset.mem_image_of_mem I hp)
          (fun p => criticalPrimeSamplingWeight p * M (I p) ^ (q - 1))).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        rw [(Finset.mem_filter.mp hp).2]
  rw [hsplit]
  calc
    (∑ n ∈ T.image I,
      (∑ p ∈ T.filter (fun p => I p = n), criticalPrimeSamplingWeight p) *
        M n ^ (q - 1)) ≤
        ∑ n ∈ T.image I, M n * M n ^ (q - 1) := by
      exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_right
        (hfiber n hn) (Real.rpow_nonneg (hM0 n) _)
    _ = ∑ n ∈ T.image I, M n ^ q := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hn0 : M n = 0
      · simp [hn0, Real.zero_rpow (by linarith : q ≠ 0)]
      · have hnpos : 0 < M n := lt_of_le_of_ne (hM0 n) (Ne.symm hn0)
        have hr := Real.rpow_add hnpos 1 (q - 1)
        have hqeq : 1 + (q - 1) = q := by ring
        rw [hqeq, Real.rpow_one] at hr
        exact hr.symm
    _ ≤ ∑' n : ℕ, M n ^ q := by
      exact hsum.sum_le_tsum (T.image I) (fun n hn => Real.rpow_nonneg (hM0 n) _)

end

end RHTower
