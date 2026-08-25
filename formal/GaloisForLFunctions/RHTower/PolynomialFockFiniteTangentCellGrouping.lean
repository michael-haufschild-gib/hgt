import GaloisForLFunctions.RHTower.PolynomialFockFiniteTangentTrace

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

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
