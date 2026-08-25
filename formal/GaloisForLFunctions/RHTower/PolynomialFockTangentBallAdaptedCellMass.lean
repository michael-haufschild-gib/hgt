import GaloisForLFunctions.RHTower.CriticalPrimeFockAdaptedCellCover
import GaloisForLFunctions.RHTower.CriticalPrimeFockArbitraryScaledAdaptedCellMass
import GaloisForLFunctions.RHTower.PolynomialFockPrimeBallOverlap

open Set Metric

namespace RHTower

noncomputable section

/-- Fixed adapted-cell aperture containing every tangent ball meeting a tail tangent ball. -/
def criticalPrimeFockOverlapCellScale (m : ℝ) : ℝ :=
  2 ^ (m / 2 - 1) + 2

theorem criticalPrimeFockOverlapCellScale_pos (m : ℝ) :
    0 < criticalPrimeFockOverlapCellScale m := by
  unfold criticalPrimeFockOverlapCellScale
  positivity

theorem abs_primeLog_sub_primeLog_lt_overlapRadius
    {m : ℝ} (hm : 4 ≤ m) (p q : Nat.Primes)
    (hp2 : 2 ≤ Real.log (p : ℝ)) {z : ℂ}
    (hpz : dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
      polynomialFockTangentRadius m (Real.log (p : ℝ)))
    (hqz : dist z ((Real.log (q : ℝ) : ℝ) : ℂ) <
      polynomialFockTangentRadius m (Real.log (q : ℝ))) :
    |Real.log (q : ℝ) - Real.log (p : ℝ)| <
      (2 ^ (m / 2 - 1) + 1) *
        criticalPrimeFockRadius m (Real.log (p : ℝ)) := by
  let xp : ℝ := Real.log (p : ℝ)
  let xq : ℝ := Real.log (q : ℝ)
  have hcenter : |xq - xp| < 1 := by
    have htri : dist (xq : ℂ) (xp : ℂ) ≤
        dist (xq : ℂ) z + dist z (xp : ℂ) := dist_triangle _ _ _
    have hsum : dist (xq : ℂ) z + dist z (xp : ℂ) < 1 := by
      calc
        dist (xq : ℂ) z + dist z (xp : ℂ) <
            polynomialFockTangentRadius m xq +
              polynomialFockTangentRadius m xp := by
          exact add_lt_add (by simpa [xq, dist_comm] using hqz)
            (by simpa [xp] using hpz)
        _ ≤ 1 / 2 + 1 / 2 := add_le_add
          (polynomialFockTangentRadius_le_half hm)
          (polynomialFockTangentRadius_le_half hm)
        _ = 1 := by norm_num
    have : dist (xq : ℂ) (xp : ℂ) < 1 := htri.trans_lt hsum
    rw [dist_eq_norm] at this
    have heq : (xq : ℂ) - (xp : ℂ) = ((xq - xp : ℝ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hxp2 : 2 ≤ xp := hp2
  have hxq1 : 1 < xq := by
    have := (abs_lt.mp hcenter).1
    linarith
  have hhalf : xp / 2 ≤ xq := by
    have := (abs_lt.mp hcenter).1
    linarith
  have hxp0 : 0 < xp := by linarith
  have hxq0 : 0 < xq := by linarith
  have hqrad : criticalPrimeFockRadius m xq ≤
      2 ^ (m / 2 - 1) * criticalPrimeFockRadius m xp := by
    calc
      criticalPrimeFockRadius m xq ≤ criticalPrimeFockRadius m (xp / 2) :=
        criticalPrimeFockRadius_anti (by linarith) (by linarith) hhalf
      _ = 2 ^ (m / 2 - 1) * criticalPrimeFockRadius m xp :=
        criticalPrimeFockRadius_half hxp0.le
  have htri : dist (xq : ℂ) (xp : ℂ) ≤
      dist (xq : ℂ) z + dist z (xp : ℂ) := dist_triangle _ _ _
  have hlocal : |xq - xp| <
      polynomialFockTangentRadius m xq + polynomialFockTangentRadius m xp := by
    have hsum : dist (xq : ℂ) z + dist z (xp : ℂ) <
        polynomialFockTangentRadius m xq + polynomialFockTangentRadius m xp :=
      add_lt_add (by simpa [xq, dist_comm] using hqz)
        (by simpa [xp] using hpz)
    have : dist (xq : ℂ) (xp : ℂ) < _ := htri.trans_lt hsum
    rw [dist_eq_norm] at this
    have heq : (xq : ℂ) - (xp : ℂ) = ((xq - xp : ℝ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  calc
    |Real.log (q : ℝ) - Real.log (p : ℝ)| = |xq - xp| := by rfl
    _ < polynomialFockTangentRadius m xq + polynomialFockTangentRadius m xp := hlocal
    _ ≤ criticalPrimeFockRadius m xq + criticalPrimeFockRadius m xp :=
      add_le_add
        (polynomialFockTangentRadius_le_criticalPrimeFockRadius (by linarith) hxq0)
        (polynomialFockTangentRadius_le_criticalPrimeFockRadius (by linarith) hxp0)
    _ ≤ 2 ^ (m / 2 - 1) * criticalPrimeFockRadius m xp +
        criticalPrimeFockRadius m xp := add_le_add hqrad le_rfl
    _ = (2 ^ (m / 2 - 1) + 1) * criticalPrimeFockRadius m xp := by ring

theorem abs_primeLog_sub_anchorCell_lt_overlapCellScale
    {m : ℝ} (hm : 4 ≤ m) (p q : Nat.Primes)
    (hp2 : 2 ≤ Real.log (p : ℝ)) {z : ℂ}
    (hpz : dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
      polynomialFockTangentRadius m (Real.log (p : ℝ)))
    (hqz : dist z ((Real.log (q : ℝ) : ℝ) : ℂ) <
      polynomialFockTangentRadius m (Real.log (q : ℝ))) :
    |Real.log (q : ℝ) - criticalPrimeFockAdaptedCellCenter m
        (criticalPrimeFockAdaptedCellIndex m (Real.log (p : ℝ)))| <
      criticalPrimeFockOverlapCellScale m *
        criticalPrimeFockRadius m (criticalPrimeFockAdaptedCellCenter m
          (criticalPrimeFockAdaptedCellIndex m (Real.log (p : ℝ)))) := by
  let xp : ℝ := Real.log (p : ℝ)
  let xq : ℝ := Real.log (q : ℝ)
  let n : ℕ := criticalPrimeFockAdaptedCellIndex m xp
  let c : ℝ := criticalPrimeFockAdaptedCellCenter m n
  have hm0 : 0 < m := by linarith
  have hxp1 : 1 ≤ xp := by linarith
  have hcpos : 0 < c := by
    dsimp [c, n, criticalPrimeFockAdaptedCellCenter]
    exact Real.rpow_pos_of_pos (by
      exact_mod_cast criticalPrimeFockAdaptedCellIndex_pos hm0 hxp1) _
  have hcle : c ≤ xp := criticalPrimeFockAdaptedCellCenter_index_le hm0 hxp1
  have hpc : |xp - c| < criticalPrimeFockRadius m c := by
    simpa [c, n] using abs_sub_adaptedCellCenter_index_lt_radius (by linarith) hxp1
  have hprad : criticalPrimeFockRadius m xp ≤ criticalPrimeFockRadius m c :=
    criticalPrimeFockRadius_anti (by linarith) hcpos hcle
  have hqp := abs_primeLog_sub_primeLog_lt_overlapRadius hm p q hp2 hpz hqz
  have htri : |xq - c| ≤ |xq - xp| + |xp - c| := by
    calc
      |xq - c| = |(xq - xp) + (xp - c)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  calc
    |Real.log (q : ℝ) - criticalPrimeFockAdaptedCellCenter m
        (criticalPrimeFockAdaptedCellIndex m (Real.log (p : ℝ)))| = |xq - c| := by rfl
    _ ≤ |xq - xp| + |xp - c| := htri
    _ < (2 ^ (m / 2 - 1) + 1) * criticalPrimeFockRadius m xp +
        criticalPrimeFockRadius m c := add_lt_add hqp hpc
    _ ≤ (2 ^ (m / 2 - 1) + 1) * criticalPrimeFockRadius m c +
        criticalPrimeFockRadius m c := by
      gcongr
    _ = criticalPrimeFockOverlapCellScale m * criticalPrimeFockRadius m c := by
      unfold criticalPrimeFockOverlapCellScale
      ring

theorem sum_criticalPrimeSamplingWeight_overlapping_anchorBall_le_cellMass
    {m : ℝ} (hm : 4 ≤ m) (p : Nat.Primes)
    (hp2 : 2 ≤ Real.log (p : ℝ)) {z : ℂ}
    (hpz : dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
      polynomialFockTangentRadius m (Real.log (p : ℝ)))
    (T : Finset Nat.Primes) :
    (∑ q ∈ T, if dist z ((Real.log (q : ℝ) : ℝ) : ℂ) <
        polynomialFockTangentRadius m (Real.log (q : ℝ))
      then criticalPrimeSamplingWeight q else 0) ≤
      criticalPrimeFockScaledAdaptedCellMass m
        (criticalPrimeFockOverlapCellScale m)
        (criticalPrimeFockAdaptedCellIndex m (Real.log (p : ℝ))) := by
  classical
  let n : ℕ := criticalPrimeFockAdaptedCellIndex m (Real.log (p : ℝ))
  let c : ℝ := criticalPrimeFockAdaptedCellCenter m n
  let R : ℝ := criticalPrimeFockOverlapCellScale m * criticalPrimeFockRadius m c
  let S : Finset Nat.Primes := T.filter fun q =>
    dist z ((Real.log (q : ℝ) : ℝ) : ℂ) <
      polynomialFockTangentRadius m (Real.log (q : ℝ))
  have hR : 0 < R := mul_pos (criticalPrimeFockOverlapCellScale_pos m)
    (criticalPrimeFockRadius_pos (by
      dsimp [c, n, criticalPrimeFockAdaptedCellCenter]
      exact Real.rpow_pos_of_pos (by
        exact_mod_cast criticalPrimeFockAdaptedCellIndex_pos (by linarith : 0 < m)
          (by linarith : 1 ≤ Real.log (p : ℝ))) _))
  have hsub : S.image (fun q : Nat.Primes => (q : ℕ)) ⊆
      Finset.Ioc ⌊Real.exp (c - R)⌋₊ ⌊Real.exp (c + R)⌋₊ := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨q, hqS, rfl⟩ := hk
    apply mem_primeLogWindow_of_abs_log_sub_lt q.2
    exact abs_primeLog_sub_anchorCell_lt_overlapCellScale hm p q hp2 hpz
      (Finset.mem_filter.mp hqS).2
  change (∑ q ∈ T, if dist z ((Real.log (q : ℝ) : ℝ) : ℂ) <
      polynomialFockTangentRadius m (Real.log (q : ℝ))
    then criticalPrimeSamplingWeight q else 0) ≤ primeLogWindowMass c R
  rw [primeLogWindowMass_eq_sum c hR.le]
  rw [← Finset.sum_filter]
  change (∑ q ∈ S, criticalPrimeSamplingWeight q) ≤ _
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

end

end RHTower
