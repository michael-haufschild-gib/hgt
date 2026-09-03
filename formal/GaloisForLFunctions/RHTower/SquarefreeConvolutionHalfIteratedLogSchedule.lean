import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfSqrtLogScheduleBoundaryNoGo
import GaloisForLFunctions.RHTower.Sieve.KubalalikaLargeScale

/-!
# Iterated-logarithmic Cayley schedule

The schedule

`kappa(N) = log_2(log_2(N+1)+1) + 24`

tends to infinity, so its scheduled Cayley--Dirichlet products retain the Euler-chamber limit and
local boundedness would imply `RHLadder 1`.  Its exterior growth at the sharpened `s = 6/11`
test is only polylogarithmic: the base-five scale is eventually bounded by `N^(6/11)`.

Thus this explicit schedule satisfies the strongest proved prime-jump ceiling.  No local
boundedness assertion is made; that remains the exact analytic obligation.
-/

open Complex Filter Metric Set Topology

namespace RHTower

noncomputable section

def iteratedLogarithmicCayleySchedule (N : ℕ) : ℕ :=
  Nat.log 2 (Nat.log 2 (N + 1) + 1) + 24

theorem iteratedLogarithmicCayleySchedule_ge_twenty_four (N : ℕ) :
    24 ≤ iteratedLogarithmicCayleySchedule N := by
  simp [iteratedLogarithmicCayleySchedule]

theorem tendsto_iteratedLogarithmicCayleySchedule_atTop :
    Tendsto iteratedLogarithmicCayleySchedule atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨2 ^ (2 ^ b), fun N hN => ?_⟩
  have hinnerPow : 2 ^ (2 ^ b) ≤ N + 1 :=
    hN.trans (Nat.le_add_right N 1)
  have hinnerLog : 2 ^ b ≤ Nat.log 2 (N + 1) :=
    Nat.le_log_of_pow_le (by norm_num) hinnerPow
  have houterPow : 2 ^ b ≤ Nat.log 2 (N + 1) + 1 :=
    hinnerLog.trans (Nat.le_add_right _ 1)
  have houterLog : b ≤ Nat.log 2 (Nat.log 2 (N + 1) + 1) :=
    Nat.le_log_of_pow_le (by norm_num) houterPow
  exact houterLog.trans (Nat.le_add_right _ 24)

private theorem cast_natLog_add_one_le_logMajorant
    {N : ℕ} (hN : 1 ≤ N) :
    ((Nat.log 2 (N + 1) + 1 : ℕ) : ℝ) ≤
      (2 / Real.log 2) * (1 + Real.log (N : ℝ)) := by
  let m := Nat.log 2 (N + 1)
  have harg : N + 1 ≠ 0 := by omega
  have hpowNat : 2 ^ m ≤ N + 1 := Nat.pow_log_le_self 2 harg
  have hpowReal : (2 : ℝ) ^ m ≤ (N + 1 : ℕ) := by exact_mod_cast hpowNat
  have hpowPos : 0 < (2 : ℝ) ^ m := by positivity
  have hlog := Real.log_le_log hpowPos hpowReal
  rw [Real.log_pow] at hlog
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoLeOne : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
  have hmLog : ((m : ℝ) + 1) * Real.log 2 ≤ Real.log ((N + 1 : ℕ) : ℝ) + 1 := by
    nlinarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNplusPos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hNplusLe : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast (show N + 1 ≤ 2 * N by omega)
  have hlogNplus : Real.log ((N + 1 : ℕ) : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_le_log hNplusPos hNplusLe
  have hlogMul : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log (N : ℝ) := by
    rw [Real.log_mul (by norm_num) hNpos.ne']
  have hlogNnonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hmajorant : Real.log ((N + 1 : ℕ) : ℝ) + 1 ≤
      2 * (1 + Real.log (N : ℝ)) := by
    rw [hlogMul] at hlogNplus
    nlinarith
  have hmDiv : (m : ℝ) + 1 ≤
      (2 / Real.log 2) * (1 + Real.log (N : ℝ)) := by
    rw [show (2 / Real.log 2) * (1 + Real.log (N : ℝ)) =
      (2 * (1 + Real.log (N : ℝ))) / Real.log 2 by ring,
      le_div_iff₀ hlogTwoPos]
    exact hmLog.trans hmajorant
  norm_num only [Nat.cast_add, Nat.cast_one]
  exact hmDiv

private theorem five_pow_iteratedLogDegree_le_logMajorantCube
    {N : ℕ} (hN : 1 ≤ N) :
    (5 : ℝ) ^ Nat.log 2 (Nat.log 2 (N + 1) + 1) ≤
      (2 / Real.log 2) ^ (3 : ℕ) * (1 + Real.log (N : ℝ)) ^ (3 : ℕ) := by
  let L := Nat.log 2 (N + 1) + 1
  let e := Nat.log 2 L
  have hbase : (5 : ℝ) ^ e ≤ (8 : ℝ) ^ e :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) e
  have hLpos : L ≠ 0 := by dsimp [L]; omega
  have hpowNat : 2 ^ e ≤ L := Nat.pow_log_le_self 2 hLpos
  have hpowReal : (2 : ℝ) ^ e ≤ (L : ℝ) := by exact_mod_cast hpowNat
  have height : (8 : ℝ) ^ e = ((2 : ℝ) ^ e) ^ (3 : ℕ) := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    omega
  have hcube : (8 : ℝ) ^ e ≤ (L : ℝ) ^ (3 : ℕ) := by
    rw [height]
    exact pow_le_pow_left₀ (by positivity) hpowReal 3
  have hLbound := cast_natLog_add_one_le_logMajorant hN
  change (L : ℝ) ≤ (2 / Real.log 2) * (1 + Real.log (N : ℝ)) at hLbound
  have hmajorantNonneg : 0 ≤ (2 / Real.log 2) * (1 + Real.log (N : ℝ)) := by
    have hlogNnonneg : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    positivity
  have hLcube : (L : ℝ) ^ (3 : ℕ) ≤
      ((2 / Real.log 2) * (1 + Real.log (N : ℝ))) ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hLbound 3
  change (5 : ℝ) ^ e ≤ _
  calc
    (5 : ℝ) ^ e ≤ (8 : ℝ) ^ e := hbase
    _ ≤ (L : ℝ) ^ (3 : ℕ) := hcube
    _ ≤ ((2 / Real.log 2) * (1 + Real.log (N : ℝ))) ^ (3 : ℕ) := hLcube
    _ = _ := by rw [mul_pow]

theorem eventually_iteratedLogarithmicCayleySchedule_boundaryFiveScale_le :
    ∀ᶠ N : ℕ in atTop,
      (5 : ℝ) ^
          min (iteratedLogarithmicCayleySchedule N - 24)
            (iteratedLogarithmicCayleySchedule (N + 1) - 24) ≤
        (N : ℝ) ^ (6 / 11 : ℝ) := by
  let c : ℝ := (2 / Real.log 2) ^ (3 : ℕ)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have habsorb :=
    RHTower.Sieve.eventually_const_mul_one_add_log_pow_le_rpow
      (δ := (6 / 11 : ℝ)) (c := c) (by norm_num) hc 3
  have habsorbNat := tendsto_natCast_atTop_atTop.eventually habsorb
  filter_upwards [habsorbNat, eventually_ge_atTop 1] with N hNbound hN
  let e : ℕ := min (iteratedLogarithmicCayleySchedule N - 24)
    (iteratedLogarithmicCayleySchedule (N + 1) - 24)
  have he : e ≤ Nat.log 2 (Nat.log 2 (N + 1) + 1) := by
    calc
      e ≤ iteratedLogarithmicCayleySchedule N - 24 := min_le_left _ _
      _ = Nat.log 2 (Nat.log 2 (N + 1) + 1) := by
        simp [iteratedLogarithmicCayleySchedule]
  have hdegree : (5 : ℝ) ^ e ≤
      (5 : ℝ) ^ Nat.log 2 (Nat.log 2 (N + 1) + 1) :=
    pow_le_pow_right₀ (by norm_num) he
  have hpoly := five_pow_iteratedLogDegree_le_logMajorantCube hN
  change (5 : ℝ) ^ e ≤ (N : ℝ) ^ (6 / 11 : ℝ)
  exact hdegree.trans (hpoly.trans hNbound)

theorem iteratedLogarithmicCayleySchedule_boundaryFivePrimeCeiling :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, ∀ p : ℕ, N₀ ≤ p → p.Prime →
      (5 : ℝ) ^
          min (iteratedLogarithmicCayleySchedule p - 24)
            (iteratedLogarithmicCayleySchedule (p + 1) - 24) ≤
        B * (p : ℝ) ^ (6 / 11 : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    eventually_iteratedLogarithmicCayleySchedule_boundaryFiveScale_le
  refine ⟨1, by norm_num, N₀, fun p hp _ => ?_⟩
  simpa using hN₀ p hp

theorem rhLadder_one_of_iteratedLogarithmicCayleySchedule_locallyBounded
    (hloc : PoleClearedFirstTraceScheduledLocallyBounded
      iteratedLogarithmicCayleySchedule) :
    RHLadder 1 :=
  rhLadder_one_of_poleClearedFirstTraceScheduledLocallyBounded
    tendsto_iteratedLogarithmicCayleySchedule_atTop hloc

/-- Every fixed natural exponential base in the iterated-log degree is eventually absorbed by
every positive power of the Dirichlet cutoff. -/
private theorem natBase_pow_iteratedLogDegree_le_logMajorantPow
    {q r N : ℕ} (hq : q ≤ 2 ^ r) (hN : 1 ≤ N) :
    (q : ℝ) ^ Nat.log 2 (Nat.log 2 (N + 1) + 1) ≤
      (2 / Real.log 2) ^ r * (1 + Real.log (N : ℝ)) ^ r := by
  let L := Nat.log 2 (N + 1) + 1
  let e := Nat.log 2 L
  have hqReal : (q : ℝ) ≤ (2 : ℝ) ^ r := by exact_mod_cast hq
  have hbase : (q : ℝ) ^ e ≤ ((2 : ℝ) ^ r) ^ e :=
    pow_le_pow_left₀ (Nat.cast_nonneg q) hqReal e
  have hLpos : L ≠ 0 := by dsimp [L]; omega
  have hpowNat : 2 ^ e ≤ L := Nat.pow_log_le_self 2 hLpos
  have hpowReal : (2 : ℝ) ^ e ≤ (L : ℝ) := by exact_mod_cast hpowNat
  have height : ((2 : ℝ) ^ r) ^ e = ((2 : ℝ) ^ e) ^ r := by
    calc
      ((2 : ℝ) ^ r) ^ e = (2 : ℝ) ^ (r * e) := (pow_mul 2 r e).symm
      _ = (2 : ℝ) ^ (e * r) := by rw [Nat.mul_comm]
      _ = ((2 : ℝ) ^ e) ^ r := pow_mul 2 e r
  have hpower : ((2 : ℝ) ^ r) ^ e ≤ (L : ℝ) ^ r := by
    rw [height]
    exact pow_le_pow_left₀ (by positivity) hpowReal r
  have hLbound := cast_natLog_add_one_le_logMajorant hN
  change (L : ℝ) ≤ (2 / Real.log 2) * (1 + Real.log (N : ℝ)) at hLbound
  have hLpow : (L : ℝ) ^ r ≤
      ((2 / Real.log 2) * (1 + Real.log (N : ℝ))) ^ r :=
    pow_le_pow_left₀ (by positivity) hLbound r
  change (q : ℝ) ^ e ≤ _
  calc
    (q : ℝ) ^ e ≤ ((2 : ℝ) ^ r) ^ e := hbase
    _ ≤ (L : ℝ) ^ r := hpower
    _ ≤ ((2 / Real.log 2) * (1 + Real.log (N : ℝ))) ^ r := hLpow
    _ = _ := by rw [mul_pow]

/-- Universal fixed-base ceiling for the iterated-log schedule.  Any obstruction whose value at a
fixed test point grows at most exponentially in the Cayley degree is eventually dominated by every
positive power of the arithmetic cutoff. -/
theorem eventually_iteratedLogarithmicCayleySchedule_fixedBaseScale_le
    {q : ℕ} (hq : 1 ≤ q) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      (q : ℝ) ^
          min (iteratedLogarithmicCayleySchedule N - 24)
            (iteratedLogarithmicCayleySchedule (N + 1) - 24) ≤
        (N : ℝ) ^ δ := by
  let c : ℝ := (2 / Real.log 2) ^ q
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have habsorb :=
    RHTower.Sieve.eventually_const_mul_one_add_log_pow_le_rpow
      (δ := δ) (c := c) hδ hc q
  have habsorbNat := tendsto_natCast_atTop_atTop.eventually habsorb
  filter_upwards [habsorbNat, eventually_ge_atTop 1] with N hNbound hN
  let e : ℕ := min (iteratedLogarithmicCayleySchedule N - 24)
    (iteratedLogarithmicCayleySchedule (N + 1) - 24)
  have he : e ≤ Nat.log 2 (Nat.log 2 (N + 1) + 1) := by
    calc
      e ≤ iteratedLogarithmicCayleySchedule N - 24 := min_le_left _ _
      _ = Nat.log 2 (Nat.log 2 (N + 1) + 1) := by
        simp [iteratedLogarithmicCayleySchedule]
  have hdegree : (q : ℝ) ^ e ≤
      (q : ℝ) ^ Nat.log 2 (Nat.log 2 (N + 1) + 1) :=
    pow_le_pow_right₀ (by exact_mod_cast hq) he
  have hqpow : q ≤ 2 ^ q := (Nat.lt_two_pow_self (n := q)).le
  have hpoly := natBase_pow_iteratedLogDegree_le_logMajorantPow hqpow hN
  change (q : ℝ) ^ e ≤ (N : ℝ) ^ δ
  exact hdegree.trans (hpoly.trans hNbound)

end

end RHTower
