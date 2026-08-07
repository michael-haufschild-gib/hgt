import GaloisForLFunctions.RHTower.EulerActivationOccupancyPhaseTransition
import GaloisForLFunctions.HTGeometry.GeometricTailMass

/-!
# The level cascade of the Euler activation product

The activation law at `p` reaches level `m` with probability `q_p^m / (1 + q_p)`, so for
`q_p = p^{-σ}` the local level-`m` masses behave like `p^{-mσ}`.  The hitting dichotomy therefore
gives one phase boundary per level, and they are exactly the reciprocals of the integers:

`the level-m part of the source is almost surely finite  ↔  1 < m·σ  ↔  1/m < σ.`

Level one is the Euler edge `σ = 1`, already the occupancy boundary.  Level two — the part of the
source divisible by the square of a prime — has its boundary at `σ = 1/2`: above the critical line the
squarefull part of the random source is almost surely finite, and at or below it the source is
divisible by infinitely many prime squares.  Each further level adds a boundary at `1/m`, so the whole
harmonic sequence of abscissas is visible inside one product measure.
-/

open MeasureTheory ProbabilityTheory Filter Set
open GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## The local level mass -/

theorem unitIntervalComplement_coe (q : unitInterval) :
    ((unitIntervalComplement q : unitInterval) : ℝ) = 1 - (q : ℝ) := rfl

theorem unitIntervalComplement_ne_zero {q : unitInterval} (hq : (q : ℝ) ≠ 1) :
    unitIntervalComplement q ≠ 0 := by
  intro h
  have hcoe : ((unitIntervalComplement q : unitInterval) : ℝ) = 0 := by
    rw [h]; rfl
  rw [unitIntervalComplement_coe] at hcoe
  exact hq (by linarith)

/-- **The local activation law reaches level `n + 1` with probability `q^{n+1} / (1 + q)`.**  The
occupancy bit contributes the factor `q / (1 + q)` and the conditional geometric fibre contributes the
tail `q^n`. -/
theorem diagonalActivationMeasure_Ici_succ (q : unitInterval) (hq : (q : ℝ) ≠ 1) (n : ℕ) :
    diagonalActivationMeasure q {k : ℕ | n + 1 ≤ k} =
      ENNReal.ofReal ((q : ℝ) ^ (n + 1) / (1 + (q : ℝ))) := by
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := q.2.1
  have hd : (0 : ℝ) < 1 + (q : ℝ) := by linarith
  have hcoe : ((unitIntervalToNNReal q : NNReal) : ENNReal) = ENNReal.ofReal (q : ℝ) := by
    rw [ENNReal.ofReal_eq_coe_nnreal hq0]
    rfl
  have hpre : Nat.succ ⁻¹' {k : ℕ | n + 1 ≤ k} = {j : ℕ | n ≤ j} := by
    ext j
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    omega
  have hdirac : (Measure.dirac (0 : ℕ)) {k : ℕ | n + 1 ≤ k} = 0 := by
    rw [Measure.dirac_apply' _ MeasurableSet.of_discrete, Set.indicator_of_notMem]
    intro h
    exact absurd h (by simp)
  have hmap : ((ProbabilityTheory.geometricMeasure (unitIntervalComplement q)).map Nat.succ)
      {k : ℕ | n + 1 ≤ k} = ENNReal.ofReal ((q : ℝ) ^ n) := by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.of_discrete, hpre,
      geometricMeasure_Ici (unitIntervalComplement_ne_zero hq) n,
      unitIntervalComplement_coe]
    congr 1
    ring
  have hreal : (q : ℝ) ^ (n + 1) / (1 + (q : ℝ)) =
      (q : ℝ) ^ n * ((q : ℝ) / (1 + (q : ℝ))) := by
    field_simp
    ring
  rw [diagonalActivationMeasure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    hdirac, hmap, hcoe, smul_eq_mul, smul_eq_mul, mul_zero, zero_add, hreal,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos hd,
    ENNReal.ofReal_add (by norm_num) hq0, ENNReal.ofReal_one, mul_comm]

/-! ## The level threshold -/

/-- **The local level masses are summable exactly above `1/m`.**  Above the boundary they are
dominated by `p^{-mσ}`; at or below it they exceed half a prime reciprocal. -/
theorem summable_diagonalActivationLevel_iff {σ : ℝ} (hσ : 0 < σ) {m : ℕ} (hm : 1 ≤ m) :
    Summable (fun p : Nat.Primes =>
        ((p : ℝ) ^ (-σ)) ^ m / (1 + (p : ℝ) ^ (-σ))) ↔ 1 < (m : ℝ) * σ := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hpow : ∀ p : Nat.Primes, ((p : ℝ) ^ (-σ)) ^ m = (p : ℝ) ^ (-((m : ℝ) * σ)) := by
    intro p
    have hp : (0 : ℝ) ≤ (p : ℝ) := by positivity
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-σ)) m, ← Real.rpow_mul hp]
    congr 1
    ring
  constructor
  · intro h
    by_contra hle
    have hle' : (m : ℝ) * σ ≤ 1 := not_lt.mp hle
    refine Nat.Primes.not_summable_one_div ?_
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (h.mul_left 2)
    · have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
      positivity
    · have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
      have hq0 : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by linarith) _
      have hq1 : (p : ℝ) ^ (-σ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hp1.le (by linarith)
      have hd : (0 : ℝ) < 1 + (p : ℝ) ^ (-σ) := by linarith
      have hlev : (1 : ℝ) / (p : ℝ) ≤ ((p : ℝ) ^ (-σ)) ^ m := by
        rw [hpow p, one_div, ← Real.rpow_neg_one]
        exact (Real.rpow_le_rpow_left_iff hp1).mpr (by linarith)
      have hpow0 : (0 : ℝ) ≤ ((p : ℝ) ^ (-σ)) ^ m := by positivity
      have hpow1 : ((p : ℝ) ^ (-σ)) ^ m ≤ 1 := pow_le_one₀ hq0.le hq1
      have hhalf : ((p : ℝ) ^ (-σ)) ^ m ≤
          2 * (((p : ℝ) ^ (-σ)) ^ m / (1 + (p : ℝ) ^ (-σ))) := by
        have hid : 2 * (((p : ℝ) ^ (-σ)) ^ m / (1 + (p : ℝ) ^ (-σ))) -
            ((p : ℝ) ^ (-σ)) ^ m =
              ((p : ℝ) ^ (-σ)) ^ m * (1 - (p : ℝ) ^ (-σ)) / (1 + (p : ℝ) ^ (-σ)) := by
          field_simp
          ring
        have hnn : (0 : ℝ) ≤
            ((p : ℝ) ^ (-σ)) ^ m * (1 - (p : ℝ) ^ (-σ)) / (1 + (p : ℝ) ^ (-σ)) :=
          div_nonneg (mul_nonneg hpow0 (by linarith)) hd.le
        linarith
      linarith
  · intro hgt
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
      ((Nat.Primes.summable_rpow (r := -((m : ℝ) * σ))).mpr (by linarith))
    · have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
      have hq0 : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by linarith) _
      positivity
    · have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
      have hq0 : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by linarith) _
      have hd : (1 : ℝ) ≤ 1 + (p : ℝ) ^ (-σ) := by linarith
      rw [hpow p, div_le_iff₀ (by linarith)]
      nlinarith [Real.rpow_pos_of_pos (show (0:ℝ) < (p:ℝ) by linarith) (-((m : ℝ) * σ))]

/-- The total local level mass of the activation product at exponent `σ`. -/
theorem tsum_eulerActivation_levelMass_ne_top_iff {σ : ℝ} (hσ : 0 < σ) {m : ℕ} (hm : 1 ≤ m) :
    (∑' p : Nat.Primes,
        diagonalActivationMeasure (eulerActivationParameter hσ.le p)
          {k : ℕ | m ≤ k}) ≠ ∞ ↔ 1 < (m : ℝ) * σ := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hlocal : ∀ p : Nat.Primes,
      diagonalActivationMeasure (eulerActivationParameter hσ.le p) {k : ℕ | n + 1 ≤ k} =
        ENNReal.ofReal (((p : ℝ) ^ (-σ)) ^ (n + 1) / (1 + (p : ℝ) ^ (-σ))) := by
    intro p
    have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt
    have hne : ((eulerActivationParameter hσ.le p : unitInterval) : ℝ) ≠ 1 := by
      rw [eulerActivationParameter_coe]
      have hlt : ((p : ℕ) : ℝ) ^ (-σ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
      exact ne_of_lt hlt
    rw [diagonalActivationMeasure_Ici_succ _ hne n, eulerActivationParameter_coe]
  rw [tsum_congr hlocal, tsum_ofReal_ne_top_iff_summable _ fun p => ?_]
  · exact summable_diagonalActivationLevel_iff hσ (by omega)
  · have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
    have hq0 : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by linarith) _
    positivity

/-! ## The cascade of phase boundaries -/

/-- **One phase boundary per level, at the reciprocals of the integers.**  The level-`m` part of the
activation source is almost surely finite exactly when `1 < m·σ`. -/
theorem eulerActivationProductMeasure_finiteLevel_eq_one_iff {σ : ℝ} (hσ : 0 < σ)
    {m : ℕ} (hm : 1 ≤ m) :
    eulerActivationProductMeasure hσ.le
        {K : CriticalEulerConfiguration | {p : Nat.Primes | m ≤ K p}.Finite} = 1 ↔
      1 < (m : ℝ) * σ := by
  have h := measure_finiteHit_eq_one_iff
    (fun p : Nat.Primes => diagonalActivationMeasure (eulerActivationParameter hσ.le p))
    (fun _ => {k : ℕ | m ≤ k})
    (Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes)))
  rw [eulerActivationProductMeasure]
  exact h.trans (tsum_eulerActivation_levelMass_ne_top_iff hσ hm)

/-- The same boundary written as an abscissa. -/
theorem eulerActivationProductMeasure_finiteLevel_eq_one_iff_inv_lt {σ : ℝ} (hσ : 0 < σ)
    {m : ℕ} (hm : 1 ≤ m) :
    eulerActivationProductMeasure hσ.le
        {K : CriticalEulerConfiguration | {p : Nat.Primes | m ≤ K p}.Finite} = 1 ↔
      1 / (m : ℝ) < σ := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  rw [eulerActivationProductMeasure_finiteLevel_eq_one_iff hσ hm, div_lt_iff₀ hmpos]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **The critical line is the level-two boundary.**  Above `σ = 1/2` the squarefull part of the
activation source is almost surely finite; at or below it, almost every configuration is divisible by
infinitely many prime squares. -/
theorem eulerActivationProductMeasure_finiteSquarefull_eq_one_iff {σ : ℝ} (hσ : 0 < σ) :
    eulerActivationProductMeasure hσ.le
        {K : CriticalEulerConfiguration | {p : Nat.Primes | 2 ≤ K p}.Finite} = 1 ↔
      1 / 2 < σ := by
  have h := eulerActivationProductMeasure_finiteLevel_eq_one_iff_inv_lt hσ
    (m := 2) (by norm_num)
  rwa [show ((2 : ℕ) : ℝ) = 2 by norm_num] at h

/-- At or below the critical line the squarefull part is almost surely infinite. -/
theorem eulerActivationProductMeasure_infiniteSquarefull_of_le_half {σ : ℝ} (hσ : 0 < σ)
    (h1 : σ ≤ 1 / 2) :
    eulerActivationProductMeasure hσ.le
        {K : CriticalEulerConfiguration | {p : Nat.Primes | 2 ≤ K p}.Infinite} = 1 := by
  rw [eulerActivationProductMeasure]
  refine measure_infiniteHit_eq_one _ (fun _ => {k : ℕ | 2 ≤ k})
    (Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes))) ?_
  by_contra hne
  have hgt := (tsum_eulerActivation_levelMass_ne_top_iff hσ (m := 2) (by norm_num)).mp hne
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num] at hgt
  linarith

end

end RHTower
