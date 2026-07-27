import GaloisForLFunctions.RHTower.GammaOrbitDomainNoGo
import GaloisForLFunctions.RHTower.SquarefreePartitionPole

/-!
# The Gamma-damped squarefree Dirichlet series

The damped source series of the card is

```text
F(σ) = ∑_d μ(d)² η_d d^(-σ) ,      η_d = (1 + d^(-4))^(-1/4) ,
```

and it differs from the squarefree partition `Z(σ) = ∑_d μ(d)² d^(-σ)` by the correction series
`∑_d μ(d)² (η_d - 1) d^(-σ)`.  Because `0 ≤ 1 - η_d ≤ d^(-4)/4`, the correction converges absolutely
in the far larger half plane `σ > -3` and is uniformly bounded for `σ ≥ 0`.  This is the
holomorphic-remainder structure of `(19)`: the damping does not move the pole, so `F` inherits the
critical scaling of `Z`,

```text
(σ - 1) F(σ) → 1/ζ(2) = 6/π²        (σ → 1+).
```
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ### The damping defect -/

/-- Concavity bound for the quarter root: `1 - (1+x)^(-1/4) ≤ x/4` on the unit interval. -/
theorem one_sub_rpow_quarter_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - (1 + x) ^ (-(1 : ℝ) / 4) ≤ x / 4 := by
  have hbase : (0 : ℝ) < 1 + x := by linarith
  have hpos : (0 : ℝ) < (1 + x) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos hbase _
  have hlow : (0 : ℝ) ≤ 1 - x / 4 := by linarith
  have h4 : ((1 + x) ^ (-(1 : ℝ) / 4)) ^ (4 : ℕ) = (1 + x)⁻¹ := by
    rw [← Real.rpow_natCast ((1 + x) ^ (-(1 : ℝ) / 4)) 4, ← Real.rpow_mul hbase.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hprod : (1 - x / 4) ^ (4 : ℕ) * (1 + x) ≤ 1 := by
    nlinarith [sq_nonneg x, sq_nonneg (x * x), sq_nonneg (x - 1)]
  have hle4 : (1 - x / 4) ^ (4 : ℕ) ≤ ((1 + x) ^ (-(1 : ℝ) / 4)) ^ (4 : ℕ) := by
    rw [h4, ← one_div, le_div_iff₀ hbase]
    exact hprod
  have hle : 1 - x / 4 ≤ (1 + x) ^ (-(1 : ℝ) / 4) := by
    by_contra hcon
    have hba : (1 + x) ^ (-(1 : ℝ) / 4) < 1 - x / 4 := not_le.mp hcon
    have hfac : (1 - x / 4) ^ (4 : ℕ) - ((1 + x) ^ (-(1 : ℝ) / 4)) ^ (4 : ℕ)
        = ((1 - x / 4) - (1 + x) ^ (-(1 : ℝ) / 4)) *
          ((1 - x / 4) ^ 3 + (1 - x / 4) ^ 2 * (1 + x) ^ (-(1 : ℝ) / 4)
            + (1 - x / 4) * ((1 + x) ^ (-(1 : ℝ) / 4)) ^ 2
            + ((1 + x) ^ (-(1 : ℝ) / 4)) ^ 3) := by ring
    have hsecond : (0 : ℝ) < (1 - x / 4) ^ 3 + (1 - x / 4) ^ 2 * (1 + x) ^ (-(1 : ℝ) / 4)
        + (1 - x / 4) * ((1 + x) ^ (-(1 : ℝ) / 4)) ^ 2
        + ((1 + x) ^ (-(1 : ℝ) / 4)) ^ 3 := by positivity
    nlinarith [hfac, hsecond, hba, hle4]
  linarith

/-- The damping defect at `d` is at most a quarter of the fourth-power weight. -/
theorem one_sub_gammaDampingFactor_le (d : ℕ) :
    1 - gammaDampingFactor d ≤ (1 / 4) * (d : ℝ) ^ (-4 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (d : ℝ) ^ (-4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hx1 : (d : ℝ) ^ (-4 : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
      norm_num
    · have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have := Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num : (-4 : ℝ) ≤ 0)
      rwa [Real.rpow_zero] at this
  have h := one_sub_rpow_quarter_le hx0 hx1
  rw [gammaDampingFactor]
  linarith

/-! ### The damped mass and its correction -/

/-- The Gamma-damped squarefree mass. -/
def gammaDampedMass (σ : ℝ) (d : ℕ) : ℝ :=
  if Squarefree d then gammaDampingFactor d * (d : ℝ) ^ (-σ) else 0

theorem gammaDampedMass_nonneg (σ : ℝ) (d : ℕ) : 0 ≤ gammaDampedMass σ d := by
  rw [gammaDampedMass]
  split_ifs
  · exact mul_nonneg (gammaDampingFactor_pos d).le (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  · exact le_rfl

theorem gammaDampedMass_le (σ : ℝ) (d : ℕ) :
    gammaDampedMass σ d ≤ squarefreeMobiusMass σ d := by
  rw [gammaDampedMass, squarefreeMobiusMass]
  split_ifs
  · have hpow : (0 : ℝ) ≤ (d : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg d) _
    nlinarith [gammaDampingFactor_le_one d]
  · exact le_rfl

theorem summable_gammaDampedMass {σ : ℝ} (hσ : 1 < σ) : Summable (gammaDampedMass σ) :=
  Summable.of_nonneg_of_le (gammaDampedMass_nonneg σ) (gammaDampedMass_le σ)
    (summable_squarefreeMobiusMass hσ)

/-- The damping correction is bounded by the fourth-power weight, uniformly for `σ ≥ 0`. -/
theorem abs_gammaDampedMass_sub_le {σ : ℝ} (hσ : 0 ≤ σ) (d : ℕ) :
    |gammaDampedMass σ d - squarefreeMobiusMass σ d| ≤ (1 / 4) * (d : ℝ) ^ (-4 : ℝ) := by
  have hnn : (0 : ℝ) ≤ (1 / 4) * (d : ℝ) ^ (-4 : ℝ) := by
    have := Real.rpow_nonneg (Nat.cast_nonneg d) (-4 : ℝ)
    positivity
  rw [gammaDampedMass, squarefreeMobiusMass]
  split_ifs with hsq
  · have hd0 : d ≠ 0 := by
      intro h
      rw [h] at hsq
      exact not_squarefree_zero hsq
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
      have : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
      exact_mod_cast this
    have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
    have hpow : (0 : ℝ) < (d : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hdpos _
    have hpowle : (d : ℝ) ^ (-σ) ≤ 1 := by
      have := Real.rpow_le_rpow_of_exponent_le hd1 (by linarith : (-σ : ℝ) ≤ 0)
      rwa [Real.rpow_zero] at this
    have hdefect := one_sub_gammaDampingFactor_le d
    have hle1 := gammaDampingFactor_le_one d
    have hkey : |gammaDampingFactor d * (d : ℝ) ^ (-σ) - (d : ℝ) ^ (-σ)|
        = (1 - gammaDampingFactor d) * (d : ℝ) ^ (-σ) := by
      rw [show gammaDampingFactor d * (d : ℝ) ^ (-σ) - (d : ℝ) ^ (-σ)
          = -((1 - gammaDampingFactor d) * (d : ℝ) ^ (-σ)) by ring, abs_neg,
        abs_of_nonneg (by nlinarith)]
    rw [hkey]
    calc (1 - gammaDampingFactor d) * (d : ℝ) ^ (-σ)
        ≤ ((1 / 4) * (d : ℝ) ^ (-4 : ℝ)) * 1 := by
          refine mul_le_mul hdefect hpowle hpow.le ?_
          have := Real.rpow_nonneg (Nat.cast_nonneg d) (-4 : ℝ)
          positivity
      _ = (1 / 4) * (d : ℝ) ^ (-4 : ℝ) := by ring
  · simpa using hnn

/-- The damping correction converges absolutely far to the left of the critical line. -/
theorem summable_gammaDampedCorrection {σ : ℝ} (hσ : 0 ≤ σ) :
    Summable (fun d : ℕ => gammaDampedMass σ d - squarefreeMobiusMass σ d) := by
  have hbase : Summable (fun d : ℕ => (1 : ℝ) / (d : ℝ) ^ (4 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hneg : Summable (fun d : ℕ => (d : ℝ) ^ (-4 : ℝ)) := by
    refine hbase.congr fun d => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg d), one_div]
  refine Summable.of_norm_bounded (hneg.mul_left (1 / 4)) fun d => ?_
  rw [Real.norm_eq_abs]
  exact abs_gammaDampedMass_sub_le hσ d

/-- The damped total `F(σ)`. -/
def gammaDampedTotal (σ : ℝ) : ℝ := ∑' d : ℕ, gammaDampedMass σ d

/-- The damped total is the squarefree partition plus the bounded correction. -/
theorem gammaDampedTotal_eq {σ : ℝ} (hσ : 1 < σ) :
    gammaDampedTotal σ
      = squarefreeMobiusTotal σ
        + ∑' d : ℕ, (gammaDampedMass σ d - squarefreeMobiusMass σ d) := by
  rw [gammaDampedTotal, squarefreeMobiusTotal,
    (summable_gammaDampedMass hσ).tsum_sub (summable_squarefreeMobiusMass hσ)]
  ring

/-- The correction total is uniformly bounded for `σ ≥ 0`. -/
theorem abs_tsum_gammaDampedCorrection_le {σ : ℝ} (hσ : 0 ≤ σ) :
    |∑' d : ℕ, (gammaDampedMass σ d - squarefreeMobiusMass σ d)|
      ≤ (1 / 4) * ∑' d : ℕ, (d : ℝ) ^ (-4 : ℝ) := by
  have hbase : Summable (fun d : ℕ => (1 : ℝ) / (d : ℝ) ^ (4 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hneg : Summable (fun d : ℕ => (d : ℝ) ^ (-4 : ℝ)) := by
    refine hbase.congr fun d => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg d), one_div]
  have hdom : Summable (fun d : ℕ => (1 / 4) * (d : ℝ) ^ (-4 : ℝ)) := hneg.mul_left _
  have hpt : ∀ d : ℕ, ‖gammaDampedMass σ d - squarefreeMobiusMass σ d‖
      ≤ (1 / 4) * (d : ℝ) ^ (-4 : ℝ) := by
    intro d
    rw [Real.norm_eq_abs]
    exact abs_gammaDampedMass_sub_le hσ d
  have hnorms : Summable (fun d : ℕ => ‖gammaDampedMass σ d - squarefreeMobiusMass σ d‖) :=
    Summable.of_nonneg_of_le (fun d => norm_nonneg _) hpt hdom
  calc |∑' d : ℕ, (gammaDampedMass σ d - squarefreeMobiusMass σ d)|
      = ‖∑' d : ℕ, (gammaDampedMass σ d - squarefreeMobiusMass σ d)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' d : ℕ, ‖gammaDampedMass σ d - squarefreeMobiusMass σ d‖ :=
        norm_tsum_le_tsum_norm hnorms
    _ ≤ ∑' d : ℕ, (1 / 4) * (d : ℝ) ^ (-4 : ℝ) := Summable.tsum_mono hnorms hdom hpt
    _ = (1 / 4) * ∑' d : ℕ, (d : ℝ) ^ (-4 : ℝ) := tsum_mul_left

/-- **The damping does not move the pole.**  `(σ - 1) F(σ) → 6/π²` as `σ ↓ 1`. -/
theorem tendsto_sub_one_mul_gammaDampedTotal :
    Tendsto (fun σ : ℝ => (σ - 1) * gammaDampedTotal σ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (6 / Real.pi ^ 2)) := by
  set C : ℝ := (1 / 4) * ∑' d : ℕ, (d : ℝ) ^ (-4 : ℝ) with hC
  have hZ := tendsto_sub_one_mul_squarefreeMobiusTotal
  have hcorr : Tendsto
      (fun σ : ℝ => (σ - 1) * ∑' d : ℕ, (gammaDampedMass σ d - squarefreeMobiusMass σ d))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    have hzero : Tendsto (fun σ : ℝ => (σ - 1) * C) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
      have hcont : Continuous (fun σ : ℝ => (σ - 1) * C) := by fun_prop
      have h0 : Tendsto (fun σ : ℝ => (σ - 1) * C) (nhds 1) (nhds 0) := by
        simpa using hcont.tendsto (1 : ℝ)
      exact h0.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hzero
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : (1 : ℝ) < σ := hσ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ - 1)]
    exact mul_le_mul_of_nonneg_left (abs_tsum_gammaDampedCorrection_le (by linarith))
      (by linarith)
  have hsum := hZ.add hcorr
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ1 : (1 : ℝ) < σ := hσ
  rw [gammaDampedTotal_eq hσ1]
  ring

end

end RHTower
