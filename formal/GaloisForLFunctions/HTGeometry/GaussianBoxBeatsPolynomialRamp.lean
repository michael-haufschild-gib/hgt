import GaloisForLFunctions.HTGeometry.PauliCountOrderBounds
import GaloisForLFunctions.HTGeometry.PolyLogBeatenByOneMorePower
import GaloisForLFunctions.HTGeometry.GaussianProductBoxFloor

/-!
# The Gaussian box outlives any polynomial ramp

The negative logarithm of the Gaussian product-box floor grows like `n^q log n`, while the negative
logarithm of a ramp bound with exponent proportional to the observer rank grows like `n^{q+1}`.  One
more power beats a logarithm, so the floor eventually exceeds the ramp bound and the ramp bound
fails.

The comparison is uniform in the ramp's own parameters: no positive time exponent and no exponent
deficit below one can rescue it, because both only move constants.
-/

open Filter

namespace HTGeometry

noncomputable section

/-- **The rarity exponent is `O_q(n^q log n)`**, with the constants explicit rather than
asymptotic.  The negative logarithm of the Gaussian product-box floor is eventually below a fixed
multiple of `n^q` times the logarithm of a fixed multiple of `n^q`. -/
theorem eventually_rarityExponent_le_polyLog (q : ℕ) (hq : 1 ≤ q) {ε : ℝ} (hε0 : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (Quantum.nonidentityPauliWeightCount n q : ℝ) *
          Real.log (8 * (Quantum.nonidentityPauliWeightCount n q : ℝ) /
            (gaussianFloorConstant * ε ^ (2 : ℕ)))
        ≤ (q : ℝ) * 3 ^ q * (n : ℝ) ^ q *
            Real.log (8 * ((q : ℝ) * 3 ^ q) / (gaussianFloorConstant * ε ^ (2 : ℕ)) * (n : ℝ) ^ q) := by
  set A : ℝ := (q : ℝ) * 3 ^ q with hAdef
  set K : ℝ := gaussianFloorConstant * ε ^ (2 : ℕ) with hKdef
  have hK : 0 < K := by
    rw [hKdef]; exact mul_pos gaussianFloorConstant_pos (by positivity)
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hA : 0 < A := by rw [hAdef]; positivity
  set d : ℝ := 8 * A / K with hddef
  have hd : 0 < d := by rw [hddef]; positivity
  have htend : Filter.Tendsto (fun n : ℕ => d * (n : ℝ) ^ q) atTop atTop := by
    refine Filter.Tendsto.const_mul_atTop hd ?_
    exact (tendsto_pow_atTop (n := q) (by omega)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, htend.eventually_ge_atTop 1] with n h1 hone
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h1
  have hlognn : (0 : ℝ) ≤ Real.log (d * (n : ℝ) ^ q) := Real.log_nonneg hone
  have hmr : (0 : ℝ) < (Quantum.nonidentityPauliWeightCount n q : ℝ) := by
    exact_mod_cast Quantum.one_le_nonidentityPauliWeightCount h1 hq
  have hmle : (Quantum.nonidentityPauliWeightCount n q : ℝ) ≤ A * (n : ℝ) ^ q := by
    have h := Quantum.nonidentityPauliWeightCount_le n q h1
    have hcast : ((q * 3 ^ q * n ^ q : ℕ) : ℝ) = A * (n : ℝ) ^ q := by
      rw [hAdef]; push_cast; ring
    calc (Quantum.nonidentityPauliWeightCount n q : ℝ) ≤ ((q * 3 ^ q * n ^ q : ℕ) : ℝ) := by
          exact_mod_cast h
      _ = A * (n : ℝ) ^ q := hcast
  have harg : 8 * (Quantum.nonidentityPauliWeightCount n q : ℝ) / K ≤ d * (n : ℝ) ^ q := by
    rw [hddef, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hK]
    nlinarith [hmle, pow_nonneg hnr.le q]
  have hlogle : Real.log (8 * (Quantum.nonidentityPauliWeightCount n q : ℝ) / K)
      ≤ Real.log (d * (n : ℝ) ^ q) := Real.log_le_log (by positivity) harg
  calc (Quantum.nonidentityPauliWeightCount n q : ℝ) *
        Real.log (8 * (Quantum.nonidentityPauliWeightCount n q : ℝ) / K)
      ≤ (Quantum.nonidentityPauliWeightCount n q : ℝ) * Real.log (d * (n : ℝ) ^ q) :=
        mul_le_mul_of_nonneg_left hlogle hmr.le
    _ ≤ A * (n : ℝ) ^ q * Real.log (d * (n : ℝ) ^ q) :=
        mul_le_mul_of_nonneg_right hmle hlognn

/-- **The rarity exponent is eventually below the ramp exponent.**  Consequently the Gaussian
product-box floor eventually exceeds any bound whose exponent is proportional to the observer rank,
for every positive time exponent and every exponent deficit below one. -/
theorem eventually_rarityExponent_lt_rampExponent (q : ℕ) (hq : 1 ≤ q)
    {c η ε : ℝ} (hc : 0 < c) (hη : η < 1) (hε0 : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (Quantum.nonidentityPauliWeightCount n q : ℝ) *
          Real.log (8 * (Quantum.nonidentityPauliWeightCount n q : ℝ) /
            (gaussianFloorConstant * ε ^ (2 : ℕ)))
        < (1 - η) * (Quantum.productInputObserverRank n q : ℝ) *
            (c * (n : ℝ) * Real.log 2) := by
  set A : ℝ := (q : ℝ) * 3 ^ q with hAdef
  set K : ℝ := gaussianFloorConstant * ε ^ (2 : ℕ) with hKdef
  have hK : 0 < K := by
    rw [hKdef]; exact mul_pos gaussianFloorConstant_pos (by positivity)
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hA : 0 < A := by rw [hAdef]; positivity
  set d : ℝ := 8 * A / K with hddef
  have hd : 0 < d := by rw [hddef]; positivity
  have hfac : (0 : ℝ) < (q.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos q
  set D : ℝ := (1 - η) * 2 * c * Real.log 2 / (2 ^ q * (q.factorial : ℝ)) with hDdef
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by
    rw [hDdef]
    have h1 : (0 : ℝ) < 1 - η := by linarith
    positivity
  have htend : Filter.Tendsto (fun n : ℕ => d * (n : ℝ) ^ q) atTop atTop := by
    refine Filter.Tendsto.const_mul_atTop hd ?_
    exact (tendsto_pow_atTop (n := q) (by omega)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_polyLog_lt_pow_succ_nat q (a := D) (b := A) hD hd,
    eventually_ge_atTop (2 * q),
    eventually_rarityExponent_le_polyLog q hq hε0] with n hpoly h2q hleft0
  -- the left side is below the polynomial-logarithm profile
  have hleft : (Quantum.nonidentityPauliWeightCount n q : ℝ) *
      Real.log (8 * (Quantum.nonidentityPauliWeightCount n q : ℝ) / K)
      ≤ A * (n : ℝ) ^ q * Real.log (d * (n : ℝ) ^ q) := by
    simpa only [hddef, hAdef, hKdef] using hleft0
  -- the right side dominates the next power
  have hright : D * (n : ℝ) ^ (q + 1)
      ≤ (1 - η) * (Quantum.productInputObserverRank n q : ℝ) * (c * (n : ℝ) * Real.log 2) := by
    have hrank := Quantum.pow_le_productInputObserverRank n q hq h2q
    have hpos : (0 : ℝ) < (1 - η) * (c * Real.log 2) := by
      have : (0 : ℝ) < 1 - η := by linarith
      positivity
    have hstep : (1 - η) * (2 * ((n : ℝ) / 2) ^ q / (q.factorial : ℝ)) * (c * (n : ℝ) * Real.log 2)
        ≤ (1 - η) * (Quantum.productInputObserverRank n q : ℝ) * (c * (n : ℝ) * Real.log 2) := by
      have h1η : (0 : ℝ) ≤ 1 - η := by linarith
      have hcn : (0 : ℝ) ≤ c * (n : ℝ) * Real.log 2 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrank h1η) hcn
    refine le_trans (le_of_eq ?_) hstep
    rw [hDdef, div_pow]
    field_simp
    ring
  linarith [hpoly, hleft, hright]

end

end HTGeometry
