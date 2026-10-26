import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FakeCurvesAndTheWindowLaw
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Moment amplification of any family loses linearly

A rate from an amplified observable needs a loss law `b_k = o(k)` (B1.9). ACG proved that
amplification through the moments of the gauge torus loses linearly (gauge Jensen). This file
proves the same for every family average — characters mod `q`, archimedean windows, any finite
weighted family of twists — and identifies the only lossless case.

* **Family Jensen** (`family_moment_le`): for weights `w ≥ 0` with `Σ w = 1` and an observable
  `z ≥ 0`, `(Σ w z)^k ≤ Σ w z^k`.
* **The loss law** (`mul_log_mean_le_log_bound`): any bound `Σ w z^k ≤ B_k` has
  `k log(Σ w z) ≤ log B_k`. The exponent of the bound grows at least linearly in the order, with
  slope the logarithm of the mean: family averages amplify depth exactly as fast as they pay.
* **Zero loss is flatness** (`sq_mean_eq_mean_sq_iff`): `(Σ w z)² = Σ w z²` iff `z` is constant on
  the support of `w`. A family amplifies without loss only if the observable has the same size on
  every member.
* **Calibration over `𝔽_q`** (`curveDatum_flat_iff_unitary`, `goldenDatum_not_flat`): for the family
  of Frobenius eigenvalues of a curve datum with uniform weights and `z_i = |β_i|²`, zero loss is
  unitarity, by the functional equation `|β_i| |β_{fe(i)}| = 1`. The golden datum loses:
  `(Σ|β|⁴)/2 = 7/2 > (3/2)² = ((Σ|β|²)/2)²`.

So family averages over `χ mod q`, over windows of the archimedean line, or over any other finite
family of twists lose linearly, as moments of the gauge torus do; the one lossless family is a
flat one, and on a curve flatness of the eigenvalue family is purity. A sublinear loss law must come
from a structure that is not an average of sizes.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

section Family

variable {ι : Type*} (s : Finset ι) (w z : ι → ℝ)

/-- **Family Jensen**: `(Σ w z)^k ≤ Σ w z^k` for probability weights and `z ≥ 0`. -/
theorem family_moment_le (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i) (k : ℕ) :
    (∑ i ∈ s, w i * z i) ^ k ≤ ∑ i ∈ s, w i * z i ^ k :=
  Real.pow_arith_mean_le_arith_mean_pow s w z hw hw1 hz k

/-- **The loss law of family averages**: a bound `Σ w z^k ≤ B` gives `k log(Σ w z) ≤ log B`. -/
theorem mul_log_mean_le_log_bound (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i) (hm : 0 < ∑ i ∈ s, w i * z i) (k : ℕ) {B : ℝ}
    (hB : ∑ i ∈ s, w i * z i ^ k ≤ B) :
    k * Real.log (∑ i ∈ s, w i * z i) ≤ Real.log B := by
  have h := (family_moment_le s w z hw hw1 hz k).trans hB
  have hpos : 0 < (∑ i ∈ s, w i * z i) ^ k := pow_pos hm k
  rw [← Real.log_pow]
  exact Real.log_le_log hpos h

/-- **Zero loss is flatness.** `(Σ w z)² = Σ w z²` iff `z` equals its mean on the support of `w`. -/
theorem sq_mean_eq_mean_sq_iff (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) :
    (∑ i ∈ s, w i * z i) ^ 2 = ∑ i ∈ s, w i * z i ^ 2 ↔
      ∀ i ∈ s, w i ≠ 0 → z i = ∑ j ∈ s, w j * z j := by
  set m := ∑ j ∈ s, w j * z j
  -- the variance `Σ w (z − m)²` equals `Σ w z² − m²`
  have hvar : ∑ i ∈ s, w i * (z i - m) ^ 2 = ∑ i ∈ s, w i * z i ^ 2 - m ^ 2 := by
    have e : ∀ i ∈ s, w i * (z i - m) ^ 2 = w i * z i ^ 2 - 2 * m * (w i * z i) + m ^ 2 * w i :=
      fun i _ => by ring
    rw [sum_congr rfl e, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hw1]
    ring
  have hterm : ∀ i ∈ s, 0 ≤ w i * (z i - m) ^ 2 := fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  constructor
  · intro h i hi hwi
    have h0 : ∑ i ∈ s, w i * (z i - m) ^ 2 = 0 := by rw [hvar, h]; ring
    have := (sum_eq_zero_iff_of_nonneg hterm).mp h0 i hi
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hwi
    · exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
  · intro h
    have h0 : ∑ i ∈ s, w i * (z i - m) ^ 2 = 0 := by
      refine sum_eq_zero fun i hi => ?_
      by_cases hwi : w i = 0
      · rw [hwi, zero_mul]
      · rw [h i hi hwi, sub_self]; ring
    rw [hvar] at h0
    linarith

end Family

/-! ### Calibration over `𝔽_q` -/

open ArithmeticCastelnuovoSeveri

/-- **On a curve datum, a flat eigenvalue family is a unitary one.** If all `|β_i|` are equal, the
functional equation `|β_i| |β_{fe(i)}| = 1` forces `|β_i| = 1`. -/
theorem curveDatum_flat_iff_unitary {ι : Type*} [Fintype ι] (D : CurveDatum ι) :
    (∀ i j, ‖D.β i‖ = ‖D.β j‖) ↔ ∀ i, ‖D.β i‖ = 1 := by
  constructor
  · intro h i
    have hfe : ‖D.β (D.fePerm i)‖ * ‖D.β i‖ = 1 := by rw [← norm_mul, D.β_fePerm, norm_one]
    rw [h (D.fePerm i) i] at hfe
    have h2 : ‖D.β i‖ ^ 2 = 1 := by rw [sq]; exact hfe
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  · intro h i j; rw [h i, h j]

open Real in
/-- **The golden datum loses**: with uniform weights, `((φ² + φ⁻²)/2)² = 9/4 < 7/2 = (φ⁴ + φ⁻⁴)/2`. -/
theorem goldenDatum_not_flat :
    ((goldenRatio ^ 2 + goldenRatio⁻¹ ^ 2) / 2) ^ 2 < (goldenRatio ^ 4 + goldenRatio⁻¹ ^ 4) / 2 := by
  -- `φ² + φ⁻² = 3` and `φ φ⁻¹ = 1`, so `φ⁴ + φ⁻⁴ = 3² − 2 = 7`
  have hmul : goldenRatio * goldenRatio⁻¹ = 1 := mul_inv_cancel₀ goldenRatio_ne_zero
  have h2 : goldenRatio ^ 2 + goldenRatio⁻¹ ^ 2 = 3 := by
    have hinv : goldenRatio⁻¹ = goldenRatio - 1 := by
      rw [inv_goldenRatio, ← one_sub_goldenConj]; ring
    rw [hinv]
    nlinarith [goldenRatio_sq]
  have h4 : goldenRatio ^ 4 + goldenRatio⁻¹ ^ 4 =
      (goldenRatio ^ 2 + goldenRatio⁻¹ ^ 2) ^ 2 - 2 * (goldenRatio * goldenRatio⁻¹) ^ 2 := by ring
  rw [h4, h2, hmul]
  norm_num

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
