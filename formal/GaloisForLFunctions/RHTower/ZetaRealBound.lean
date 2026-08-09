import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# A uniform bound for zeta on a right half plane

On `Re s ≥ a > 1` the Dirichlet series of `ζ` is dominated termwise by the series at the real
abscissa `a`, so `‖ζ(s)‖` is bounded there by a single constant.  This is the summability input for
interchanging a power series in `ξ` with the Dirichlet series of `ζ(1+sk)`: the zeta factors are
uniformly bounded in `k`, so the double family is dominated by a geometric series.

* `GaloisForLFunctions.RHTower.summable_one_div_nat_add_one_rpow`;
* `GaloisForLFunctions.RHTower.norm_riemannZeta_le_tsum`;
* `GaloisForLFunctions.RHTower.summable_uncurry_geometric_zeta`;
* `GaloisForLFunctions.RHTower.tsum_mul_riemannZeta_eq_tsum_comm`.
-/

open Complex

namespace GaloisForLFunctions.RHTower

/-- The shifted `p`-series converges above the abscissa one. -/
theorem summable_one_div_nat_add_one_rpow {a : ℝ} (ha : 1 < a) :
    Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ a := by
  have hbase : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ a :=
    Real.summable_one_div_nat_rpow.2 ha
  have hshift : Summable fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ a :=
    (summable_nat_add_iff 1).2 hbase
  refine hshift.congr fun n => ?_
  push_cast
  ring_nf

/-- **A uniform bound for zeta above a real abscissa.**  For `1 < a ≤ Re s` the norm of `ζ(s)` is at
most the value of the `a`-series, a constant independent of `s`. -/
theorem norm_riemannZeta_le_tsum {a : ℝ} (ha : 1 < a) {s : ℂ} (hs : a ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ a := by
  have hs1 : 1 < s.re := lt_of_lt_of_le ha hs
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow hs1
  have hnormterm : ∀ n : ℕ, ‖(1 : ℂ) / ((n : ℂ) + 1) ^ s‖ = (1 : ℝ) / ((n : ℝ) + 1) ^ s.re := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [norm_div, norm_one, hcast, norm_cpow_eq_rpow_re_of_pos hpos]
  have hbound : ∀ n : ℕ, ‖(1 : ℂ) / ((n : ℂ) + 1) ^ s‖ ≤ (1 : ℝ) / ((n : ℝ) + 1) ^ a := by
    intro n
    rw [hnormterm n]
    have hone : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hmono : ((n : ℝ) + 1) ^ a ≤ ((n : ℝ) + 1) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hone hs
    have hpa : (0 : ℝ) < ((n : ℝ) + 1) ^ a := Real.rpow_pos_of_pos (by linarith) a
    exact one_div_le_one_div_of_le hpa hmono
  have hsummable : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ a :=
    summable_one_div_nat_add_one_rpow ha
  have hnormsummable : Summable fun n : ℕ => ‖(1 : ℂ) / ((n : ℂ) + 1) ^ s‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hsummable
  calc ‖riemannZeta s‖ = ‖∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ s‖ := by rw [hzeta]
    _ ≤ ∑' n : ℕ, ‖(1 : ℂ) / ((n : ℂ) + 1) ^ s‖ := norm_tsum_le_tsum_norm hnormsummable
    _ ≤ ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ a :=
        Summable.tsum_le_tsum hbound hnormsummable hsummable

/-- The double family of a geometrically small coefficient against a Dirichlet term is summable,
uniformly in the exponent as long as its real part stays above a fixed abscissa. -/
theorem summable_uncurry_geometric_zeta {a : ℝ} (ha : 1 < a) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {c : ℕ → ℂ} (hc : ∀ k, ‖c k‖ ≤ r ^ k) {e : ℕ → ℂ} (he : ∀ k, a ≤ (e k).re) :
    Summable (Function.uncurry fun k n : ℕ => c k / ((n : ℂ) + 1) ^ (e k)) := by
  have hgeo : Summable fun k : ℕ => r ^ k := summable_geometric_of_lt_one hr0 hr1
  have hzeta : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ a :=
    summable_one_div_nat_add_one_rpow ha
  have hprod : Summable fun p : ℕ × ℕ => r ^ p.1 * ((1 : ℝ) / ((p.2 : ℝ) + 1) ^ a) := by
    refine hgeo.mul_of_nonneg hzeta (fun k => pow_nonneg hr0 k) (fun n => ?_)
    have : (0 : ℝ) < ((n : ℝ) + 1) ^ a := Real.rpow_pos_of_pos (by positivity) a
    positivity
  refine Summable.of_norm_bounded hprod fun p => ?_
  obtain ⟨k, n⟩ := p
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have hnorm : ‖c k / ((n : ℂ) + 1) ^ (e k)‖ = ‖c k‖ / ((n : ℝ) + 1) ^ (e k).re := by
    rw [norm_div, hcast, norm_cpow_eq_rpow_re_of_pos hpos]
  have hone : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hmono : ((n : ℝ) + 1) ^ a ≤ ((n : ℝ) + 1) ^ (e k).re :=
    Real.rpow_le_rpow_of_exponent_le hone (he k)
  have hpa : (0 : ℝ) < ((n : ℝ) + 1) ^ a := Real.rpow_pos_of_pos hpos a
  have hdiv : ‖c k‖ / ((n : ℝ) + 1) ^ (e k).re ≤ r ^ k * ((1 : ℝ) / ((n : ℝ) + 1) ^ a) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_of_le (hc k) (norm_nonneg _) hpa hmono
  simpa [Function.uncurry, hnorm] using hdiv

/-- **The interchange behind the Lambert form.**  A power series in geometrically small
coefficients against values of `ζ` above a fixed abscissa may be summed in the other order, term by
term against the Dirichlet series. -/
theorem tsum_mul_riemannZeta_eq_tsum_comm {a : ℝ} (ha : 1 < a) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {c : ℕ → ℂ} (hc : ∀ k, ‖c k‖ ≤ r ^ k) {e : ℕ → ℂ} (he : ∀ k, a ≤ (e k).re) :
    ∑' k : ℕ, c k * riemannZeta (e k)
      = ∑' n : ℕ, ∑' k : ℕ, c k / ((n : ℂ) + 1) ^ (e k) := by
  have hsum := summable_uncurry_geometric_zeta ha hr0 hr1 hc he
  have hcomm := hsum.tsum_comm
  rw [← hcomm]
  refine tsum_congr fun k => ?_
  have hre : 1 < (e k).re := lt_of_lt_of_le ha (he k)
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow hre
  have hfun : (fun n : ℕ => c k / ((n : ℂ) + 1) ^ (e k))
      = fun n : ℕ => c k * ((1 : ℂ) / ((n : ℂ) + 1) ^ (e k)) := by
    funext n
    rw [mul_one_div]
  rw [hfun, tsum_mul_left, ← hz]

end GaloisForLFunctions.RHTower
