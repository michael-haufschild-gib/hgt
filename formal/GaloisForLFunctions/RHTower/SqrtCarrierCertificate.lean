import GaloisForLFunctions.RHTower.MFreeLadder

/-!
# Finite-cutoff certificate for the ζ(2z)⁻¹ carrier

The square-dilated Möbius carrier converges to `ζ(2z)⁻¹` on `re z > 1/2`; this file makes
the convergence effective, so the limit becomes a finite-cutoff certificate usable by the
off-line floor machinery of `DpolyOffline`.

* `RHTower.dpoly2_sqrtMoebiusCoeff_eq_moebius_sqrt` — the finite dilation identity: the
  square-dilated carrier at `z` with cutoff `N` *is* the Möbius carrier at `2z` with cutoff
  `√N`.  The analytic dilation law holds already at every finite level.
* `RHTower.sum_range_add_rpow_neg_le` / `RHTower.tsum_add_rpow_neg_le` — the integral-test
  tail bound `∑_{k > M} k^(-c) ≤ M^(1-c)/(c-1)` for `c > 1`, `M ≥ 1`.
* `RHTower.norm_LSeries_sub_dpoly2_le` — the effective truncation certificate for **any**
  mollifier-grade coefficient sequence (`|a n| ≤ 1`): on `re w > 1`,
  `‖L(a, w) − dpoly2 a (Icc 1 M) w‖ ≤ M^(1-re w)/(re w - 1)`.
* `RHTower.norm_inv_riemannZeta_sub_dpoly2_moebiusCoeff_le` — the Möbius instance: the
  mollifier coefficients approximate `ζ(w)⁻¹` with explicit error.
* `RHTower.sqrtCarrier_certificate` / `RHTower.sqrtCarrier_certificate_uniform` — the
  square-dilated instance: for `re z ≥ 1/2 + δ`,
  `‖ζ(2z)⁻¹ − dpoly2 sqrtMoebiusCoeff (Icc 1 N) z‖ ≤ (√N)^(-2δ)/(2δ)`, uniform in `z` on
  the shifted half-plane.
* `RHTower.sqrtCarrier_floor_of_inv_zeta_floor` — the floor transfer: a floor for
  `ζ(2z)⁻¹` exceeding the certificate radius forces the same floor (minus the radius) on
  the finite carrier — exactly the `hline` premise consumed by `dpoly2_chart_floor` and
  `chart_floor_cofinal_of_line_cofinal`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction LSeries Complex Filter
open scoped LSeries.notation Moebius ArithmeticFunction.zeta

/-! ## Integral-test tail bound for p-series -/

theorem antitoneOn_rpow_neg {c : ℝ} (hc : 0 < c) {K : ℝ} (hK : 0 < K) (n : ℕ) :
    AntitoneOn (fun x : ℝ => x ^ (-c)) (Set.Icc K (K + n)) := fun _ hx _ _ hxy =>
  Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hK hx.1) hxy (neg_nonpos.mpr hc.le)

/-- Partial integral-test bound: `∑_{i<n} (M+1+i)^(-c) ≤ M^(1-c)/(c-1)` for `c > 1`,
`M ≥ 1`. -/
theorem sum_range_add_rpow_neg_le {c : ℝ} (hc : 1 < c) {M : ℕ} (hM : 1 ≤ M) (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i + (M + 1) : ℕ) : ℝ) ^ (-c) ≤ (M : ℝ) ^ (1 - c) / (c - 1) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hint : ∫ x in (M : ℝ)..((M : ℝ) + n), x ^ (-c)
      = ((M : ℝ) ^ (1 - c) - ((M : ℝ) + n) ^ (1 - c)) / (c - 1) := by
    rw [integral_rpow (Or.inr ⟨fun h => by linarith [neg_eq_iff_eq_neg.mp h], fun h => by
      rcases Set.mem_uIcc.mp h with ⟨h1, _⟩ | ⟨_, h2⟩ <;>
        nlinarith [Nat.cast_nonneg (α := ℝ) n]⟩)]
    have he : -c + 1 = 1 - c := by ring
    rw [he, show (1 : ℝ) - c = -(c - 1) by ring, div_neg, ← neg_div, neg_sub]
  calc ∑ i ∈ Finset.range n, ((i + (M + 1) : ℕ) : ℝ) ^ (-c)
      ≤ ∫ x in (M : ℝ)..((M : ℝ) + n), x ^ (-c) := by
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
          ((antitoneOn_rpow_neg (by linarith) hM0 n).sum_le_integral)
        congr 1
        push_cast
        ring
    _ = ((M : ℝ) ^ (1 - c) - ((M : ℝ) + n) ^ (1 - c)) / (c - 1) := hint
    _ ≤ (M : ℝ) ^ (1 - c) / (c - 1) := by
        have hnum : (M : ℝ) ^ (1 - c) - ((M : ℝ) + n) ^ (1 - c) ≤ (M : ℝ) ^ (1 - c) :=
          sub_le_self _ (Real.rpow_nonneg (by positivity) _)
        have hden : (0 : ℝ) < c - 1 := by linarith
        gcongr

/-- Tail integral-test bound: `∑_{k > M} k^(-c) ≤ M^(1-c)/(c-1)` for `c > 1`, `M ≥ 1`. -/
theorem tsum_add_rpow_neg_le {c : ℝ} (hc : 1 < c) {M : ℕ} (hM : 1 ≤ M) :
    ∑' i : ℕ, ((i + (M + 1) : ℕ) : ℝ) ^ (-c) ≤ (M : ℝ) ^ (1 - c) / (c - 1) :=
  Real.tsum_le_of_sum_range_le (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (sum_range_add_rpow_neg_le hc hM)

/-! ## The effective truncation certificate for mollifier-grade coefficients -/

set_option maxHeartbeats 1600000 in
/-- **Effective truncation certificate.**  For any coefficient sequence bounded by `1`
(mollifier grade), the off-line carrier polynomial approximates the L-series value with
the explicit integral-test error: on `re w > 1`,
`‖L(a, w) − dpoly2 a (Icc 1 M) w‖ ≤ M^(1-re w)/(re w - 1)`. -/
theorem norm_LSeries_sub_dpoly2_le {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1) {w : ℂ}
    (hw : 1 < w.re) {M : ℕ} (hM : 1 ≤ M) :
    ‖LSeries (fun n => (a n : ℂ)) w - dpoly2 a (Finset.Icc 1 M) w‖
      ≤ (M : ℝ) ^ (1 - w.re) / (w.re - 1) := by
  have hsum : LSeriesSummable (fun n => (a n : ℂ)) w :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n _ => by rw [Complex.norm_real, Real.norm_eq_abs]; exact ha n) hw
  have hsplit := Summable.sum_add_tsum_nat_add (M + 1) hsum
  have htail : LSeries (fun n => (a n : ℂ)) w - dpoly2 a (Finset.Icc 1 M) w
      = ∑' i, term (fun n => (a n : ℂ)) w (i + (M + 1)) := by
    rw [dpoly2_Icc_eq_sum_range_term]
    unfold LSeries
    linear_combination -hsplit
  rw [htail]
  have hnormsum : Summable (fun i => ‖term (fun n => (a n : ℂ)) w (i + (M + 1))‖) :=
    (summable_nat_add_iff (M + 1)).mpr (summable_norm_iff.mpr hsum)
  refine le_trans (norm_tsum_le_tsum_norm hnormsum) ?_
  refine Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _) fun n => ?_
  calc ∑ i ∈ Finset.range n, ‖term (fun k => (a k : ℂ)) w (i + (M + 1))‖
      ≤ ∑ i ∈ Finset.range n, ((i + (M + 1) : ℕ) : ℝ) ^ (-w.re) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hi0 : i + (M + 1) ≠ 0 := by omega
        rw [term_of_ne_zero hi0, norm_div,
          Complex.norm_natCast_cpow_of_pos (by omega),
          Real.rpow_neg (Nat.cast_nonneg _), ← one_div]
        have hb : ‖(a (i + (M + 1)) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact ha _
        have hpos : (0 : ℝ) < ((i + (M + 1) : ℕ) : ℝ) ^ w.re :=
          Real.rpow_pos_of_pos (by positivity) _
        gcongr
    _ ≤ (M : ℝ) ^ (1 - w.re) / (w.re - 1) := sum_range_add_rpow_neg_le hw hM n

/-- The Möbius instance: the mollifier coefficients approximate `ζ(w)⁻¹` with explicit
integral-test error on `re w > 1`. -/
theorem norm_inv_riemannZeta_sub_dpoly2_moebiusCoeff_le {w : ℂ} (hw : 1 < w.re) {M : ℕ}
    (hM : 1 ≤ M) :
    ‖(riemannZeta w)⁻¹ - dpoly2 moebiusCoeff (Finset.Icc 1 M) w‖
      ≤ (M : ℝ) ^ (1 - w.re) / (w.re - 1) := by
  have h := norm_LSeries_sub_dpoly2_le (a := moebiusCoeff)
    (fun n => abs_moebiusCoeff_le_one n) hw hM
  rwa [show (fun n => ((moebiusCoeff n : ℝ) : ℂ)) = ↗μ from funext moebiusCoeff_complex,
    LSeries_moebius_eq_inv_riemannZeta hw] at h

/-! ## The finite dilation identity -/

/-- **Finite dilation identity.**  The square-dilated carrier at `z` with cutoff `N` *is*
the Möbius carrier at `2z` with cutoff `√N`: the dilation law `L(sqrtPart μ, s) = L(μ, 2s)`
holds already at every finite level. -/
theorem dpoly2_sqrtMoebiusCoeff_eq_moebius_sqrt (N : ℕ) (z : ℂ) :
    dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) z
      = dpoly2 moebiusCoeff (Finset.Icc 1 (Nat.sqrt N)) (2 * z) := by
  rw [dpoly2, dpoly2,
    ← Finset.sum_filter_of_ne (p := fun n => n.sqrt * n.sqrt = n) (fun x _ hx => ?_)]
  · refine Finset.sum_nbij' (fun n => n.sqrt) (fun k => k * k) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      obtain ⟨hn1, hnsq⟩ := Finset.mem_filter.mp hn
      obtain ⟨h1n, hnN⟩ := Finset.mem_Icc.mp hn1
      refine Finset.mem_Icc.mpr ⟨Nat.le_sqrt.mpr (by omega), Nat.sqrt_le_sqrt hnN⟩
    · intro k hk
      obtain ⟨h1k, hkN⟩ := Finset.mem_Icc.mp hk
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), Nat.le_sqrt.mp hkN⟩, ?_⟩
      show (k * k).sqrt * (k * k).sqrt = k * k
      rw [Nat.sqrt_eq]
    · intro n hn
      exact (Finset.mem_filter.mp hn).2
    · intro k _
      show (k * k).sqrt = k
      exact Nat.sqrt_eq k
    · intro n hn
      obtain ⟨-, hnsq⟩ := Finset.mem_filter.mp hn
      conv_lhs => rw [← hnsq]
      have hcoeff : sqrtMoebiusCoeff (n.sqrt * n.sqrt) = moebiusCoeff n.sqrt := by
        rw [sqrtMoebiusCoeff, sqrtPart_apply_mul_self, moebiusCoeff]
      have hpow : ((n.sqrt * n.sqrt : ℕ) : ℂ) ^ (-z) = ((n.sqrt : ℕ) : ℂ) ^ (-(2 * z)) := by
        rw [show n.sqrt * n.sqrt = n.sqrt ^ 2 from (pow_two n.sqrt).symm,
          natCast_sq_cpow, mul_neg]
      rw [hcoeff, hpow]
  · by_contra hpx
    refine hx ?_
    have hzero : sqrtMoebiusCoeff x = 0 := by
      rw [sqrtMoebiusCoeff, sqrtPart_apply_of_not_isSquare]
      · norm_num
      · rintro ⟨r, hr⟩
        refine hpx ?_
        show x.sqrt * x.sqrt = x
        rw [hr, Nat.sqrt_eq]
    rw [hzero]
    norm_num

/-! ## The finite-cutoff certificate for the ζ(2z)⁻¹ carrier -/

private theorem two_mul_re' (z : ℂ) : (2 * z).re = 2 * z.re := by
  simp [Complex.mul_re]

/-- **Finite-cutoff certificate, exact-rate form.**  On `re z > 1/2`, the square-dilated
carrier at cutoff `N` approximates `ζ(2z)⁻¹` with the explicit error
`(√N)^(1-2·re z)/(2·re z - 1)`. -/
theorem sqrtCarrier_certificate {z : ℂ} (hz : 1 / 2 < z.re) {N : ℕ}
    (hN : 1 ≤ Nat.sqrt N) :
    ‖(riemannZeta (2 * z))⁻¹ - dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) z‖
      ≤ (Nat.sqrt N : ℝ) ^ (1 - 2 * z.re) / (2 * z.re - 1) := by
  have h2 : 1 < (2 * z).re := by rw [two_mul_re']; linarith
  have h := norm_inv_riemannZeta_sub_dpoly2_moebiusCoeff_le h2 hN
  rw [two_mul_re'] at h
  rwa [dpoly2_sqrtMoebiusCoeff_eq_moebius_sqrt]

/-- **Finite-cutoff certificate, uniform form.**  On the shifted half-plane
`re z ≥ 1/2 + δ`, the error is bounded by `(√N)^(-2δ)/(2δ)`, uniformly in `z` — the
height-independent certificate radius the chart-floor machinery consumes. -/
theorem sqrtCarrier_certificate_uniform {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : 1 / 2 + ε ≤ z.re) {N : ℕ} (hN : 1 ≤ Nat.sqrt N) :
    ‖(riemannZeta (2 * z))⁻¹ - dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) z‖
      ≤ (Nat.sqrt N : ℝ) ^ (-(2 * ε)) / (2 * ε) := by
  refine le_trans (sqrtCarrier_certificate (by linarith) hN) ?_
  have hbase : (1 : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast hN
  have hnum : (Nat.sqrt N : ℝ) ^ (1 - 2 * z.re) ≤ (Nat.sqrt N : ℝ) ^ (-(2 * ε)) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hden : 2 * ε ≤ 2 * z.re - 1 := by linarith
  have hε2 : (0 : ℝ) < 2 * ε := by linarith
  exact div_le_div₀ (Real.rpow_nonneg (by positivity) _) hnum hε2 hden

/-- **Floor transfer into the chart machinery.**  A floor for `ζ(2z)⁻¹` exceeding
`t₀ + (√N)^(-2δ)/(2δ)` forces the floor `t₀` on the finite square-dilated carrier — this
is the `hline` premise of `dpoly2_chart_floor` and `chart_floor_cofinal_of_line_cofinal`,
so an off-line `ζ(2·)⁻¹` floor now transports through the certificate to the chart
floors of `DpolyOffline`. -/
theorem sqrtCarrier_floor_of_inv_zeta_floor {ε t₀ : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : 1 / 2 + ε ≤ z.re) {N : ℕ} (hN : 1 ≤ Nat.sqrt N)
    (hfloor : t₀ + (Nat.sqrt N : ℝ) ^ (-(2 * ε)) / (2 * ε) < ‖(riemannZeta (2 * z))⁻¹‖) :
    t₀ < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) z‖ := by
  have hcert := sqrtCarrier_certificate_uniform hε hz hN
  have htri : ‖(riemannZeta (2 * z))⁻¹‖ - ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) z‖
      ≤ ‖(riemannZeta (2 * z))⁻¹ - dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) z‖ :=
    norm_sub_norm_le _ _
  linarith

end RHTower
