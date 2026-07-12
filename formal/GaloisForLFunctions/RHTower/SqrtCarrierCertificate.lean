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

/-! ## The elementary zeta bound and the certified chart floor -/

/-- **The elementary zeta bound.**  Termwise triangle inequality plus the integral-test
tail: on `re w ≥ 1 + ε'`, `‖ζ(w)‖ ≤ 1 + 1/ε'`. -/
theorem norm_riemannZeta_le {ε' : ℝ} (hε' : 0 < ε') {w : ℂ} (hw : 1 + ε' ≤ w.re) :
    ‖riemannZeta w‖ ≤ 1 + 1 / ε' := by
  have hw1 : 1 < w.re := by linarith
  have hre0 : w.re ≠ 0 := by linarith
  have hmaj : Summable (fun n : ℕ => 1 / (n : ℝ) ^ w.re) :=
    Real.summable_one_div_nat_rpow.mpr hw1
  have hterm : ∀ n : ℕ, ‖1 / (n : ℂ) ^ w‖ = 1 / (n : ℝ) ^ w.re := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.cast_zero, Complex.zero_cpow
          (fun h => by rw [h] at hw1; simp at hw1; exact absurd hw1 (by norm_num)),
        div_zero, norm_zero, Nat.cast_zero, Real.zero_rpow hre0, div_zero]
    · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn]
  have hnorm : Summable (fun n : ℕ => ‖1 / (n : ℂ) ^ w‖) :=
    (summable_congr fun n => hterm n).mpr hmaj
  rw [zeta_eq_tsum_one_div_nat_cpow hw1]
  refine le_trans (norm_tsum_le_tsum_norm hnorm) ?_
  rw [tsum_congr hterm]
  have hsplit := Summable.sum_add_tsum_nat_add 2 hmaj
  have h01 : ∑ i ∈ Finset.range 2, 1 / ((i : ℕ) : ℝ) ^ w.re = 1 := by
    simp [Finset.sum_range_succ, Real.zero_rpow hre0]
  have htail : ∑' i : ℕ, 1 / ((i + 2 : ℕ) : ℝ) ^ w.re ≤ 1 / (w.re - 1) := by
    have hb := tsum_add_rpow_neg_le hw1 (M := 1) le_rfl
    rw [Nat.cast_one, Real.one_rpow] at hb
    refine le_trans (le_of_eq (tsum_congr fun i => ?_)) hb
    rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
  have h1ε : 1 / (w.re - 1) ≤ 1 / ε' := by
    gcongr
    linarith
  rw [← hsplit, h01]
  linarith

/-- **Inverse-zeta floor.**  On `re w ≥ 1 + ε'` the reciprocal zeta value has the
explicit floor `ε'/(1+ε')`. -/
theorem inv_zeta_floor {ε' : ℝ} (hε' : 0 < ε') {w : ℂ} (hw : 1 + ε' ≤ w.re) :
    ε' / (1 + ε') ≤ ‖(riemannZeta w)⁻¹‖ := by
  have hw1 : 1 < w.re := by linarith
  have hpos : 0 < ‖riemannZeta w‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hw1)
  rw [norm_inv]
  refine le_trans (le_of_eq ?_) (inv_anti₀ hpos (norm_riemannZeta_le hε' hw))
  rw [eq_comm, inv_eq_iff_eq_inv, eq_comm, inv_div]
  field_simp
  ring

/-- **Certified chart floor, parametric.**  A purely numeric gap condition in
`(ε, N, t₀)` — the certificate radius plus `t₀` below the elementary inverse-zeta floor —
forces the explicit floor `t₀` on the finite square-dilated carrier, everywhere on the
half-plane `re z ≥ 1/2 + ε`.  No unproved input remains. -/
theorem sqrtCarrier_certified_floor {ε t₀ : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : 1 / 2 + ε ≤ z.re) {N : ℕ} (hN : 1 ≤ Nat.sqrt N)
    (hgap : t₀ + (Nat.sqrt N : ℝ) ^ (-(2 * ε)) / (2 * ε) < 2 * ε / (1 + 2 * ε)) :
    t₀ < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) z‖ := by
  refine sqrtCarrier_floor_of_inv_zeta_floor hε hz hN (lt_of_lt_of_le hgap ?_)
  refine inv_zeta_floor (by linarith : (0 : ℝ) < 2 * ε) ?_
  rw [two_mul_re']
  linarith

/-- **The first certified chart floor** (numeric witness): on the half-plane `re z ≥ 1`,
the cutoff-`16` square-dilated carrier is bounded below by `1/8`, unconditionally. -/
theorem sqrtCarrier_floor_witness {z : ℂ} (hz : 1 ≤ z.re) :
    (1 / 8 : ℝ) < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 16) z‖ := by
  have hsqrt : Nat.sqrt 16 = 4 := by
    rw [show (16 : ℕ) = 4 ^ 2 by norm_num, Nat.sqrt_eq']
  refine sqrtCarrier_certified_floor (ε := 1 / 2) (by norm_num) (by linarith) ?_ ?_
  · rw [hsqrt]
    norm_num
  · rw [hsqrt, show -(2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
    norm_num

/-! ## Certified rpow bracketing and the strip witness -/

/-- **Certified rpow bracketing.**  The transcendental bound `x^(-(a/b)) ≤ r` reduces to
the pure-power certificate `1 ≤ r^b · x^a`, checkable by `norm_num` — the brick that lets
the certified floor emit numeric witnesses at any rational `ε`, not only where the rpow
exponent is an integer. -/
theorem rpow_neg_div_le_of_one_le_pow {x r : ℝ} (hx : 1 ≤ x) (hr : 0 < r) {a b : ℕ}
    (hb : b ≠ 0) (h : 1 ≤ r ^ b * x ^ a) : x ^ (-((a : ℝ) / (b : ℝ))) ≤ r := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hxq : (0 : ℝ) < x ^ ((a : ℝ) / (b : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have key : 1 / r ≤ x ^ ((a : ℝ) / (b : ℝ)) := by
    have hxab : (x ^ ((a : ℝ) / (b : ℝ))) ^ b = x ^ (a : ℕ) := by
      rw [← Real.rpow_natCast (x ^ ((a : ℝ) / (b : ℝ))) b, ← Real.rpow_mul hx0.le,
        div_mul_cancel₀ _ (by exact_mod_cast hb : ((b : ℕ) : ℝ) ≠ 0), Real.rpow_natCast]
    have hpow : (1 / r) ^ b ≤ (x ^ ((a : ℝ) / (b : ℝ))) ^ b := by
      rw [hxab, div_pow, one_pow, div_le_iff₀ (by positivity)]
      calc (1 : ℝ) ≤ r ^ b * x ^ a := h
        _ = x ^ a * r ^ b := mul_comm _ _
    exact le_of_pow_le_pow_left₀ hb hxq.le hpow
  calc x ^ (-((a : ℝ) / (b : ℝ))) = (x ^ ((a : ℝ) / (b : ℝ)))⁻¹ := Real.rpow_neg hx0.le _
    _ ≤ (1 / r)⁻¹ := inv_anti₀ (by positivity) key
    _ = r := by rw [one_div, inv_inv]

/-- **Lower bracketing** — the two-sided companion: `r ≤ x^(-(a/b))` from the pure-power
certificate `r^b · x^a ≤ 1`.  Together with the upper bracket this pins any rpow value
between rationals by `norm_num`-checkable power inequalities. -/
theorem le_rpow_neg_div_of_pow_le_one {x r : ℝ} (hx : 1 ≤ x) {a b : ℕ}
    (hb : b ≠ 0) (h : r ^ b * x ^ a ≤ 1) : r ≤ x ^ (-((a : ℝ) / (b : ℝ))) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hxq : (0 : ℝ) < x ^ ((a : ℝ) / (b : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hxab : (x ^ ((a : ℝ) / (b : ℝ))) ^ b = x ^ (a : ℕ) := by
    rw [← Real.rpow_natCast (x ^ ((a : ℝ) / (b : ℝ))) b, ← Real.rpow_mul hx0.le,
      div_mul_cancel₀ _ (by exact_mod_cast hb : ((b : ℕ) : ℝ) ≠ 0), Real.rpow_natCast]
  have hpow : r ^ b ≤ ((x ^ ((a : ℝ) / (b : ℝ)))⁻¹) ^ b := by
    rw [inv_pow, hxab, ← one_div, le_div_iff₀ (by positivity)]
    exact h
  have hle := le_of_pow_le_pow_left₀ hb (by positivity) hpow
  rwa [Real.rpow_neg hx0.le]

/-- Certified-radius form of the chart floor: any bracketing bound `r` for the rpow
radius may replace it in the gap condition. -/
theorem sqrtCarrier_certified_floor_of_le {ε t₀ r : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : 1 / 2 + ε ≤ z.re) {N : ℕ} (hN : 1 ≤ Nat.sqrt N)
    (hr : (Nat.sqrt N : ℝ) ^ (-(2 * ε)) ≤ r)
    (hgap : t₀ + r / (2 * ε) < 2 * ε / (1 + 2 * ε)) :
    t₀ < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) z‖ := by
  refine sqrtCarrier_certified_floor hε hz hN (lt_of_le_of_lt ?_ hgap)
  have h2ε : (0 : ℝ) < 2 * ε := by linarith
  have hdiv : (Nat.sqrt N : ℝ) ^ (-(2 * ε)) / (2 * ε) ≤ r / (2 * ε) :=
    div_le_div₀ (le_trans (Real.rpow_nonneg (by positivity) _) hr) hr h2ε le_rfl
  linarith

/-- **Strip-adjacent certified floor witness**: at `ε = 1/4`, on the half-plane
`re z ≥ 3/4`, the cutoff-`10000` square-dilated carrier has the certified floor `1/10`.
The rpow radius is certified by the pure-power bracketing `(1/10)² · 100 = 1`. -/
theorem sqrtCarrier_floor_witness_strip {z : ℂ} (hz : 3 / 4 ≤ z.re) :
    (1 / 10 : ℝ) < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 10000) z‖ := by
  have hsqrt : Nat.sqrt 10000 = 100 := by
    rw [show (10000 : ℕ) = 100 ^ 2 by norm_num, Nat.sqrt_eq']
  refine sqrtCarrier_certified_floor_of_le (ε := 1 / 4) (r := 1 / 10) (by norm_num)
    (by linarith) ?_ ?_ ?_
  · rw [hsqrt]
    norm_num
  · rw [hsqrt, show -(2 * (1 / 4 : ℝ)) = -(((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) by norm_num]
    refine rpow_neg_div_le_of_one_le_pow (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num
  · norm_num

end RHTower
