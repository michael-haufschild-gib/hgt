import Mathlib.Tactic

/-!
# The terminal one-point projective boundary of a polynomial tuple

A finite nonzero tuple `H ∈ ℂ[z]^r` has a one-point upper projective boundary: writing
`d = max_j deg H_j`, the normalised translates

```text
w^{-d} (H_1(z + w), …, H_r(z + w))
```

converge, as `‖w‖ → ∞` and uniformly on every compact set of `z`, to the constant vector whose
`j`-th entry is the leading coefficient of `H_j` when `deg H_j = d` and `0` otherwise.  That vector
is nonzero.  This is the second arrow of the carrier chain `E(u) → ℂ[z] → ℂ`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Polynomial

/-- Along any filter on which `‖w‖ → ∞`, a negative pure power of `w` vanishes. -/
theorem tendsto_inv_pow_of_norm_atTop {ι : Type*} {l : Filter ι} {w : ι → ℂ}
    (hw : Tendsto (fun i => ‖w i‖) l atTop) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun i => ((w i) ^ m)⁻¹) l (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ i, ‖((w i) ^ m)⁻¹‖ = (‖w i‖ ^ m)⁻¹ := by
    intro i
    rw [norm_inv, norm_pow]
  simp only [hnorm]
  have hpow : Tendsto (fun i => ‖w i‖ ^ m) l atTop :=
    (tendsto_pow_atTop (by omega : m ≠ 0)).comp hw
  exact hpow.inv_tendsto_atTop

/-- **The projective limit of a polynomial.**  For `deg Q ≤ d`, the quotient `Q(w)/w^d` tends to the
`d`-th coefficient of `Q` as `‖w‖ → ∞`. -/
theorem tendsto_eval_div_pow {ι : Type*} {l : Filter ι} {w : ι → ℂ}
    (hw : Tendsto (fun i => ‖w i‖) l atTop) {Q : Polynomial ℂ} {d : ℕ} (hd : Q.natDegree ≤ d) :
    Tendsto (fun i => Q.eval (w i) / (w i) ^ d) l (nhds (Q.coeff d)) := by
  have hne : ∀ᶠ i in l, w i ≠ 0 := by
    filter_upwards [hw.eventually_gt_atTop 0] with i hi
    exact norm_pos_iff.mp hi
  -- the tail sum
  have hzero : Tendsto (fun i => ∑ k ∈ Finset.range d, Q.coeff k * ((w i) ^ (d - k))⁻¹) l
      (nhds 0) := by
    have : (0 : ℂ) = ∑ _k ∈ Finset.range d, (0 : ℂ) := by simp
    rw [this]
    refine tendsto_finset_sum _ fun k hk => ?_
    have hk' : 1 ≤ d - k := by
      rw [Finset.mem_range] at hk
      omega
    have := tendsto_inv_pow_of_norm_atTop hw hk'
    simpa using this.const_mul (Q.coeff k)
  have hconv := hzero.const_add (Q.coeff d)
  rw [add_zero] at hconv
  refine hconv.congr' ?_
  filter_upwards [hne] with i hi
  -- expand `Q` in the range `d + 1`
  have hsum : Q.eval (w i) = (∑ k ∈ Finset.range d, Q.coeff k * (w i) ^ k)
      + Q.coeff d * (w i) ^ d := by
    rw [Polynomial.eval_eq_sum_range' (n := d + 1) (by omega), Finset.sum_range_succ]
  have hpowne : (w i) ^ d ≠ 0 := pow_ne_zero _ hi
  rw [hsum, add_div, mul_div_assoc, div_self hpowne, mul_one, Finset.sum_div]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hsplit : (w i) ^ d = (w i) ^ k * (w i) ^ (d - k) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, mul_div_assoc]
  congr 1
  rw [div_mul_eq_div_div, div_self (pow_ne_zero _ hi), one_div]

/-- The shift of a polynomial keeps its degree and its top coefficient. -/
theorem coeff_comp_shift (P : Polynomial ℂ) (z : ℂ) {d : ℕ} (hd : P.natDegree ≤ d) :
    (P.comp (Polynomial.X + Polynomial.C z)).natDegree ≤ d ∧
      (P.comp (Polynomial.X + Polynomial.C z)).coeff d = P.coeff d := by
  have hq : (Polynomial.X + Polynomial.C z).natDegree = 1 := Polynomial.natDegree_X_add_C z
  have hdeg : (P.comp (Polynomial.X + Polynomial.C z)).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_comp, hq, mul_one]
  refine ⟨by rw [hdeg]; exact hd, ?_⟩
  rcases lt_or_eq_of_le hd with hlt | heq
  · have h1 : P.coeff d = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    have h2 : (P.comp (Polynomial.X + Polynomial.C z)).coeff d = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hlt)
    rw [h1, h2]
  · have hlead : (P.comp (Polynomial.X + Polynomial.C z)).leadingCoeff = P.leadingCoeff := by
      rw [Polynomial.leadingCoeff_comp (by rw [hq]; norm_num)]
      have : (Polynomial.X + Polynomial.C z).leadingCoeff = 1 := Polynomial.monic_X_add_C z
      rw [this, one_pow, mul_one]
    have h1 : (P.comp (Polynomial.X + Polynomial.C z)).coeff d
        = (P.comp (Polynomial.X + Polynomial.C z)).leadingCoeff := by
      rw [Polynomial.leadingCoeff, hdeg, heq]
    have h2 : P.coeff d = P.leadingCoeff := by rw [Polynomial.leadingCoeff, heq]
    rw [h1, h2, hlead]

/-- **The one-point terminal boundary, pointwise in `z`.** -/
theorem tendsto_translate_div_pow {ι : Type*} {l : Filter ι} {w : ι → ℂ}
    (hw : Tendsto (fun i => ‖w i‖) l atTop) {P : Polynomial ℂ} {d : ℕ} (hd : P.natDegree ≤ d)
    (z : ℂ) :
    Tendsto (fun i => P.eval (z + w i) / (w i) ^ d) l (nhds (P.coeff d)) := by
  obtain ⟨hdeg, hcoeff⟩ := coeff_comp_shift P z hd
  have hval : ∀ i, (P.comp (Polynomial.X + Polynomial.C z)).eval (w i) = P.eval (z + w i) := by
    intro i
    rw [Polynomial.eval_comp]
    simp [add_comm]
  have := tendsto_eval_div_pow hw hdeg
  rw [hcoeff] at this
  refine this.congr fun i => ?_
  rw [hval i]

/-- **The limit vector of a nonzero tuple is nonzero.**  With `d` the maximal degree, the entry at
an index realising the maximum is the leading coefficient there. -/
theorem coeff_top_ne_zero_of_natDegree_eq {P : Polynomial ℂ} (hP : P ≠ 0) {d : ℕ}
    (hd : P.natDegree = d) : P.coeff d ≠ 0 := by
  rw [← hd]
  exact Polynomial.leadingCoeff_ne_zero.mpr hP

/-- The pointwise estimate behind the uniform terminal boundary: for `‖z‖ ≤ Rad ≤ ‖w‖` and
`‖w‖ ≥ 1`, the normalised translate differs from the top coefficient by `O(1/‖w‖)`. -/
theorem norm_translate_div_pow_sub_coeff_le {P : Polynomial ℂ} {d : ℕ} (hd : P.natDegree ≤ d)
    {Rad : ℝ} {z w : ℂ} (hz : ‖z‖ ≤ Rad) (hw1 : 1 ≤ ‖w‖) (hwR : Rad ≤ ‖w‖) :
    ‖P.eval (z + w) / w ^ d - P.coeff d‖
      ≤ (2 ^ d * (∑ k ∈ Finset.range d, ‖P.coeff k‖)
          + ‖P.coeff d‖ * ((d : ℝ) * 2 ^ d * Rad)) / ‖w‖ := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw1
    linarith
  have hwpos : (0 : ℝ) < ‖w‖ := by linarith
  have hzw : ‖z + w‖ ≤ 2 * ‖w‖ := by
    calc ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le _ _
      _ ≤ Rad + ‖w‖ := by linarith
      _ ≤ 2 * ‖w‖ := by linarith
  have hsum : P.eval (z + w) = (∑ k ∈ Finset.range d, P.coeff k * (z + w) ^ k)
      + P.coeff d * (z + w) ^ d := by
    rw [Polynomial.eval_eq_sum_range' (n := d + 1) (by omega), Finset.sum_range_succ]
  have hdecomp : P.eval (z + w) / w ^ d - P.coeff d
      = (∑ k ∈ Finset.range d, P.coeff k * (z + w) ^ k) / w ^ d
        + P.coeff d * (((z + w) / w) ^ d - 1) := by
    rw [hsum, add_div, div_pow, mul_sub, mul_one, mul_div_assoc]
    ring
  have hpiece1 : ‖(∑ k ∈ Finset.range d, P.coeff k * (z + w) ^ k) / w ^ d‖
      ≤ 2 ^ d * (∑ k ∈ Finset.range d, ‖P.coeff k‖) / ‖w‖ := by
    rw [Finset.sum_div]
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [norm_div, norm_mul, norm_pow, norm_pow, div_le_div_iff₀ (by positivity) hwpos]
    have hzwk : ‖z + w‖ ^ k ≤ 2 ^ k * ‖w‖ ^ k := by
      calc ‖z + w‖ ^ k ≤ (2 * ‖w‖) ^ k := pow_le_pow_left₀ (norm_nonneg _) hzw k
        _ = 2 ^ k * ‖w‖ ^ k := by rw [mul_pow]
    have h2k : (2 : ℝ) ^ k ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) (le_of_lt hk)
    have hwk : ‖w‖ ^ k * ‖w‖ ≤ ‖w‖ ^ d := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hw1 (by omega)
    have hc : (0 : ℝ) ≤ ‖P.coeff k‖ := norm_nonneg _
    calc ‖P.coeff k‖ * ‖z + w‖ ^ k * ‖w‖
        ≤ ‖P.coeff k‖ * (2 ^ k * ‖w‖ ^ k) * ‖w‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzwk hc) hwpos.le
      _ = ‖P.coeff k‖ * 2 ^ k * (‖w‖ ^ k * ‖w‖) := by ring
      _ ≤ 2 ^ d * ‖P.coeff k‖ * ‖w‖ ^ d := by
          have h5 : ‖P.coeff k‖ * 2 ^ k ≤ 2 ^ d * ‖P.coeff k‖ := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right h2k hc
          exact mul_le_mul h5 hwk (by positivity) (by positivity)
  have hxsub : (z + w) / w - 1 = z / w := by
    field_simp
    ring
  have hxnorm : ‖(z + w) / w‖ ≤ 2 := by
    rw [norm_div, div_le_iff₀ hwpos]
    linarith
  have hgeom : ((z + w) / w) ^ d - 1
      = (∑ i ∈ Finset.range d, ((z + w) / w) ^ i) * ((z + w) / w - 1) := by
    rw [geom_sum_mul]
  have hpiece2 : ‖P.coeff d * (((z + w) / w) ^ d - 1)‖
      ≤ ‖P.coeff d‖ * ((d : ℝ) * 2 ^ d * Rad) / ‖w‖ := by
    rw [norm_mul, hgeom, norm_mul, hxsub, norm_div]
    have hgs : ‖∑ i ∈ Finset.range d, ((z + w) / w) ^ i‖ ≤ (d : ℝ) * 2 ^ d := by
      refine le_trans (norm_sum_le _ _) ?_
      have hb : ∀ i ∈ Finset.range d, ‖((z + w) / w) ^ i‖ ≤ (2 : ℝ) ^ d := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [norm_pow]
        calc ‖(z + w) / w‖ ^ i ≤ (2 : ℝ) ^ i := pow_le_pow_left₀ (norm_nonneg _) hxnorm i
          _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) (le_of_lt hi)
      calc ∑ i ∈ Finset.range d, ‖((z + w) / w) ^ i‖
          ≤ ∑ _i ∈ Finset.range d, (2 : ℝ) ^ d := Finset.sum_le_sum hb
        _ = (d : ℝ) * 2 ^ d := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hzn : ‖z‖ / ‖w‖ ≤ Rad / ‖w‖ := by gcongr
    calc ‖P.coeff d‖ * (‖∑ i ∈ Finset.range d, ((z + w) / w) ^ i‖ * (‖z‖ / ‖w‖))
        ≤ ‖P.coeff d‖ * (((d : ℝ) * 2 ^ d) * (Rad / ‖w‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hgs hzn (by positivity) (by positivity))
            (norm_nonneg _)
      _ = ‖P.coeff d‖ * ((d : ℝ) * 2 ^ d * Rad) / ‖w‖ := by ring
  rw [hdecomp]
  refine le_trans (norm_add_le _ _) ?_
  have hsplitrhs : (2 ^ d * (∑ k ∈ Finset.range d, ‖P.coeff k‖)
        + ‖P.coeff d‖ * ((d : ℝ) * 2 ^ d * Rad)) / ‖w‖
      = 2 ^ d * (∑ k ∈ Finset.range d, ‖P.coeff k‖) / ‖w‖
        + ‖P.coeff d‖ * ((d : ℝ) * 2 ^ d * Rad) / ‖w‖ := by ring
  rw [hsplitrhs]
  exact add_le_add hpiece1 hpiece2

/-- **The terminal one-point boundary of a polynomial.**  Uniformly on every closed ball, the
normalised translates converge to the constant `P.coeff d`. -/
theorem tendstoUniformlyOn_translate_div_pow {ι : Type*} {l : Filter ι} {w : ι → ℂ}
    (hw : Tendsto (fun i => ‖w i‖) l atTop) {P : Polynomial ℂ} {d : ℕ} (hd : P.natDegree ≤ d)
    (Rad : ℝ) :
    TendstoUniformlyOn (fun i z => P.eval (z + w i) / (w i) ^ d) (fun _ => P.coeff d) l
      (Metric.closedBall (0 : ℂ) Rad) := by
  set B : ℝ := 2 ^ d * (∑ k ∈ Finset.range d, ‖P.coeff k‖)
      + ‖P.coeff d‖ * ((d : ℝ) * 2 ^ d * max Rad 0) with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have h1 : (0 : ℝ) ≤ ∑ k ∈ Finset.range d, ‖P.coeff k‖ :=
      Finset.sum_nonneg fun k _ => norm_nonneg _
    have h2 : (0 : ℝ) ≤ max Rad 0 := le_max_right _ _
    positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hw.eventually_ge_atTop (max (max Rad 0) 1),
    hw.eventually_gt_atTop (B / ε)] with i hi hiB
  intro z hz
  have hzn : ‖z‖ ≤ max Rad 0 := by
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact le_trans hz (le_max_left _ _)
  have hw1 : 1 ≤ ‖w i‖ := le_trans (le_max_right _ _) hi
  have hwR : max Rad 0 ≤ ‖w i‖ := le_trans (le_max_left _ _) hi
  have hwpos : (0 : ℝ) < ‖w i‖ := by linarith
  have hest := norm_translate_div_pow_sub_coeff_le hd hzn hw1 hwR
  rw [Complex.dist_eq]
  have hlt : B / ‖w i‖ < ε := by
    rw [div_lt_iff₀ hwpos]
    rw [div_lt_iff₀ hε] at hiB
    linarith
  calc ‖P.coeff d - P.eval (z + w i) / (w i) ^ d‖
      = ‖P.eval (z + w i) / (w i) ^ d - P.coeff d‖ := by rw [norm_sub_rev]
    _ ≤ B / ‖w i‖ := hest
    _ < ε := hlt

end GaloisForLFunctions.HTGeometry
