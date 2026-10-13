import GaloisForLFunctions.RHTower.ZetaTypicalLocalZeroCount

/-!
# Critical-scale zero clusters are rare at every scale at once

`ZetaTypicalLocalZeroCount` bounds the local zero count at ONE scale `R` from typical
log-derivative box data, and shows that clusters larger than `10 R log T` occupy an exponentially
small set of heights. This module makes the bound uniform in the scale.

**Theorem** (`exists_volume_multiscale_localZeroCount_gt_le`).  There are `C` and `κ₂` such that,
for all large `T` and every `0 < R₀ ≤ 1/16` with `R₀ log T ≥ κ₂`, the set of heights `t ∈ [T, 2T]`
at which SOME scale `u ∈ [R₀, 1/16]` carries more than `20 u log T` zero copies with ordinates
within `u` of `t` has measure at most `12 C T e^{−R₀ log T/120000} + C T^{3/4}`.

So outside an exponentially small set of heights the local counts are regular down to the critical
scale: `n_t(u) ≤ 20 u log T` for every `u ∈ [R₀, 1/16]`, hence `n_t(u) ≤ 20 R₀ log T + 20 u log T`
for every `u ≤ 1/16`. With `R₀ = κ/log T` the additive constant `a = 20κ` is bounded, which is the
"regular local counting" hypothesis of linear-scale off-line detection in the slice-heat lane.

**Proof.**  Use box data at the dyadic scales `2^j R₀ ≤ 1/16` and at `1/16`. For `u ∈ [R₀, 1/16]`
the least dyadic scale `R ≥ u` (or `1/16`) satisfies `R ≤ 2u`, so the single-scale count
`≤ 10 R log T` (`card_le_ten_mul_of_zetaLogDerivScaleData_half`) gives `≤ 20 u log T`. The
exceptional sets are bounded scale by scale
(`exists_volume_not_zetaLogDerivScaleData_half_le`). Their exponential parts sum geometrically
(`sum_exp_neg_two_pow_mul_le`), and the `≤ log T + 1` scales cost `C(log T + 2)√T ≤ CT^{3/4}`.
-/

open MeasureTheory Set Filter GaloisForLFunctions

namespace RHTower

noncomputable section

/-- `x² e^{−x/16} ≤ e^{−x/120000}` for `x ≥ 48000`. -/
theorem sq_mul_exp_neg_div_sixteen_le {x : ℝ} (hx : 48000 ≤ x) :
    x ^ 2 * Real.exp (-(x / 16)) ≤ Real.exp (-(x / 120000)) := by
  have hx0 : 0 ≤ x := by linarith
  have h3 := Real.pow_div_factorial_le_exp (x / 20) (by positivity) 3
  have hfact : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfact] at h3
  have hsq : x ^ 2 ≤ Real.exp (x / 20) := by
    have e : (x / 20) ^ 3 / 6 = x ^ 2 * (x / 48000) := by ring
    have h1 : 1 ≤ x / 48000 := by rw [le_div_iff₀ (by norm_num)]; linarith
    have : x ^ 2 ≤ (x / 20) ^ 3 / 6 := by
      rw [e]; nlinarith [sq_nonneg x]
    linarith
  calc x ^ 2 * Real.exp (-(x / 16)) ≤ Real.exp (x / 20) * Real.exp (-(x / 16)) :=
        mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ = Real.exp (-(x / 80)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(x / 120000)) := Real.exp_le_exp.mpr (by linarith)

/-- **One scale, one exponential.**  The typical-box exceptional set at scale `R` with
`|ζ'/ζ| ≤ ½ log T` has measure `≤ 4CT e^{−R log T/120000} + C√T` once `R log T ≥ κ₂`. -/
theorem exists_volume_not_zetaLogDerivScaleData_half_le :
    ∃ C κ₂ : ℝ, 0 < C ∧ 120000 ≤ κ₂ ∧ ∀ᶠ T in atTop, ∀ R : ℝ, 0 < R → R ≤ 1 / 16 →
      κ₂ ≤ R * Real.log T →
      volume {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R (1 / 2 * Real.log T)} ≤
        ENNReal.ofReal (4 * C * T * Real.exp (-(R * Real.log T / 120000)) +
          C * T ^ ((1 : ℝ) / 2)) := by
  obtain ⟨C, κ₁, hC, hκ₁, hev⟩ := exists_volume_not_zetaLogDerivScaleData_le_exp (ε := 1 / 2)
    (by norm_num) (by norm_num)
  refine ⟨C, max κ₁ 120000, hC, le_max_right _ _, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with T hT hT1 R hR hR1 hκ
  refine (hT R hR hR1 ((le_max_left _ _).trans hκ)).trans (ENNReal.ofReal_le_ofReal ?_)
  set x := R * Real.log T with hxdef
  have hx : 120000 ≤ x := (le_max_right _ _).trans hκ
  have h1 := sq_mul_exp_neg_div_sixteen_le (x := x) (by linarith)
  have h2 : Real.exp (-(x * (1 / 2) / 15)) ≤ Real.exp (-(x / 120000)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hCT : 0 ≤ C * T := by positivity
  have hsum : Real.exp (-(x / 120000)) / (1 / 2) +
      (x ^ 2 * Real.exp (-(x / 16)) + Real.exp (-(x * (1 / 2) / 15))) ≤
      4 * Real.exp (-(x / 120000)) := by
    have : Real.exp (-(x / 120000)) / (1 / 2) = 2 * Real.exp (-(x / 120000)) := by ring
    linarith
  have := mul_le_mul_of_nonneg_left hsum hCT
  linarith

/-- `Σ_{j<K} e^{−2^j x} ≤ 2e^{−x}` for `x ≥ 1`. -/
theorem sum_exp_neg_two_pow_mul_le {x : ℝ} (hx : 1 ≤ x) (K : ℕ) :
    ∑ j ∈ Finset.range K, Real.exp (-(2 ^ j * x)) ≤ 2 * Real.exp (-x) := by
  set q := Real.exp (-x) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q ≤ 1 / 2 := by
    have : Real.exp (-x) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 := Real.exp_one_gt_d9
    have : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    have h3 : (Real.exp 1)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
    linarith
  have hterm : ∀ j : ℕ, Real.exp (-(2 ^ j * x)) ≤ q * q ^ j := by
    intro j
    have hj : ((j : ℝ) + 1) ≤ 2 ^ j := by
      have := (Nat.lt_two_pow_self (n := j))
      exact_mod_cast this
    have : Real.exp (-(2 ^ j * x)) ≤ Real.exp (-(((j : ℝ) + 1) * x)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    refine this.trans (le_of_eq ?_)
    rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc ∑ j ∈ Finset.range K, Real.exp (-(2 ^ j * x)) ≤ ∑ j ∈ Finset.range K, q * q ^ j :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = q * ∑ j ∈ Finset.range K, q ^ j := by rw [Finset.mul_sum]
    _ ≤ q * (1 / (1 - q)) := by
        refine mul_le_mul_of_nonneg_left ?_ hq0.le
        rw [geom_sum_eq (by linarith : q ≠ 1), show q ^ K - 1 = -(1 - q ^ K) by ring,
          show q - 1 = -(1 - q) by ring, neg_div_neg_eq]
        exact (div_le_div_iff_of_pos_right (by linarith)).mpr (by linarith [pow_pos hq0 K])
    _ ≤ 2 * q := by
        rw [mul_one_div, div_le_iff₀ (by linarith)]
        nlinarith

/-- `(log T + 2) √T ≤ T^{3/4}` for large `T`. -/
theorem eventually_log_add_two_mul_sqrt_le :
    ∀ᶠ T : ℝ in atTop, (Real.log T + 2) * T ^ ((1 : ℝ) / 2) ≤ T ^ ((3 : ℝ) / 4) := by
  have h1 := (isLittleO_log_rpow_atTop (r := 1 / 4) (by norm_num)).bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have h2 : Tendsto (fun T : ℝ => T ^ ((1 : ℝ) / 4)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [h1, h2.eventually_ge_atTop 4, eventually_ge_atTop (1 : ℝ)] with T hT hT4 hT1
  have hT0 : 0 < T := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hT1),
    abs_of_nonneg (by positivity)] at hT
  have hsplit : T ^ ((3 : ℝ) / 4) = T ^ ((1 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add hT0]; norm_num
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- **Critical-scale clusters are rare at all scales at once.**  There are `C` and `κ₂` such that
for all large `T` and every `0 < R₀ ≤ 1/16` with `R₀ log T ≥ κ₂`, the heights `t ∈ [T, 2T]` at
which some scale `u ∈ [R₀, 1/16]` carries more than `20 u log T` zero copies within `u` of `t`
have measure at most `12 C T e^{−R₀ log T/120000} + C T^{3/4}`. -/
theorem exists_volume_multiscale_localZeroCount_gt_le :
    ∃ C κ₂ : ℝ, 0 < C ∧ 120000 ≤ κ₂ ∧ ∀ᶠ T in atTop, ∀ R₀ : ℝ, 0 < R₀ → R₀ ≤ 1 / 16 →
      κ₂ ≤ R₀ * Real.log T →
      volume {t | t ∈ Icc T (2 * T) ∧ ∃ u : ℝ, R₀ ≤ u ∧ u ≤ 1 / 16 ∧ ∃ F : Finset XiZeroCopy,
          (∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ u) ∧ 20 * (u * Real.log T) < F.card} ≤
        ENNReal.ofReal (12 * C * T * Real.exp (-(R₀ * Real.log T / 120000)) +
          C * T ^ ((3 : ℝ) / 4)) := by
  classical
  obtain ⟨C, κ₂, hC, hκ₂, hev⟩ := exists_volume_not_zetaLogDerivScaleData_half_le
  refine ⟨C, κ₂, hC, hκ₂, ?_⟩
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop
    (4 * (13 / 2 * (Real.log 2 + digammaVerticalLogConstant + 1)))
  filter_upwards [hev, hlog, eventually_ge_atTop (8 : ℝ), eventually_log_add_two_mul_sqrt_le]
    with T hT hTlog hT8 hTpow R₀ hR₀ hR₀1 hκ
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := Real.log_pos (by linarith)
  set E : ℝ → Set ℝ := fun R =>
    {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R (1 / 2 * Real.log T)} with hE
  have hex : ∃ k : ℕ, 1 / 16 < 2 ^ k * R₀ := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 16 / R₀) (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, by rwa [div_lt_iff₀ hR₀] at hk⟩
  set K := Nat.find hex with hKdef
  have hKspec : 1 / 16 < 2 ^ K * R₀ := Nat.find_spec hex
  have hKmin : ∀ j < K, 2 ^ j * R₀ ≤ 1 / 16 := fun j hj => not_lt.mp (Nat.find_min hex hj)
  have hK1 : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0, pow_zero, one_mul] at hKspec; linarith
    · exact hpos
  -- covering by the exceptional sets at the scales `2^j R₀`, `j < K`, and `1/16`
  have hcover : {t | t ∈ Icc T (2 * T) ∧ ∃ u : ℝ, R₀ ≤ u ∧ u ≤ 1 / 16 ∧
      ∃ F : Finset XiZeroCopy, (∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ u) ∧
        20 * (u * Real.log T) < F.card} ⊆
      (⋃ j ∈ Finset.range K, E (2 ^ j * R₀)) ∪ E (1 / 16) := by
    rintro t ⟨ht, u, hu0, hu1, F, hF, hcard⟩
    by_contra hnot
    have hsmall : ∀ j < K, ZetaLogDerivScaleData t (2 ^ j * R₀) (1 / 2 * Real.log T) := by
      intro j hj
      by_contra hd
      exact hnot (Or.inl (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hj, ⟨ht, hd⟩⟩))
    have hbig : ZetaLogDerivScaleData t (1 / 16) (1 / 2 * Real.log T) := by
      by_contra hd
      exact hnot (Or.inr ⟨ht, hd⟩)
    have hexu : ∃ j : ℕ, u ≤ 2 ^ j * R₀ := ⟨K, by linarith⟩
    set j := Nat.find hexu with hjdef
    have hjspec : u ≤ 2 ^ j * R₀ := Nat.find_spec hexu
    have hj2 : 2 ^ j * R₀ ≤ 2 * u := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0, pow_zero, one_mul]; linarith
      · have hprev := Nat.find_min hexu (show j - 1 < j by omega)
        push Not at hprev
        have e : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [e]; nlinarith
    by_cases hjK : j < K
    · have hb := card_le_ten_mul_of_zetaLogDerivScaleData_half hT8 hTlog ht (by positivity)
        (hKmin j hjK) (hsmall j hjK) F (fun q hq => (hF q hq).trans hjspec)
      nlinarith
    · push Not at hjK
      have h16 : 1 / 16 ≤ 2 * u := by
        have : (2 : ℝ) ^ K * R₀ ≤ 2 ^ j * R₀ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hjK) hR₀.le
        linarith
      have hb := card_le_ten_mul_of_zetaLogDerivScaleData_half hT8 hTlog ht (by norm_num) le_rfl
        hbig F (fun q hq => (hF q hq).trans hu1)
      nlinarith
  -- the measure of the cover
  set x : ℝ := R₀ * Real.log T / 120000 with hx
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ (by norm_num)]; linarith
  set a : ℕ → ℝ := fun j =>
    4 * C * T * Real.exp (-(2 ^ j * R₀ * Real.log T / 120000)) + C * T ^ ((1 : ℝ) / 2) with ha
  set b : ℝ := 4 * C * T * Real.exp (-(1 / 16 * Real.log T / 120000)) +
    C * T ^ ((1 : ℝ) / 2) with hb
  have ha0 : ∀ j, 0 ≤ a j := fun j => by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hsmallvol : ∀ j ∈ Finset.range K, volume (E (2 ^ j * R₀)) ≤ ENNReal.ofReal (a j) := by
    intro j hj
    have h2j : R₀ ≤ 2 ^ j * R₀ := le_mul_of_one_le_left hR₀.le (one_le_pow₀ (by norm_num))
    exact hT _ (by positivity) (hKmin j (Finset.mem_range.mp hj)) (by nlinarith)
  have hbigvol : volume (E (1 / 16)) ≤ ENNReal.ofReal b := hT _ (by norm_num) le_rfl (by nlinarith)
  -- the real bound
  have hgeom : ∑ j ∈ Finset.range K, Real.exp (-(2 ^ j * R₀ * Real.log T / 120000)) ≤
      2 * Real.exp (-x) := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
      (sum_exp_neg_two_pow_mul_le hx1 K)
    rw [hx]; congr 1; ring
  have hKL : (K : ℝ) ≤ Real.log T := by
    have hprev := hKmin (K - 1) (by omega)
    have h1 : (K - 1 : ℕ) < 2 ^ (K - 1) := Nat.lt_two_pow_self
    have hR₀L : 1 / R₀ ≤ Real.log T := by
      rw [div_le_iff₀ hR₀]; nlinarith
    have h2 : (2 : ℝ) ^ (K - 1) ≤ 1 / 16 / R₀ := by rw [le_div_iff₀ hR₀]; exact hprev
    have h3 : ((K - 1 : ℕ) : ℝ) + 1 ≤ 2 ^ (K - 1) := by exact_mod_cast h1
    have h4 : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
      rw [Nat.cast_sub hK1]; simp
    have h5 : 1 / 16 / R₀ ≤ 1 / R₀ := by
      rw [div_le_div_iff_of_pos_right hR₀]; norm_num
    linarith
  have hbig_le : Real.exp (-(1 / 16 * Real.log T / 120000)) ≤ Real.exp (-x) :=
    Real.exp_le_exp.mpr (by rw [hx]; nlinarith)
  have hreal : ∑ j ∈ Finset.range K, a j + b ≤
      12 * C * T * Real.exp (-(R₀ * Real.log T / 120000)) + C * T ^ ((3 : ℝ) / 4) := by
    have hsum : ∑ j ∈ Finset.range K, a j =
        4 * C * T * ∑ j ∈ Finset.range K, Real.exp (-(2 ^ j * R₀ * Real.log T / 120000)) +
          K * (C * T ^ ((1 : ℝ) / 2)) := by
      rw [ha]; simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, ← Finset.mul_sum]
    rw [hsum, hb]
    have hCT : 0 ≤ 4 * C * T := by positivity
    have hsq : 0 ≤ C * T ^ ((1 : ℝ) / 2) := by positivity
    have e1 := mul_le_mul_of_nonneg_left hgeom hCT
    have e2 := mul_le_mul_of_nonneg_left hbig_le hCT
    have e3 : (K : ℝ) * (C * T ^ ((1 : ℝ) / 2)) + C * T ^ ((1 : ℝ) / 2) ≤
        C * T ^ ((3 : ℝ) / 4) := by
      have := mul_le_mul_of_nonneg_left hTpow hC.le
      nlinarith
    have hxe : Real.exp (-x) = Real.exp (-(R₀ * Real.log T / 120000)) := by rw [hx]
    rw [hxe] at e1 e2
    nlinarith
  calc volume {t | t ∈ Icc T (2 * T) ∧ ∃ u : ℝ, R₀ ≤ u ∧ u ≤ 1 / 16 ∧
          ∃ F : Finset XiZeroCopy, (∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ u) ∧
            20 * (u * Real.log T) < F.card}
        ≤ volume ((⋃ j ∈ Finset.range K, E (2 ^ j * R₀)) ∪ E (1 / 16)) := measure_mono hcover
    _ ≤ volume (⋃ j ∈ Finset.range K, E (2 ^ j * R₀)) + volume (E (1 / 16)) :=
        measure_union_le _ _
    _ ≤ (∑ j ∈ Finset.range K, volume (E (2 ^ j * R₀))) + volume (E (1 / 16)) :=
        add_le_add (measure_biUnion_finset_le _ _) le_rfl
    _ ≤ (∑ j ∈ Finset.range K, ENNReal.ofReal (a j)) + ENNReal.ofReal b :=
        add_le_add (Finset.sum_le_sum hsmallvol) hbigvol
    _ = ENNReal.ofReal (∑ j ∈ Finset.range K, a j + b) := by
        rw [ENNReal.ofReal_add (Finset.sum_nonneg fun j _ => ha0 j) hb0,
          ENNReal.ofReal_sum_of_nonneg fun j _ => ha0 j]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end

end RHTower
