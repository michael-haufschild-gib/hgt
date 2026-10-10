import GaloisForLFunctions.RHTower.MertensPolylogStrictMultiplicity

/-!
# Strict polylogarithmic multiplicity along a ray

Two abstract steps behind every `1/ζ`-type multiplicity law.

* **Ray lemma** (`natCast_lt_of_ray_littleO`). Let `F·E = H` along the ray `z = ρ + r v`,
  `r ↓ 0`, with `H` continuous at `ρ` and `H ρ ≠ 0`. Let `E z = (z - ρ)^n p z` near `ρ` with `p`
  continuous at `ρ`, and suppose `‖F(ρ + r v)‖ ≤ η r^{-(a+1)} + C_η` for every `η > 0`. Then
  `n < a + 1`. If `n ≥ a + 1`, then `r^n F → 0`, so `F·E → 0`.
* **Mellin tail bound** (`norm_integral_Ioi_one_cpow_mul_le`). If `‖f t‖ ≤ B t^c (1 + log t)^a`
  on `t > 1` and `‖f t‖ ≤ ε t^c (1 + log t)^a` for `t ≥ T_ε`, then for `c < Re s ≤ c + 1`,
  `‖∫_1^∞ t^{-s-1} f(t) dt‖ ≤ η (Re s - c)^{-(a+1)} + C_η` for every `η > 0`.

Together: a little-`o` polylogarithmic bound at the abscissa `c` caps the order of every pole of the
transform on `Re s = c` strictly below `a + 1`.
-/

open Complex Filter Topology MeasureTheory Set

namespace RHTower

noncomputable section

/-- **Ray lemma.** -/
theorem natCast_lt_of_ray_littleO {E F H p : ℂ → ℂ} {ρ v : ℂ} {a : ℝ} {n : ℕ} (ha : 0 ≤ a)
    (hp : ContinuousAt p ρ) (hfac : ∀ᶠ z in 𝓝 ρ, E z = (z - ρ) ^ n * p z)
    (hH : ContinuousAt H ρ) (hHρ : H ρ ≠ 0)
    (hFE : ∀ᶠ r : ℝ in 𝓝[>] 0, F (ρ + r * v) * E (ρ + r * v) = H (ρ + r * v))
    (hF : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖F (ρ + r * v)‖ ≤ η * r ^ (-(a + 1)) + C) :
    (n : ℝ) < a + 1 := by
  by_contra hlt
  have hn_ge : a + 1 ≤ (n : ℝ) := not_lt.mp hlt
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)
  have hray : Tendsto (fun r : ℝ => ρ + (r : ℂ) * v) (𝓝[>] 0) (𝓝 ρ) := by
    have h : Tendsto (fun r : ℝ => ρ + (r : ℂ) * v) (𝓝 0) (𝓝 (ρ + ((0 : ℝ) : ℂ) * v)) :=
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).tendsto 0)
    rw [Complex.ofReal_zero, zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hsmall : Tendsto (fun r : ℝ => (r : ℂ) ^ n * F (ρ + r * v)) (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨C, hC⟩ := hF (η / 2) (by positivity)
    set m : ℝ := min 1 (η / (4 * (|C| + 1))) with hm
    have hm0 : 0 < m := lt_min one_pos (by positivity)
    filter_upwards [hC, Ioo_mem_nhdsGT hm0] with r hr hrI
    have hr0 : 0 < r := hrI.1
    have hr1 : r ≤ 1 := hrI.2.le.trans (min_le_left _ _)
    have hrC : r < η / (4 * (|C| + 1)) := hrI.2.trans_le (min_le_right _ _)
    rw [dist_zero_right, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    have hpow : r ^ n * r ^ (-(a + 1)) ≤ 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr0]
      exact Real.rpow_le_one hr0.le hr1 (by linarith)
    have hrn : r ^ n ≤ r := by
      calc r ^ n ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le hr1 hn1
        _ = r := pow_one r
    have hrn0 : 0 ≤ r ^ n := pow_nonneg hr0.le n
    have hCr : |C| * r ≤ η / 4 := by
      have h4 : 4 * (|C| + 1) * r < η := by
        rwa [lt_div_iff₀ (by positivity), mul_comm] at hrC
      nlinarith [abs_nonneg C]
    calc r ^ n * ‖F (ρ + r * v)‖
        ≤ r ^ n * (η / 2 * r ^ (-(a + 1)) + C) := mul_le_mul_of_nonneg_left hr hrn0
      _ = η / 2 * (r ^ n * r ^ (-(a + 1))) + C * r ^ n := by ring
      _ ≤ η / 2 * 1 + |C| * r := by
          have h1 : C * r ^ n ≤ |C| * r :=
            (mul_le_mul_of_nonneg_right (le_abs_self C) hrn0).trans
              (mul_le_mul_of_nonneg_left hrn (abs_nonneg C))
          have h2 : η / 2 * (r ^ n * r ^ (-(a + 1))) ≤ η / 2 * 1 :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
          linarith
      _ < η := by linarith
  have hother : Tendsto (fun r : ℝ => v ^ n * p (ρ + (r : ℂ) * v)) (𝓝[>] 0)
      (𝓝 (v ^ n * p ρ)) := tendsto_const_nhds.mul (hp.tendsto.comp hray)
  have hzero : Tendsto (fun r : ℝ => F (ρ + (r : ℂ) * v) * E (ρ + (r : ℂ) * v)) (𝓝[>] 0)
      (𝓝 0) := by
    have := hsmall.mul hother
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [hray.eventually hfac] with r hfr
    rw [hfr]
    ring
  have hval : Tendsto (fun r : ℝ => F (ρ + (r : ℂ) * v) * E (ρ + (r : ℂ) * v)) (𝓝[>] 0)
      (𝓝 (H ρ)) := (hH.tendsto.comp hray).congr' (hFE.mono fun r hr => hr.symm)
  exact hHρ (tendsto_nhds_unique hval hzero)

/-- **Mellin tail bound.** -/
theorem norm_integral_Ioi_one_cpow_mul_le {f : ℝ → ℂ} {c a B : ℝ} (ha : 0 ≤ a)
    (hB : ∀ t : ℝ, 1 < t → ‖f t‖ ≤ B * t ^ c * (1 + Real.log t) ^ a)
    (hlittle : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      ‖f t‖ ≤ ε * t ^ c * (1 + Real.log t) ^ a) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ s : ℂ, c < s.re → s.re ≤ c + 1 →
      ‖∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * f t‖ ≤ η * (s.re - c) ^ (-(a + 1)) + C := by
  intro η hη
  set K : ℝ := polylogConst a with hK
  have hK0 : 0 < K := polylogConst_pos a
  set ε : ℝ := η / (K * 2 ^ (a + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨T, hT1, hT⟩ := hlittle ε hε0
  have hB0 : 0 ≤ B := by
    have h := hB 2 (by norm_num)
    have hpos : 0 < (2 : ℝ) ^ c * (1 + Real.log 2) ^ a :=
      mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
        (Real.rpow_pos_of_pos (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]) _)
    by_contra hneg
    have : B * 2 ^ c * (1 + Real.log 2) ^ a < 0 := by
      rw [mul_assoc]; exact mul_neg_of_neg_of_pos (not_le.mp hneg) hpos
    linarith [norm_nonneg (f 2)]
  set B' : ℝ := B * (1 + Real.log T) ^ a with hB'
  have hB'0 : 0 ≤ B' := mul_nonneg hB0 (Real.rpow_nonneg (by linarith [Real.log_nonneg hT1]) _)
  refine ⟨B' * (T - 1), fun s hs hs1 => ?_⟩
  set r : ℝ := s.re - c with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r ≤ 1 := by rw [hr]; linarith
  set G : ℝ → ℝ := fun t => (Iic T).indicator (fun _ => B') t +
    ε * ((2 / r) ^ a * K) * t ^ (-1 - r / 2) with hG
  have hi1 : IntegrableOn (fun t : ℝ => t ^ (-1 - r / 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hind : IntegrableOn ((Iic T).indicator (fun _ : ℝ => B')) (Ioi 1) := by
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioi]
    exact integrableOn_const measure_Ioc_lt_top.ne
  have hGi : IntegrableOn G (Ioi 1) := hind.add (hi1.const_mul _)
  have hbound : ∀ t ∈ Ioi (1 : ℝ), ‖(t : ℂ) ^ (-s - 1) * f t‖ ≤ G t := by
    intro t ht
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := by linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-s - 1).re = -c - r - 1 := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, hr]; ring
    rw [hre]
    have hpow0 : 0 < t ^ (-c - r - 1) := Real.rpow_pos_of_pos ht0 _
    have hlog0 : 0 ≤ (1 + Real.log t) ^ a :=
      Real.rpow_nonneg (by linarith [Real.log_nonneg ht1.le]) _
    have hsplit : t ^ (-c - r - 1) * t ^ c = t ^ (-1 - r) := by
      rw [← Real.rpow_add ht0]; ring_nf
    have hind0 : 0 ≤ (Iic T).indicator (fun _ : ℝ => B') t := by
      by_cases htT : t ∈ Iic T
      · rw [Set.indicator_of_mem htT]; exact hB'0
      · rw [Set.indicator_of_notMem htT]
    have hlogle := one_add_log_rpow_le ha hr0 hr1 ht1.le
    have e2 : t ^ (-1 - r) * t ^ (r / 2) = t ^ (-1 - r / 2) := by
      rw [← Real.rpow_add ht0]; ring_nf
    have htail : ε * t ^ (-1 - r) * (1 + Real.log t) ^ a ≤
        ε * ((2 / r) ^ a * K) * t ^ (-1 - r / 2) := by
      calc ε * t ^ (-1 - r) * (1 + Real.log t) ^ a
          ≤ ε * t ^ (-1 - r) * ((2 / r) ^ a * K * t ^ (r / 2)) := by
            gcongr
        _ = ε * ((2 / r) ^ a * K) * (t ^ (-1 - r) * t ^ (r / 2)) := by ring
        _ = ε * ((2 / r) ^ a * K) * t ^ (-1 - r / 2) := by rw [e2]
    have hGt : G t = (Iic T).indicator (fun _ : ℝ => B') t +
        ε * ((2 / r) ^ a * K) * t ^ (-1 - r / 2) := rfl
    have htailnn : 0 ≤ ε * ((2 / r) ^ a * K) * t ^ (-1 - r / 2) := by positivity
    rcases le_or_gt t T with htT | htT
    · -- head: bounded by `B'`
      rw [hGt, Set.indicator_of_mem (show t ∈ Iic T from htT)]
      have h1 : t ^ (-1 - r) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by linarith)
      have h2 : (1 + Real.log t) ^ a ≤ (1 + Real.log T) ^ a :=
        Real.rpow_le_rpow (by linarith [Real.log_nonneg ht1.le])
          (by linarith [Real.log_le_log ht0 htT]) ha
      calc t ^ (-c - r - 1) * ‖f t‖ ≤ t ^ (-c - r - 1) * (B * t ^ c * (1 + Real.log t) ^ a) :=
            mul_le_mul_of_nonneg_left (hB t ht1) hpow0.le
        _ = B * (t ^ (-c - r - 1) * t ^ c) * (1 + Real.log t) ^ a := by ring
        _ = B * t ^ (-1 - r) * (1 + Real.log t) ^ a := by rw [hsplit]
        _ ≤ B * 1 * (1 + Real.log T) ^ a := by
            gcongr
        _ = B' := by rw [hB']; ring
        _ ≤ B' + ε * ((2 / r) ^ a * K) * t ^ (-1 - r / 2) := by linarith
    · rw [hGt, Set.indicator_of_notMem (show t ∉ Iic T from not_le.mpr htT), zero_add]
      calc t ^ (-c - r - 1) * ‖f t‖ ≤ t ^ (-c - r - 1) * (ε * t ^ c * (1 + Real.log t) ^ a) :=
            mul_le_mul_of_nonneg_left (hT t htT.le) hpow0.le
        _ = ε * (t ^ (-c - r - 1) * t ^ c) * (1 + Real.log t) ^ a := by ring
        _ = ε * t ^ (-1 - r) * (1 + Real.log t) ^ a := by rw [hsplit]
        _ ≤ ε * ((2 / r) ^ a * K) * t ^ (-1 - r / 2) := htail
  have hle := norm_integral_le_of_norm_le hGi
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hbound))
  refine hle.trans ?_
  rw [integral_add hind (hi1.const_mul _), integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
    show (-1 - r / 2 + 1 : ℝ) = -(r / 2) by ring, neg_div_neg_eq, one_div_div,
    setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic, setIntegral_const,
    Real.volume_real_Ioc_of_le hT1, smul_eq_mul]
  have h2 : (2 / r) ^ a * (2 / r) = 2 ^ (a + 1) * r ^ (-(a + 1)) := by
    rw [Real.div_rpow (by norm_num) hr0.le, Real.rpow_add_one (by norm_num),
      Real.rpow_neg hr0.le, Real.rpow_add_one hr0.ne']
    field_simp
  have : ε * ((2 / r) ^ a * K) * (2 / r) = η * r ^ (-(a + 1)) := by
    calc ε * ((2 / r) ^ a * K) * (2 / r) = ε * K * ((2 / r) ^ a * (2 / r)) := by ring
      _ = ε * K * (2 ^ (a + 1) * r ^ (-(a + 1))) := by rw [h2]
      _ = η * r ^ (-(a + 1)) := by rw [hε]; field_simp
  rw [this]
  linarith

end

end RHTower
