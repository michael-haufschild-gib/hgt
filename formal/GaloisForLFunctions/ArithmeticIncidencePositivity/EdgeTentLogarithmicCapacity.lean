import GaloisForLFunctions.ArithmeticIncidencePositivity.EdgeTentSharingObstruction

/-!
# The logarithmic capacity of the shared surplus

The surplus of an odd test is a logarithmic energy: a pair at distance `t` carries `ω(t) ≈ 1/(2t)`.
For the odd edge tent `F` of width `ε` at the common edge `r` of all prime strips
(`EdgeTentSharingObstruction`) the pairs across the foot `a = r − ε` carry
`∫_0^a ω(x − y) dy = Ω(x − a) − Ω(x) ≤ ½ log(4/ε) + ε/(2(x − a)) + 4/5`, the pairs on the tent at
most `ε/2 + ε²/4`, and the tent mass is `∫ F² ≥ ε³/32`. Hence (`stripBoxEnergy_edgeTent_le_log`)

    T(0, r) ≤ (log(4/ε) + 42) ∫_0^r F²,

uniformly in the window `r`. Every strip `[L − r, r]` with `r ≤ L ≤ 2(r − ε)` charges the edge tent
`½ ∫_0^r F²` on its odd part (`edgeTent_oddPart_eq_half_mass`). So one copy of the surplus of all
pairs of the support pays the odd parts of a family of strips wider than `ε` only if their weights
sum to at most `2 log(4/ε) + 84` (`stripBoxEnergy_edgeTent_lt_sum_oddPart`): the shared surplus has
logarithmic capacity at the common edge. The telescoping chain of `SharedStripSurplusAllocation`
attains this order, a strip per geometric width layer.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- `Ω(s) ≤ ½ log(4/ε) + ε/(2s) + 4/5` for `0 < s ≤ ε ≤ 1`: the logarithm of `Ω` split at the scale `ε`. -/
theorem archLevyAntideriv_le_capacity {s ε : ℝ} (hs : 0 < s) (hsε : s ≤ ε) (hε1 : ε ≤ 1) :
    archLevyAntideriv s ≤ Real.log (4 / ε) / 2 + ε / (2 * s) + 4 / 5 := by
  have hε0 : 0 < ε := hs.trans_le hsε
  have h := archLevyAntideriv_le_expansion hs
  have hlog : -(1 / 2) * Real.log (s / 4) = Real.log (4 / ε) / 2 + Real.log (ε / s) / 2 := by
    rw [Real.log_div hs.ne' (by norm_num), Real.log_div (by norm_num) hε0.ne',
      Real.log_div hε0.ne' hs.ne']
    ring
  have hle : Real.log (ε / s) ≤ ε / s := by
    have := Real.log_le_sub_one_of_pos (show 0 < ε / s by positivity); linarith
  have hpi := Real.pi_lt_d2
  have hs1 : s ≤ 1 := hsε.trans hε1
  have hpoly : s ^ 2 / 96 - s / 4 + 5 / 384 * s ^ 3 ≤ 0 := by nlinarith
  have e : ε / (2 * s) = ε / s / 2 := by field_simp
  rw [e]
  linarith

/-- `ω(x − y) τ(x)² ≤ (3/2)(x − a)` for `y ≤ a < x ≤ r`, `a = r − ε`, `ε ≤ 1`. -/
theorem archLevyDensity_mul_edgeTent_sq_le {r ε x y : ℝ} (hε1 : ε ≤ 1) (hya : y ≤ r - ε)
    (hax : r - ε < x) (hxr : x ≤ r) :
    archLevyDensity (x - y) * edgeTent r ε x ^ 2 ≤ 3 / 2 * (x - (r - ε)) := by
  set d := x - (r - ε) with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hxy : 0 < x - y := by linarith
  have hτ2 : edgeTent r ε x ^ 2 ≤ d ^ 2 :=
    pow_le_pow_left₀ (edgeTent_nonneg r ε x) (edgeTent_le_sub hax.le) 2
  have hd1 : d ≤ 1 := by rw [hd]; linarith
  have hω : archLevyDensity (x - y) ≤ 3 / 2 / d := by
    rcases le_or_gt (x - y) 1 with h1 | h1
    · refine (archLevyDensity_le_of_le_one hxy h1).trans ?_
      exact div_le_div_of_nonneg_left (by norm_num) hd0 (by rw [hd]; linarith)
    · have hmono : archLevyDensity (x - y) ≤ archLevyDensity 1 :=
        strictAntiOn_archLevyDensity.antitoneOn (show (0 : ℝ) < 1 by norm_num) hxy h1.le
      have h1' := archLevyDensity_le_of_le_one (show (0 : ℝ) < 1 by norm_num) le_rfl
      have : (3 : ℝ) / 2 / 1 ≤ 3 / 2 / d := div_le_div_of_nonneg_left (by norm_num) hd0 hd1
      linarith
  have hω0 := archLevyDensity_pos hxy
  calc archLevyDensity (x - y) * edgeTent r ε x ^ 2 ≤ 3 / 2 / d * d ^ 2 :=
        mul_le_mul hω hτ2 (sq_nonneg _) (by positivity)
    _ = 3 / 2 * d := by field_simp

/-- The pairs across the foot `a = r − ε`, read from the tent: `ω(x − y) τ(x)²` for `y ≤ a < x`. -/
def edgeTentCross (r ε x y : ℝ) : ℝ :=
  if r - ε < x ∧ y ≤ r - ε then archLevyDensity (x - y) * edgeTent r ε x ^ 2 else 0

/-- The pairs on the tent: `ε/2 + ε²/4` for `a < x, y`. -/
def edgeTentTop (r ε x y : ℝ) : ℝ := if r - ε < x ∧ r - ε < y then ε / 2 + ε ^ 2 / 4 else 0

theorem measurable_edgeTentCross (r ε : ℝ) : Measurable (Function.uncurry (edgeTentCross r ε)) := by
  have hs : MeasurableSet {z : ℝ × ℝ | r - ε < z.1 ∧ z.2 ≤ r - ε} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_snd measurable_const)
  refine Measurable.ite hs ?_ measurable_const
  exact (measurable_archLevyDensity.comp (measurable_fst.sub measurable_snd)).mul
    (((continuous_edgeTent r ε).measurable.comp measurable_fst).pow_const 2)

theorem edgeTentCross_bounds {r ε x y : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    0 ≤ edgeTentCross r ε x y ∧ edgeTentCross r ε x y ≤ 3 / 2 * ε := by
  unfold edgeTentCross
  split_ifs with h
  · have h0 := archLevyDensity_pos (show 0 < x - y by linarith [h.1, h.2])
    refine ⟨mul_nonneg h0.le (sq_nonneg _), ?_⟩
    by_cases hxr : x ≤ r
    · have hb := archLevyDensity_mul_edgeTent_sq_le hε1 h.2 h.1 hxr
      linarith
    · rw [edgeTent_eq_zero_of_ge (not_le.mp hxr).le]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      positivity
  · exact ⟨le_rfl, by positivity⟩

/-- Pointwise: `k(x, y)(F x − F y)² ≤ C(x, y) + C(y, x) + top(x, y)` on `[0, r]²`. -/
theorem stripIntegrand_edgeTentOdd_le_cross {r ε x y : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hεr : ε < r) (hx : x ∈ Icc 0 r) (hy : y ∈ Icc 0 r) :
    stripIntegrand (edgeTentOdd r ε) x y ≤
      edgeTentCross r ε x y + edgeTentCross r ε y x + edgeTentTop r ε x y := by
  have hC1 := (edgeTentCross_bounds (r := r) (x := x) (y := y) hε0.le hε1).1
  have hC2 := (edgeTentCross_bounds (r := r) (x := y) (y := x) hε0.le hε1).1
  have hT0 : 0 ≤ edgeTentTop r ε x y := by unfold edgeTentTop; split_ifs <;> positivity
  have hFx := edgeTentOdd_of_nonneg hεr hx.1
  have hFy := edgeTentOdd_of_nonneg hεr hy.1
  unfold stripIntegrand
  rw [hFx, hFy]
  by_cases hxy : x = y
  · subst hxy; simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero]; linarith
  rcases le_or_gt x (r - ε) with hxa | hxa <;> rcases le_or_gt y (r - ε) with hya | hya
  · rw [edgeTent_eq_zero_of_le hxa, edgeTent_eq_zero_of_le hya, sub_self]; simp; linarith
  · -- `y` on the tent: `k(x, y) τ(y)² ≤ ω(y − x) τ(y)²`
    rw [edgeTent_eq_zero_of_le hxa, zero_sub, neg_sq]
    have hC : edgeTentCross r ε y x = archLevyDensity (y - x) * edgeTent r ε y ^ 2 := by
      unfold edgeTentCross; rw [if_pos ⟨hya, hxa⟩]
    have hk : surplusKernel x y ≤ archLevyDensity (y - x) := by
      rcases eq_or_lt_of_le hx.1 with h0 | h0
      · rw [← h0, surplusKernel_zero_left hy.1]; exact (archLevyDensity_pos (by linarith)).le
      · have := surplusKernel_le h0 (by linarith : 0 < y)
        rwa [abs_sub_comm, abs_of_pos (by linarith)] at this
    have := mul_le_mul_of_nonneg_right hk (sq_nonneg (edgeTent r ε y))
    linarith
  · -- `x` on the tent
    rw [edgeTent_eq_zero_of_le hya, sub_zero]
    have hC : edgeTentCross r ε x y = archLevyDensity (x - y) * edgeTent r ε x ^ 2 := by
      unfold edgeTentCross; rw [if_pos ⟨hxa, hya⟩]
    have hk : surplusKernel x y ≤ archLevyDensity (x - y) := by
      rcases eq_or_lt_of_le hy.1 with h0 | h0
      · rw [← h0, surplusKernel_comm, surplusKernel_zero_left hx.1]
        exact (archLevyDensity_pos (by linarith)).le
      · have := surplusKernel_le (by linarith : 0 < x) h0
        rwa [abs_of_pos (by linarith)] at this
    have := mul_le_mul_of_nonneg_right hk (sq_nonneg (edgeTent r ε x))
    linarith
  · -- both on the tent: `k ≤ 1/(2|x − y|) + 1/4` and the tent is `1`-Lipschitz
    have hx0 : 0 < x := by linarith
    have hy0 : 0 < y := by linarith
    have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have hdε : |x - y| ≤ ε := by rw [abs_le]; constructor <;> linarith [hx.2, hy.2]
    have hk := (surplusKernel_le hx0 hy0).trans (archLevyDensity_le_inv hd)
    have hL2 : (edgeTent r ε x - edgeTent r ε y) ^ 2 ≤ |x - y| ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_edgeTent_sub_le r ε x y) 2
    have hk0 := surplusKernel_nonneg hx0 hy0 hxy
    have h : surplusKernel x y * (edgeTent r ε x - edgeTent r ε y) ^ 2 ≤
        |x - y| / 2 + |x - y| ^ 2 / 4 := by
      calc surplusKernel x y * (edgeTent r ε x - edgeTent r ε y) ^ 2 ≤
            (1 / (2 * |x - y|) + 1 / 4) * |x - y| ^ 2 := mul_le_mul hk hL2 (sq_nonneg _) (by positivity)
        _ = |x - y| / 2 + |x - y| ^ 2 / 4 := by field_simp
    have hT : edgeTentTop r ε x y = ε / 2 + ε ^ 2 / 4 := by
      unfold edgeTentTop; rw [if_pos ⟨hxa, hya⟩]
    have h2 : |x - y| ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hdε 2
    linarith

/-- The cross pairs of a point `x` on the tent: `∫_0^r C(x, y) dy ≤ (½ log(4/ε) + 4/5) F(x)² +
1_{x > a} ε(x − a)/2`. -/
theorem integral_edgeTentCross_le {r ε x : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hεr : ε < r)
    (hx : x ∈ Icc 0 r) :
    (∫ y in (0 : ℝ)..r, edgeTentCross r ε x y) ≤
      (Real.log (4 / ε) / 2 + 4 / 5) * edgeTentOdd r ε x ^ 2 +
        (if r - ε < x then ε * (x - (r - ε)) / 2 else 0) := by
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hlog0 : 0 ≤ Real.log (4 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε0]; linarith)
  have hcoef : 0 ≤ Real.log (4 / ε) / 2 + 4 / 5 := by positivity
  by_cases hxa : r - ε < x
  · rw [if_pos hxa, edgeTentOdd_of_nonneg hεr hx.1]
    set a := r - ε with ha
    have hsub1 : uIcc 0 a ⊆ uIcc 0 r := by
      rw [uIcc_of_le (by linarith), uIcc_of_le hr0]; exact Icc_subset_Icc le_rfl (by linarith)
    have hsub2 : uIcc a r ⊆ uIcc 0 r := by
      rw [uIcc_of_le (by linarith), uIcc_of_le hr0]; exact Icc_subset_Icc (by linarith) le_rfl
    have hint : IntervalIntegrable (edgeTentCross r ε x) volume 0 r :=
      intervalIntegrable_of_abs_le hr0 (measurable_edgeTentCross r ε).of_uncurry_left
        fun y _ => by
          obtain ⟨h0, h1⟩ := edgeTentCross_bounds (r := r) (x := x) (y := y) hε0.le hε1
          rw [abs_of_nonneg h0]; exact h1
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint.mono_set hsub1)
      (hint.mono_set hsub2)]
    -- below the foot: `τ(x)² ∫_0^a ω(x − y) dy = τ(x)² (Ω(x − a) − Ω(x))`
    have hbelow : (∫ y in (0 : ℝ)..a, edgeTentCross r ε x y) =
        edgeTent r ε x ^ 2 * (archLevyAntideriv (x - a) - archLevyAntideriv x) := by
      have e : (∫ y in (0 : ℝ)..a, edgeTentCross r ε x y) =
          ∫ y in (0 : ℝ)..a, edgeTent r ε x ^ 2 * archLevyDensity (x - y) := by
        refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun y hy => ?_)
        rw [uIoc_of_le (by linarith)] at hy
        unfold edgeTentCross; rw [if_pos ⟨hxa, hy.2⟩, mul_comm]
      rw [e, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (fun t => archLevyDensity t) x, sub_zero,
        integral_archLevyDensity_Icc (by linarith) (by linarith)]
    have habove : (∫ y in a..r, edgeTentCross r ε x y) = 0 := by
      have e : (∫ y in a..r, edgeTentCross r ε x y) = ∫ _ in a..r, (0 : ℝ) := by
        refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun y hy => ?_)
        rw [uIoc_of_le (by linarith)] at hy
        unfold edgeTentCross; rw [if_neg fun h => absurd h.2 (not_le.mpr hy.1)]
      rw [e, intervalIntegral.integral_zero]
    rw [hbelow, habove, add_zero]
    -- `Ω(x) > 0` and the capacity bound for `Ω(x − a)`
    have hs : 0 < x - a := by linarith
    have hsε : x - a ≤ ε := by
      by_contra hc
      have := edgeTent_le_sub (r := r) (ε := ε) hxa.le
      linarith [hx.2]
    have hΩ := archLevyAntideriv_le_capacity hs hsε hε1
    have hΩx := archLevyAntideriv_pos (show 0 < x by linarith)
    have hτ0 := edgeTent_nonneg r ε x
    have hτ := edgeTent_le_sub (r := r) (ε := ε) hxa.le
    have hτ2 : edgeTent r ε x ^ 2 ≤ (x - a) ^ 2 := pow_le_pow_left₀ hτ0 hτ 2
    have hfrac : edgeTent r ε x ^ 2 * (ε / (2 * (x - a))) ≤ ε * (x - a) / 2 := by
      calc edgeTent r ε x ^ 2 * (ε / (2 * (x - a))) ≤ (x - a) ^ 2 * (ε / (2 * (x - a))) :=
            mul_le_mul_of_nonneg_right hτ2 (by positivity)
        _ = ε * (x - a) / 2 := by field_simp
    have h1 := mul_le_mul_of_nonneg_left hΩ (sq_nonneg (edgeTent r ε x))
    have h2 := mul_le_mul_of_nonneg_left hΩx.le (sq_nonneg (edgeTent r ε x))
    nlinarith
  · rw [if_neg hxa, add_zero]
    have e : (∫ y in (0 : ℝ)..r, edgeTentCross r ε x y) = ∫ _ in (0 : ℝ)..r, (0 : ℝ) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun y _ => ?_)
      unfold edgeTentCross; rw [if_neg fun h => hxa h.1]
    rw [e, intervalIntegral.integral_zero]
    positivity

/-- **The logarithmic capacity of the shared surplus.** For the odd edge tent of width `ε ≤ 1`:
`T(0, r) ≤ (log(4/ε) + 42) ∫_0^r F²`, uniformly in `r > ε`. -/
theorem stripBoxEnergy_edgeTent_le_log {r ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hεr : ε < r) :
    stripBoxEnergy (edgeTentOdd r ε) 0 r ≤
      (Real.log (4 / ε) + 42) * ∫ x in (0 : ℝ)..r, edgeTentOdd r ε x ^ 2 := by
  have hr0 : (0 : ℝ) ≤ r := by linarith
  set F := edgeTentOdd r ε with hFdef
  set M := ∫ x in (0 : ℝ)..r, F x ^ 2 with hM
  -- the comparison integrand and its pieces
  have hCm := measurable_edgeTentCross r ε
  have hCb : ∀ x ∈ Icc 0 r, ∀ y ∈ Icc 0 r, |edgeTentCross r ε x y| ≤ 3 / 2 * ε := fun x _ y _ => by
    obtain ⟨h0, h1⟩ := edgeTentCross_bounds (r := r) (x := x) (y := y) hε0.le hε1
    rw [abs_of_nonneg h0]; exact h1
  have hTm : Measurable (Function.uncurry (edgeTentTop r ε)) := by
    have hs : MeasurableSet {z : ℝ × ℝ | r - ε < z.1 ∧ r - ε < z.2} :=
      (measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_const measurable_snd)
    exact Measurable.ite hs measurable_const measurable_const
  have hTb : ∀ x ∈ Icc 0 r, ∀ y ∈ Icc 0 r, |edgeTentTop r ε x y| ≤ ε / 2 + ε ^ 2 / 4 :=
    fun x _ y _ => by
      unfold edgeTentTop
      split_ifs
      · rw [abs_of_nonneg (by positivity)]
      · rw [abs_zero]; positivity
  have hCm' : Measurable (Function.uncurry fun x y => edgeTentCross r ε y x) := hCm.comp measurable_swap
  obtain ⟨hCi, hCo⟩ := intervalIntegrable_iterated hr0 hCm hCb
  obtain ⟨hCi', hCo'⟩ := intervalIntegrable_iterated hr0 hCm' fun x hx y hy => hCb y hy x hx
  obtain ⟨hTi, hTo⟩ := intervalIntegrable_iterated hr0 hTm hTb
  have hgm := measurable_stripIntegrand (continuous_edgeTentOdd r ε)
  have hgb : ∀ x ∈ Icc 0 r, ∀ y ∈ Icc 0 r, |stripIntegrand F x y| ≤ 3 * ε := fun x hx y hy => by
    obtain ⟨h0, h1⟩ := stripIntegrand_edgeTentOdd_bounds hε0 hε1 hεr hx hy
    rw [abs_of_nonneg h0]
    refine h1.trans ?_
    unfold edgeTentWeight; split_ifs <;> linarith
  obtain ⟨hgi, hgo⟩ := intervalIntegrable_iterated hr0 hgm hgb
  -- `T ≤ ∫∫ (C + C' + top)`
  have hpt : ∀ x ∈ Icc 0 r, (∫ y in (0 : ℝ)..r, stripIntegrand F x y) ≤
      (∫ y in (0 : ℝ)..r, edgeTentCross r ε x y) + (∫ y in (0 : ℝ)..r, edgeTentCross r ε y x) +
        ∫ y in (0 : ℝ)..r, edgeTentTop r ε x y := fun x hx => by
    rw [← intervalIntegral.integral_add (hCi x hx) (hCi' x hx),
      ← intervalIntegral.integral_add ((hCi x hx).add (hCi' x hx)) (hTi x hx)]
    exact intervalIntegral.integral_mono_on hr0 (hgi x hx) (((hCi x hx).add (hCi' x hx)).add
      (hTi x hx)) fun y hy => stripIntegrand_edgeTentOdd_le_cross hε0 hε1 hεr hx hy
  have hT : stripBoxEnergy F 0 r ≤
      (∫ x in (0 : ℝ)..r, ∫ y in (0 : ℝ)..r, edgeTentCross r ε x y) +
        (∫ x in (0 : ℝ)..r, ∫ y in (0 : ℝ)..r, edgeTentCross r ε y x) +
          ∫ x in (0 : ℝ)..r, ∫ y in (0 : ℝ)..r, edgeTentTop r ε x y := by
    unfold stripBoxEnergy
    rw [← intervalIntegral.integral_add hCo hCo', ← intervalIntegral.integral_add (hCo.add hCo') hTo]
    exact intervalIntegral.integral_mono_on hr0 hgo ((hCo.add hCo').add hTo) hpt
  -- the swapped cross pairs have the same integral
  have hswap := integral_integral_swap_box hr0 hCm hCb
  -- the cross pairs: `≤ (½ log(4/ε) + 4/5) M + ε³/4`
  have hFi : IntervalIntegrable (fun x => F x ^ 2) volume 0 r :=
    ((continuous_edgeTentOdd r ε).pow 2).intervalIntegrable _ _
  have hlin : IntervalIntegrable (fun x => if r - ε < x then ε * (x - (r - ε)) / 2 else 0)
      volume 0 r :=
    intervalIntegrable_of_abs_le (C := ε * r) hr0
      (Measurable.ite (measurableSet_lt measurable_const measurable_id) (by fun_prop)
        measurable_const) fun x hx => by
        split_ifs
        · rw [abs_of_nonneg (by nlinarith [hx.1])]; nlinarith [hx.1, hx.2]
        · rw [abs_zero]; positivity
  have hcross : (∫ x in (0 : ℝ)..r, ∫ y in (0 : ℝ)..r, edgeTentCross r ε x y) ≤
      (Real.log (4 / ε) / 2 + 4 / 5) * M + ε ^ 3 / 4 := by
    have hmono := intervalIntegral.integral_mono_on hr0 hCo ((hFi.const_mul
      (Real.log (4 / ε) / 2 + 4 / 5)).add hlin) fun x hx => integral_edgeTentCross_le hε0 hε1 hεr hx
    rw [intervalIntegral.integral_add (hFi.const_mul _) hlin, intervalIntegral.integral_const_mul,
      integral_ite_lt (φ := fun x => ε * (x - (r - ε)) / 2) (by linarith) le_rfl] at hmono
    have hpoly : (∫ x in (r - ε)..r, ε * (x - (r - ε)) / 2) = ε ^ 3 / 4 := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_right (fun x => x) (r - ε), integral_id]
      ring
    rw [hpoly] at hmono
    exact hmono
  -- the pairs on the tent: `(ε/2 + ε²/4) ε²`
  have htop : (∫ x in (0 : ℝ)..r, ∫ y in (0 : ℝ)..r, edgeTentTop r ε x y) =
      (ε / 2 + ε ^ 2 / 4) * ε * ε := by
    have hin : ∀ x, (∫ y in (0 : ℝ)..r, edgeTentTop r ε x y) =
        if r - ε < x then (ε / 2 + ε ^ 2 / 4) * ε else 0 := fun x => by
      by_cases hx : r - ε < x
      · rw [if_pos hx]
        have e : (fun y => edgeTentTop r ε x y) = fun y => if r - ε < y then ε / 2 + ε ^ 2 / 4 else 0 :=
          funext fun y => by unfold edgeTentTop; by_cases hy : r - ε < y <;> simp [hx, hy]
        rw [e, integral_ite_lt (φ := fun _ => ε / 2 + ε ^ 2 / 4) (by linarith) (by linarith),
          intervalIntegral.integral_const, smul_eq_mul]
        ring
      · rw [if_neg hx]
        have e : (fun y => edgeTentTop r ε x y) = fun _ => (0 : ℝ) :=
          funext fun y => by unfold edgeTentTop; rw [if_neg fun h => hx h.1]
        rw [e, intervalIntegral.integral_zero]
    simp_rw [hin]
    rw [integral_ite_lt (φ := fun _ => (ε / 2 + ε ^ 2 / 4) * ε) (by linarith) le_rfl,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  -- the tent mass: `ε³ ≤ 32 M`
  have hmass := edgeTent_sq_integral_ge hε0 hεr (L := r) (by linarith)
  rw [sub_self] at hmass
  have hε3 : ε ^ 4 ≤ ε ^ 3 := by
    have := pow_le_pow_of_le_one hε0.le hε1 (show 3 ≤ 4 by norm_num); linarith
  rw [hswap] at hT
  nlinarith

/-- On every strip `[L − r, r]` with `r ≤ L ≤ 2(r − ε)` the odd part of the edge tent carries half its
mass: `∫_{L−r}^{r} α_L² = ½ ∫_0^r F²`. -/
theorem edgeTent_oddPart_eq_half_mass {r ε L : ℝ} (hε0 : 0 < ε) (hεr : ε < r) (hrL : r ≤ L)
    (hL : L ≤ 2 * (r - ε)) :
    (∫ a in (L - r)..r, reflectedOddPart (edgeTentOdd r ε) L a ^ 2) =
      (∫ x in (0 : ℝ)..r, edgeTentOdd r ε x ^ 2) / 2 := by
  obtain ⟨-, h⟩ := edgeTent_oddPart_eq hε0 hεr hrL hL
  have hFi : ∀ a b, IntervalIntegrable (fun x => edgeTentOdd r ε x ^ 2) volume a b := fun a b =>
    ((continuous_edgeTentOdd r ε).pow 2).intervalIntegrable _ _
  have hzero : (∫ x in (0 : ℝ)..(L - r), edgeTentOdd r ε x ^ 2) = 0 := by
    have e : (∫ x in (0 : ℝ)..(L - r), edgeTentOdd r ε x ^ 2) = ∫ _ in (0 : ℝ)..(L - r), (0 : ℝ) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
      rw [uIoc_of_le (by linarith)] at hx
      rw [edgeTentOdd_of_nonneg hεr hx.1.le, edgeTent_eq_zero_of_le (by linarith [hx.2])]
      norm_num
    rw [e, intervalIntegral.integral_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hFi 0 (L - r)) (hFi (L - r) r), hzero,
    zero_add]
  linarith

/-- **The capacity bound.** For any finite family of strips `[L_j − r, r]` with
`r ≤ L_j ≤ 2(r − ε)`, `0 < ε ≤ 1`, and weights `c_j ≥ 0` summing to more than `2 log(4/ε) + 84`, the
odd parts of the odd edge tent charged with these weights exceed the surplus of all pairs of the
support: `T(0, r) < Σ_j c_j ∫_{L_j − r}^{r} α_{L_j}²`. -/
theorem stripBoxEnergy_edgeTent_lt_sum_oddPart {ι : Type*} {r ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hεr : ε < r) (s : Finset ι) (L c : ι → ℝ) (hL : ∀ j ∈ s, r ≤ L j ∧ L j ≤ 2 * (r - ε))
    (hc : ∀ j ∈ s, 0 ≤ c j) (hsum : 2 * (Real.log (4 / ε) + 42) < ∑ j ∈ s, c j) :
    stripBoxEnergy (edgeTentOdd r ε) 0 r <
      ∑ j ∈ s, c j * ∫ a in (L j - r)..r, reflectedOddPart (edgeTentOdd r ε) (L j) a ^ 2 := by
  set M := ∫ x in (0 : ℝ)..r, edgeTentOdd r ε x ^ 2 with hM
  have hM0 : 0 < M := by
    have := edgeTent_sq_integral_ge hε0 hεr (L := r) (by linarith)
    rw [sub_self] at this
    have : 0 < ε ^ 3 / 32 := by positivity
    linarith
  have hT := stripBoxEnergy_edgeTent_le_log hε0 hε1 hεr
  have hterm : ∀ j ∈ s, c j * ∫ a in (L j - r)..r, reflectedOddPart (edgeTentOdd r ε) (L j) a ^ 2 =
      c j * (M / 2) := fun j hj => by
    rw [edgeTent_oddPart_eq_half_mass hε0 hεr (hL j hj).1 (hL j hj).2]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  nlinarith

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
