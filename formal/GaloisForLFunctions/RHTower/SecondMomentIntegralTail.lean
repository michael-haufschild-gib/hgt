import GaloisForLFunctions.RHTower.CCMHighRadialFirstRowBV

/-!
# A second-moment bound controls the far part of an integral

For `x ≠ 0` and any splitting weight `s > 0` the elementary inequality

`|f| ≤ (s / x² + x² f² / s) / 2`

holds, since it rearranges to `(s − x²|f|)² ≥ 0`.  Integrating it away from the origin turns a
bound on the second moment `∫ x² f²` into a bound on `∫ |f|` there, with the weight `s` free:

`|∫_K^R f| ≤ (s/K + M/s)/2` .

Choosing `s = √K` makes the right-hand side `O(K^{-1/2})`, so a family with a *uniform* second
moment has uniformly small far integrals.  This is what lets a norm-limit of such a family be
integrated term by term: the near part converges by Cauchy–Schwarz on a bounded window, and the far
part is uniformly negligible.
-/

open MeasureTheory Set

namespace RHTower

/-- **Weighted arithmetic–geometric split.**  Away from the origin, a function is dominated by a
free multiple of `1/x²` plus the reciprocal multiple of its second-moment density. -/
theorem abs_le_weighted_split {x s f : ℝ} (hs : 0 < s) (hx : x ≠ 0) :
    |f| ≤ (s / x ^ 2 + x ^ 2 * f ^ 2 / s) / 2 := by
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  have hf : f ^ 2 = |f| ^ 2 := (sq_abs f).symm
  rw [hf, ← sub_nonneg]
  have hid : (s / x ^ 2 + x ^ 2 * |f| ^ 2 / s) / 2 - |f|
      = (s - x ^ 2 * |f|) ^ 2 / (2 * x ^ 2 * s) := by
    field_simp
    ring
  rw [hid]
  positivity

/-- **Far-field bound from a second moment.**  On `[K, R]` with `K > 0`, a bound `M` on the second
moment `∫ x² f²` gives `|∫ f| ≤ (s/K + M/s)/2` for every splitting weight `s > 0`. -/
theorem abs_integral_le_of_secondMoment
    {f : ℝ → ℝ} {K R s M : ℝ} (hK : 0 < K) (hKR : K ≤ R) (hs : 0 < s)
    (hint : IntervalIntegrable f volume K R)
    (hint2 : IntervalIntegrable (fun x => x ^ 2 * f x ^ 2) volume K R)
    (hM : (∫ x in K..R, x ^ 2 * f x ^ 2) ≤ M) :
    |∫ x in K..R, f x| ≤ (s / K + M / s) / 2 := by
  have hinvsq : IntervalIntegrable (fun x : ℝ => 1 / x ^ 2) volume K R := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hKR]
    refine ContinuousOn.div continuousOn_const (continuousOn_pow 2) ?_
    intro x hx
    have : 0 < x := lt_of_lt_of_le hK hx.1
    positivity
  have hmaj : IntervalIntegrable
      (fun x : ℝ => (s / x ^ 2 + x ^ 2 * f x ^ 2 / s) / 2) volume K R := by
    have h1 : IntervalIntegrable (fun x : ℝ => s / x ^ 2) volume K R := by
      simpa [div_eq_mul_inv, mul_comm] using hinvsq.const_mul s
    have h2 : IntervalIntegrable (fun x : ℝ => x ^ 2 * f x ^ 2 / s) volume K R := by
      simpa [div_eq_mul_inv] using hint2.mul_const s⁻¹
    simpa [div_eq_mul_inv] using (h1.add h2).mul_const (2 : ℝ)⁻¹
  have habs : IntervalIntegrable (fun x => |f x|) volume K R := hint.abs
  have step1 : |∫ x in K..R, f x| ≤ ∫ x in K..R, |f x| :=
    intervalIntegral.abs_integral_le_integral_abs hKR
  have step2 : (∫ x in K..R, |f x|)
      ≤ ∫ x in K..R, (s / x ^ 2 + x ^ 2 * f x ^ 2 / s) / 2 := by
    refine intervalIntegral.integral_mono_on hKR habs hmaj ?_
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hK hx.1)
    exact abs_le_weighted_split hs hx0
  have hsplit : (∫ x in K..R, (s / x ^ 2 + x ^ 2 * f x ^ 2 / s) / 2)
      = (s * (∫ x in K..R, 1 / x ^ 2) + (∫ x in K..R, x ^ 2 * f x ^ 2) / s) / 2 := by
    have h1 : IntervalIntegrable (fun x : ℝ => s / x ^ 2) volume K R := by
      simpa [div_eq_mul_inv, mul_comm] using hinvsq.const_mul s
    have h2 : IntervalIntegrable (fun x : ℝ => x ^ 2 * f x ^ 2 / s) volume K R := by
      simpa [div_eq_mul_inv] using hint2.mul_const s⁻¹
    rw [show (fun x : ℝ => (s / x ^ 2 + x ^ 2 * f x ^ 2 / s) / 2)
        = fun x : ℝ => (s / x ^ 2 + x ^ 2 * f x ^ 2 / s) * (2 : ℝ)⁻¹ by
      funext x; ring]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_add h1 h2]
    have e1 : (∫ x in K..R, s / x ^ 2) = s * ∫ x in K..R, 1 / x ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext x
      ring
    have e2 : (∫ x in K..R, x ^ 2 * f x ^ 2 / s) = (∫ x in K..R, x ^ 2 * f x ^ 2) / s := by
      simp only [div_eq_mul_inv]
      rw [← intervalIntegral.integral_mul_const]
    rw [e1, e2]
    ring
  have hinv : (∫ x in K..R, 1 / x ^ 2) ≤ 1 / K :=
    GaloisForLFunctions.RHTower.integral_one_div_sq_le' hK hKR
  have hmono : (s * (∫ x in K..R, 1 / x ^ 2) + (∫ x in K..R, x ^ 2 * f x ^ 2) / s) / 2
      ≤ (s / K + M / s) / 2 := by
    have h1 : s * (∫ x in K..R, 1 / x ^ 2) ≤ s / K := by
      calc s * (∫ x in K..R, 1 / x ^ 2) ≤ s * (1 / K) :=
            mul_le_mul_of_nonneg_left hinv hs.le
        _ = s / K := by ring
    have h2 : (∫ x in K..R, x ^ 2 * f x ^ 2) / s ≤ M / s := by gcongr
    linarith
  calc |∫ x in K..R, f x| ≤ ∫ x in K..R, |f x| := step1
    _ ≤ ∫ x in K..R, (s / x ^ 2 + x ^ 2 * f x ^ 2 / s) / 2 := step2
    _ = (s * (∫ x in K..R, 1 / x ^ 2) + (∫ x in K..R, x ^ 2 * f x ^ 2) / s) / 2 := hsplit
    _ ≤ (s / K + M / s) / 2 := hmono

/-- With the balanced weight `s = √K` the far-field bound decays like `K^{-1/2}`. -/
theorem abs_integral_le_of_secondMoment_sqrt
    {f : ℝ → ℝ} {K R M : ℝ} (hK : 0 < K) (hKR : K ≤ R)
    (hint : IntervalIntegrable f volume K R)
    (hint2 : IntervalIntegrable (fun x => x ^ 2 * f x ^ 2) volume K R)
    (hM : (∫ x in K..R, x ^ 2 * f x ^ 2) ≤ M) :
    |∫ x in K..R, f x| ≤ (1 + M) / (2 * Real.sqrt K) := by
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hbase := abs_integral_le_of_secondMoment hK hKR hsK hint hint2 hM
  have hsq : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK.le
  have hrw : (Real.sqrt K / K + M / Real.sqrt K) / 2 = (1 + M) / (2 * Real.sqrt K) := by
    field_simp
    nlinarith [hsq]
  rwa [hrw] at hbase

/-- **Near-window bound.**  On a bounded window the same split with `x = 1` turns a bound on
`∫ f²` into a bound on `|∫ f|`, with the weight `s` free. -/
theorem abs_integral_le_of_sq
    {f : ℝ → ℝ} {a b s D : ℝ} (hab : a ≤ b) (hs : 0 < s)
    (hint : IntervalIntegrable f volume a b)
    (hint2 : IntervalIntegrable (fun x => f x ^ 2) volume a b)
    (hD : (∫ x in a..b, f x ^ 2) ≤ D) :
    |∫ x in a..b, f x| ≤ ((b - a) * s + D / s) / 2 := by
  have hmaj : IntervalIntegrable (fun x : ℝ => (s + f x ^ 2 / s) / 2) volume a b := by
    have h2 : IntervalIntegrable (fun x : ℝ => f x ^ 2 / s) volume a b := by
      simpa [div_eq_mul_inv] using hint2.mul_const s⁻¹
    simpa [div_eq_mul_inv] using
      ((intervalIntegrable_const (c := s)).add h2).mul_const (2 : ℝ)⁻¹
  have habs : IntervalIntegrable (fun x => |f x|) volume a b := hint.abs
  have step1 : |∫ x in a..b, f x| ≤ ∫ x in a..b, |f x| :=
    intervalIntegral.abs_integral_le_integral_abs hab
  have step2 : (∫ x in a..b, |f x|) ≤ ∫ x in a..b, (s + f x ^ 2 / s) / 2 := by
    refine intervalIntegral.integral_mono_on hab habs hmaj ?_
    intro x _
    have := abs_le_weighted_split (x := (1 : ℝ)) (s := s) (f := f x) hs one_ne_zero
    simpa using this
  have hsplit : (∫ x in a..b, (s + f x ^ 2 / s) / 2)
      = ((b - a) * s + (∫ x in a..b, f x ^ 2) / s) / 2 := by
    have h2 : IntervalIntegrable (fun x : ℝ => f x ^ 2 / s) volume a b := by
      simpa [div_eq_mul_inv] using hint2.mul_const s⁻¹
    rw [show (fun x : ℝ => (s + f x ^ 2 / s) / 2)
        = fun x : ℝ => (s + f x ^ 2 / s) * (2 : ℝ)⁻¹ by funext x; ring]
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_add intervalIntegrable_const h2,
      intervalIntegral.integral_const]
    have e2 : (∫ x in a..b, f x ^ 2 / s) = (∫ x in a..b, f x ^ 2) / s := by
      simp only [div_eq_mul_inv]
      rw [← intervalIntegral.integral_mul_const]
    rw [e2, smul_eq_mul]
    ring
  have hfin : ((b - a) * s + (∫ x in a..b, f x ^ 2) / s) / 2 ≤ ((b - a) * s + D / s) / 2 := by
    have : (∫ x in a..b, f x ^ 2) / s ≤ D / s := by gcongr
    linarith
  calc |∫ x in a..b, f x| ≤ ∫ x in a..b, |f x| := step1
    _ ≤ ∫ x in a..b, (s + f x ^ 2 / s) / 2 := step2
    _ = ((b - a) * s + (∫ x in a..b, f x ^ 2) / s) / 2 := hsplit
    _ ≤ ((b - a) * s + D / s) / 2 := hfin

/-- A nonnegative integrand's integral over an interval never exceeds its integral over the line. -/
theorem intervalIntegral_le_integral_of_nonneg
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ x in a..b, f x) ≤ ∫ x, f x := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_le_integral hf (Filter.Eventually.of_forall hf0)

/-- **Whole-line bound.**  For an even function, a bound `D` on `∫ f²` and a bound `M` on the second
moment `∫ x² f²` give, for every window `K > 0` and weight `s > 0`,

`|∫ f| ≤ (2Ks + D/s)/2 + (1+M)/√K` .

The near window is controlled by `D` with the weight `s` free, and the two far tails — equal by
evenness — by the second moment. -/
theorem abs_integral_le_of_sq_and_secondMoment
    {g : ℝ → ℝ} {K s D M : ℝ} (hK : 0 < K) (hs : 0 < s)
    (heven : ∀ x, g (-x) = g x)
    (hg : Integrable g) (hg2 : Integrable fun x => g x ^ 2)
    (hgm : Integrable fun x => x ^ 2 * g x ^ 2)
    (hD : (∫ x, g x ^ 2) ≤ D) (hM : (∫ x, x ^ 2 * g x ^ 2) ≤ M) :
    |∫ x, g x| ≤ (2 * K * s + D / s) / 2 + (1 + M) / Real.sqrt K := by
  set Bd : ℝ := (2 * K * s + D / s) / 2 + (1 + M) / Real.sqrt K with hBd
  -- uniform bound on symmetric truncations
  have hunif : ∀ R : ℝ, K ≤ R → |∫ x in (-R)..R, g x| ≤ Bd := by
    intro R hKR
    have hKR' : (-K : ℝ) ≤ K := by linarith
    have hsplit1 : (∫ x in (-R)..R, g x)
        = (∫ x in (-R)..(-K), g x) + (∫ x in (-K)..R, g x) :=
      (intervalIntegral.integral_add_adjacent_intervals
        hg.intervalIntegrable hg.intervalIntegrable).symm
    have hsplit2 : (∫ x in (-K)..R, g x)
        = (∫ x in (-K)..K, g x) + (∫ x in K..R, g x) :=
      (intervalIntegral.integral_add_adjacent_intervals
        hg.intervalIntegrable hg.intervalIntegrable).symm
    -- the two tails agree by evenness
    have hmirror : (∫ x in (-R)..(-K), g x) = ∫ x in K..R, g x := by
      have := intervalIntegral.integral_comp_neg (a := K) (b := R) (f := g)
      calc (∫ x in (-R)..(-K), g x) = ∫ x in K..R, g (-x) := this.symm
        _ = ∫ x in K..R, g x := by
            refine intervalIntegral.integral_congr ?_
            intro x _
            exact heven x
    -- near window
    have hnear : |∫ x in (-K)..K, g x| ≤ (2 * K * s + D / s) / 2 := by
      have hDle : (∫ x in (-K)..K, g x ^ 2) ≤ D :=
        le_trans (intervalIntegral_le_integral_of_nonneg hKR' hg2 fun x => sq_nonneg _) hD
      have := abs_integral_le_of_sq (f := g) (a := -K) (b := K) (s := s) (D := D)
        hKR' hs hg.intervalIntegrable hg2.intervalIntegrable hDle
      have hrw : (K - (-K)) * s = 2 * K * s := by ring
      rwa [hrw] at this
    -- far tail
    have hfar : |∫ x in K..R, g x| ≤ (1 + M) / (2 * Real.sqrt K) := by
      have hMle : (∫ x in K..R, x ^ 2 * g x ^ 2) ≤ M :=
        le_trans (intervalIntegral_le_integral_of_nonneg hKR hgm
          fun x => by positivity) hM
      exact abs_integral_le_of_secondMoment_sqrt hK hKR hg.intervalIntegrable
        hgm.intervalIntegrable hMle
    have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
    have htwo : (1 + M) / (2 * Real.sqrt K) + (1 + M) / (2 * Real.sqrt K)
        = (1 + M) / Real.sqrt K := by
      field_simp
      ring
    rw [hsplit1, hsplit2, hmirror, hBd]
    calc |(∫ x in K..R, g x) + ((∫ x in (-K)..K, g x) + ∫ x in K..R, g x)|
        ≤ |∫ x in K..R, g x| + |(∫ x in (-K)..K, g x) + ∫ x in K..R, g x| := abs_add_le _ _
      _ ≤ |∫ x in K..R, g x| + (|∫ x in (-K)..K, g x| + |∫ x in K..R, g x|) := by
          gcongr
          exact abs_add_le _ _
      _ ≤ (1 + M) / (2 * Real.sqrt K)
            + ((2 * K * s + D / s) / 2 + (1 + M) / (2 * Real.sqrt K)) := by
          gcongr
      _ = (2 * K * s + D / s) / 2 + (1 + M) / Real.sqrt K := by rw [← htwo]; ring
  -- pass to the limit `R → ∞`
  have hlim : Filter.Tendsto (fun R : ℝ => ∫ x in (-R)..R, g x) Filter.atTop
      (nhds (∫ x, g x)) :=
    MeasureTheory.intervalIntegral_tendsto_integral hg
      (Filter.tendsto_neg_atBot_iff.2 Filter.tendsto_id) Filter.tendsto_id
  have hlimabs : Filter.Tendsto (fun R : ℝ => |∫ x in (-R)..R, g x|) Filter.atTop
      (nhds |∫ x, g x|) := hlim.abs
  refine le_of_tendsto hlimabs ?_
  filter_upwards [Filter.eventually_ge_atTop K] with R hR
  exact hunif R hR

/-- **Integrals follow `L²` limits under a uniform second moment.**  If a family of even functions
tends to zero in `L²` while its second moments stay bounded by a single constant, its integrals tend
to zero.  Without the moment bound the mass could escape to infinity while the `L²` norm vanishes. -/
theorem tendsto_integral_of_tendsto_sq_of_secondMoment
    {ι : Type*} {L : Filter ι} {g : ι → ℝ → ℝ} {M : ℝ}
    (heven : ∀ i x, g i (-x) = g i x)
    (hg : ∀ i, Integrable (g i)) (hg2 : ∀ i, Integrable fun x => (g i x) ^ 2)
    (hgm : ∀ i, Integrable fun x => x ^ 2 * (g i x) ^ 2)
    (hM : ∀ i, (∫ x, x ^ 2 * (g i x) ^ 2) ≤ M)
    (hD : Filter.Tendsto (fun i => ∫ x, (g i x) ^ 2) L (nhds 0)) :
    Filter.Tendsto (fun i => ∫ x, g i x) L (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- choose the window so the far part is below `ε/3`
  obtain ⟨K, hKpos, hKfar⟩ : ∃ K : ℝ, 0 < K ∧ (1 + |M|) / Real.sqrt K < ε / 3 := by
    set c : ℝ := 3 * (1 + |M|) / ε with hc
    have hcnn : (0 : ℝ) ≤ c := by rw [hc]; positivity
    obtain ⟨N, hN⟩ := exists_nat_gt (c ^ 2 + 1)
    have hNpos : (0 : ℝ) < N := by nlinarith [sq_nonneg c]
    refine ⟨(N : ℝ), hNpos, ?_⟩
    have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
    have hsq : c < Real.sqrt (N : ℝ) := by
      rw [show c = |c| from (abs_of_nonneg hcnn).symm]
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
    have hce : c * ε = 3 * (1 + |M|) := by rw [hc]; field_simp
    have hkey : 3 * (1 + |M|) < Real.sqrt (N : ℝ) * ε := by
      have := mul_lt_mul_of_pos_right hsq hε
      rwa [hce] at this
    rw [div_lt_div_iff₀ hsN (by norm_num : (0 : ℝ) < 3)]
    nlinarith [hkey]
  -- choose the near weight so the constant part is below `ε/3`
  obtain ⟨s, hspos, hsnear⟩ : ∃ s : ℝ, 0 < s ∧ K * s < ε / 3 := by
    refine ⟨ε / (6 * K), by positivity, ?_⟩
    have hKne : K ≠ 0 := ne_of_gt hKpos
    have hid : K * (ε / (6 * K)) = ε / 6 := by field_simp
    rw [hid]
    linarith
  have hfinal : ∀ᶠ i in L, (∫ x, (g i x) ^ 2) / (2 * s) < ε / 3 := by
    have hpos : (0 : ℝ) < 2 * s := by positivity
    have hgoal : Filter.Tendsto (fun i => (∫ x, (g i x) ^ 2) / (2 * s)) L (nhds 0) := by
      have := hD.div_const (2 * s)
      simpa using this
    exact hgoal.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [hfinal] with i hi
  have hMi : (∫ x, x ^ 2 * (g i x) ^ 2) ≤ |M| := le_trans (hM i) (le_abs_self M)
  have hbase := abs_integral_le_of_sq_and_secondMoment (g := g i) (K := K) (s := s)
    (D := ∫ x, (g i x) ^ 2) (M := |M|) hKpos hspos (heven i) (hg i) (hg2 i) (hgm i)
    le_rfl hMi
  rw [Real.dist_eq, sub_zero]
  have hrw : (2 * K * s + (∫ x, (g i x) ^ 2) / s) / 2
      = K * s + (∫ x, (g i x) ^ 2) / (2 * s) := by
    field_simp
  rw [hrw] at hbase
  linarith

end RHTower
