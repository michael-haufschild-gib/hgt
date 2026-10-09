import GaloisForLFunctions.HTGeometry.ThetaSumPeriodParseval

/-!
# First-order filters vanishing at two scales

Let `ψ′ = a(ψ − F)`.

* **Grönwall from one zero** (`sq_le_of_firstOrder_zero`, `exp_mul_sq_le_of_firstOrder_zero`): if
  `ψ(q) = 0` with `q ≤ x ≤ q + r`, then `ψ(x)² ≤ a²e^{2|a|r}·r·∫_{x−r}^x F²`, with an `e^{βr}` loss
  when the square carries a weight `e^{βx}`.
* **Window averaging** (`integral_integral_window_le`): `∫_X^Y∫_{x−r}^x H ≤ r∫_{X−r}^Y H` for
  measurable `H ≥ 0`, by the substitution `y = x − s` and a swap on `[X, Y] × [0, r]`.
* **Two radii** (`integral_exp_mul_sq_le_two_radius`): `ψ` vanishes within `r_s` to the left of
  every point of a set `G`, and within `r_l` everywhere. If `B ⊇ [x − r_l, x]` for every `x ∉ G`, then
  `∫_X^Y e^{βx}ψ² ≤ K(r_s²∫e^{βy}F² + r_l²∫1_B e^{βy}F²)`.
* **Few zeros force a flat stretch** (`exists_flat_stretch_of_count_le_one`,
  `quarter_le_integral_flat`): a monotone integer counting function `N` that increases by at most
  `1` on `(x − r_s, x]` is constant on `(t, t + r_s/4]` for every `t` in a stretch of length `r_s/4`.
* **Bad-set measure** (`integral_indicator_bad_le`): for `B = {y : |E ∩ [y − r_s, y + r_l]| ≥ r_s/4}`,
  `(r_s/4)|B ∩ [X, Y]| ≤ (r_s + r_l)|E ∩ [X − r_s, Y + r_l]|`.

These are the deterministic parts of the degree-one LP-maximality argument. A first-order LP
preimage of Ξ vanishes in every gap between zeros of Ξ. The short gaps cost `r_s²`. The long gaps
are confined to a set controlled by the zero-free stretches of the zero counting function.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **Grönwall from one zero.** If `ψ′ = a(ψ − F)` and `ψ(q) = 0` with `q ≤ x ≤ q + r`, then
`ψ(x)² ≤ a²e^{2|a|r}·r·∫_{x−r}^x F²`. -/
theorem sq_le_of_firstOrder_zero {ψ F : ℝ → ℝ} {a : ℝ}
    (hψ : ∀ t, HasDerivAt ψ (a * (ψ t - F t)) t) (hF : Continuous F) {q x r : ℝ}
    (hqx : q ≤ x) (hxr : x ≤ q + r) (hq : ψ q = 0) :
    ψ x ^ 2 ≤ a ^ 2 * Real.exp (2 * |a| * r) * r * ∫ t in x - r..x, F t ^ 2 := by
  have hr : 0 ≤ r := by linarith
  -- `e^{-at}ψ(t)` has derivative `-a e^{-at} F(t)`
  have hd : ∀ t, HasDerivAt (fun t => Real.exp (-a * t) * ψ t) (-a * (Real.exp (-a * t) * F t)) t := by
    intro t
    have h1 : HasDerivAt (fun t => Real.exp (-a * t)) (Real.exp (-a * t) * (-a)) t := by
      have := (Real.hasDerivAt_exp (-a * t)).comp t ((hasDerivAt_id t).const_mul (-a))
      simpa [Function.comp_def] using this
    refine (h1.mul (hψ t)).congr_deriv ?_
    ring
  have hcont : Continuous fun t => -a * (Real.exp (-a * t) * F t) := by fun_prop
  have hFTC : Real.exp (-a * x) * ψ x - Real.exp (-a * q) * ψ q =
      ∫ t in q..x, -a * (Real.exp (-a * t) * F t) :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      (hcont.intervalIntegrable _ _)).symm
  rw [hq, mul_zero, sub_zero] at hFTC
  have hψx : ψ x = ∫ t in q..x, -a * (Real.exp (a * (x - t)) * F t) := by
    have hpos : Real.exp (-a * x) ≠ 0 := (Real.exp_pos _).ne'
    have : ψ x = Real.exp (a * x) * (Real.exp (-a * x) * ψ x) := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [this, hFTC, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [show a * (x - t) = a * x + -a * t by ring, Real.exp_add]; ring
  -- `|ψ x| ≤ |a| e^{|a| r} ∫_q^x |F|`
  have habs : |ψ x| ≤ |a| * Real.exp (|a| * r) * ∫ t in q..x, |F t| := by
    rw [hψx]
    refine (intervalIntegral.abs_integral_le_integral_abs hqx).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hqx ((by fun_prop : Continuous fun t =>
        |-a * (Real.exp (a * (x - t)) * F t)|).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t => |a| * Real.exp (|a| * r) * |F t|).intervalIntegrable _ _)
      fun t ht => ?_
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
    have : Real.exp (a * (x - t)) ≤ Real.exp (|a| * r) := by
      apply Real.exp_le_exp.mpr
      have h1 : a * (x - t) ≤ |a| * (x - t) :=
        mul_le_mul_of_nonneg_right (le_abs_self a) (by linarith [ht.2])
      have h2 : |a| * (x - t) ≤ |a| * r :=
        mul_le_mul_of_nonneg_left (by linarith [ht.1]) (abs_nonneg a)
      linarith
    have hF0 := abs_nonneg (F t)
    have ha0 := abs_nonneg a
    calc |a| * (Real.exp (a * (x - t)) * |F t|) ≤ |a| * (Real.exp (|a| * r) * |F t|) := by gcongr
      _ = |a| * Real.exp (|a| * r) * |F t| := by ring
  -- Cauchy–Schwarz
  have hCS := sq_integral_le_mul_integral_sq hqx (g := fun t => |F t|)
    (continuous_abs.comp hF).continuousOn
  have hI : 0 ≤ ∫ t in q..x, |F t| := intervalIntegral.integral_nonneg hqx fun _ _ => abs_nonneg _
  have hmono : ∫ t in q..x, |F t| ^ 2 ≤ ∫ t in x - r..x, F t ^ 2 := by
    have : (fun t => |F t| ^ 2) = fun t => F t ^ 2 := funext fun t => sq_abs _
    rw [this]
    exact intervalIntegral.integral_mono_interval (by linarith) hqx le_rfl
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      ((hF.pow 2).intervalIntegrable _ _)
  have hsq : ψ x ^ 2 ≤ (|a| * Real.exp (|a| * r)) ^ 2 * (∫ t in q..x, |F t|) ^ 2 := by
    rw [← mul_pow, ← sq_abs (ψ x)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have he : (|a| * Real.exp (|a| * r)) ^ 2 = a ^ 2 * Real.exp (2 * |a| * r) := by
    rw [mul_pow, sq_abs, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  rw [he] at hsq
  have hxq : x - q ≤ r := by linarith
  calc ψ x ^ 2 ≤ a ^ 2 * Real.exp (2 * |a| * r) * (∫ t in q..x, |F t|) ^ 2 := hsq
    _ ≤ a ^ 2 * Real.exp (2 * |a| * r) * ((x - q) * ∫ t in q..x, |F t| ^ 2) := by gcongr
    _ ≤ a ^ 2 * Real.exp (2 * |a| * r) * (r * ∫ t in x - r..x, F t ^ 2) := by
        have h0 : 0 ≤ ∫ t in q..x, |F t| ^ 2 :=
          intervalIntegral.integral_nonneg hqx fun _ _ => sq_nonneg _
        gcongr
    _ = a ^ 2 * Real.exp (2 * |a| * r) * r * ∫ t in x - r..x, F t ^ 2 := by ring


/-- **Window averaging.** For a measurable `H ≥ 0`, bounded on `[X − r, Y]`,
`∫_X^Y ∫_{x−r}^x H(y)dy dx ≤ r ∫_{X−r}^Y H`. -/
theorem integral_integral_window_le {H : ℝ → ℝ} (hHm : Measurable H) (hH0 : ∀ y, 0 ≤ H y)
    {X Y r M : ℝ} (hXY : X ≤ Y) (hr : 0 ≤ r) (hHb : ∀ y ∈ Icc (X - r) Y, H y ≤ M) :
    ∫ x in X..Y, (∫ y in x - r..x, H y) ≤ r * ∫ y in X - r..Y, H y := by
  have hM : 0 ≤ M := le_trans (hH0 (X - r)) (hHb _ ⟨le_rfl, by linarith⟩)
  have hHi : ∀ a b, X - r ≤ a → a ≤ b → b ≤ Y → IntervalIntegrable H volume a b := by
    intro a b ha hab hb
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 ?_
    refine Measure.integrableOn_of_bounded (M := M) (by simp) hHm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hH0 y)]
    exact hHb y ⟨by linarith [hy.1], by linarith [hy.2]⟩
  -- substitute `y = x − s`
  have hsub : ∀ x, ∫ y in x - r..x, H y = ∫ s in (0 : ℝ)..r, H (x - s) := by
    intro x
    rw [intervalIntegral.integral_comp_sub_left (fun y => H y) x]
    simp
  simp_rw [hsub]
  -- swap the order on the rectangle `[X, Y] × [0, r]`
  have hint : Integrable (Function.uncurry fun x s => H (x - s))
      ((volume.restrict (Set.uIoc X Y)).prod (volume.restrict (Set.uIoc 0 r))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    refine Measure.integrableOn_of_bounded (M := M) ?_ ?_ ?_
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      exact ENNReal.mul_ne_top (by simp) (by simp)
    · exact (hHm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
    · refine (ae_restrict_iff' (measurableSet_uIoc.prod measurableSet_uIoc)).2
        (Filter.Eventually.of_forall fun p hp => ?_)
      rw [Set.uIoc_of_le hXY, Set.uIoc_of_le hr] at hp
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp
      show ‖H (p.1 - p.2)‖ ≤ M
      rw [Real.norm_eq_abs, abs_of_nonneg (hH0 _)]
      exact hHb _ ⟨by linarith, by linarith⟩
  have hswap := intervalIntegral_integral_swap (μ := volume.restrict (Set.uIoc 0 r)) hint
  have hleft : ∫ x in X..Y, ∫ s in (0 : ℝ)..r, H (x - s) =
      ∫ x in X..Y, ∫ s, H (x - s) ∂(volume.restrict (Set.uIoc 0 r)) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [intervalIntegral.integral_of_le hr, Set.uIoc_of_le hr]
  rw [hleft, hswap]
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) r, ∫ x in X..Y, H (x - s) ≤ ∫ y in X - r..Y, H y := by
    intro s hs
    rw [Set.uIoc_of_le hr] at hs
    rw [intervalIntegral.integral_comp_sub_right (fun y => H y) s]
    exact intervalIntegral.integral_mono_interval (by linarith [hs.2]) (by linarith)
      (by linarith [hs.1]) (Filter.Eventually.of_forall fun y => hH0 y)
      (hHi _ _ le_rfl (by linarith) le_rfl)
  have hint1 : Integrable (fun s => ∫ x in X..Y, H (x - s)) (volume.restrict (Set.uIoc 0 r)) := by
    refine hint.integral_prod_right.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [intervalIntegral.integral_of_le hXY, Set.uIoc_of_le hXY]
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) r)) := by
    rw [Set.uIoc_of_le hr]; infer_instance
  calc ∫ s, (∫ x in X..Y, H (x - s)) ∂(volume.restrict (Set.uIoc 0 r))
      ≤ ∫ s, (∫ y in X - r..Y, H y) ∂(volume.restrict (Set.uIoc 0 r)) :=
        integral_mono_ae hint1 (integrable_const _)
          ((ae_restrict_iff' measurableSet_uIoc).2 (Filter.Eventually.of_forall hbound))
    _ = r * ∫ y in X - r..Y, H y := by
        rw [integral_const, smul_eq_mul, Set.uIoc_of_le hr, measureReal_restrict_apply_univ,
          Real.volume_real_Ioc_of_le hr, sub_zero]


/-- Weighted form of `sq_le_of_firstOrder_zero`: `e^{βx}ψ(x)² ≤ a²e^{2|a|r}e^{βr}·r·∫_{x−r}^x e^{βy}F²`. -/
theorem exp_mul_sq_le_of_firstOrder_zero {ψ F : ℝ → ℝ} {a β : ℝ}
    (hψ : ∀ t, HasDerivAt ψ (a * (ψ t - F t)) t) (hF : Continuous F) (hβ : 0 ≤ β) {q x r : ℝ}
    (hqx : q ≤ x) (hxr : x ≤ q + r) (hq : ψ q = 0) :
    Real.exp (β * x) * ψ x ^ 2 ≤ a ^ 2 * Real.exp (2 * |a| * r) * Real.exp (β * r) * r *
      ∫ y in x - r..x, Real.exp (β * y) * F y ^ 2 := by
  have hr : 0 ≤ r := by linarith
  have h1 := sq_le_of_firstOrder_zero hψ hF hqx hxr hq
  have h2 : Real.exp (β * x) * ∫ y in x - r..x, F y ^ 2 ≤
      Real.exp (β * r) * ∫ y in x - r..x, Real.exp (β * y) * F y ^ 2 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith)
      ((by fun_prop : Continuous fun y => Real.exp (β * x) * F y ^ 2).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun y => Real.exp (β * r) * (Real.exp (β * y) * F y ^ 2)).intervalIntegrable _ _)
      fun y hy => ?_
    have : Real.exp (β * x) ≤ Real.exp (β * r) * Real.exp (β * y) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
      nlinarith [hy.1]
    calc Real.exp (β * x) * F y ^ 2 ≤ (Real.exp (β * r) * Real.exp (β * y)) * F y ^ 2 := by
          gcongr
      _ = Real.exp (β * r) * (Real.exp (β * y) * F y ^ 2) := by ring
  have hex := Real.exp_pos (β * x)
  calc Real.exp (β * x) * ψ x ^ 2
      ≤ Real.exp (β * x) * (a ^ 2 * Real.exp (2 * |a| * r) * r * ∫ t in x - r..x, F t ^ 2) := by
        gcongr
    _ = a ^ 2 * Real.exp (2 * |a| * r) * r * (Real.exp (β * x) * ∫ t in x - r..x, F t ^ 2) := by
        ring
    _ ≤ a ^ 2 * Real.exp (2 * |a| * r) * r *
          (Real.exp (β * r) * ∫ y in x - r..x, Real.exp (β * y) * F y ^ 2) := by gcongr
    _ = _ := by ring

theorem continuous_integral_window {g : ℝ → ℝ} (hg : ∀ a b, IntervalIntegrable g volume a b) (r : ℝ) :
    Continuous fun x => ∫ y in x - r..x, g y := by
  have hP : Continuous fun x => ∫ y in (0 : ℝ)..x, g y :=
    intervalIntegral.continuous_primitive hg 0
  have : (fun x => ∫ y in x - r..x, g y) =
      fun x => (∫ y in (0 : ℝ)..x, g y) - ∫ y in (0 : ℝ)..(x - r), g y := by
    funext x
    rw [intervalIntegral.integral_interval_sub_left (hg _ _) (hg _ _)]
  rw [this]
  exact hP.sub (hP.comp (continuous_id.sub continuous_const))

/-- **Two-radius Grönwall.** Let `ψ′ = a(ψ − F)`. Suppose `ψ` vanishes within `r_s` to the left of
every point of `G ∩ [X, Y]`, and within `r_l` to the left of every point of `[X, Y]`, and
`B ⊇ [x − r_l, x]` for every `x ∈ [X, Y] ∖ G`. Then
`∫_X^Y e^{βx}ψ² ≤ a²e^{2|a|r_l}e^{βr_l}(r_s²∫_{X−r_l}^Y e^{βy}F² + r_l²∫_{X−r_l}^Y 1_B e^{βy}F²)`. -/
theorem integral_exp_mul_sq_le_two_radius {ψ F : ℝ → ℝ} {a β rs rl X Y : ℝ}
    (hψ : ∀ t, HasDerivAt ψ (a * (ψ t - F t)) t) (hF : Continuous F) (hβ : 0 ≤ β)
    (hrs : 0 ≤ rs) (hrl : rs ≤ rl) (hXY : X ≤ Y) {G B : Set ℝ} (hBm : MeasurableSet B)
    (hG : ∀ x ∈ Icc X Y, x ∈ G → ∃ q ∈ Icc (x - rs) x, ψ q = 0)
    (hall : ∀ x ∈ Icc X Y, ∃ q ∈ Icc (x - rl) x, ψ q = 0)
    (hB : ∀ x ∈ Icc X Y, x ∉ G → ∀ y ∈ Icc (x - rl) x, y ∈ B) :
    ∫ x in X..Y, Real.exp (β * x) * ψ x ^ 2 ≤
      a ^ 2 * Real.exp (2 * |a| * rl) * Real.exp (β * rl) *
        (rs ^ 2 * (∫ y in X - rl..Y, Real.exp (β * y) * F y ^ 2) +
          rl ^ 2 * ∫ y in X - rl..Y, B.indicator (fun y => Real.exp (β * y) * F y ^ 2) y) := by
  set H : ℝ → ℝ := fun y => Real.exp (β * y) * F y ^ 2 with hH_def
  set HB : ℝ → ℝ := B.indicator H with hHB_def
  have hHc : Continuous H := by rw [hH_def]; fun_prop
  have hH0 : ∀ y, 0 ≤ H y := fun y => by rw [hH_def]; positivity
  have hHB0 : ∀ y, 0 ≤ HB y := fun y => Set.indicator_nonneg (fun y _ => hH0 y) y
  have hHBm : Measurable HB := hHc.measurable.indicator hBm
  have hHBle : ∀ y, HB y ≤ H y := fun y => Set.indicator_le_self' (fun y _ => hH0 y) y
  have hHi : ∀ a b, IntervalIntegrable H volume a b := fun a b => hHc.intervalIntegrable a b
  have hHBi : ∀ a b, IntervalIntegrable HB volume a b := fun a b =>
    (hHi a b).mono_fun' hHBm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        show ‖HB y‖ ≤ H y
        rw [Real.norm_eq_abs, abs_of_nonneg (hHB0 y)]; exact hHBle y)
  set K : ℝ := a ^ 2 * Real.exp (2 * |a| * rl) * Real.exp (β * rl) with hK_def
  have hK : 0 ≤ K := by rw [hK_def]; positivity
  have hpt : ∀ x ∈ Icc X Y, Real.exp (β * x) * ψ x ^ 2 ≤
      K * (rs * (∫ y in x - rs..x, H y) + rl * ∫ y in x - rl..x, HB y) := by
    intro x hx
    have hIs : 0 ≤ ∫ y in x - rs..x, H y :=
      intervalIntegral.integral_nonneg (by linarith) fun y _ => hH0 y
    have hIl : 0 ≤ ∫ y in x - rl..x, HB y :=
      intervalIntegral.integral_nonneg (by linarith) fun y _ => hHB0 y
    by_cases hxG : x ∈ G
    · obtain ⟨q, hq, hq0⟩ := hG x hx hxG
      have h := exp_mul_sq_le_of_firstOrder_zero (r := rs) hψ hF hβ hq.2 (by linarith [hq.1]) hq0
      have e1 : Real.exp (2 * |a| * rs) ≤ Real.exp (2 * |a| * rl) :=
        Real.exp_le_exp.mpr (by nlinarith [abs_nonneg a])
      have e2 : Real.exp (β * rs) ≤ Real.exp (β * rl) := Real.exp_le_exp.mpr (by nlinarith)
      calc Real.exp (β * x) * ψ x ^ 2
          ≤ a ^ 2 * Real.exp (2 * |a| * rs) * Real.exp (β * rs) * rs * ∫ y in x - rs..x, H y := h
        _ ≤ K * (rs * ∫ y in x - rs..x, H y) := by
            rw [hK_def]
            have : a ^ 2 * Real.exp (2 * |a| * rs) * Real.exp (β * rs) ≤
                a ^ 2 * Real.exp (2 * |a| * rl) * Real.exp (β * rl) := by gcongr
            nlinarith [mul_nonneg hrs hIs]
        _ ≤ K * (rs * (∫ y in x - rs..x, H y) + rl * ∫ y in x - rl..x, HB y) := by
            gcongr
            nlinarith [hIl]
    · obtain ⟨q, hq, hq0⟩ := hall x hx
      have h := exp_mul_sq_le_of_firstOrder_zero (r := rl) hψ hF hβ hq.2 (by linarith [hq.1]) hq0
      have hHBeq : ∫ y in x - rl..x, HB y = ∫ y in x - rl..x, H y := by
        refine intervalIntegral.integral_congr fun y hy => ?_
        rw [Set.uIcc_of_le (by linarith)] at hy
        simp only [hHB_def]
        rw [Set.indicator_of_mem (hB x hx hxG y hy)]
      calc Real.exp (β * x) * ψ x ^ 2
          ≤ K * rl * ∫ y in x - rl..x, H y := h
        _ = K * (rl * ∫ y in x - rl..x, HB y) := by rw [hHBeq]; ring
        _ ≤ K * (rs * (∫ y in x - rs..x, H y) + rl * ∫ y in x - rl..x, HB y) := by
            gcongr
            nlinarith [mul_nonneg hrs hIs]
  have hcs := continuous_integral_window hHi rs
  have hcl := continuous_integral_window hHBi rl
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun t => (hψ t).continuousAt
  have hmono := intervalIntegral.integral_mono_on hXY
    ((by fun_prop : Continuous fun x => Real.exp (β * x) * ψ x ^ 2).intervalIntegrable
      (μ := volume) _ _)
    (((hcs.const_mul rs).add (hcl.const_mul rl)).const_mul K |>.intervalIntegrable
      (μ := volume) _ _) hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  simp only [Pi.add_apply] at hmono
  rw [intervalIntegral.integral_add
    ((hcs.const_mul rs).intervalIntegrable (μ := volume) _ _)
    ((hcl.const_mul rl).intervalIntegrable (μ := volume) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  have hMs : ∀ y ∈ Icc (X - rs) Y, H y ≤ (sSup (H '' Icc (X - rl) Y)) := by
    intro y hy
    exact le_csSup ((isCompact_Icc.image hHc).bddAbove) ⟨y, ⟨by linarith [hy.1], hy.2⟩, rfl⟩
  have hMl : ∀ y ∈ Icc (X - rl) Y, HB y ≤ (sSup (H '' Icc (X - rl) Y)) := by
    intro y hy
    exact (hHBle y).trans (le_csSup ((isCompact_Icc.image hHc).bddAbove) ⟨y, hy, rfl⟩)
  have w1 := integral_integral_window_le hHc.measurable hH0 hXY hrs hMs
  have w2 := integral_integral_window_le hHBm hHB0 hXY (le_trans hrs hrl) hMl
  have w1' : ∫ y in X - rs..Y, H y ≤ ∫ y in X - rl..Y, H y :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) le_rfl
      (Filter.Eventually.of_forall hH0) (hHi _ _)
  have hIs0 : 0 ≤ ∫ x in X..Y, ∫ y in x - rs..x, H y :=
    intervalIntegral.integral_nonneg hXY fun x _ =>
      intervalIntegral.integral_nonneg (by linarith) fun y _ => hH0 y
  calc ∫ x in X..Y, Real.exp (β * x) * ψ x ^ 2
      ≤ K * (rs * (∫ x in X..Y, ∫ y in x - rs..x, H y) +
          rl * ∫ x in X..Y, ∫ y in x - rl..x, HB y) := hmono
    _ ≤ K * (rs * (rs * ∫ y in X - rl..Y, H y) + rl * (rl * ∫ y in X - rl..Y, HB y)) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left (w1.trans (mul_le_mul_of_nonneg_left w1' hrs)) hrs)
          (mul_le_mul_of_nonneg_left w2 (le_trans hrs hrl))) hK
    _ = K * (rs ^ 2 * (∫ y in X - rl..Y, H y) + rl ^ 2 * ∫ y in X - rl..Y, HB y) := by ring
    _ = _ := by rw [hK_def]


/-! ## From few zeros to a zero-free stretch -/

/-- If a monotone integer counting function increases by at most `1` on `(x − r, x]`, then some
stretch `[p, p + r/4] ⊆ [x − r, x]` consists of points `t` with `N(t + r/4) = N(t)`. -/
theorem exists_flat_stretch_of_count_le_one {N : ℝ → ℤ} (hN : Monotone N) {r x : ℝ} (hr : 0 < r)
    (hx : N x - N (x - r) ≤ 1) :
    ∃ p, x - r ≤ p ∧ p + r / 4 ≤ x ∧ ∀ t ∈ Icc p (p + r / 4), N (t + r / 4) = N t := by
  set m := x - r / 2
  have h1 : N (x - r) ≤ N m := hN (by simp only [m]; linarith)
  have h2 : N m ≤ N x := hN (by simp only [m]; linarith)
  have hcase : N m = N (x - r) ∨ N x = N m := by omega
  have key : ∀ p, N (p + r / 2) = N p → ∀ t ∈ Icc p (p + r / 4), N (t + r / 4) = N t := by
    intro p hp t ht
    have a1 : N p ≤ N t := hN ht.1
    have a2 : N t ≤ N (t + r / 4) := hN (by linarith)
    have a3 : N (t + r / 4) ≤ N (p + r / 2) := hN (by linarith [ht.2])
    omega
  rcases hcase with h | h
  · refine ⟨x - r, le_rfl, by linarith, key _ ?_⟩
    rw [show x - r + r / 2 = m by simp only [m]; ring]; exact h
  · refine ⟨m, by simp only [m]; linarith, by simp only [m]; linarith, key _ ?_⟩
    rw [show m + r / 2 = x by simp only [m]; ring]; exact h

/-- The flat set `E = {t : N(t + r/4) = N(t)}` of a monotone counting function is measurable. -/
theorem measurableSet_flat {N : ℝ → ℤ} (hN : Monotone N) (c : ℝ) :
    MeasurableSet {t : ℝ | N (t + c) = N t} := by
  have h1 : Measurable fun t : ℝ => (N (t + c) : ℝ) :=
    (Int.cast_mono.comp (hN.comp (fun a b h => by linarith : Monotone fun t : ℝ => t + c))).measurable
  have h2 : Measurable fun t : ℝ => (N t : ℝ) := (Int.cast_mono.comp hN).measurable
  have : {t : ℝ | N (t + c) = N t} = {t : ℝ | (N (t + c) : ℝ) = (N t : ℝ)} := by
    ext t; simp
  rw [this]
  exact measurableSet_eq_fun h1 h2

/-- **Few zeros force flat mass nearby.** With `E` the flat set, if `N` increases by at most `1` on
`(x − r_s, x]` and `y ≤ x ≤ y + r_l`, then `|E ∩ [y − r_s, y + r_l]| ≥ r_s/4`. -/
theorem quarter_le_integral_flat {N : ℝ → ℤ} (hN : Monotone N) {rs rl x y : ℝ} (hrs : 0 < rs)
    (hx : N x - N (x - rs) ≤ 1) (hyx : y ≤ x) (hxy : x ≤ y + rl) :
    rs / 4 ≤ ∫ t in (y - rs)..(y + rl),
      ({t : ℝ | N (t + rs / 4) = N t}.indicator (fun _ => (1 : ℝ)) t) := by
  obtain ⟨p, hp1, hp2, hp⟩ := exists_flat_stretch_of_count_le_one hN hrs hx
  set E := {t : ℝ | N (t + rs / 4) = N t}
  have hEm : MeasurableSet E := measurableSet_flat hN _
  have hind : ∀ t, 0 ≤ E.indicator (fun _ => (1 : ℝ)) t :=
    fun t => Set.indicator_nonneg (fun _ _ => zero_le_one) t
  have hint : ∀ a b, IntervalIntegrable (E.indicator fun _ => (1 : ℝ)) volume a b := fun a b =>
    (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))).mono_fun'
      ((measurable_const.indicator hEm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by
        show ‖E.indicator (fun _ => (1 : ℝ)) t‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (hind t)]
        exact Set.indicator_le_self' (fun _ _ => zero_le_one) t)
  have hsub : ∫ t in p..(p + rs / 4), E.indicator (fun _ => (1 : ℝ)) t ≤
      ∫ t in (y - rs)..(y + rl), E.indicator (fun _ => (1 : ℝ)) t :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall hind) (hint _ _)
  have heq : ∫ t in p..(p + rs / 4), E.indicator (fun _ => (1 : ℝ)) t = rs / 4 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) fun t ht => ?_]
    · simp
    · rw [Set.uIcc_of_le (by linarith)] at ht
      simp only
      rw [Set.indicator_of_mem (show t ∈ E from hp t ht)]
  linarith


/-- `y ↦ ∫_{y−r_s}^{y+r_l} 1_E` is continuous. -/
theorem continuous_integral_indicator_window {E : Set ℝ} (hEm : MeasurableSet E) (rs rl : ℝ) :
    Continuous fun y => ∫ t in (y - rs)..(y + rl), E.indicator (fun _ => (1 : ℝ)) t := by
  have hint : ∀ a b, IntervalIntegrable (E.indicator fun _ => (1 : ℝ)) volume a b := fun a b =>
    (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))).mono_fun'
      ((measurable_const.indicator hEm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by
        show ‖E.indicator (fun _ => (1 : ℝ)) t‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) t)]
        exact Set.indicator_le_self' (fun _ _ => zero_le_one) t)
  have hP : Continuous fun x => ∫ t in (0 : ℝ)..x, E.indicator (fun _ => (1 : ℝ)) t :=
    intervalIntegral.continuous_primitive hint 0
  have : (fun y => ∫ t in (y - rs)..(y + rl), E.indicator (fun _ => (1 : ℝ)) t) =
      fun y => (∫ t in (0 : ℝ)..(y + rl), E.indicator (fun _ => (1 : ℝ)) t) -
        ∫ t in (0 : ℝ)..(y - rs), E.indicator (fun _ => (1 : ℝ)) t := by
    funext y
    rw [intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
  rw [this]
  exact (hP.comp (continuous_id.add continuous_const)).sub
    (hP.comp (continuous_id.sub continuous_const))

/-- **Mesh-free measure bound.** With `m(y) = |E ∩ [y − r_s, y + r_l]|` and `B = {m ≥ r_s/4}`,
`(r_s/4)|B ∩ [X, Y]| ≤ (r_s + r_l)|E ∩ [X − r_s, Y + r_l]|`. -/
theorem integral_indicator_bad_le {E : Set ℝ} (hEm : MeasurableSet E) {rs rl X Y : ℝ}
    (hrs : 0 < rs) (hrl : 0 ≤ rl) (hXY : X ≤ Y) :
    rs / 4 * ∫ y in X..Y, {y : ℝ | rs / 4 ≤ ∫ t in (y - rs)..(y + rl),
        E.indicator (fun _ => (1 : ℝ)) t}.indicator (fun _ => (1 : ℝ)) y ≤
      (rs + rl) * ∫ t in (X - rs)..(Y + rl), E.indicator (fun _ => (1 : ℝ)) t := by
  set m : ℝ → ℝ := fun y => ∫ t in (y - rs)..(y + rl), E.indicator (fun _ => (1 : ℝ)) t with hm
  have hmc : Continuous m := continuous_integral_indicator_window hEm rs rl
  set B := {y : ℝ | rs / 4 ≤ m y} with hB
  have hBm : MeasurableSet B := (isClosed_le continuous_const hmc).measurableSet
  have hind1 : ∀ y, B.indicator (fun _ => (1 : ℝ)) y ≤ 1 :=
    fun y => Set.indicator_le_self' (fun _ _ => zero_le_one) y
  have hpt : ∀ y, rs / 4 * B.indicator (fun _ => (1 : ℝ)) y ≤ m y := by
    intro y
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy, mul_one]; exact hy
    · rw [Set.indicator_of_notMem hy, mul_zero]
      exact intervalIntegral.integral_nonneg (by linarith)
        fun t _ => Set.indicator_nonneg (fun _ _ => zero_le_one) t
  have hBint : IntervalIntegrable (B.indicator fun _ => (1 : ℝ)) volume X Y :=
    (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))).mono_fun'
      ((measurable_const.indicator hBm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by
        show ‖B.indicator (fun _ => (1 : ℝ)) t‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) t)]
        exact hind1 t)
  have h1 : rs / 4 * ∫ y in X..Y, B.indicator (fun _ => (1 : ℝ)) y ≤ ∫ y in X..Y, m y := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hXY (hBint.const_mul _) (hmc.intervalIntegrable _ _)
      fun y _ => hpt y
  -- shift `y ↦ y + r_l` and use the window lemma with radius `r_s + r_l`
  have hshift : ∫ y in X..Y, m y =
      ∫ y in (X + rl)..(Y + rl), ∫ t in (y - (rs + rl))..y, E.indicator (fun _ => (1 : ℝ)) t := by
    rw [← intervalIntegral.integral_comp_add_right]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [hm]
    congr 1; ring
  have hw := integral_integral_window_le (H := E.indicator fun _ => (1 : ℝ))
    (measurable_const.indicator hEm) (fun t => Set.indicator_nonneg (fun _ _ => zero_le_one) t)
    (X := X + rl) (Y := Y + rl) (r := rs + rl) (M := 1) (by linarith) (by linarith)
    (fun t _ => Set.indicator_le_self' (fun _ _ => zero_le_one) t)
  rw [show X + rl - (rs + rl) = X - rs by ring] at hw
  linarith [h1, hshift ▸ hw]

/-- **AM–GM for a set indicator.** `1_B·H ≤ (λ/2)1_B + H²/(2λ)` for `λ > 0`. -/
theorem indicator_mul_le_amgm {B : Set ℝ} {H : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    B.indicator H y ≤ lam / 2 * B.indicator (fun _ => (1 : ℝ)) y + H y ^ 2 / (2 * lam) := by
  by_cases hy : y ∈ B
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_one]
    rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (H y - lam)]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero, zero_add]
    positivity

end GaloisForLFunctions.HTGeometry
