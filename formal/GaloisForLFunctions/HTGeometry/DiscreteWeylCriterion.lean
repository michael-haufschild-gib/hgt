import Mathlib.Analysis.Fourier.AddCircle

/-!
# Weyl's criterion for sequences modulo one

If the exponential sums `N⁻¹ Σ_{n<N} e(k yₙ)` tend to `0` for every integer `k ≠ 0`, then the
sequence `yₙ` is equidistributed modulo one.

* `tendsto_weylAverage`: the Cesàro averages of every continuous function on the circle along `yₙ`
  converge to its mean.  On the monomials this is the hypothesis; the functions with this property
  form a closed submodule (averages and means are bounded by the uniform norm), and the monomials
  span a dense subspace.
* `tendsto_card_fract_mem_Ico`: for `0 < a ≤ b < 1` the proportion of `n < N` with
  `{yₙ} ∈ [a, b)` tends to `b − a`.  The indicator is squeezed between two continuous tents
  supported in `(0, 1)`, whose integrals differ from `b − a` by at most `2δ`.
-/

open AddCircle MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry.DiscreteWeyl

/-- The Cesàro average of `f` along the sequence `y` reduced modulo one. -/
noncomputable def weylAverage (y : ℕ → ℝ) (f : C(UnitAddCircle, ℂ)) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ range N, f (y n)

theorem circleIntegrable (f : C(UnitAddCircle, ℂ)) :
    Integrable (fun x => f x) (haarAddCircle : Measure UnitAddCircle) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem norm_integral_le (f : C(UnitAddCircle, ℂ)) :
    ‖∫ x, f x ∂(haarAddCircle : Measure UnitAddCircle)‖ ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const (μ := (haarAddCircle : Measure UnitAddCircle))
    (C := ‖f‖) (Eventually.of_forall fun x => f.norm_coe_le_norm x)
  simpa [probReal_univ] using h

/-- The monomials have mean `0` except the constant one. -/
theorem integral_fourier (k : ℤ) :
    ∫ x, fourier k x ∂(haarAddCircle : Measure UnitAddCircle) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk
    simp [probReal_univ]
  · have h : (inner ℂ (fourierLp (T := 1) 2 0) (fourierLp 2 k) : ℂ) = 0 :=
      orthonormal_fourier.2 (Ne.symm hk)
    rw [fourierLp, fourierLp, ContinuousMap.inner_toLp] at h
    simpa [fourier_zero] using h

theorem weylAverage_add (y : ℕ → ℝ) (f g : C(UnitAddCircle, ℂ)) (N : ℕ) :
    weylAverage y (f + g) N = weylAverage y f N + weylAverage y g N := by
  simp only [weylAverage, ContinuousMap.add_apply, sum_add_distrib, mul_add]

theorem weylAverage_sub (y : ℕ → ℝ) (f g : C(UnitAddCircle, ℂ)) (N : ℕ) :
    weylAverage y (f - g) N = weylAverage y f N - weylAverage y g N := by
  simp only [weylAverage, ContinuousMap.sub_apply, sum_sub_distrib, mul_sub]

theorem weylAverage_smul (y : ℕ → ℝ) (c : ℂ) (f : C(UnitAddCircle, ℂ)) (N : ℕ) :
    weylAverage y (c • f) N = c * weylAverage y f N := by
  simp only [weylAverage, ContinuousMap.smul_apply, smul_eq_mul, ← mul_sum]
  ring

theorem norm_weylAverage_le (y : ℕ → ℝ) (f : C(UnitAddCircle, ℂ)) (N : ℕ) :
    ‖weylAverage y f N‖ ≤ ‖f‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [weylAverage]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [weylAverage, norm_mul, norm_inv, Complex.norm_natCast]
  have : ‖∑ n ∈ range N, f (y n)‖ ≤ N * ‖f‖ := by
    refine (norm_sum_le _ _).trans ?_
    simpa using sum_le_sum fun n (_ : n ∈ range N) => f.norm_coe_le_norm (y n)
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ range N, f (y n)‖ ≤ (N : ℝ)⁻¹ * (N * ‖f‖) := by gcongr
    _ = ‖f‖ := by field_simp

/-- The continuous functions whose averages along `y` converge to their mean. -/
def meanSubmodule (y : ℕ → ℝ) : Submodule ℂ C(UnitAddCircle, ℂ) where
  carrier := {f | Tendsto (weylAverage y f) atTop
    (𝓝 (∫ x, f x ∂(haarAddCircle : Measure UnitAddCircle)))}
  add_mem' := by
    intro f g hf hg
    show Tendsto (weylAverage y (f + g)) atTop _
    have hint : ∫ x, (f + g) x ∂(haarAddCircle : Measure UnitAddCircle) =
        (∫ x, f x ∂haarAddCircle) + ∫ x, g x ∂haarAddCircle :=
      integral_add (circleIntegrable f) (circleIntegrable g)
    rw [hint]
    exact (hf.add hg).congr fun N => (weylAverage_add y f g N).symm
  zero_mem' := by
    show Tendsto (weylAverage y 0) atTop _
    have h0 : ∀ N, weylAverage y 0 N = 0 := fun N => by simp [weylAverage]
    simp only [ContinuousMap.zero_apply, integral_zero]
    exact tendsto_const_nhds.congr fun N => (h0 N).symm
  smul_mem' := by
    intro c f hf
    show Tendsto (weylAverage y (c • f)) atTop _
    have hint : ∫ x, (c • f) x ∂(haarAddCircle : Measure UnitAddCircle) =
        c * ∫ x, f x ∂haarAddCircle := by
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      exact integral_const_mul c _
    rw [hint]
    exact (hf.const_mul c).congr fun N => (weylAverage_smul y c f N).symm

theorem meanSubmodule_isClosed (y : ℕ → ℝ) :
    IsClosed ((meanSubmodule y : Submodule ℂ C(UnitAddCircle, ℂ)) : Set C(UnitAddCircle, ℂ)) := by
  rw [← closure_subset_iff_isClosed]
  intro f hf
  show Tendsto (weylAverage y f) atTop (𝓝 (∫ x, f x ∂(haarAddCircle : Measure UnitAddCircle)))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hf (ε / 3) (by linarith)
  have hgt : Tendsto (weylAverage y g) atTop
      (𝓝 (∫ x, g x ∂(haarAddCircle : Measure UnitAddCircle))) := hg
  rw [Metric.tendsto_atTop] at hgt
  obtain ⟨N₀, hN₀⟩ := hgt (ε / 3) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : dist (weylAverage y f N) (weylAverage y g N) < ε / 3 := by
    rw [dist_eq_norm, ← weylAverage_sub]
    exact lt_of_le_of_lt (norm_weylAverage_le y _ N) (by rwa [← dist_eq_norm])
  have h3 : dist (∫ x, g x ∂(haarAddCircle : Measure UnitAddCircle))
      (∫ x, f x ∂haarAddCircle) < ε / 3 := by
    rw [dist_eq_norm, ← integral_sub (circleIntegrable g) (circleIntegrable f)]
    calc ‖∫ x, (g x - f x) ∂(haarAddCircle : Measure UnitAddCircle)‖ ≤ ‖g - f‖ := by
          simpa using norm_integral_le (g - f)
      _ < ε / 3 := by rw [← dist_eq_norm, dist_comm]; exact hdist
  have htri := dist_triangle4 (weylAverage y f N) (weylAverage y g N)
    (∫ x, g x ∂(haarAddCircle : Measure UnitAddCircle)) (∫ x, f x ∂haarAddCircle)
  linarith [hN₀ N hN]

/-- **Weyl's criterion.**  If `N⁻¹ Σ_{n<N} e(k yₙ) → 0` for every `k ≠ 0`, the averages of
every continuous function on the circle along `yₙ` converge to its mean. -/
theorem tendsto_weylAverage (y : ℕ → ℝ)
    (hW : ∀ k : ℤ, k ≠ 0 → Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
      ∑ n ∈ range N, Complex.exp (2 * Real.pi * Complex.I * k * y n)) atTop (𝓝 0))
    (f : C(UnitAddCircle, ℂ)) :
    Tendsto (weylAverage y f) atTop (𝓝 (∫ x, f x ∂(haarAddCircle : Measure UnitAddCircle))) := by
  have hchar : ∀ k : ℤ, fourier k ∈ meanSubmodule y := by
    intro k
    show Tendsto (weylAverage y (fourier k)) atTop _
    have hav : ∀ N, weylAverage y (fourier k) N = (N : ℂ)⁻¹ *
        ∑ n ∈ range N, Complex.exp (2 * Real.pi * Complex.I * k * y n) := by
      intro N
      simp only [weylAverage, fourier_coe_apply, Complex.ofReal_one, div_one]
    rw [integral_fourier]
    split_ifs with hk
    · subst hk
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_gt_atTop 0] with N hN
      rw [hav]
      simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, sum_const, card_range,
        nsmul_eq_mul, mul_one]
      have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp
    · exact (hW k hk).congr fun N => (hav N).symm
  have hsub : Submodule.span ℂ (Set.range (fourier (T := 1))) ≤ meanSubmodule y :=
    Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hchar k)
  have htop := Submodule.topologicalClosure_minimal _ hsub (meanSubmodule_isClosed y)
  rw [span_fourier_closure_eq_top] at htop
  exact htop Submodule.mem_top

/-! ### Intervals -/

/-- The tent of height one over `[c + δ, d − δ]`, vanishing outside `(c, d)`. -/
noncomputable def tent (c d δ t : ℝ) : ℝ := max 0 (min 1 (min ((t - c) / δ) ((d - t) / δ)))

theorem continuous_tent (c d δ : ℝ) : Continuous (tent c d δ) := by
  unfold tent; fun_prop

theorem tent_nonneg (c d δ t : ℝ) : 0 ≤ tent c d δ t := le_max_left _ _

theorem tent_le_one (c d δ t : ℝ) : tent c d δ t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem tent_eq_zero_of_le {c d δ t : ℝ} (hδ : 0 < δ) (h : t ≤ c) : tent c d δ t = 0 := by
  unfold tent
  have : (t - c) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  exact max_eq_left ((min_le_right _ _).trans ((min_le_left _ _).trans this))

theorem tent_eq_zero_of_ge {c d δ t : ℝ} (hδ : 0 < δ) (h : d ≤ t) : tent c d δ t = 0 := by
  unfold tent
  have : (d - t) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  exact max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans this))

theorem tent_eq_one {c d δ t : ℝ} (hδ : 0 < δ) (h1 : c + δ ≤ t) (h2 : t ≤ d - δ) :
    tent c d δ t = 1 := by
  unfold tent
  have e1 : 1 ≤ (t - c) / δ := by rw [le_div_iff₀ hδ]; linarith
  have e2 : 1 ≤ (d - t) / δ := by rw [le_div_iff₀ hδ]; linarith
  rw [min_eq_left (le_min e1 e2), max_eq_right zero_le_one]

theorem integral_tent_le {c d δ : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    ∫ t in (0 : ℝ)..1, tent c d δ t ≤ d - c := by
  have hi : ∀ u v : ℝ, IntervalIntegrable (tent c d δ) volume u v :=
    fun u v => (continuous_tent c d δ).intervalIntegrable u v
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 c) (hi c 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hi c d) (hi d 1)]
  have h0 : ∫ t in (0 : ℝ)..c, tent c d δ t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
    · simp
    rw [Set.uIcc_of_le hc] at ht
    exact tent_eq_zero_of_le hδ ht.2
  have h1 : ∫ t in d..1, tent c d δ t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
    · simp
    rw [Set.uIcc_of_le hd] at ht
    exact tent_eq_zero_of_ge hδ ht.1
  have hmid : ∫ t in c..d, tent c d δ t ≤ ∫ _t in c..d, (1 : ℝ) :=
    intervalIntegral.integral_mono_on hcd (hi c d) intervalIntegrable_const
      fun t _ => tent_le_one c d δ t
  rw [h0, h1, intervalIntegral.integral_const, smul_eq_mul, mul_one] at *
  linarith

theorem integral_tent_ge {c d δ : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hd : d ≤ 1) :
    d - c - 2 * δ ≤ ∫ t in (0 : ℝ)..1, tent c d δ t := by
  have hi : ∀ u v : ℝ, IntervalIntegrable (tent c d δ) volume u v :=
    fun u v => (continuous_tent c d δ).intervalIntegrable u v
  have hnn : ∀ u v : ℝ, u ≤ v → 0 ≤ ∫ t in u..v, tent c d δ t :=
    fun u v huv => intervalIntegral.integral_nonneg huv fun t _ => tent_nonneg c d δ t
  by_cases h : c + δ ≤ d - δ
  · rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (c + δ)) (hi (c + δ) 1),
      ← intervalIntegral.integral_add_adjacent_intervals (hi (c + δ) (d - δ)) (hi (d - δ) 1)]
    have hmid : ∫ t in (c + δ)..(d - δ), tent c d δ t = d - δ - (c + δ) := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) fun t ht => ?_]
      · simp
      rw [Set.uIcc_of_le h] at ht
      exact tent_eq_one hδ ht.1 ht.2
    have := hnn 0 (c + δ) (by linarith)
    have := hnn (d - δ) 1 (by linarith)
    linarith
  · have := hnn 0 1 zero_le_one
    linarith

/-- The tent as a continuous function on the circle. -/
noncomputable def tentCircle {c d δ : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hd : d ≤ 1) :
    C(UnitAddCircle, ℂ) :=
  ⟨liftIco 1 0 (fun t => (tent c d δ t : ℂ)), liftIco_zero_continuous
    (by rw [tent_eq_zero_of_le hδ hc, tent_eq_zero_of_ge hδ hd])
    (Complex.continuous_ofReal.comp (continuous_tent c d δ)).continuousOn⟩

theorem tentCircle_coe {c d δ : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hd : d ≤ 1) (x : ℝ) :
    tentCircle hδ hc hd (x : UnitAddCircle) = (tent c d δ (Int.fract x) : ℂ) := by
  show liftIco 1 0 (fun t => (tent c d δ t : ℂ)) (x : UnitAddCircle) = _
  rw [← AddCircle.coe_fract, liftIco_zero_coe_apply ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩]

theorem integral_tentCircle {c d δ : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hd : d ≤ 1) :
    ∫ x, tentCircle hδ hc hd x ∂(haarAddCircle : Measure UnitAddCircle) =
      ((∫ t in (0 : ℝ)..1, tent c d δ t : ℝ) : ℂ) := by
  have h := fourierCoeff_liftIco_eq (T := 1) (a := 0) (fun t => (tent c d δ t : ℂ)) 0
  rw [fourierCoeffOn_eq_integral] at h
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul, sub_zero, div_one, zero_add] at h
  rw [intervalIntegral.integral_ofReal] at h
  exact h

/-- The proportion `N⁻¹ #{n < N : {yₙ} ∈ [a, b)}` as an average of the indicator. -/
theorem card_div_eq (y : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    (#{n ∈ range N | Int.fract (y n) ∈ Set.Ico a b} : ℝ) / N =
      (N : ℝ)⁻¹ * ∑ n ∈ range N, if Int.fract (y n) ∈ Set.Ico a b then (1 : ℝ) else 0 := by
  rw [card_filter, Nat.cast_sum, div_eq_inv_mul]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem re_weylAverage_tentCircle {c d δ : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hd : d ≤ 1)
    (y : ℕ → ℝ) (N : ℕ) :
    (weylAverage y (tentCircle hδ hc hd) N).re =
      (N : ℝ)⁻¹ * ∑ n ∈ range N, tent c d δ (Int.fract (y n)) := by
  simp only [weylAverage, tentCircle_coe]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_sum,
    ← Complex.ofReal_mul, Complex.ofReal_re]

theorem tendsto_re_weylAverage_tent (y : ℕ → ℝ)
    (hW : ∀ k : ℤ, k ≠ 0 → Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
      ∑ n ∈ range N, Complex.exp (2 * Real.pi * Complex.I * k * y n)) atTop (𝓝 0))
    {c d δ : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hd : d ≤ 1) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ range N, tent c d δ (Int.fract (y n))) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, tent c d δ t)) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_weylAverage y hW (tentCircle hδ hc hd))
  rw [integral_tentCircle, Complex.ofReal_re] at h
  exact h.congr fun N => re_weylAverage_tentCircle hδ hc hd y N

/-- **Equidistribution in intervals.**  Under the Weyl hypothesis, for `0 < a ≤ b < 1` the
proportion of `n < N` with `{yₙ} ∈ [a, b)` tends to `b − a`. -/
theorem tendsto_card_fract_mem_Ico (y : ℕ → ℝ)
    (hW : ∀ k : ℤ, k ≠ 0 → Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
      ∑ n ∈ range N, Complex.exp (2 * Real.pi * Complex.I * k * y n)) atTop (𝓝 0))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    Tendsto (fun N : ℕ => (#{n ∈ range N | Int.fract (y n) ∈ Set.Ico a b} : ℝ) / N) atTop
      (𝓝 (b - a)) := by
  rw [tendsto_order]
  constructor
  · intro r hr
    obtain ⟨δ, hδ, hδa, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ a ∧ 2 * δ < b - a - r :=
      ⟨min a ((b - a - r) / 4), lt_min ha (by linarith), min_le_left _ _,
        by linarith [min_le_right a ((b - a - r) / 4)]⟩
    have hlim := tendsto_re_weylAverage_tent y hW hδ ha.le hb.le
    have hint := integral_tent_ge hδ ha.le hb.le (c := a) (d := b)
    filter_upwards [(tendsto_order.1 hlim).1 r (by linarith)] with N hN
    refine lt_of_lt_of_le hN ?_
    rw [card_div_eq]
    gcongr with n _
    split_ifs with hn
    · exact tent_le_one _ _ _ _
    · rw [Set.mem_Ico, not_and_or, not_le, not_lt] at hn
      rcases hn with hn | hn
      · exact (tent_eq_zero_of_le hδ hn.le).le
      · exact (tent_eq_zero_of_ge hδ hn).le
  · intro r hr
    obtain ⟨δ, hδ, hδa, hδb, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ a ∧ δ ≤ 1 - b ∧ 2 * δ < r - (b - a) :=
      ⟨min (min a (1 - b)) ((r - (b - a)) / 4), lt_min (lt_min ha (by linarith)) (by linarith),
        (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
        by linarith [min_le_right (min a (1 - b)) ((r - (b - a)) / 4)]⟩
    have hc : 0 ≤ a - δ := by linarith
    have hd : b + δ ≤ 1 := by linarith
    have hlim := tendsto_re_weylAverage_tent y hW hδ hc hd
    have hint := integral_tent_le hδ hc (by linarith) hd
    filter_upwards [(tendsto_order.1 hlim).2 r (by linarith)] with N hN
    refine lt_of_le_of_lt ?_ hN
    rw [card_div_eq]
    gcongr with n _
    split_ifs with hn
    · rw [tent_eq_one hδ (by linarith [hn.1]) (by linarith [hn.2])]
    · exact tent_nonneg _ _ _ _

end GaloisForLFunctions.HTGeometry.DiscreteWeyl
