import GaloisForLFunctions.RHTower.EntireWeightedLittlewoodLeftClosure
import GaloisForLFunctions.RHTower.JensenMeanLog

/-!
# From Littlewood's rectangle identity to a zero count

Levinson's method bounds the number of zeros of a detector to the right of an abscissa `σ` by
Littlewood's weighted zero-mass identity: a zero with real part at least `σ` carries horizontal
weight at least `σ − c` in that identity, so the whole count is controlled by the boundary data of
the rectangle `[c,d] × [T₁,T₂]`.

Two of the four boundary terms are left as they stand (the horizontal edges and the logarithmic
derivative on the right edge, both `O(log T)` in the application).  The other two are estimated
here: the *left*-edge logarithmic integral is bounded above by Jensen's inequality against the mean
square on that edge, and the right-edge logarithmic integral is bounded below by a pointwise lower
bound for `‖f‖`.  The output is exactly the shape Levinson's method consumes,

```text
2π (σ − c) · #{zeros with Re ≥ σ}
    ≤ ½(T₂−T₁)·log( mean square on Re s = c )  −  (T₂−T₁)·log A  +  edges.
```

Zeros on the left edge are permitted throughout: they carry zero weight in the identity, and the
logarithmic integral of an entire function on a vertical segment always converges.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- The logarithmic norm of an entire function is interval integrable on every vertical segment,
zeros on the segment included. -/
theorem intervalIntegrable_log_norm_vertical_of_entire
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) (a T₁ T₂ : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖f ((a : ℂ) + (t : ℂ) * I)‖) volume T₁ T₂ := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro t _
  have hpath : AnalyticAt ℝ (fun u : ℝ => (a : ℂ) + (u : ℂ) * I) t :=
    analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
  exact AnalyticAt.comp (f := fun u : ℝ => (a : ℂ) + (u : ℂ) * I)
    (hf _ (Set.mem_univ _)).restrictScalars hpath |>.meromorphicAt

/-- Jensen's logarithmic mean-value step, with the nonvanishing hypothesis relaxed to a null
exceptional set. -/
theorem two_mul_integral_log_norm_le_ae {a b : ℝ} (hab : a < b) {f : ℝ → ℂ}
    (hne : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), f t ≠ 0)
    (hint : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume a b)
    (hlogint : IntervalIntegrable (fun t => Real.log ‖f t‖) volume a b)
    (hpos : 0 < ∫ t in a..b, ‖f t‖ ^ 2) :
    2 * (∫ t in a..b, Real.log ‖f t‖)
      ≤ (b - a) * Real.log ((∫ t in a..b, ‖f t‖ ^ 2) / (b - a)) := by
  have hlen : (0 : ℝ) < b - a := by linarith
  set C : ℝ := (∫ t in a..b, ‖f t‖ ^ 2) / (b - a) with hC
  have hC0 : 0 < C := div_pos hpos hlen
  have hmono : (∫ t in a..b, 2 * Real.log ‖f t‖)
      ≤ ∫ t in a..b, (‖f t‖ ^ 2 / C + Real.log C - 1) := by
    refine intervalIntegral.integral_mono_ae_restrict hab.le (hlogint.const_mul 2)
      (((hint.div_const C).add intervalIntegrable_const).sub intervalIntegrable_const) ?_
    filter_upwards [hne] with t ht
    have hn : 0 < ‖f t‖ := norm_pos_iff.mpr ht
    have hu : 0 < ‖f t‖ ^ 2 := by positivity
    have h := log_le_div_add_log_sub_one hu hC0
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [intervalIntegral.integral_sub ((hint.div_const C).add intervalIntegrable_const)
      intervalIntegrable_const, intervalIntegral.integral_add (hint.div_const C)
      intervalIntegrable_const, intervalIntegral.integral_div] at hmono
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hcancel : (∫ t in a..b, ‖f t‖ ^ 2) / C = b - a := by
    rw [hC]; field_simp
  rw [hcancel] at hmono
  linarith

/-- Positive interior sample plus continuity and global nonnegativity gives a positive interval
integral. -/
theorem intervalIntegral_pos_of_continuous_global_nonneg {g : ℝ → ℝ} {A B : ℝ}
    (hg : Continuous g) (hnonneg : ∀ t, 0 ≤ g t)
    (hposn : ∃ t ∈ Set.Ioo A B, 0 < g t) :
    0 < ∫ t in A..B, g t := by
  obtain ⟨t₀, ht₀, htpos⟩ := hposn
  have hAB : A < B := lt_trans ht₀.1 ht₀.2
  have hgi : IntervalIntegrable g volume A B := hg.intervalIntegrable A B
  have hnonneg_ae : 0 ≤ᶠ[ae (volume.restrict (Set.uIoc A B))] g := by
    filter_upwards with x using hnonneg x
  have hsupp_pos : 0 < volume (Function.support g ∩ Set.Ioc A B) := by
    have hne_ev : ∀ᶠ x in 𝓝 t₀, g x ≠ 0 := hg.continuousAt.eventually_ne htpos.ne'
    have hIoo_ev : Set.Ioo A B ∈ 𝓝 t₀ := Ioo_mem_nhds ht₀.1 ht₀.2
    have hnhds : Function.support g ∩ Set.Ioc A B ∈ 𝓝 t₀ := by
      filter_upwards [hne_ev, hIoo_ev] with x hxne hxIoo
      exact ⟨Function.mem_support.mpr hxne, Set.Ioo_subset_Ioc_self hxIoo⟩
    exact Measure.measure_pos_of_mem_nhds volume hnhds
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hnonneg_ae hgi]
  exact ⟨hAB, hsupp_pos⟩

/-- **Littlewood's zero count from a mean square.**  For an entire `f`, nonvanishing on the bottom,
top and right edges of the rectangle `[c,d] × [T₁,T₂]`, the number of zeros with real part at least
`σ`, counted with analytic multiplicity, is bounded by the boundary data, with the left edge
estimated through its mean square and the right edge through a pointwise lower bound. -/
theorem exists_entire_zeroCount_le_of_meanSquare
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) (hne : ∃ z : ℂ, f z ≠ 0)
    {c d σ T₁ T₂ Msq A : ℝ} (hcd : c < d) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ uIcc c d, f ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d, f ((x : ℂ) + T₂ * I) ≠ 0)
    (hrightne : ∀ t ∈ uIcc T₁ T₂, f ((d : ℂ) + t * I) ≠ 0)
    (hA : 0 < A) (hAle : ∀ t ∈ uIcc T₁ T₂, A ≤ ‖f ((d : ℂ) + t * I)‖)
    (hMsq : (∫ t in T₁..T₂, ‖f ((c : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq) :
    ∃ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) ∧ f z = 0) ∧
      2 * Real.pi * ((σ - c) *
          (∑ w ∈ Z.filter (fun w => σ ≤ w.re), ((analyticOrderAt f w).toNat : ℝ)))
        ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
            - (T₂ - T₁) * Real.log A
            + (d - c) * (∫ t in T₁..T₂, (logDeriv f ((d : ℂ) + t * I)).re)
            + (∫ x in c..d, (x - c) * (logDeriv f ((x : ℂ) + T₁ * I)).im)
            - ∫ x in c..d, (x - c) * (logDeriv f ((x : ℂ) + T₂ * I)).im := by
  classical
  obtain ⟨Z, hZ, hident⟩ :=
    exists_entire_weighted_littlewood_rectangle_left_boundary_zeros hf hne hcd hT hbot htop hrightne
  refine ⟨Z, hZ, ?_⟩
  have hlen : (0 : ℝ) < T₂ - T₁ := by linarith
  have hmemrect : ∀ t : ℝ, t ∈ Set.Icc T₁ T₂ →
      ((c : ℂ) + (t : ℂ) * I) ∈ (uIcc c d ×ℂ uIcc T₁ T₂) := by
    intro t ht
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have hre : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
      rw [hre, uIcc_of_le hcd.le]
      exact ⟨le_rfl, hcd.le⟩
    · have him : ((c : ℂ) + (t : ℂ) * I).im = t := by simp
      rw [him, uIcc_of_le hT.le]
      exact ht
  -- the weighted zero mass dominates `(σ − c)` times the count above `σ`
  have hZre : ∀ w ∈ Z, c ≤ w.re ∧ w.re ≤ d := by
    intro w hw
    have hmem := ((hZ w).mp hw).1
    have hre := (Complex.mem_reProdIm.mp hmem).1
    rw [uIcc_of_le hcd.le] at hre
    exact ⟨hre.1, hre.2⟩
  have hmass : (σ - c) *
      (∑ w ∈ Z.filter (fun w => σ ≤ w.re), ((analyticOrderAt f w).toNat : ℝ))
      ≤ ∑ w ∈ Z, ((analyticOrderAt f w).toNat : ℝ) * (w.re - c) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
    · intro w hw
      have hwZ : w ∈ Z := Finset.mem_of_mem_filter w hw
      have hσw : σ ≤ w.re := (Finset.mem_filter.mp hw).2
      have hord : (0 : ℝ) ≤ ((analyticOrderAt f w).toNat : ℝ) := Nat.cast_nonneg _
      nlinarith
    · intro w hwZ _
      have hord : (0 : ℝ) ≤ ((analyticOrderAt f w).toNat : ℝ) := Nat.cast_nonneg _
      have hge := (hZre w hwZ).1
      have hnn : (0 : ℝ) ≤ w.re - c := by linarith
      positivity
  -- the left edge: Jensen against the mean square
  have hcont : Continuous (fun t : ℝ => f ((c : ℂ) + (t : ℂ) * I)) := by
    have h1 : Continuous (fun t : ℝ => (c : ℂ) + (t : ℂ) * I) := by fun_prop
    have h2 : Continuous f := by
      rw [continuous_iff_continuousAt]
      exact fun z => (hf z (Set.mem_univ z)).continuousAt
    exact h2.comp h1
  have hsqint : IntervalIntegrable (fun t : ℝ => ‖f ((c : ℂ) + (t : ℂ) * I)‖ ^ 2) volume T₁ T₂ :=
    ((hcont.norm.pow 2)).intervalIntegrable T₁ T₂
  have hlogint := intervalIntegrable_log_norm_vertical_of_entire hf c T₁ T₂
  have hSfin : {t : ℝ | t ∈ Set.Icc T₁ T₂ ∧ f ((c : ℂ) + (t : ℂ) * I) = 0}.Finite := by
    have hinj : Set.InjOn (fun t : ℝ => (c : ℂ) + (t : ℂ) * I)
        {t : ℝ | t ∈ Set.Icc T₁ T₂ ∧ f ((c : ℂ) + (t : ℂ) * I) = 0} := by
      intro x _ y _ hxy
      simpa using congrArg Complex.im hxy
    refine Set.Finite.of_finite_image (Set.Finite.subset Z.finite_toSet ?_) hinj
    rintro z ⟨t, ⟨ht, hz⟩, rfl⟩
    exact (hZ _).mpr ⟨hmemrect t ht, hz⟩
  have hexists : ∃ t ∈ Set.Ioo T₁ T₂, f ((c : ℂ) + (t : ℂ) * I) ≠ 0 := by
    by_cases hall : ∃ t ∈ Set.Ioo T₁ T₂, f ((c : ℂ) + (t : ℂ) * I) ≠ 0
    · exact hall
    exfalso
    have hcon : ∀ t ∈ Set.Ioo T₁ T₂, f ((c : ℂ) + (t : ℂ) * I) = 0 := by
      intro t ht
      by_contra h0
      exact hall ⟨t, ht, h0⟩
    have hsub : Set.Ioo T₁ T₂ ⊆
        {t : ℝ | t ∈ Set.Icc T₁ T₂ ∧ f ((c : ℂ) + (t : ℂ) * I) = 0} := by
      intro t ht
      exact ⟨Set.Ioo_subset_Icc_self ht, hcon t ht⟩
    exact (Set.Ioo_infinite hT) (hSfin.subset hsub)
  have hIpos : 0 < ∫ t in T₁..T₂, ‖f ((c : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    refine intervalIntegral_pos_of_continuous_global_nonneg (hcont.norm.pow 2)
      (fun t => by positivity) ?_
    obtain ⟨t, ht, hnz⟩ := hexists
    refine ⟨t, ht, ?_⟩
    have : 0 < ‖f ((c : ℂ) + (t : ℂ) * I)‖ := norm_pos_iff.mpr hnz
    positivity
  have haeleft : ∀ᵐ (t : ℝ) ∂(volume.restrict (Set.Icc T₁ T₂)),
      f ((c : ℂ) + (t : ℂ) * I) ≠ 0 := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr ?_
    have hnull := hSfin.measure_zero volume
    have hae : ∀ᵐ (t : ℝ) ∂volume,
        t ∉ {t : ℝ | t ∈ Set.Icc T₁ T₂ ∧ f ((c : ℂ) + (t : ℂ) * I) = 0} :=
      MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [hae] with t ht hmem h0
    exact ht ⟨hmem, h0⟩
  have hleft : 2 * (∫ t in T₁..T₂, Real.log ‖f ((c : ℂ) + (t : ℂ) * I)‖)
      ≤ (T₂ - T₁) * Real.log (Msq / (T₂ - T₁)) := by
    have hJ := two_mul_integral_log_norm_le_ae hT haeleft hsqint hlogint hIpos
    have hdiv : (∫ t in T₁..T₂, ‖f ((c : ℂ) + (t : ℂ) * I)‖ ^ 2) / (T₂ - T₁)
        ≤ Msq / (T₂ - T₁) := by gcongr
    have hlogmono := Real.log_le_log (div_pos hIpos hlen) hdiv
    calc 2 * (∫ t in T₁..T₂, Real.log ‖f ((c : ℂ) + (t : ℂ) * I)‖)
        ≤ (T₂ - T₁) *
            Real.log ((∫ t in T₁..T₂, ‖f ((c : ℂ) + (t : ℂ) * I)‖ ^ 2) / (T₂ - T₁)) := hJ
      _ ≤ (T₂ - T₁) * Real.log (Msq / (T₂ - T₁)) :=
          mul_le_mul_of_nonneg_left hlogmono hlen.le
  -- the right edge: a pointwise lower bound
  have hright : (T₂ - T₁) * Real.log A
      ≤ ∫ t in T₁..T₂, Real.log ‖f ((d : ℂ) + (t : ℂ) * I)‖ := by
    have hmono : ∀ t ∈ Set.Icc T₁ T₂,
        Real.log A ≤ Real.log ‖f ((d : ℂ) + (t : ℂ) * I)‖ := by
      intro t ht
      refine Real.log_le_log hA (hAle t ?_)
      rw [uIcc_of_le hT.le]; exact ht
    have hcmp := intervalIntegral.integral_mono_on hT.le intervalIntegrable_const
      (intervalIntegrable_log_norm_vertical_of_entire hf d T₁ T₂) hmono
    simpa using hcmp
  have hkey : 2 * Real.pi * ((σ - c) *
      (∑ w ∈ Z.filter (fun w => σ ≤ w.re), ((analyticOrderAt f w).toNat : ℝ)))
      ≤ 2 * Real.pi * (∑ w ∈ Z, ((analyticOrderAt f w).toNat : ℝ) * (w.re - c)) :=
    mul_le_mul_of_nonneg_left hmass (by positivity)
  rw [hident] at hkey
  linarith

end

end RHTower
