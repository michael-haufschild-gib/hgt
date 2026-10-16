import GaloisForLFunctions.RHTower.CHMDKleinGordonTransmutationComplexTime
import GaloisForLFunctions.RHTower.CHMDMasslessBoundaryContinuation

/-!
# CHMD: continuation of the Klein–Gordon causal wave across the boundary

The causal wave of the CHMD route is the Klein–Gordon zero-side wave
`Φ(z) = Σ_ρ m_ρ cos(z √(γ_ρ² + 2)) sech²(γ_ρ/2)`, with `Φ(y) = φ_Λ(y) = chmdWave y` for real `y`
(`kgZeroWave_ofReal`).  It is holomorphic on the time strip `|Im z| < 1`, and the strip is sharp:
the boundary lines `Im z = ±1` carry the primes.

The light-cone transmutation `Φ = L[Φ₀]` (`kgZeroWave_eq_lightConeTransmuteC`) samples the massless
wave `Φ₀` only on the segment `[0, z]`, so the continuation `masslessBoundaryWave` of `Φ₀` transports
to `Φ`:

* **Continuation** (`kgBoundaryWave`, `kgZeroWave_eq_kgBoundaryWave`, `analyticAt_kgBoundaryWave`):
  `L[masslessBoundaryWave]` agrees with `Φ` on the strip and is holomorphic at every `z` whose
  segment `[0, z]` avoids the singularities of the massless continuation (`LightConeRegular`); in
  particular at every boundary point `x ± i`, `x ≠ 0`, other than a prime point
  (`analyticAt_kgBoundaryWave_boundary`).
* **Prime boundary points** (`tendsto_kgZeroWave_boundary`): at `log n + i` (`Λ(n) ≠ 0`) the wave
  blows up at the simple-pole rate along the vertical approach from inside the strip,

  `ε · Φ(log n + i(1 − ε)) → −(2/π) Λ(n)/√n`   (`ε → 0⁺`).

  The Bessel tail integrates `Φ₀` along `[0, z]`, where the pole is only touched at the endpoint,
  and `ε · (tail)` tends to `0` by dominated convergence.
* **All four families** (`tendsto_kgZeroWave_boundary_four`): by the symmetries `Φ(−z) = Φ(z)` and
  `Φ(z̄) = conj Φ(z)`, the same law holds at `±log n ± i`.
-/

open Complex MeasureTheory Set Filter Topology Metric Zeta23
open scoped Real ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.CHMDLightCone

open RHTower.CHMDGrowthCollapse

/-! ## The continued causal wave -/

/-- The continued Klein–Gordon causal wave `L[masslessBoundaryWave]`. -/
def kgBoundaryWave (z : ℂ) : ℂ := lightConeTransmuteC masslessBoundaryWave z

theorem abs_im_mul_ofReal_le {z : ℂ} {t : ℝ} (ht : |t| ≤ 1) : |(z * t).im| ≤ |z.im| := by
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) ht

/-- **The continuation agrees with the causal wave on the time strip.** -/
theorem kgZeroWave_eq_kgBoundaryWave {z : ℂ} (hz : |z.im| < 1) :
    kgZeroWave z = kgBoundaryWave z := by
  rw [kgZeroWave_eq_lightConeTransmuteC hz, kgBoundaryWave, lightConeTransmuteC, lightConeTransmuteC,
    masslessBoundaryWave_of_strip hz]
  congr 2
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  have hta : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  simp only [masslessBoundaryWave_of_strip (lt_of_le_of_lt (abs_im_mul_ofReal_le hta) hz)]

/-- The points whose light-cone segment `[0, z]` lies in the analyticity domain of the massless
continuation. -/
def LightConeRegular (z : ℂ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ masslessBoundaryWave (z * t)

theorem isOpen_lightConeRegular : IsOpen {z : ℂ | LightConeRegular z} := by
  rw [Metric.isOpen_iff]
  intro z hz
  set S := (fun t : ℝ => z * t) '' Icc (0 : ℝ) 1
  have hSc : IsCompact S := isCompact_Icc.image (continuous_const.mul continuous_ofReal)
  have hSΩ : S ⊆ {w | AnalyticAt ℂ masslessBoundaryWave w} := by
    rintro _ ⟨t, ht, rfl⟩; exact hz t ht
  obtain ⟨δ, hδ, hthick⟩ := hSc.exists_thickening_subset_open
    (isOpen_analyticAt ℂ masslessBoundaryWave) hSΩ
  refine ⟨δ, hδ, fun z' hz' t ht => hthick (Metric.mem_thickening_iff.mpr ⟨z * t, ⟨t, ht, rfl⟩, ?_⟩)⟩
  rw [dist_eq_norm, ← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1,
    ← dist_eq_norm]
  calc dist z' z * t ≤ dist z' z * 1 := mul_le_mul_of_nonneg_left ht.2 dist_nonneg
    _ < δ := by rw [mul_one]; exact hz'

/-- **The continued causal wave is holomorphic wherever its light-cone segment is regular.** -/
theorem analyticAt_kgBoundaryWave {z : ℂ} (hz : LightConeRegular z) :
    AnalyticAt ℂ kgBoundaryWave z :=
  DifferentiableOn.analyticAt (fun _ hw => (differentiableAt_lightConeTransmuteC hw).differentiableWithinAt)
    (isOpen_lightConeRegular.mem_nhds hz)

theorem lightConeRegular_of_strip {z : ℂ} (hz : |z.im| < 1) : LightConeRegular z := fun t ht =>
  analyticAt_masslessBoundaryWave (Or.inl (lt_of_le_of_lt
    (abs_im_mul_ofReal_le (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)) hz))

/-- **Regular boundary points**: every point `x ± i` with `x ≠ 0` that is not a prime point. -/
theorem lightConeRegular_boundary {x : ℝ} (hx : x ≠ 0) {s : ℝ} (hs : |s| = 1)
    (hav : AvoidsPrimePoints ((x : ℂ) + s * I)) : LightConeRegular ((x : ℂ) + s * I) := by
  intro t ht
  have him : (((x : ℂ) + s * I) * t).im = s * t := by simp
  rcases ht.2.lt_or_eq with htlt | hteq
  · refine analyticAt_masslessBoundaryWave (Or.inl ?_)
    rw [him, abs_mul, hs, one_mul, abs_of_nonneg ht.1]
    exact htlt
  · subst hteq
    rw [ofReal_one, mul_one]
    refine analyticAt_masslessBoundaryWave (Or.inr ⟨?_, ?_, hav⟩)
    · simp [hs]; norm_num
    · simpa using hx

/-- **The causal wave continues across every regular boundary point.** -/
theorem analyticAt_kgBoundaryWave_boundary {x : ℝ} (hx : x ≠ 0) {s : ℝ} (hs : |s| = 1)
    (hav : AvoidsPrimePoints ((x : ℂ) + s * I)) :
    AnalyticAt ℂ kgBoundaryWave ((x : ℂ) + s * I) :=
  analyticAt_kgBoundaryWave (lightConeRegular_boundary hx hs hav)

/-! ## The boundary law at the prime points -/

theorem one_sub_mul_ge (t ε : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ε / 2 ≤ 1 - t * (1 - ε) := by
  rcases le_or_gt (1 / 2) t with h | h
  · nlinarith
  · nlinarith

/-- **The boundary law**: `ε · Φ(log n + i(1 − ε)) → −(2/π) Λ(n)/√n` as `ε → 0⁺`. -/
theorem tendsto_kgZeroWave_boundary {n₀ : ℕ} (hw : chmdPrimeWeight n₀ ≠ 0) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * kgZeroWave ((Real.log n₀ : ℂ) + I - ε * I)) (𝓝[>] 0)
      (𝓝 (-2 / π * chmdPrimeWeight n₀)) := by
  set v₀ : ℂ := (Real.log n₀ : ℂ) + I with hv₀
  set R : ℂ := 2 * I / π * chmdPrimeWeight n₀ with hR
  set zε : ℝ → ℂ := fun ε => v₀ - ε * I with hzε
  have hn₀ := two_le_of_chmdPrimeWeight_ne_zero hw
  have hlog := half_lt_log_of_two_le hn₀
  have hzre : ∀ ε : ℝ, (zε ε).re = Real.log n₀ := fun ε => by
    simp only [hzε, hv₀, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.I_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_im]
    ring
  have hzim : ∀ ε : ℝ, (zε ε).im = 1 - ε := fun ε => by
    simp only [hzε, hv₀, Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.I_re,
      Complex.mul_im, Complex.ofReal_im, Complex.I_im]
    ring
  have hres := tendsto_masslessContinuation_residue (a := 1 / 2) (by norm_num) le_rfl hw
  -- the map `ε ↦ v₀ − iε` into the punctured neighbourhood
  have hmap : Tendsto zε (𝓝[>] 0) (𝓝[≠] v₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto zε (𝓝 0) (𝓝 (zε 0)) := (by fun_prop : Continuous zε).tendsto 0
      simp only [hzε, ofReal_zero, zero_mul, sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hzε]
      intro h
      have := congrArg Complex.im h
      simp at this
      exact (ne_of_gt (show (0 : ℝ) < ε from hε)) this
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  -- part 1: the massless wave
  have hpart1 : Tendsto (fun ε : ℝ => (ε : ℂ) * masslessZeroWave (zε ε)) (𝓝[>] 0) (𝓝 (I * R)) := by
    have h := (hres.comp hmap).const_mul I
    refine h.congr' ?_
    filter_upwards [hsmall] with ε hε
    simp only [Function.comp]
    rw [← masslessZeroWave_eq_masslessContinuation (a := 1 / 2) (by norm_num) le_rfl
      (by rw [hzre]; exact hlog)
      (by rw [hzim]; linarith [hε.2]) (by rw [hzim]; linarith [hε.1])]
    simp only [hzε]
    linear_combination (-(ε : ℂ) * masslessZeroWave (v₀ - ε * I)) * I_sq
  -- part 2: the Bessel tail
  obtain ⟨δ₀, hδ₀, hδ₀res⟩ := Metric.tendsto_nhdsWithin_nhds.mp hres 1 one_pos
  set δ := min δ₀ (min (Real.log n₀ - 1 / 2) (1 / 2)) with hδ
  have hδpos : 0 < δ := lt_min hδ₀ (lt_min (by linarith) (by norm_num))
  set η := δ / (Real.log n₀ + 2) with hη
  have hlog0 : 0 < Real.log n₀ := by linarith
  have hηpos : 0 < η := by positivity
  have hη1 : η < 1 := by
    rw [hη, div_lt_one (by linarith)]
    linarith [min_le_right δ₀ (min (Real.log n₀ - 1 / 2) (1 / 2)),
      min_le_right (Real.log n₀ - 1 / 2) (1 / 2)]
  set Kc : Set ℂ := Icc (0 : ℝ) (Real.log n₀) ×ℂ Icc (0 : ℝ) (1 - η)
  have hKc : IsCompact Kc := isCompact_Icc.reProdIm isCompact_Icc
  have hKcs : Kc ⊆ causalTimeStrip := fun v hv => by
    have := (Complex.mem_reProdIm.mp hv).2
    show |v.im| < 1
    rw [abs_lt]; constructor <;> linarith [this.1, this.2]
  obtain ⟨M₂', hM₂'⟩ := hKc.exists_bound_of_continuousOn
    (differentiableOn_masslessZeroWave.continuousOn.mono hKcs)
  set M₂ := max M₂' 0
  have hM₂ : ∀ v ∈ Kc, ‖masslessZeroWave v‖ ≤ M₂ := fun v hv => (hM₂' v hv).trans (le_max_left _ _)
  have hM₂0 : 0 ≤ M₂ := le_max_right _ _
  -- the pointwise bound `ε ‖Φ₀(zε t)‖ ≤ M₂ + 2(‖R‖ + 1)`
  have hkey : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ε * ‖masslessZeroWave (zε ε * t)‖ ≤ M₂ + 2 * (‖R‖ + 1) := by
    intro ε hε0 hε1 t ht0 ht1
    set v := zε ε * t
    have hvre : v.re = t * Real.log n₀ := by
      show (zε ε * (t : ℂ)).re = _
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hzre, mul_comm]
    have hvim : v.im = t * (1 - ε) := by
      show (zε ε * (t : ℂ)).im = _
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, hzim, mul_comm]
    have hgap : ε / 2 ≤ ‖v - v₀‖ := by
      have h1 := one_sub_mul_ge t ε ht0 ht1 hε0 hε1
      have h2 : |(v - v₀).im| ≤ ‖v - v₀‖ := Complex.abs_im_le_norm _
      have h3 : (v - v₀).im = t * (1 - ε) - 1 := by
        rw [Complex.sub_im, hvim, hv₀, Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]
      rw [h3] at h2
      linarith [neg_abs_le (t * (1 - ε) - 1)]
    have hgap0 : 0 < ‖v - v₀‖ := lt_of_lt_of_le (by positivity) hgap
    have hbound : ‖masslessZeroWave v‖ ≤ M₂ + (‖R‖ + 1) / ‖v - v₀‖ := by
      by_cases hnear : dist v v₀ < δ
      · have hne : v ≠ v₀ := fun h => by rw [h] at hgap0; simp at hgap0
        have hb := hδ₀res (Set.mem_compl_singleton_iff.mpr hne)
          (lt_of_lt_of_le hnear (min_le_left _ _))
        rw [dist_eq_norm] at hb hnear
        have hvre' : 1 / 2 < v.re := by
          have := (Complex.abs_re_le_norm (v - v₀)).trans_lt hnear
          rw [Complex.sub_re, hv₀, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero] at this
          have hδ2 : δ ≤ Real.log n₀ - 1 / 2 :=
            (min_le_right _ _).trans (min_le_left _ _)
          linarith [(abs_lt.mp this).1]
        have hvim' : -1 / 2 < v.im := by rw [hvim]; nlinarith
        have hvim'' : v.im < 1 := by rw [hvim]; nlinarith
        rw [masslessZeroWave_eq_masslessContinuation (a := 1 / 2) (by norm_num) le_rfl hvre' hvim'
          hvim'']
        have hprod : ‖(v - v₀) * masslessContinuation (1 / 2) v‖ ≤ ‖R‖ + 1 := by
          have := norm_sub_norm_le ((v - v₀) * masslessContinuation (1 / 2) v) R
          linarith
        rw [norm_mul] at hprod
        have : ‖masslessContinuation (1 / 2) v‖ ≤ (‖R‖ + 1) / ‖v - v₀‖ := by
          rw [le_div_iff₀ hgap0]; linarith
        linarith
      · have hvK : v ∈ Kc := by
          refine Complex.mem_reProdIm.mpr ⟨⟨by rw [hvre]; positivity, by rw [hvre]; nlinarith⟩,
            ⟨by rw [hvim]; nlinarith, ?_⟩⟩
          rw [hvim]
          by_contra hcon'
          have hcon := not_le.mp hcon'
          apply hnear
          rw [dist_eq_norm]
          have hd : ‖v - v₀‖ ≤ (1 - t) * Real.log n₀ + (1 - t * (1 - ε)) := by
            refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
            rw [Complex.sub_re, Complex.sub_im, hvre, hvim, hv₀, Complex.add_re, Complex.add_im,
              Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, add_zero, zero_add]
            rw [abs_of_nonpos (by nlinarith), abs_of_nonpos (by nlinarith)]
            linarith
          have h1 : 1 - t * (1 - ε) < η := by linarith
          have h2 : 1 - t < η := by nlinarith
          calc ‖v - v₀‖ ≤ (1 - t) * Real.log n₀ + (1 - t * (1 - ε)) := hd
            _ ≤ η * Real.log n₀ + η := by nlinarith
            _ < δ := by
              rw [hη]; field_simp; nlinarith
        have := hM₂ v hvK
        have : 0 ≤ (‖R‖ + 1) / ‖v - v₀‖ := by positivity
        linarith
    calc ε * ‖masslessZeroWave v‖ ≤ ε * (M₂ + (‖R‖ + 1) / ‖v - v₀‖) :=
          mul_le_mul_of_nonneg_left hbound hε0.le
      _ = ε * M₂ + (‖R‖ + 1) * (ε / ‖v - v₀‖) := by ring
      _ ≤ 1 * M₂ + (‖R‖ + 1) * 2 := by
          gcongr
          rw [div_le_iff₀ hgap0]; linarith
      _ = M₂ + 2 * (‖R‖ + 1) := by ring
  set CB := Real.exp ((‖v₀‖ + 1) ^ 2 / 2)
  have hpart2 : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in (0 : ℝ)..1,
      lightConeBessel (2 * (zε ε) ^ 2 * (1 - (t : ℂ) ^ 2)) * masslessZeroWave (zε ε * t))
      (𝓝[>] 0) (𝓝 0) := by
    have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := 0) (b := 1) (l := 𝓝[>] (0 : ℝ)) (f := fun _ => (0 : ℂ))
      (F := fun ε t => (ε : ℂ) * (lightConeBessel (2 * (zε ε) ^ 2 * (1 - (t : ℂ) ^ 2)) *
        masslessZeroWave (zε ε * t)))
      (fun _ => CB * (M₂ + 2 * (‖R‖ + 1))) ?_ ?_ intervalIntegrable_const ?_
    · simp only [intervalIntegral.integral_zero] at hlim
      refine hlim.congr' (Eventually.of_forall fun ε => ?_)
      simp only
      rw [intervalIntegral.integral_const_mul]
    · filter_upwards [hsmall] with ε hε
      refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_uIoc
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hstrip : zε ε * t ∈ causalTimeStrip := by
        show |(zε ε * t).im| < 1
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, hzim,
          abs_mul, abs_of_pos (by linarith [hε.2] : (0 : ℝ) < 1 - ε), abs_of_pos ht.1]
        have : (1 - ε) * t ≤ 1 - ε := mul_le_of_le_one_right (by linarith [hε.2]) ht.2
        linarith [hε.1]
      have hcont : ContinuousAt (fun t : ℝ => masslessZeroWave (zε ε * t)) t :=
        ContinuousAt.comp (f := fun t : ℝ => zε ε * t) (g := masslessZeroWave)
          ((differentiableOn_masslessZeroWave.differentiableAt
            (isOpen_causalTimeStrip.mem_nhds hstrip)).continuousAt)
          (continuous_const.mul continuous_ofReal).continuousAt
      exact (continuousAt_const.mul (((differentiable_lightConeBessel.continuous.comp
        (by fun_prop : Continuous fun t : ℝ => 2 * (zε ε) ^ 2 * (1 - (t : ℂ) ^ 2))).continuousAt).mul
          hcont)).continuousWithinAt
    · filter_upwards [hsmall] with ε hε
      refine Eventually.of_forall fun t ht => ?_
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hta : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      have hzn : ‖zε ε‖ ≤ ‖v₀‖ + 1 := by
        simp only [hzε]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
          abs_of_pos hε.1]
        linarith [hε.2]
      have hB : ‖lightConeBessel (2 * (zε ε) ^ 2 * (1 - (t : ℂ) ^ 2))‖ ≤ CB :=
        (norm_lightConeBessel_light_cone_le _ hta).trans (Real.exp_le_exp.mpr (by gcongr))
      have hk := hkey ε hε.1 hε.2.le t ht.1.le ht.2
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε.1]
      calc ε * (‖lightConeBessel (2 * (zε ε) ^ 2 * (1 - (t : ℂ) ^ 2))‖ *
            ‖masslessZeroWave (zε ε * t)‖)
          = ‖lightConeBessel (2 * (zε ε) ^ 2 * (1 - (t : ℂ) ^ 2))‖ *
              (ε * ‖masslessZeroWave (zε ε * t)‖) := by ring
        _ ≤ CB * (M₂ + 2 * (‖R‖ + 1)) :=
            mul_le_mul hB hk (mul_nonneg hε.1.le (norm_nonneg _)) (Real.exp_pos _).le
    · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t ht1 ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
      have hz0 : Tendsto zε (𝓝[>] 0) (𝓝 v₀) := hmap.mono_right nhdsWithin_le_nhds
      have hstrip0 : v₀ * t ∈ causalTimeStrip := by
        show |(v₀ * t).im| < 1
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, hv₀,
          Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add, one_mul, abs_of_pos ht.1]
        exact htlt
      have hΦ : Tendsto (fun ε => masslessZeroWave (zε ε * t)) (𝓝[>] 0)
          (𝓝 (masslessZeroWave (v₀ * t))) :=
        ((differentiableOn_masslessZeroWave.differentiableAt
          (isOpen_causalTimeStrip.mem_nhds hstrip0)).continuousAt.tendsto).comp
          (hz0.mul_const _)
      have hBl : Tendsto (fun ε => lightConeBessel (2 * (zε ε) ^ 2 * (1 - (t : ℂ) ^ 2))) (𝓝[>] 0)
          (𝓝 (lightConeBessel (2 * v₀ ^ 2 * (1 - (t : ℂ) ^ 2)))) :=
        (differentiable_lightConeBessel.continuous.tendsto _).comp
          (((hz0.pow 2).const_mul 2).mul_const _)
      have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
        have := (continuous_ofReal.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      simpa using hε.mul (hBl.mul hΦ)
  -- assembly
  have hzt : Tendsto zε (𝓝[>] 0) (𝓝 v₀) := hmap.mono_right nhdsWithin_le_nhds
  have hlimit := hpart1.sub ((hzt.pow 2).mul hpart2)
  have hval : I * R - v₀ ^ 2 * 0 = -2 / π * chmdPrimeWeight n₀ := by
    rw [hR, mul_zero, sub_zero, show I * (2 * I / (π : ℂ) * chmdPrimeWeight n₀) =
      2 * (I * I) / π * chmdPrimeWeight n₀ by ring, I_mul_I]
    ring
  rw [hval] at hlimit
  refine hlimit.congr' ?_
  filter_upwards [hsmall] with ε hε
  have hzs : |(zε ε).im| < 1 := by
    rw [hzim, abs_lt]; constructor <;> linarith [hε.1, hε.2]
  show _ = (ε : ℂ) * kgZeroWave (zε ε)
  rw [kgZeroWave_eq_lightConeTransmuteC hzs, lightConeTransmuteC]
  ring

/-! ## Symmetries -/

theorem kgZeroWave_neg (z : ℂ) : kgZeroWave (-z) = kgZeroWave z := by
  unfold kgZeroWave
  exact tsum_congr fun ρ => by rw [neg_mul, Complex.cos_neg]

theorem kgZeroWave_conj (z : ℂ) : kgZeroWave (conj z) = conj (kgZeroWave z) := by
  unfold kgZeroWave
  rw [Complex.conj_tsum, ← reflectEquiv.tsum_eq]
  refine tsum_congr fun ρ => ?_
  simp only [reflectEquiv, Equiv.coe_fn_mk, mult_reflectZero, kgFreq_reflectZero,
    kgWeight_reflectZero, map_mul, map_natCast, ← Complex.cos_conj]

/-- **The boundary law at all four families** `±log n ± i`. -/
theorem tendsto_kgZeroWave_boundary_four {n : ℕ} (hw : chmdPrimeWeight n ≠ 0) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * kgZeroWave ((Real.log n : ℂ) + I - ε * I)) (𝓝[>] 0)
        (𝓝 (-2 / π * chmdPrimeWeight n)) ∧
    Tendsto (fun ε : ℝ => (ε : ℂ) * kgZeroWave ((Real.log n : ℂ) - I + ε * I)) (𝓝[>] 0)
        (𝓝 (-2 / π * chmdPrimeWeight n)) ∧
    Tendsto (fun ε : ℝ => (ε : ℂ) * kgZeroWave (-(Real.log n : ℂ) + I - ε * I)) (𝓝[>] 0)
        (𝓝 (-2 / π * chmdPrimeWeight n)) ∧
    Tendsto (fun ε : ℝ => (ε : ℂ) * kgZeroWave (-(Real.log n : ℂ) - I + ε * I)) (𝓝[>] 0)
        (𝓝 (-2 / π * chmdPrimeWeight n)) := by
  have ha := tendsto_kgZeroWave_boundary hw
  have hconj : ∀ ε : ℝ, (Real.log n : ℂ) - I + ε * I = conj ((Real.log n : ℂ) + I - ε * I) := by
    intro ε
    rw [map_sub, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hb : Tendsto (fun ε : ℝ => (ε : ℂ) * kgZeroWave ((Real.log n : ℂ) - I + ε * I)) (𝓝[>] 0)
      (𝓝 (-2 / π * chmdPrimeWeight n)) := by
    have h := (Complex.continuous_conj.tendsto _).comp ha
    have hc : conj (-2 / (π : ℂ) * chmdPrimeWeight n) = -2 / π * chmdPrimeWeight n := by
      rw [map_mul, map_div₀, map_neg, Complex.conj_ofReal, Complex.conj_ofReal, map_ofNat]
    rw [hc] at h
    refine h.congr fun ε => ?_
    simp only [Function.comp, hconj, kgZeroWave_conj, map_mul, Complex.conj_ofReal]
  refine ⟨ha, hb, ?_, ?_⟩
  · refine hb.congr fun ε => ?_
    rw [← kgZeroWave_neg]; congr 2; ring
  · refine ha.congr fun ε => ?_
    rw [← kgZeroWave_neg]; congr 2; ring

end RHTower.CHMDLightCone
