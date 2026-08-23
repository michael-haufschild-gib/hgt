import GaloisForLFunctions.RHTower.BurnolEvaluatorSystemZ
import GaloisForLFunctions.RHTower.SoninDilationMellin

/-!
# Burnol's Lemma 7.5: minimality at aperture `a` kills completeness below `a`

If some vector of `L_a` annihilates every evaluator of the system attached to `(Z,m)` except the
top one at `ρ` — that is, its continued Mellin transform vanishes to order `m(w)` at every other
`w ∈ Z` and to order at least `m(ρ) - 1` at `ρ` — then for every smaller aperture `b < a` there is a
*nonzero* vector of `L_b` annihilating **all** the evaluators.  So the system cannot be complete
in `L_b`.

Burnol multiplies the transform by the Mellin transform `θ(s)` of a bump supported near `1`, then
by `(s - ρ)` to force `θ(ρ) = 0`.  Here the same effect is obtained from a single dilation: the
combination `U_r v - r^{ρ-1/2} v` has continued Mellin transform `(r^{s-1/2} - r^{ρ-1/2})·M(v)(s)`,
whose multiplier is entire, vanishes at `ρ`, and is not identically zero; and dilating by `r > 1`
moves `L_a` into `L_{a/r}`.

## Main results

* `exists_nonzero_annihilating_of_lt` — **Lemma 7.5**
* `not_isCompleteEvaluatorSystem_of_lt`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem integrableOn_cpow_mul_Ioi_zero {a : ℝ} (ha : 0 < a) {f : SoninL2} {d : ℂ}
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {s : ℂ} (hs1 : 1 / 2 < s.re) (hs2 : s.re < 1) :
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t) (Ioi (0 : ℝ)) volume := by
  have hhead : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) a)), (f : ℝ → ℂ) t = d := by
    filter_upwards [ae_restrict_of_ae hd,
      self_mem_ae_restrict (measurableSet_Ioc (a := (0 : ℝ)) (b := a))] with t ht hmem
    refine ht ?_
    rcases hmem with ⟨h1, h2⟩
    exact ⟨by linarith, h2⟩
  have hint1 : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t)
      (Ioc (0 : ℝ) a) volume := by
    refine (integrableOn_head_cpow ha hs2 d).congr_fun_ae ?_
    filter_upwards [hhead] with t ht
    rw [ht]
  have hint2 : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t)
      (Ioi a) volume := integrableOn_cpow_mul_Ioi ha f hs1
  have hunion := hint1.union hint2
  rwa [Ioc_union_Ioi_eq_Ioi ha.le] at hunion

/-- **The dilation shift.**  Passing from aperture `a` to any smaller aperture `b` one may multiply
the continued Mellin transform by the entire multiplier `(a/b)^{s-1/2} - (a/b)^{ρ-1/2}`, which
vanishes at the prescribed point `ρ`. -/
theorem exists_dilationShift {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < a)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {v : SoninL2} {c d : ℂ} (hev : v ∈ evenSubspace)
    (hmem : v ∈ centralSoninExtendedCarrier a)
    (hc : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d)
    (hv : v ≠ 0) :
    ∃ (V : SoninL2) (c' d' : ℂ), V ≠ 0 ∧ V ∈ evenSubspace ∧
      V ∈ centralSoninExtendedCarrier b ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval b →
        ((fourierUnitary V : SoninL2) : ℝ → ℂ) x = c') ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (V : ℝ → ℂ) t = d') ∧
      ∀ w : ℂ, 0 < w.re → w.re < 1 →
        meromorphicOrderAt (extendedMellinContinuation b c' d' V) w
          = meromorphicOrderAt (dilationDifferenceMultiplier (a / b) ρ) w
            + meromorphicOrderAt (extendedMellinContinuation a c d v) w := by
  classical
  set r : ℝ := a / b with hr
  have hr0 : 0 < r := div_pos ha hb
  have hr1 : r ≠ 1 := by
    intro h
    rw [hr, div_eq_one_iff_eq (ne_of_gt hb)] at h
    linarith
  set lam : ℂ := ((r : ℝ) : ℂ) ^ (ρ - 1 / 2) with hlam
  set V : SoninL2 := rayDilate r v - lam • v with hV
  -- membership
  have hdil : rayDilate r v ∈ centralSoninExtendedCarrier b := by
    rw [rayDilate_of_pos hr0]
    refine dilation_mem_centralSoninExtendedCarrier hr0 hmem ?_ ?_
    · have hval : a / r = b := by
        rw [hr]
        field_simp
      rw [hval]
    · have hval : a * r = a * a / b := by
        rw [hr]
        ring
      rw [hval, le_div_iff₀ hb]
      nlinarith
  have hvb : v ∈ centralSoninExtendedCarrier b :=
    centralSoninExtendedCarrier_antitone hab.le hmem
  have hVmem : V ∈ centralSoninExtendedCarrier b :=
    Submodule.sub_mem _ hdil (Submodule.smul_mem _ _ hvb)
  have hVev : V ∈ evenSubspace := by
    refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ hev)
    rw [rayDilate_of_pos hr0]
    exact dilation_mem_evenSubspace hr0 hev
  obtain ⟨c', hc'⟩ := ae_fourier_eq_of_mem_extended hVmem
  obtain ⟨d', hd'⟩ := ae_eq_of_mem_extended hVmem
  -- the multiplier identity on the convergence strip
  have hstrip : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      extendedMellinContinuation b c' d' V s
        = dilationDifferenceMultiplier r ρ s * extendedMellinContinuation a c d v s := by
    intro s hs1 hs2
    have hVint : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (rayDilate r v : ℝ → ℂ) t)
        (Ioi (0 : ℝ)) volume := by
      obtain ⟨dd, hdd⟩ := ae_eq_of_mem_extended hdil
      exact integrableOn_cpow_mul_Ioi_zero hb hdd hs1 hs2
    have hvint : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (v : ℝ → ℂ) t)
        (Ioi (0 : ℝ)) volume := integrableOn_cpow_mul_Ioi_zero ha hd hs1 hs2
    have hsub : soninMellinIntegral V s
        = soninMellinIntegral (rayDilate r v) s - lam * soninMellinIntegral v s := by
      rw [soninMellinIntegral, soninMellinIntegral, soninMellinIntegral,
        ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_sub hVint (hvint.const_mul lam)]
      refine setIntegral_congr_ae measurableSet_Ioi ?_
      filter_upwards [Lp.coeFn_sub (rayDilate r v) (lam • v), Lp.coeFn_smul lam v] with t h1 h2 _
      rw [hV, h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul]
      ring
    rw [extendedMellinContinuation_eq_soninMellinIntegral hb hVev hc' hd' hs1 hs2, hsub,
      soninMellinIntegral_rayDilate hr0 v s,
      ← extendedMellinContinuation_eq_soninMellinIntegral ha hev hc hd hs1 hs2,
      dilationDifferenceMultiplier, hlam]
    ring
  -- propagate to the whole strip
  have hA1 : AnalyticOnNhd ℂ (extendedMellinContinuation b c' d' V)
      {y : ℂ | 0 < y.re ∧ y.re < 1} := by
    intro y hy
    have hy0 : y ≠ 0 := by intro h; rw [h] at hy; norm_num at hy
    have hy1 : y ≠ 1 := by intro h; rw [h] at hy; norm_num at hy
    exact analyticAt_extendedMellinContinuation_of_ne hb hVev hc' hd' hy0 hy1
  have hA2 : AnalyticOnNhd ℂ
      (fun s : ℂ => dilationDifferenceMultiplier r ρ s * extendedMellinContinuation a c d v s)
      {y : ℂ | 0 < y.re ∧ y.re < 1} := by
    intro y hy
    have hy0 : y ≠ 0 := by intro h; rw [h] at hy; norm_num at hy
    have hy1 : y ≠ 1 := by intro h; rw [h] at hy; norm_num at hy
    exact ((differentiable_dilationDifferenceMultiplier hr0 ρ).analyticAt y).mul
      (analyticAt_extendedMellinContinuation_of_ne ha hev hc hd hy0 hy1)
  have hz₀ : ((3 / 4 : ℝ) : ℂ) ∈ {y : ℂ | 0 < y.re ∧ y.re < 1} := by
    constructor <;> simp <;> norm_num
  have hev₀ : extendedMellinContinuation b c' d' V =ᶠ[𝓝 ((3 / 4 : ℝ) : ℂ)]
      fun s : ℂ => dilationDifferenceMultiplier r ρ s * extendedMellinContinuation a c d v s := by
    have hopen : IsOpen {y : ℂ | 1 / 2 < y.re ∧ y.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hmem₀ : ((3 / 4 : ℝ) : ℂ) ∈ {y : ℂ | 1 / 2 < y.re ∧ y.re < 1} := by
      constructor <;> simp <;> norm_num
    filter_upwards [hopen.mem_nhds hmem₀] with y hy
    exact hstrip y hy.1 hy.2
  have hall : ∀ y : ℂ, 0 < y.re → y.re < 1 →
      extendedMellinContinuation b c' d' V y
        = dilationDifferenceMultiplier r ρ y * extendedMellinContinuation a c d v y :=
    fun y hy0 hy1 =>
      hA1.eqOn_of_preconnected_of_eventuallyEq hA2 isPreconnected_criticalStrip hz₀ hev₀ ⟨hy0, hy1⟩
  -- orders
  have hordfun : ∀ y : ℂ, 0 < y.re → y.re < 1 →
      meromorphicOrderAt (extendedMellinContinuation b c' d' V) y
        = meromorphicOrderAt (dilationDifferenceMultiplier r ρ) y
          + meromorphicOrderAt (extendedMellinContinuation a c d v) y := by
    intro y hy0 hy1
    have heq : extendedMellinContinuation b c' d' V
        =ᶠ[𝓝[≠] y] (dilationDifferenceMultiplier r ρ) * extendedMellinContinuation a c d v := by
      refine EventuallyEq.filter_mono ?_ nhdsWithin_le_nhds
      filter_upwards [isOpen_criticalOpenStrip.mem_nhds
        (⟨hy0, hy1⟩ : y ∈ {u : ℂ | 0 < u.re ∧ u.re < 1})] with u hu
      rw [Pi.mul_apply]
      exact hall u hu.1 hu.2
    rw [meromorphicOrderAt_congr heq,
      meromorphicOrderAt_mul ((differentiable_dilationDifferenceMultiplier hr0 ρ).analyticAt y).meromorphicAt
        (meromorphicAt_extendedMellinContinuation ha hev hc hd y)]
  have hmultρ : ((1 : ℤ) : WithTop ℤ)
      ≤ meromorphicOrderAt (dilationDifferenceMultiplier r ρ) ρ :=
    one_le_meromorphicOrderAt_of_eq_zero
      ((differentiable_dilationDifferenceMultiplier hr0 ρ).analyticAt ρ)
      (dilationDifferenceMultiplier_self r ρ)
  have hmultnn : ∀ y : ℂ, (0 : WithTop ℤ)
      ≤ meromorphicOrderAt (dilationDifferenceMultiplier r ρ) y := fun y =>
    meromorphicOrderAt_nonneg_of_analyticAt
      ((differentiable_dilationDifferenceMultiplier hr0 ρ).analyticAt y)
  -- finiteness at `ρ`
  have hmultfin : meromorphicOrderAt (dilationDifferenceMultiplier r ρ) ρ ≠ ⊤ := by
    intro htop
    have hana : AnalyticAt ℂ (dilationDifferenceMultiplier r ρ) ρ :=
      (differentiable_dilationDifferenceMultiplier hr0 ρ).analyticAt ρ
    have hordtop : analyticOrderAt (dilationDifferenceMultiplier r ρ) ρ = ⊤ := by
      rw [hana.meromorphicOrderAt_eq] at htop
      induction hx : analyticOrderAt (dilationDifferenceMultiplier r ρ) ρ with
      | top => rfl
      | coe n =>
          rw [hx] at htop
          simp at htop
    have hzero := analyticOrderAt_eq_top.1 hordtop
    have hA : AnalyticOnNhd ℂ (dilationDifferenceMultiplier r ρ) Set.univ :=
      fun y _ => (differentiable_dilationDifferenceMultiplier hr0 ρ).analyticAt y
    have hB : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ := fun _ _ => analyticAt_const
    have hallz := hA.eqOn_of_preconnected_of_eventuallyEq hB isPreconnected_univ (Set.mem_univ ρ)
      (by filter_upwards [hzero] with y hy; exact hy) (Set.mem_univ (ρ + 1))
    exact dilationDifferenceMultiplier_ne_zero hr0 hr1 ρ hallz
  have hvfin : meromorphicOrderAt (extendedMellinContinuation a c d v) ρ ≠ ⊤ :=
    meromorphicOrderAt_extendedMellin_ne_top ha hev hc hd hv hρ0 hρ1
  -- `V` is nonzero
  have hVne : V ≠ 0 := by
    intro hV0
    have hzero : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
        extendedMellinContinuation b c' d' V s = 0 := by
      intro s hs1 hs2
      rw [extendedMellinContinuation_eq_soninMellinIntegral hb hVev hc' hd' hs1 hs2,
        soninMellinIntegral]
      refine integral_eq_zero_of_ae ?_
      have hzc : ((V : SoninL2) : ℝ → ℂ) =ᵐ[volume] 0 := by
        rw [hV0]
        exact Lp.coeFn_zero ℂ 2 volume
      filter_upwards [ae_restrict_of_ae hzc] with t ht
      simp [ht]
    have hordV : meromorphicOrderAt (extendedMellinContinuation b c' d' V) ρ
        = meromorphicOrderAt (dilationDifferenceMultiplier r ρ) ρ
          + meromorphicOrderAt (extendedMellinContinuation a c d v) ρ := hordfun ρ hρ0 hρ1
    -- but a function vanishing on an open subset of the strip has order `⊤` at `ρ`
    have hA0 : AnalyticOnNhd ℂ (extendedMellinContinuation b c' d' V)
        {y : ℂ | 0 < y.re ∧ y.re < 1} := hA1
    have hB0 : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) {y : ℂ | 0 < y.re ∧ y.re < 1} :=
      fun _ _ => analyticAt_const
    have hzz : extendedMellinContinuation b c' d' V =ᶠ[𝓝 ((3 / 4 : ℝ) : ℂ)] fun _ : ℂ => 0 := by
      have hopen : IsOpen {y : ℂ | 1 / 2 < y.re ∧ y.re < 1} :=
        (isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const)
      have hmem₀ : ((3 / 4 : ℝ) : ℂ) ∈ {y : ℂ | 1 / 2 < y.re ∧ y.re < 1} := by
        constructor <;> simp <;> norm_num
      filter_upwards [hopen.mem_nhds hmem₀] with y hy
      exact hzero y hy.1 hy.2
    have hnb : extendedMellinContinuation b c' d' V =ᶠ[𝓝 ρ] fun _ : ℂ => 0 := by
      have hallzero : ∀ y : ℂ, 0 < y.re → y.re < 1 →
          extendedMellinContinuation b c' d' V y = 0 := fun y hy0 hy1 =>
        hA0.eqOn_of_preconnected_of_eventuallyEq hB0 isPreconnected_criticalStrip hz₀ hzz
          ⟨hy0, hy1⟩
      filter_upwards [isOpen_criticalOpenStrip.mem_nhds
        (⟨hρ0, hρ1⟩ : ρ ∈ {u : ℂ | 0 < u.re ∧ u.re < 1})] with y hy
      exact hallzero y hy.1 hy.2
    have hordtop : meromorphicOrderAt (extendedMellinContinuation b c' d' V) ρ = ⊤ := by
      have hana : AnalyticAt ℂ (extendedMellinContinuation b c' d' V) ρ := hA1 ρ ⟨hρ0, hρ1⟩
      rw [hana.meromorphicOrderAt_eq, analyticOrderAt_eq_top.2 (by
        filter_upwards [hnb] with y hy; exact hy)]
      rfl
    rw [hordtop] at hordV
    induction h1 : meromorphicOrderAt (dilationDifferenceMultiplier r ρ) ρ with
    | top => exact hmultfin h1
    | coe n =>
        induction h2 : meromorphicOrderAt (extendedMellinContinuation a c d v) ρ with
        | top => exact hvfin h2
        | coe k =>
            rw [h1, h2, ← WithTop.coe_add] at hordV
            exact absurd hordV.symm WithTop.coe_ne_top
  exact ⟨V, c', d', hVne, hVev, hVmem, hc', hd', hordfun⟩

/-- **Burnol's Lemma 7.5.** -/
theorem exists_nonzero_annihilating_of_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < a)
    {Z : Set ℂ} {m : ℂ → ℕ} (hZ : ∀ w ∈ Z, 0 < w.re ∧ w.re < 1)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {v : SoninL2} {c d : ℂ} (hev : v ∈ evenSubspace)
    (hmem : v ∈ centralSoninExtendedCarrier a)
    (hc : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d)
    (hv : v ≠ 0)
    (hother : ∀ w ∈ Z, w ≠ ρ →
      ((m w : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (extendedMellinContinuation a c d v) w)
    (hself : (((m ρ : ℤ) - 1 : ℤ) : WithTop ℤ)
      ≤ meromorphicOrderAt (extendedMellinContinuation a c d v) ρ)
    (hρZ : ρ ∈ Z) :
    ∃ (V : SoninL2) (c' d' : ℂ), V ≠ 0 ∧ V ∈ evenSubspace ∧
      V ∈ centralSoninExtendedCarrier b ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval b →
        ((fourierUnitary V : SoninL2) : ℝ → ℂ) x = c') ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (V : ℝ → ℂ) t = d') ∧
      ∀ w ∈ Z, ((m w : ℤ) : WithTop ℤ)
        ≤ meromorphicOrderAt (extendedMellinContinuation b c' d' V) w := by
  have hr0 : 0 < a / b := div_pos ha hb
  obtain ⟨V, c', d', hVne, hVev, hVmem, hc', hd', hordfun⟩ :=
    exists_dilationShift ha hb hab hρ0 hρ1 hev hmem hc hd hv
  have hmultρ : ((1 : ℤ) : WithTop ℤ)
      ≤ meromorphicOrderAt (dilationDifferenceMultiplier (a / b) ρ) ρ :=
    one_le_meromorphicOrderAt_of_eq_zero
      ((differentiable_dilationDifferenceMultiplier hr0 ρ).analyticAt ρ)
      (dilationDifferenceMultiplier_self (a / b) ρ)
  have hmultnn : ∀ y : ℂ, (0 : WithTop ℤ)
      ≤ meromorphicOrderAt (dilationDifferenceMultiplier (a / b) ρ) y := fun y =>
    meromorphicOrderAt_nonneg_of_analyticAt
      ((differentiable_dilationDifferenceMultiplier hr0 ρ).analyticAt y)
  refine ⟨V, c', d', hVne, hVev, hVmem, hc', hd', ?_⟩
  intro w hw
  obtain ⟨hw0, hw1⟩ := hZ w hw
  rw [hordfun w hw0 hw1]
  by_cases hwρ : w = ρ
  · subst hwρ
    have hmw : ((m w : ℤ) : WithTop ℤ)
        = ((1 : ℤ) : WithTop ℤ) + (((m w : ℤ) - 1 : ℤ) : WithTop ℤ) := by
      rw [← WithTop.coe_add]
      congr 1
      ring
    rw [hmw]
    exact add_le_add hmultρ hself
  · have h0 : (0 : WithTop ℤ) + ((m w : ℤ) : WithTop ℤ) = ((m w : ℤ) : WithTop ℤ) := zero_add _
    rw [← h0]
    exact add_le_add (hmultnn w) (hother w hw hwρ)

/-- **Lemma 7.5, packaged**: minimality data at aperture `a` destroys completeness at every
smaller aperture. -/
theorem not_isCompleteEvaluatorSystem_of_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < a)
    {Z : Set ℂ} {m : ℂ → ℕ} (hZ : ∀ w ∈ Z, 0 < w.re ∧ w.re < 1)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {v : SoninL2} {c d : ℂ} (hev : v ∈ evenSubspace)
    (hmem : v ∈ centralSoninExtendedCarrier a)
    (hc : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d)
    (hv : v ≠ 0)
    (hother : ∀ w ∈ Z, w ≠ ρ →
      ((m w : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (extendedMellinContinuation a c d v) w)
    (hself : (((m ρ : ℤ) - 1 : ℤ) : WithTop ℤ)
      ≤ meromorphicOrderAt (extendedMellinContinuation a c d v) ρ)
    (hρZ : ρ ∈ Z) :
    ¬ IsCompleteEvaluatorSystem b Z m := by
  intro hcomp
  obtain ⟨V, c', d', hVne, hVev, _hVmem, hc', hd', hann⟩ :=
    exists_nonzero_annihilating_of_lt ha hb hab hZ hρ0 hρ1 hev hmem hc hd hv hother hself hρZ
  exact hVne (hcomp V c' d' hVev hc' hd' hann)

end

end RHTower
