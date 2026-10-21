import GaloisForLFunctions.RHTower.ZetaDiscRecurrenceOnZeroFreeDiscs

/-!
# Fixed-base recurrence of `ζ` on every closed disc of the strip

The disc-uniform Carlson tail laws (`eventually_eventually_volume_discTailBadSet_le`,
`eventually_eventually_volume_eulerDiscTailBadSet_le`) control the heights at which the Dirichlet
head, respectively the finite Euler product, misses `ζ` somewhere on `closedBall c r`.  They were
proved under the doubled-closure margin `closedBall c (2r) ⊂ {1/2 < Re s < 1}`, because the
planar mean-value discs that turn the sup on the disc into a planar energy have the same radius
`r`.  This file removes the margin by a finite covering: a closed disc `closedBall c r` with
`closedBall c R` in the strip for some `R > r` is covered by finitely many balls of radius
`ρ = (R − r)/2` centred in it, each of whose doubled closures lies in the strip, and the bad set of
the big disc is contained in the finite union of the bad sets of the small discs
(`discTailBadSet_subset_biUnion`, `eulerDiscTailBadSet_subset_biUnion`).  Densities add over a
finite union (`eventually_volume_biUnion_inter_Icc_le`), so both tail laws hold on every closed
disc of the open strip (`eventually_eventually_volume_discTailBadSet_le_of_lt`,
`eventually_eventually_volume_eulerDiscTailBadSet_le_of_lt`).

Consequences:

* `zetaDiscStronglyRecurrentOn_of_zeroFree_of_lt`: if `ζ` has no zero on `ball c R` and
  `closedBall c R` lies in the strip, then `ζ` is strongly recurrent on `closedBall c r` for every
  `r < R`;
* `zetaDiscStronglyRecurrentOn_iff_headTargetUniformlyDense_of_lt`: on every closed disc of the
  strip, strong recurrence is equivalent to cutoff-uniform head-target density;
* `riemannHypothesis_iff_forall_closedBall_zetaDiscStronglyRecurrentOn` and
  `riemannHypothesis_iff_forall_closedBall_headTargetUniformlyDense`: the Riemann hypothesis holds
  if and only if `ζ` is strongly recurrent on every closed disc of the open strip, equivalently
  if and only if the Dirichlet heads approximate `ζ` on every such disc at cutoff-uniform positive
  density;
* `riemannHypothesis_iff_zetaDiscRecurrent`: **Bagchi's criterion in disc form** — the Riemann
  hypothesis is equivalent to the disc recurrence `ZetaDiscRecurrent` of the receiver.
-/

open Complex Filter Topology Metric MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace RHTower

/-! ## Finite covers of a closed disc and finite unions of bad sets -/

/-- A closed disc is covered by finitely many balls of radius `ρ` centred in it. -/
theorem exists_finset_closedBall_subset_biUnion_ball (c : ℂ) (r : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ t : Finset ℂ, (↑t : Set ℂ) ⊆ closedBall c r ∧ closedBall c r ⊆ ⋃ x ∈ t, ball x ρ := by
  obtain ⟨t, hts, htf, hcov⟩ := finite_cover_balls_of_compact (isCompact_closedBall c r) hρ
  refine ⟨htf.toFinset, by simpa using hts, ?_⟩
  simpa [htf.coe_toFinset] using hcov

/-- The tail-bad set of the big disc lies in the union of the tail-bad sets of covering discs. -/
theorem discTailBadSet_subset_biUnion (M : ℕ) {c : ℂ} {r ρ ε : ℝ} {t : Finset ℂ}
    (hcov : closedBall c r ⊆ ⋃ x ∈ t, ball x ρ) :
    discTailBadSet M c r ε ⊆ ⋃ x ∈ t, discTailBadSet M x ρ ε := by
  rintro τ ⟨z, hz, hε⟩
  obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (hcov hz)
  exact Set.mem_iUnion₂.mpr ⟨x, hx, z, ball_subset_closedBall hzx, hε⟩

/-- The Euler-tail-bad set of the big disc lies in the union over covering discs. -/
theorem eulerDiscTailBadSet_subset_biUnion (y : ℕ) {c : ℂ} {r ρ ε : ℝ} {t : Finset ℂ}
    (hcov : closedBall c r ⊆ ⋃ x ∈ t, ball x ρ) :
    eulerDiscTailBadSet y c r ε ⊆ ⋃ x ∈ t, eulerDiscTailBadSet y x ρ ε := by
  rintro τ ⟨z, hz, hε⟩
  obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (hcov hz)
  exact Set.mem_iUnion₂.mpr ⟨x, hx, z, ball_subset_closedBall hzx, hε⟩

/-- **Densities add over a finite union.**  If each of the sets `S i`, `i ∈ t`, eventually has
`volume (S i ∩ [0, T]) ≤ δ' T`, then their union eventually has density at most `card t · δ'`. -/
theorem eventually_volume_biUnion_inter_Icc_le {ι : Type*} (t : Finset ι) (S : ι → Set ℝ)
    {δ' : ℝ}
    (h : ∀ i ∈ t, ∀ᶠ T : ℝ in atTop, volume (S i ∩ Icc 0 T) ≤ ENNReal.ofReal (δ' * T)) :
    ∀ᶠ T : ℝ in atTop,
      volume ((⋃ i ∈ t, S i) ∩ Icc 0 T) ≤ ENNReal.ofReal (t.card * δ' * T) := by
  filter_upwards [(Filter.eventually_all_finset t).mpr h, eventually_ge_atTop (0 : ℝ)]
    with T hT hT0
  rw [Set.iUnion₂_inter]
  calc volume (⋃ i ∈ t, S i ∩ Icc 0 T) ≤ ∑ i ∈ t, volume (S i ∩ Icc 0 T) :=
        measure_biUnion_finset_le t _
    _ ≤ ∑ i ∈ t, ENNReal.ofReal (δ' * T) := Finset.sum_le_sum hT
    _ = t.card * ENNReal.ofReal (δ' * T) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal (t.card * δ' * T) := by
        rw [mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg t.card), ENNReal.ofReal_natCast]

/-- The margin `card t · δ/(card t + 1) ≤ δ`. -/
theorem card_mul_div_card_add_one_le {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    (n : ℝ) * (δ / (n + 1)) ≤ δ := by
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

/-! ## The tail laws on every closed disc of the strip -/

/-- **Disc-uniform Carlson tail law, any margin.**  Let `closedBall c R` lie in `1/2 < Re s < 1`
and `r < R`.  For all large `M`, the heights `τ ∈ [0, T]` at which `|ζ − head_M| ≥ ε` somewhere on
`closedBall c r + iτ` have measure at most `δ T` for all large `T`. -/
theorem eventually_eventually_volume_discTailBadSet_le_of_lt {c : ℂ} {r R : ℝ}
    (hrR : r < R) (h0 : 1 / 2 < c.re - R) (h1 : c.re + R < 1) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      volume (discTailBadSet M c r ε ∩ Icc 0 T) ≤ ENNReal.ofReal (δ * T) := by
  set ρ : ℝ := (R - r) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  obtain ⟨t, hts, hcov⟩ := exists_finset_closedBall_subset_biUnion_ball c r hρ0
  set δ' : ℝ := δ / (t.card + 1) with hδ'
  have hδ'0 : 0 < δ' := by rw [hδ']; positivity
  -- every covering disc satisfies the doubled-closure margin
  have hsmall : ∀ x ∈ t, ∀ᶠ M : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      volume (discTailBadSet M x ρ ε ∩ Icc 0 T) ≤ ENNReal.ofReal (δ' * T) := by
    intro x hx
    have hxc : x ∈ closedBall c r := hts hx
    have hxre : c.re - r ≤ x.re := re_ge_of_mem_closedBall hxc
    have hxre' : x.re ≤ c.re + r := re_le_of_mem_closedBall hxc
    exact eventually_eventually_volume_discTailBadSet_le hρ0 (by rw [hρ]; linarith)
      (by rw [hρ]; linarith) hε hδ'0
  filter_upwards [(Filter.eventually_all_finset t).mpr hsmall] with M hM
  have hcard : (t.card : ℝ) * δ' ≤ δ := card_mul_div_card_add_one_le hδ.le t.card
  filter_upwards [eventually_volume_biUnion_inter_Icc_le t (fun x => discTailBadSet M x ρ ε)
    hM, eventually_ge_atTop (0 : ℝ)] with T hT hT0
  calc volume (discTailBadSet M c r ε ∩ Icc 0 T)
      ≤ volume ((⋃ x ∈ t, discTailBadSet M x ρ ε) ∩ Icc 0 T) :=
        measure_mono (inter_subset_inter_left _ (discTailBadSet_subset_biUnion M hcov))
    _ ≤ ENNReal.ofReal (t.card * δ' * T) := hT
    _ ≤ ENNReal.ofReal (δ * T) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hT0)

/-- **Disc-uniform Carlson tail law for the finite Euler product, any margin.**  Let
`closedBall c R` lie in `1/2 < Re s < 1` and `r < R`.  For all large `y`, the heights `τ ∈ [0, T]`
at which `|ζ − E_y| ≥ ε` somewhere on `closedBall c r + iτ` have measure at most `δ T` for all
large `T`. -/
theorem eventually_eventually_volume_eulerDiscTailBadSet_le_of_lt {c : ℂ} {r R : ℝ}
    (hrR : r < R) (h0 : 1 / 2 < c.re - R) (h1 : c.re + R < 1) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) :
    ∀ᶠ y : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      volume (eulerDiscTailBadSet y c r ε ∩ Icc 0 T) ≤ ENNReal.ofReal (δ * T) := by
  set ρ : ℝ := (R - r) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  obtain ⟨t, hts, hcov⟩ := exists_finset_closedBall_subset_biUnion_ball c r hρ0
  set δ' : ℝ := δ / (t.card + 1) with hδ'
  have hδ'0 : 0 < δ' := by rw [hδ']; positivity
  have hsmall : ∀ x ∈ t, ∀ᶠ y : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      volume (eulerDiscTailBadSet y x ρ ε ∩ Icc 0 T) ≤ ENNReal.ofReal (δ' * T) := by
    intro x hx
    have hxc : x ∈ closedBall c r := hts hx
    have hxre : c.re - r ≤ x.re := re_ge_of_mem_closedBall hxc
    have hxre' : x.re ≤ c.re + r := re_le_of_mem_closedBall hxc
    exact eventually_eventually_volume_eulerDiscTailBadSet_le hρ0 (by rw [hρ]; linarith)
      (by rw [hρ]; linarith) hε hδ'0
  filter_upwards [(Filter.eventually_all_finset t).mpr hsmall] with y hy
  have hcard : (t.card : ℝ) * δ' ≤ δ := card_mul_div_card_add_one_le hδ.le t.card
  filter_upwards [eventually_volume_biUnion_inter_Icc_le t
    (fun x => eulerDiscTailBadSet y x ρ ε) hy, eventually_ge_atTop (0 : ℝ)] with T hT hT0
  calc volume (eulerDiscTailBadSet y c r ε ∩ Icc 0 T)
      ≤ volume ((⋃ x ∈ t, eulerDiscTailBadSet y x ρ ε) ∩ Icc 0 T) :=
        measure_mono (inter_subset_inter_left _ (eulerDiscTailBadSet_subset_biUnion y hcov))
    _ ≤ ENNReal.ofReal (t.card * δ' * T) := hT
    _ ≤ ENNReal.ofReal (δ * T) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hT0)

/-! ## Recurrence on every closed disc of a zero-free region -/

/-- **Fixed-base recurrence of `ζ` on a closed disc with any margin.**  If `ζ` has no zero on
`ball c R`, `closedBall c R` lies in the strip and `r < R`, then `ζ` is strongly recurrent on
`closedBall c r`.  The Hardy disc has radius `(r + R)/2`, the zero-free disc of the universality
step has radius `((r + R)/2 + R)/2 < R`. -/
theorem zetaDiscStronglyRecurrentOn_of_zeroFree_of_lt {c : ℂ} {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) (h0 : 1 / 2 < c.re - R) (h1 : c.re + R < 1)
    (hζ : ∀ z ∈ ball c R, riemannZeta z ≠ 0) :
    ZetaDiscStronglyRecurrentOn (closedBall c r) := by
  set ρH : ℝ := (r + R) / 2 with hρH
  have hρH0 : 0 < ρH := by rw [hρH]; linarith
  have hρHne : ρH ≠ 0 := hρH0.ne'
  have hρHR : ρH < R := by rw [hρH]; linarith
  set R₂ : ℝ := (ρH + R) / (2 * ρH) with hR₂
  have hR₂1 : 1 < R₂ := by
    rw [hR₂, lt_div_iff₀ (by positivity)]
    linarith
  have hρHR₂ : ρH * R₂ = (ρH + R) / 2 := by
    rw [hR₂]
    field_simp
  set r₁ : ℝ := r / ρH with hr₁
  have hr₁0 : 0 ≤ r₁ := by positivity
  have hr₁1 : r₁ < 1 := by
    rw [hr₁, div_lt_one hρH0, hρH]
    linarith
  have hrr : ρH * r₁ = r := by
    rw [hr₁]
    field_simp
  intro ε hε
  obtain ⟨κ, hκ, y₁, hy₁⟩ := exists_uniform_pos_density_eulerTargetReturnSet_zeta c hρH0
    (by linarith) (by rw [hρH]; linarith) (by rw [hρH]; linarith) hR₂1 (by rw [hρHR₂]; linarith)
    (fun z hz => hζ z (ball_subset_ball (by rw [hρHR₂]; linarith) hz)) hr₁0 hr₁1 (half_pos hε)
  rw [hrr] at hy₁
  have hbad := eventually_eventually_volume_eulerDiscTailBadSet_le_of_lt hrR h0 h1
    (half_pos hε) (half_pos hκ)
  obtain ⟨y, hy, hyb⟩ := ((eventually_ge_atTop y₁).and hbad).exists
  refine ⟨κ / 2, half_pos hκ, ?_⟩
  filter_upwards [hy₁ y hy, hyb, eventually_ge_atTop (0 : ℝ)] with T hT1 hT2 hT0
  have hsub := eulerTargetReturnSet_diff_eulerDiscTailBadSet_subset_zetaReturnSet y c r
    (ε / 2) (ε / 2)
  rw [add_halves] at hsub
  exact (ofReal_half_le_volume_diff_inter hκ hT0 hT1 hT2).trans
    (measure_mono (inter_subset_inter_left _ hsub))

/-! ## Head-target density on every closed disc of the strip -/

/-- Uniform head-target density gives strong recurrence, on any closed disc of the strip. -/
theorem zetaDiscStronglyRecurrentOn_of_headTargetUniformlyDense_of_lt {c : ℂ} {r R : ℝ}
    (hrR : r < R) (h0 : 1 / 2 < c.re - R) (h1 : c.re + R < 1)
    (hU : HeadTargetUniformlyDense (closedBall c r)) :
    ZetaDiscStronglyRecurrentOn (closedBall c r) := by
  intro ε hε
  obtain ⟨c₀, hc₀, hM⟩ := hU (ε / 2) (half_pos hε)
  obtain ⟨M, hM1, hM2⟩ := (hM.and (eventually_eventually_volume_discTailBadSet_le_of_lt hrR
    h0 h1 (half_pos hε) (half_pos hc₀))).exists
  refine ⟨c₀ / 2, half_pos hc₀, ?_⟩
  filter_upwards [hM1, hM2, eventually_ge_atTop (0 : ℝ)] with T hT1 hT2 hT0
  have hsub := headTargetReturnSet_diff_discTailBadSet_subset_zetaReturnSet M c r (ε / 2) (ε / 2)
  rw [add_halves] at hsub
  exact (ofReal_half_le_volume_diff_inter hc₀ hT0 hT1 hT2).trans
    (measure_mono (inter_subset_inter_left _ hsub))

/-- Strong recurrence gives uniform head-target density, on any closed disc of the strip. -/
theorem headTargetUniformlyDense_of_zetaDiscStronglyRecurrentOn_of_lt {c : ℂ} {r R : ℝ}
    (hrR : r < R) (h0 : 1 / 2 < c.re - R) (h1 : c.re + R < 1)
    (hR : ZetaDiscStronglyRecurrentOn (closedBall c r)) :
    HeadTargetUniformlyDense (closedBall c r) := by
  intro ε hε
  obtain ⟨κ, hκ, hT⟩ := hR (ε / 2) (half_pos hε)
  refine ⟨κ / 2, half_pos hκ, ?_⟩
  filter_upwards [eventually_eventually_volume_discTailBadSet_le_of_lt hrR h0 h1
    (half_pos hε) (half_pos hκ)] with M hM
  filter_upwards [hT, hM, eventually_ge_atTop (0 : ℝ)] with T hT1 hT2 hT0
  have hsub := zetaReturnSet_diff_discTailBadSet_subset_headTargetReturnSet M c r (ε / 2) (ε / 2)
  rw [add_halves] at hsub
  exact (ofReal_half_le_volume_diff_inter hκ hT0 hT1 hT2).trans
    (measure_mono (inter_subset_inter_left _ hsub))

/-- **Fixed-base recurrence is uniform head-target density on every closed disc of the strip.** -/
theorem zetaDiscStronglyRecurrentOn_iff_headTargetUniformlyDense_of_lt {c : ℂ} {r R : ℝ}
    (hrR : r < R) (h0 : 1 / 2 < c.re - R) (h1 : c.re + R < 1) :
    ZetaDiscStronglyRecurrentOn (closedBall c r) ↔ HeadTargetUniformlyDense (closedBall c r) :=
  ⟨headTargetUniformlyDense_of_zetaDiscStronglyRecurrentOn_of_lt hrR h0 h1,
    zetaDiscStronglyRecurrentOn_of_headTargetUniformlyDense_of_lt hrR h0 h1⟩

/-! ## The Riemann hypothesis and recurrence on every closed disc -/

/-- A closed disc of the open strip has a margin: some `R > r` with `closedBall c R` in the
strip. -/
theorem exists_strip_margin_of_closedBall {c : ℂ} {r : ℝ} (h0 : 1 / 2 < c.re - r)
    (h1 : c.re + r < 1) : ∃ R : ℝ, r < R ∧ 1 / 2 < c.re - R ∧ c.re + R < 1 := by
  refine ⟨(r + min (c.re - 1 / 2) (1 - c.re)) / 2, ?_, ?_, ?_⟩
  · have := lt_min (show r < c.re - 1 / 2 by linarith) (show r < 1 - c.re by linarith)
    linarith
  · have := min_le_left (c.re - 1 / 2) (1 - c.re)
    linarith
  · have := min_le_right (c.re - 1 / 2) (1 - c.re)
    linarith

/-- **Under RH, `ζ` is strongly recurrent on every closed disc of the open strip.** -/
theorem zetaDiscStronglyRecurrentOn_of_riemannHypothesis_of_closedBall (hRH : RiemannHypothesis)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (h0 : 1 / 2 < c.re - r) (h1 : c.re + r < 1) :
    ZetaDiscStronglyRecurrentOn (closedBall c r) := by
  obtain ⟨R, hrR, hR0, hR1⟩ := exists_strip_margin_of_closedBall h0 h1
  exact zetaDiscStronglyRecurrentOn_of_zeroFree_of_lt hr hrR hR0 hR1 fun z hz =>
    riemannZeta_ne_zero_on_ball_of_riemannHypothesis hRH c z
      (ball_subset_ball (by linarith) hz)

/-- Every point of the open strip is the centre of a closed disc of the open strip. -/
theorem exists_closedBall_subset_strip {z₀ : ℂ} (h1 : 1 / 2 < z₀.re) (h2 : z₀.re < 1) :
    ∃ r : ℝ, 0 < r ∧ 1 / 2 < z₀.re - r ∧ z₀.re + r < 1 := by
  refine ⟨min ((z₀.re - 1 / 2) / 2) ((1 - z₀.re) / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩
  · have := min_le_left ((z₀.re - 1 / 2) / 2) ((1 - z₀.re) / 2)
    linarith
  · have := min_le_right ((z₀.re - 1 / 2) / 2) ((1 - z₀.re) / 2)
    linarith

/-- **Bagchi's criterion on every closed disc of the strip.**  The Riemann hypothesis holds if and
only if `ζ` is strongly recurrent on every closed disc whose closure lies in `1/2 < Re s < 1`. -/
theorem riemannHypothesis_iff_forall_closedBall_zetaDiscStronglyRecurrentOn :
    RiemannHypothesis ↔ ∀ (c : ℂ) (r : ℝ), 0 < r → 1 / 2 < c.re - r → c.re + r < 1 →
      ZetaDiscStronglyRecurrentOn (closedBall c r) := by
  constructor
  · intro hRH c r hr h0 h1
    exact zetaDiscStronglyRecurrentOn_of_riemannHypothesis_of_closedBall hRH hr h0 h1
  · intro h
    rw [riemannHypothesis_iff_forall_exists_zetaDiscStronglyRecurrentOn]
    intro z₀ h1 h2
    obtain ⟨r, hr, hr0, hr1⟩ := exists_closedBall_subset_strip h1 h2
    exact ⟨r, hr, h z₀ r hr hr0 hr1⟩

/-- **Bagchi's criterion on every closed disc of the strip, head-target form.**  The Riemann
hypothesis holds if and only if on every closed disc of the open strip the Dirichlet heads
approximate `ζ` at cutoff-uniform positive lower density. -/
theorem riemannHypothesis_iff_forall_closedBall_headTargetUniformlyDense :
    RiemannHypothesis ↔ ∀ (c : ℂ) (r : ℝ), 0 < r → 1 / 2 < c.re - r → c.re + r < 1 →
      HeadTargetUniformlyDense (closedBall c r) := by
  rw [riemannHypothesis_iff_forall_closedBall_zetaDiscStronglyRecurrentOn]
  refine forall_congr' fun c => forall_congr' fun r => imp_congr_right fun _ =>
    imp_congr_right fun h0 => imp_congr_right fun h1 => ?_
  obtain ⟨R, hrR, hR0, hR1⟩ := exists_strip_margin_of_closedBall h0 h1
  exact zetaDiscStronglyRecurrentOn_iff_headTargetUniformlyDense_of_lt hrR hR0 hR1

/-- The real points `c ± r` of a closed disc in the strip give its margins. -/
theorem strip_margins_of_forall_mem_closedBall {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hK : ∀ s ∈ closedBall c r, 1 / 2 < s.re ∧ s.re < 1) :
    1 / 2 < c.re - r ∧ c.re + r < 1 := by
  have hmem1 : c - (r : ℂ) ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
  have hmem2 : c + (r : ℂ) ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
  have h1 := (hK _ hmem1).1
  have h2 := (hK _ hmem2).2
  rw [Complex.sub_re, Complex.ofReal_re] at h1
  rw [Complex.add_re, Complex.ofReal_re] at h2
  exact ⟨h1, h2⟩

/-- **Bagchi's criterion in disc form.**  The Riemann hypothesis is equivalent to the disc
recurrence of `ζ`: for every closed disc in `1/2 < Re s < 1` and every `ε > 0`, the `ε`-return
shifts have positive upper density. -/
theorem riemannHypothesis_iff_zetaDiscRecurrent : RiemannHypothesis ↔ ZetaDiscRecurrent := by
  constructor
  · intro hRH c r hr hK ε hε
    obtain ⟨h0, h1⟩ := strip_margins_of_forall_mem_closedBall hr hK
    obtain ⟨κ, hκ, hT⟩ :=
      zetaDiscStronglyRecurrentOn_of_riemannHypothesis_of_closedBall hRH hr h0 h1 ε hε
    exact ⟨κ, hκ, hT.frequently⟩
  · exact riemannHypothesis_of_zetaDiscRecurrent

end RHTower
