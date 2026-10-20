import GaloisForLFunctions.RHTower.ZetaTypicalHeightApproximationExcludesZeroTargets

/-!
# Fixed-base recurrence of zeta on a disc is uniform head-target density

Write `head_M(s) = Σ_{n ≤ M} n^{-s}`, `D = closedBall c r` with `closedBall c (2r)` inside
`1/2 < Re s < 1`, and call `τ` a *head-target height* when the moving head `head_M(· + iτ)` is within
`ε` of the base function `ζ` on `D` (`headTargetReturnSet M D ε`).

**The equivalence** (`zetaDiscStronglyRecurrentOn_iff_headTargetUniformlyDense`).  `ζ` is strongly
recurrent on `D` — every `ε`-return set has positive lower density — if and only if for every `ε`
the head-target heights have lower density bounded below by a constant that is uniform in all large
`M`.  Both directions are the disc-uniform Carlson tail law: at tail-good heights the moving head
and the moving `ζ` agree on `D`, and the tail-bad heights have density tending to zero with `M`, so
a lower bound that is uniform in `M` survives the intersection.  Hence RH follows from uniform
head-target density on every disc (`riemannHypothesis_of_forall_headTargetUniformlyDense`).

**What paying the Abel base-point pole means.**  The Kronecker self-return heights of the head,
where `head_M(· + iτ) ≈ head_M`, are *disjoint* from the head-target heights for all large `M`
(`eventually_edPolyReturnSet_inter_headTargetReturnSet_eq_empty`): at such heights `ζ(· + iτ)`
returns to `head_M = ζ + M^{1−z}/(1−z) + O(M^{-σ})`, not to `ζ`, and the pole grows without bound.
Paying the pole therefore means replacing the identity phase pattern by the phase patterns that
steer the head onto `ζ|_D`; the equivalence says these patterns must occupy a set of heights of
`M`-uniform positive density.

**Dichotomy** (`exists_pos_density_headTargetReturnSet_of_nonempty`).  By almost periodicity of the
head orbit, the head-target set at tolerance `ε` is either empty or, at any larger tolerance, of
positive lower density.  The open core of Bagchi's criterion on a zero-free disc is thus exactly:
nonemptiness of the head-target set for each large `M` (the base function lies in the closure of
the twisted heads) together with uniformity in `M` of its density.  Voronin-type universality
supplies both on zero-free discs; the corpus does not contain it.
-/

open Complex Filter Topology MeasureTheory Set Metric
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

namespace RHTower

/-- Heights at which the moving head `head_M(· + iτ)` is within `ε` of the base function `ζ`
on `K`. -/
def headTargetReturnSet (M : ℕ) (K : Set ℂ) (ε : ℝ) : Set ℝ :=
  {τ : ℝ | ∀ z ∈ K, ‖edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) - riemannZeta z‖ < ε}

/-- Strong recurrence of `ζ` on `K`: every `ε`-return set has positive lower density. -/
def ZetaDiscStronglyRecurrentOn (K : Set ℂ) : Prop :=
  ∀ ε > 0, ∃ κ > 0, ∀ᶠ T : ℝ in atTop,
    ENNReal.ofReal (κ * T) ≤ volume (zetaReturnSet K ε ∩ Icc 0 T)

/-- Uniform head-target density on `K`: for every `ε`, the head-target heights have lower density
bounded below by a constant uniform in all large `M`. -/
def HeadTargetUniformlyDense (K : Set ℂ) : Prop :=
  ∀ ε > 0, ∃ c > 0, ∀ᶠ M : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
    ENNReal.ofReal (c * T) ≤ volume (headTargetReturnSet M K ε ∩ Icc 0 T)

/-! ## 1. Measure accounting on a window -/

/-- If `A ∩ I` has measure `≥ c T` and `B ∩ I` has measure `≤ (c/2) T`, then `(A \ B) ∩ I` has
measure `≥ (c/2) T`. -/
theorem ofReal_half_le_volume_diff_inter {A B I : Set ℝ} {c T : ℝ} (hc : 0 < c) (hT : 0 ≤ T)
    (hA : ENNReal.ofReal (c * T) ≤ volume (A ∩ I))
    (hB : volume (B ∩ I) ≤ ENNReal.ofReal (c / 2 * T)) :
    ENNReal.ofReal (c / 2 * T) ≤ volume ((A \ B) ∩ I) := by
  have hsplit : A ∩ I ⊆ ((A \ B) ∩ I) ∪ (B ∩ I) := by
    rintro τ ⟨hτ, hI⟩
    by_cases hb : τ ∈ B
    · exact Or.inr ⟨hb, hI⟩
    · exact Or.inl ⟨⟨hτ, hb⟩, hI⟩
  have hle : ENNReal.ofReal (c * T) ≤ volume ((A \ B) ∩ I) + ENNReal.ofReal (c / 2 * T) :=
    hA.trans ((measure_mono hsplit).trans ((measure_union_le _ _).trans (add_le_add le_rfl hB)))
  have h := tsub_le_iff_right.mpr hle
  rwa [← ENNReal.ofReal_sub _ (by positivity), show c * T - c / 2 * T = c / 2 * T by ring] at h

/-! ## 2. The two inclusions through tail-good heights -/

/-- Head-target heights that are tail-good are return heights of `ζ`. -/
theorem headTargetReturnSet_diff_discTailBadSet_subset_zetaReturnSet (M : ℕ) (c : ℂ) (r : ℝ)
    (ε ε' : ℝ) :
    headTargetReturnSet M (closedBall c r) ε \ discTailBadSet M c r ε' ⊆
      zetaReturnSet (closedBall c r) (ε' + ε) := by
  rintro τ ⟨hhead, hgood⟩ z hz
  have htail : ‖zetaTailFun M (z + τ * I)‖ < ε' := by
    by_contra hcon
    exact hgood ⟨z, hz, not_lt.mp hcon⟩
  have hh := hhead z hz
  have hid : riemannZeta (z + τ * I) - riemannZeta z =
      zetaTailFun M (z + τ * I) +
        (edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) - riemannZeta z) := by
    unfold zetaTailFun
    ring
  rw [hid]
  exact (norm_add_le _ _).trans_lt (add_lt_add htail hh)

/-- Return heights of `ζ` that are tail-good are head-target heights. -/
theorem zetaReturnSet_diff_discTailBadSet_subset_headTargetReturnSet (M : ℕ) (c : ℂ) (r : ℝ)
    (ε ε' : ℝ) :
    zetaReturnSet (closedBall c r) ε \ discTailBadSet M c r ε' ⊆
      headTargetReturnSet M (closedBall c r) (ε' + ε) := by
  rintro τ ⟨hret, hgood⟩ z hz
  have htail : ‖zetaTailFun M (z + τ * I)‖ < ε' := by
    by_contra hcon
    exact hgood ⟨z, hz, not_lt.mp hcon⟩
  have hr := hret z hz
  have hid : edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) - riemannZeta z =
      -(zetaTailFun M (z + τ * I)) + (riemannZeta (z + τ * I) - riemannZeta z) := by
    unfold zetaTailFun
    ring
  rw [hid]
  refine (norm_add_le _ _).trans_lt ?_
  rw [norm_neg]
  exact add_lt_add htail hr

/-! ## 3. The equivalence -/

/-- **Uniform head-target density gives strong recurrence on the disc.** -/
theorem zetaDiscStronglyRecurrentOn_of_headTargetUniformlyDense {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1)
    (hU : HeadTargetUniformlyDense (closedBall c r)) :
    ZetaDiscStronglyRecurrentOn (closedBall c r) := by
  intro ε hε
  obtain ⟨c₀, hc₀, hM⟩ := hU (ε / 2) (half_pos hε)
  obtain ⟨M, hM1, hM2⟩ := (hM.and (eventually_eventually_volume_discTailBadSet_le hr h0 h1
    (half_pos hε) (half_pos hc₀))).exists
  refine ⟨c₀ / 2, half_pos hc₀, ?_⟩
  filter_upwards [hM1, hM2, eventually_ge_atTop (0 : ℝ)] with T hT1 hT2 hT0
  have hsub := headTargetReturnSet_diff_discTailBadSet_subset_zetaReturnSet M c r (ε / 2) (ε / 2)
  rw [add_halves] at hsub
  exact (ofReal_half_le_volume_diff_inter hc₀ hT0 hT1 hT2).trans
    (measure_mono (inter_subset_inter_left _ hsub))

/-- **Strong recurrence on the disc gives uniform head-target density.** -/
theorem headTargetUniformlyDense_of_zetaDiscStronglyRecurrentOn {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1)
    (hR : ZetaDiscStronglyRecurrentOn (closedBall c r)) :
    HeadTargetUniformlyDense (closedBall c r) := by
  intro ε hε
  obtain ⟨κ, hκ, hT⟩ := hR (ε / 2) (half_pos hε)
  refine ⟨κ / 2, half_pos hκ, ?_⟩
  filter_upwards [eventually_eventually_volume_discTailBadSet_le hr h0 h1 (half_pos hε)
    (half_pos hκ)] with M hM
  filter_upwards [hT, hM, eventually_ge_atTop (0 : ℝ)] with T hT1 hT2 hT0
  have hsub := zetaReturnSet_diff_discTailBadSet_subset_headTargetReturnSet M c r (ε / 2) (ε / 2)
  rw [add_halves] at hsub
  exact (ofReal_half_le_volume_diff_inter hκ hT0 hT1 hT2).trans
    (measure_mono (inter_subset_inter_left _ hsub))

/-- **Bagchi's fixed-base recurrence on a disc is uniform head-target density.** -/
theorem zetaDiscStronglyRecurrentOn_iff_headTargetUniformlyDense {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) :
    ZetaDiscStronglyRecurrentOn (closedBall c r) ↔ HeadTargetUniformlyDense (closedBall c r) :=
  ⟨headTargetUniformlyDense_of_zetaDiscStronglyRecurrentOn hr h0 h1,
    zetaDiscStronglyRecurrentOn_of_headTargetUniformlyDense hr h0 h1⟩

/-! ## 4. RH from uniform head-target density on every disc -/

/-- An isolating disc around an off-line zero with strict margins: `r < (Re ρ₀ − 1/2)/2`,
`r < (1 − Re ρ₀)/2`, and a floor `m > 0` for `|ζ|` on the circle `|s − ρ₀| = r`. -/
theorem exists_zetaIsolatingDisc_strict {ρ₀ : ℂ} (h1 : 1 / 2 < ρ₀.re) (h2 : ρ₀.re < 1) :
    ∃ r > 0, r < (ρ₀.re - 1 / 2) / 2 ∧ r < (1 - ρ₀.re) / 2 ∧
      ∃ m > 0, ∀ z ∈ sphere ρ₀ r, m ≤ ‖riemannZeta z‖ := by
  have hρ1 : ρ₀ ≠ 1 := by
    intro h
    rw [h] at h2
    simp at h2
  have hdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} :=
    fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  have han : AnalyticAt ℂ riemannZeta ρ₀ := hdiff.analyticAt (isOpen_ne.mem_nhds hρ1)
  have hne : ∀ᶠ z in 𝓝[≠] ρ₀, riemannZeta z ≠ 0 := by
    refine han.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h => ?_
    exact analyticOrderAt_riemannZeta_ne_top_of_ne_one hρ1 (analyticOrderAt_eq_top.mpr h)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hne)
  set r := min (r₁ / 2) (min ((ρ₀.re - 1 / 2) / 3) ((1 - ρ₀.re) / 3)) with hrdef
  have hr : 0 < r := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hrr₁ : r < r₁ := (min_le_left _ _).trans_lt (by linarith)
  have hr2 : r < (ρ₀.re - 1 / 2) / 2 :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hr3 : r < (1 - ρ₀.re) / 2 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  have hsph : ∀ z ∈ sphere ρ₀ r, riemannZeta z ≠ 0 ∧ z ≠ 1 := by
    intro z hz
    have hd : dist z ρ₀ = r := mem_sphere.mp hz
    have hzρ : z ≠ ρ₀ := by
      intro h
      rw [h, dist_self] at hd
      linarith
    refine ⟨hball (by rw [hd]; exact hrr₁) hzρ, fun h => ?_⟩
    have hre := abs_re_le_norm (z - ρ₀)
    rw [← dist_eq_norm, hd, h, sub_re, one_re] at hre
    have := le_abs_self (1 - ρ₀.re)
    linarith
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere ρ₀ r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le)
    (fun z hz => (differentiableAt_riemannZeta (hsph z hz).2).continuousAt.continuousWithinAt.norm)
  exact ⟨r, hr, hr2, hr3, ‖riemannZeta z₁‖, norm_pos_iff.mpr (hsph z₁ hz₁).1,
    fun z hz => hmin hz⟩

/-- **RH from uniform head-target density on every right-strip disc.**  Around an off-line zero,
uniform head-target density would give strong recurrence, but self-returns there have density
zero. -/
theorem riemannHypothesis_of_forall_headTargetUniformlyDense
    (h : ∀ (c : ℂ) (r : ℝ), 0 < r → 1 / 2 < c.re - 2 * r → c.re + 2 * r < 1 →
      HeadTargetUniformlyDense (closedBall c r)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  intro ρ₀ hρ1 hρ2 hρ0
  obtain ⟨r, hr, hr2, hr3, m, hm0, hm⟩ := exists_zetaIsolatingDisc_strict hρ1 hρ2
  have hrec := zetaDiscStronglyRecurrentOn_of_headTargetUniformlyDense hr (by linarith)
    (by linarith) (h ρ₀ r hr (by linarith) (by linarith))
  obtain ⟨κ, hκ, hfreq⟩ := hrec (m / 2) (half_pos hm0)
  have hzero := eventually_volume_zetaReturnSet_le_of_zero hr hr2.le hr3.le hρ0 hm le_rfl
    (half_pos hκ)
  obtain ⟨T, hT1, hT2, hT0⟩ := (hfreq.and (hzero.and (eventually_gt_atTop (0 : ℝ)))).exists
  have h := hT1.trans hT2
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  nlinarith

/-! ## 5. The Abel pole separates self-returns of the head from head-target heights -/

/-- **The pole is not paid by self-returns of the head.**  For all large `M`, no height is both a
Kronecker self-return height of `head_M` on `K` and a head-target height on `K`: at a point `z` of
`K` in the strip the base-point tail `head_M(z) − ζ(z) = −M^{1−z}/(1−z) + O(M^{-σ})` grows without
bound, while a common height would force it below `ε + ε'`. -/
theorem eventually_edPolyReturnSet_inter_headTargetReturnSet_eq_empty {K : Set ℂ} {z : ℂ}
    (hz : z ∈ K) (hz0 : 0 < z.re) (hz1 : z.re < 1) (ε ε' : ℝ) :
    ∀ᶠ M : ℕ in atTop,
      edPolyReturnSet (fun _ => 1) (Finset.Icc 1 M) K ε ∩ headTargetReturnSet M K ε' = ∅ := by
  filter_upwards [(tendsto_norm_zetaDirichletTail_base_atTop hz0 hz1).eventually
    (eventually_ge_atTop (ε + ε'))] with M hM
  rw [Set.eq_empty_iff_forall_notMem]
  rintro τ ⟨hself, htarget⟩
  have h1 := hself z hz
  have h2 := htarget z hz
  have h3 : ‖riemannZeta z - edPoly (fun _ => 1) (Finset.Icc 1 M) z‖ =
      ‖zetaDirichletTail M z.re z.im‖ := by
    rw [riemannZeta_sub_edPoly_one_Icc_eq_zetaDirichletTail]
  have h4 : ‖riemannZeta z - edPoly (fun _ => 1) (Finset.Icc 1 M) z‖ < ε + ε' := by
    have hid : riemannZeta z - edPoly (fun _ => 1) (Finset.Icc 1 M) z =
        (riemannZeta z - edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I)) +
          (edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) -
            edPoly (fun _ => 1) (Finset.Icc 1 M) z) := by ring
    rw [hid]
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_sub_rev]
    linarith
  rw [h3] at h4
  linarith

/-! ## 6. The head-target set is empty or of positive lower density -/

/-- Translating a set of positive lower density keeps positive lower density. -/
theorem exists_pos_density_translate {E : Set ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hE : ∀ᶠ T : ℝ in atTop, ENNReal.ofReal (κ * T) ≤ volume (E ∩ Icc 0 T)) (τ₀ : ℝ) :
    ∃ κ' > 0, ∀ᶠ T : ℝ in atTop,
      ENNReal.ofReal (κ' * T) ≤ volume ({τ : ℝ | τ - τ₀ ∈ E} ∩ Icc 0 T) := by
  refine ⟨κ / 2, half_pos hκ, ?_⟩
  set a : ℝ := |τ₀| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  have hτ₀ : -a ≤ τ₀ ∧ τ₀ ≤ a := abs_le.mp le_rfl
  filter_upwards [hE, eventually_ge_atTop (4 * a / κ), eventually_ge_atTop (2 * a)] with T hT hT4 hT2
  have hT0 : 0 ≤ T := by linarith
  have hκT : κ / 2 * T ≤ κ * T - 2 * a := by
    rw [div_le_iff₀ hκ] at hT4
    linarith
  -- the translated middle piece lands in `[0, T]`
  have hsub : (fun τ : ℝ => τ + (-τ₀)) ⁻¹' (E ∩ Icc a (T - a)) ⊆
      {τ : ℝ | τ - τ₀ ∈ E} ∩ Icc 0 T := by
    rintro τ ⟨hτE, hτI⟩
    refine ⟨?_, ?_, ?_⟩
    · show τ - τ₀ ∈ E
      rwa [sub_eq_add_neg]
    · linarith [hτI.1, hτ₀.2]
    · linarith [hτI.2, hτ₀.1]
  -- the middle piece carries almost all the mass
  have hcover : E ∩ Icc 0 T ⊆ (E ∩ Icc a (T - a)) ∪ (Icc 0 a ∪ Icc (T - a) T) := by
    rintro τ ⟨hτ, hI⟩
    by_cases h1 : τ < a
    · exact Or.inr (Or.inl ⟨hI.1, h1.le⟩)
    by_cases h2 : T - a < τ
    · exact Or.inr (Or.inr ⟨h2.le, hI.2⟩)
    · exact Or.inl ⟨hτ, not_lt.mp h1, not_lt.mp h2⟩
  have hmid : ENNReal.ofReal (κ * T - 2 * a) ≤ volume (E ∩ Icc a (T - a)) := by
    have hle : ENNReal.ofReal (κ * T) ≤ volume (E ∩ Icc a (T - a)) + ENNReal.ofReal (2 * a) := by
      refine hT.trans ((measure_mono hcover).trans ((measure_union_le _ _).trans
        (add_le_add le_rfl ?_)))
      calc volume (Icc 0 a ∪ Icc (T - a) T) ≤ volume (Icc 0 a) + volume (Icc (T - a) T) :=
            measure_union_le _ _
        _ = ENNReal.ofReal a + ENNReal.ofReal a := by
            rw [Real.volume_Icc, Real.volume_Icc, sub_zero, sub_sub_cancel]
        _ = ENNReal.ofReal (2 * a) := by
            rw [← ENNReal.ofReal_add ha0 ha0]
            congr 1
            ring
    have h := tsub_le_iff_right.mpr hle
    rwa [← ENNReal.ofReal_sub _ (by positivity)] at h
  calc ENNReal.ofReal (κ / 2 * T) ≤ ENNReal.ofReal (κ * T - 2 * a) := ENNReal.ofReal_le_ofReal hκT
    _ ≤ volume (E ∩ Icc a (T - a)) := hmid
    _ = volume ((fun τ : ℝ => τ + (-τ₀)) ⁻¹' (E ∩ Icc a (T - a))) :=
        (measure_preimage_add_right _ _ _).symm
    _ ≤ volume ({τ : ℝ | τ - τ₀ ∈ E} ∩ Icc 0 T) := measure_mono hsub

/-- **Dichotomy.**  If the head-target set at tolerance `ε` is nonempty, then at any larger
tolerance it has positive lower density: almost periods of the head translate one head-target
height into a positive-density set of them. -/
theorem exists_pos_density_headTargetReturnSet_of_nonempty {M : ℕ} {K : Set ℂ}
    (hK : ∀ z ∈ K, 0 ≤ z.re) {ε ε' : ℝ} (hεε' : ε < ε')
    (hne : (headTargetReturnSet M K ε).Nonempty) :
    ∃ κ > 0, ∀ᶠ T : ℝ in atTop,
      ENNReal.ofReal (κ * T) ≤ volume (headTargetReturnSet M K ε' ∩ Icc 0 T) := by
  obtain ⟨τ₀, hτ₀⟩ := hne
  set θ : ℝ := (ε' - ε) / (M + 1) with hθ
  have hθ0 : 0 < θ := by rw [hθ]; exact div_pos (by linarith) (by positivity)
  obtain ⟨κ, hκ, hE⟩ := exists_pos_density_headPhaseReturnSet M hθ0
  obtain ⟨κ', hκ', hE'⟩ := exists_pos_density_translate hκ hE τ₀
  refine ⟨κ', hκ', hE'.mono fun T hT => hT.trans (measure_mono (inter_subset_inter_left _ ?_))⟩
  intro τ hτ
  have hd : τ - τ₀ ∈ headPhaseReturnSet M θ := hτ
  intro z hz
  have hw : 0 ≤ (z + τ₀ * I).re := by simpa using hK z hz
  have hmove := norm_edPoly_one_Icc_shift_sub_le hd hw
  have hMθ : (M : ℝ) * θ < ε' - ε := by
    rw [hθ, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have hbase := hτ₀ z hz
  have hpt : z + τ₀ * I + ((τ - τ₀ : ℝ) : ℂ) * I = z + τ * I := by
    push_cast
    ring
  rw [hpt] at hmove
  calc ‖edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) - riemannZeta z‖
      = ‖(edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) -
          edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ₀ * I)) +
          (edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ₀ * I) - riemannZeta z)‖ := by ring_nf
    _ ≤ ‖edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) -
          edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ₀ * I)‖ +
          ‖edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ₀ * I) - riemannZeta z‖ := norm_add_le _ _
    _ < (ε' - ε) + ε := add_lt_add_of_le_of_lt (hmove.trans hMθ.le) hbase
    _ = ε' := by ring

end RHTower
