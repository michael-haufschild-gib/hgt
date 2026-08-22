import GaloisForLFunctions.RHTower.SoninApertureRestrictionDefect
import GaloisForLFunctions.RHTower.SoninBandCodimensionTwo
import GaloisForLFunctions.RHTower.RelativeShellBaireWall

/-!
# Burnol's Proposition 4.7: the Sonine apertures shrink strictly

The Sonine carriers `K_b` decrease as the aperture `b` grows, and Proposition 4.6 says that the
union over `b > a` is dense in `K_a`.  Proposition 4.7 says the union is nevertheless *proper*.

Two steps.

*Strictness at each aperture.*  Write `A_c` and `B_c` for the two forbidden bands, so that
`K_c = (A_c ⊔ B_c)ᗮ`.  A vector of `A_b` that lies in `A_a ⊔ B_a` splits as `u + v` with `u ∈ A_a`
and `v ∈ B_a`; then `v = (u+v) - u ∈ A_b`, and `A_b ⊓ B_a = ⊥` because a nonzero vector cannot be
supported in a bounded interval and have a Fourier transform supported in a bounded interval.  So
`A_b ⊓ (A_a ⊔ B_a) = A_a`, and the shell indicator of `[a,b]` witnesses `A_b ⊄ A_a ⊔ B_a`.  Taking
perpendiculars, `K_b < K_a`.

*Baire.*  The apertures `a + 1/(n+1)` are cofinal in `(a, ∞)`, and the carriers form a directed
family, so if the union exhausted `K_a` then `K_a` — a Banach space — would be a countable union of
closed proper subspaces.  The corpus's `shellBaire_exists_stage` turns this into a single stage
`K_a ≤ K_{a + 1/(N+1)}`, contradicting strictness.

## Main results

* `soninShellIndicator` — the `L²` indicator of `[a,b]`
* `centralSoninCarrier_strictAnti` — `K_b < K_a` for `0 < a < b`
* `iSup_centralSoninCarrier_lt` — **Burnol's Proposition 4.7**
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The `L²` indicator of the shell `[a, b]`. -/
def soninShellIndicator (a b : ℝ) : SoninL2 :=
  indicatorConstLp 2 (measurableSet_Icc : MeasurableSet (Set.Icc a b))
    measure_Icc_lt_top.ne (1 : ℂ)

theorem soninShellIndicator_coeFn (a b : ℝ) :
    ((soninShellIndicator a b : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (Set.Icc a b).indicator fun _ => (1 : ℂ) :=
  indicatorConstLp_coeFn

theorem soninShellIndicator_mem_centralPhysicalForbidden {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    soninShellIndicator a b ∈ centralPhysicalForbidden b := by
  show soninShellIndicator a b ∈ physicalForbidden (Set.Icc (-b) b) measurableSet_Icc
  rw [mem_physicalForbidden_iff]
  filter_upwards [soninShellIndicator_coeFn a b] with x hx hout
  rw [hx]
  refine Set.indicator_of_notMem (fun hmem => hout ?_) _
  exact ⟨by linarith [hmem.1], hmem.2⟩

theorem soninShellIndicator_notMem_centralPhysicalForbidden {a b : ℝ} (hab : a < b) :
    soninShellIndicator a b ∉ centralPhysicalForbidden a := by
  intro hmem
  have hmem' : ∀ᵐ x ∂(volume : Measure ℝ),
      x ∉ Set.Icc (-a) a → ((soninShellIndicator a b : SoninL2) : ℝ → ℂ) x = 0 := by
    rw [← mem_physicalForbidden_iff]
    exact hmem
  have hbad : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.Ioc a b := by
    filter_upwards [soninShellIndicator_coeFn a b, hmem'] with x hx hz hS
    have h1 : x ∈ Set.Icc a b := ⟨le_of_lt hS.1, hS.2⟩
    have h2 : x ∉ Set.Icc (-a) a := fun h => absurd h.2 (not_le.mpr hS.1)
    have hzero := hz h2
    rw [hx, Set.indicator_of_mem h1] at hzero
    exact one_ne_zero hzero
  have hnull : (volume : Measure ℝ) (Set.Ioc a b) = 0 := compl_mem_ae_iff.1 hbad
  rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hnull
  linarith

/-- A vector supported in the larger band cannot have a Fourier transform supported in the
smaller one unless it vanishes. -/
theorem centralPhysicalForbidden_inf_centralFourierForbidden_eq_bot {a b : ℝ} (hab : a ≤ b) :
    centralPhysicalForbidden b ⊓ centralFourierForbidden a = ⊥ := by
  refine le_antisymm ?_ bot_le
  calc centralPhysicalForbidden b ⊓ centralFourierForbidden a
      ≤ centralPhysicalForbidden b ⊓ centralFourierForbidden b :=
        inf_le_inf_left _ (centralFourierForbidden_mono hab)
    _ = ⊥ := physicalForbidden_inf_fourierForbidden_eq_bot b

/-- **The band trace of the smaller Sonine complement.**  Intersecting the sum of the two bands at
aperture `a` with the larger time band recovers exactly the smaller time band. -/
theorem centralPhysicalForbidden_inf_sup_le {a b : ℝ} (hab : a ≤ b) :
    centralPhysicalForbidden b ⊓ (centralPhysicalForbidden a ⊔ centralFourierForbidden a)
      ≤ centralPhysicalForbidden a := by
  rintro g ⟨hgb, hgsup⟩
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hgsup
  have hvb : v ∈ centralPhysicalForbidden b := by
    have hvsub : v = g - u := eq_sub_of_add_eq' huv
    rw [hvsub]
    exact Submodule.sub_mem _ hgb (centralPhysicalForbidden_mono hab hu)
  have hv0 : v = 0 := by
    have hmem : v ∈ centralPhysicalForbidden b ⊓ centralFourierForbidden a := ⟨hvb, hv⟩
    rwa [centralPhysicalForbidden_inf_centralFourierForbidden_eq_bot hab,
      Submodule.mem_bot] at hmem
  rw [← huv, hv0, add_zero]
  exact hu

/-- **The Sonine carriers shrink strictly.** -/
theorem centralSoninCarrier_strictAnti {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    centralSoninCarrier b < centralSoninCarrier a := by
  refine lt_of_le_of_ne (centralSoninCarrier_antitone hab.le) ?_
  intro heq
  have hb : 0 < b := ha.trans hab
  have horth : centralPhysicalForbidden b ⊔ centralFourierForbidden b
      = centralPhysicalForbidden a ⊔ centralFourierForbidden a := by
    rw [← orthogonal_centralSoninCarrier hb, ← orthogonal_centralSoninCarrier ha, heq]
  have hmemb : soninShellIndicator a b ∈ centralPhysicalForbidden b :=
    soninShellIndicator_mem_centralPhysicalForbidden ha.le hab.le
  have hg : soninShellIndicator a b ∈ centralPhysicalForbidden a ⊔ centralFourierForbidden a := by
    rw [← horth]
    exact Submodule.mem_sup_left hmemb
  exact soninShellIndicator_notMem_centralPhysicalForbidden hab
    (centralPhysicalForbidden_inf_sup_le hab.le ⟨hmemb, hg⟩)

theorem directed_centralSoninCarrier (a : ℝ) :
    Directed (· ≤ ·) fun b : Set.Ioi a => centralSoninCarrier (b : ℝ) := by
  rintro ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩
  refine ⟨⟨min b₁ b₂, Set.mem_Ioi.2 (lt_min hb₁ hb₂)⟩, ?_, ?_⟩
  · exact centralSoninCarrier_antitone (min_le_left b₁ b₂)
  · exact centralSoninCarrier_antitone (min_le_right b₁ b₂)

/-- **Burnol's Proposition 4.7.**  The union of the strictly smaller Sonine spaces is a *proper*
subspace of `K_a`, even though Proposition 4.6 makes it dense. -/
theorem iSup_centralSoninCarrier_lt {a : ℝ} (ha : 0 < a) :
    (⨆ b : Set.Ioi a, centralSoninCarrier (b : ℝ)) < centralSoninCarrier a := by
  refine lt_of_le_of_ne (iSup_le fun b => centralSoninCarrier_antitone (le_of_lt b.2)) ?_
  intro heq
  haveI : Nonempty (Set.Ioi a) := ⟨⟨a + 1, by simp⟩⟩
  haveI hcomplete : CompleteSpace (centralSoninCarrier a) :=
    (centralSoninCarrier_isClosed a).completeSpace_coe
  set stage : ℕ → ℝ := fun n => a + 1 / ((n : ℝ) + 1) with hstage
  have hstage_gt : ∀ n : ℕ, a < stage n := by
    intro n
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simpa [hstage] using this
  have hcover : ∀ x : (centralSoninCarrier a),
      ∃ n : ℕ, (centralSoninCarrier a).subtype x ∈ centralSoninCarrier (stage n) := by
    intro x
    have hx : (x : SoninL2) ∈ ⨆ b : Set.Ioi a, centralSoninCarrier (b : ℝ) := by
      rw [heq]; exact x.2
    obtain ⟨b, hb⟩ := (Submodule.mem_iSup_of_directed _ (directed_centralSoninCarrier a)).1 hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < (b : ℝ) - a by
      have := b.2
      simp only [Set.mem_Ioi] at this
      linarith)
    exact ⟨n, centralSoninCarrier_antitone (by simp only [hstage]; linarith) hb⟩
  obtain ⟨N, hN⟩ := shellBaire_exists_stage (centralSoninCarrier a).subtype
    continuous_subtype_val (fun n => centralSoninCarrier (stage n))
    (fun n => centralSoninCarrier_isClosed (stage n)) hcover
  have hle : centralSoninCarrier a ≤ centralSoninCarrier (stage N) := by
    intro x hx
    exact hN ⟨x, hx⟩
  exact absurd (lt_of_lt_of_le (centralSoninCarrier_strictAnti ha (hstage_gt N)) hle)
    (lt_irrefl _)

end RHTower

end
