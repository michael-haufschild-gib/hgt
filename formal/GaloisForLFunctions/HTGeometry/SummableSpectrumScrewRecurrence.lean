import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewValue

/-!
# Cofinal recurrence of a summable-spectrum screw line

Every forward tail of the screw line is dense in the relation hull. The forward phases
form a compact subsemigroup of a compact group, and such a semigroup is a group: a
convergent subsequence of the iterates of one point makes the gap iterates tend to zero,
so one step short of the gap tends to the opposite point.

Consequently the phase-defect energy of every cofinal tail accumulates exactly on
`[0, M]`, where `M` is the maximal hull energy. No value in that range is missed after
any time, and no value outside it is ever approached.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I : Type*}

/-! ## The forward screw semigroup -/

/-- Phases of the screw line at nonnegative times. -/
def screwForwardMonoid (omega : I → ℝ) : AddSubmonoid (I → UnitAddCircle) where
  carrier := screwPhase omega '' Set.Ici 0
  add_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    refine ⟨s + t, ?_, ?_⟩
    · exact Set.mem_Ici.mpr (add_nonneg (Set.mem_Ici.mp hs) (Set.mem_Ici.mp ht))
    · exact screwPhase_add omega s t
  zero_mem' := by
    refine ⟨0, ?_, ?_⟩
    · exact Set.mem_Ici.mpr (le_refl 0)
    · exact screwPhase_zero omega

/-- Closure of the forward screw semigroup. -/
def screwForwardHull (omega : I → ℝ) : AddSubmonoid (I → UnitAddCircle) :=
  (screwForwardMonoid omega).topologicalClosure

theorem screwForwardHull_coe (omega : I → ℝ) :
    (screwForwardHull omega : Set (I → UnitAddCircle)) =
      closure (screwPhase omega '' Set.Ici 0) :=
  AddSubmonoid.coe_topologicalClosure _

theorem isClosed_screwForwardHull (omega : I → ℝ) :
    IsClosed (screwForwardHull omega : Set (I → UnitAddCircle)) :=
  AddSubmonoid.isClosed_topologicalClosure _

theorem screwPhase_neg (omega : I → ℝ) (t : ℝ) :
    screwPhase omega (-t) = -screwPhase omega t :=
  map_neg (screwLineHom omega) t

theorem screwPhase_mem_screwForwardHull {omega : I → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    screwPhase omega t ∈ screwForwardHull omega :=
  (screwForwardMonoid omega).le_topologicalClosure ⟨t, Set.mem_Ici.mpr ht, rfl⟩

/-- **Compact forward semigroups invert.** A phase reachable as a forward limit has its
opposite reachable as a forward limit. -/
theorem neg_mem_screwForwardHull [Countable I] {omega : I → ℝ}
    {x : I → UnitAddCircle} (hx : x ∈ screwForwardHull omega) :
    -x ∈ screwForwardHull omega := by
  classical
  set S : AddSubmonoid (I → UnitAddCircle) := screwForwardHull omega with hSdef
  have hSclosed : IsClosed (S : Set (I → UnitAddCircle)) := isClosed_screwForwardHull omega
  have hScompact : IsCompact (S : Set (I → UnitAddCircle)) := hSclosed.isCompact
  have hmem : ∀ n : ℕ, (n + 1) • x ∈ (S : Set (I → UnitAddCircle)) := fun n =>
    S.nsmul_mem hx (n + 1)
  obtain ⟨y, _, phi, hphi, hconv⟩ := hScompact.tendsto_subseq hmem
  set g : ℕ → (I → UnitAddCircle) := fun j => (phi j + 1) • x with hg
  have hconv' : Tendsto g atTop (𝓝 y) := by
    simpa [hg, Function.comp_def] using hconv
  have hshift : Tendsto (fun j => g (j + 1)) atTop (𝓝 y) :=
    hconv'.comp (tendsto_add_atTop_nat 1)
  have hmono : ∀ j : ℕ, phi j < phi (j + 1) := fun j => hphi (Nat.lt_succ_self j)
  have hgap : ∀ j : ℕ, g (j + 1) - g j = (phi (j + 1) - phi j) • x := by
    intro j
    have hle : phi j ≤ phi (j + 1) := (hmono j).le
    have hsplit : phi (j + 1) + 1 = (phi (j + 1) - phi j) + (phi j + 1) := by omega
    show (phi (j + 1) + 1) • x - (phi j + 1) • x = (phi (j + 1) - phi j) • x
    rw [hsplit, add_nsmul]
    abel
  have hzero : Tendsto (fun j => (phi (j + 1) - phi j) • x) atTop (𝓝 0) := by
    have hsub := hshift.sub hconv'
    rw [sub_self] at hsub
    simpa [hgap] using hsub
  have hstep : ∀ j : ℕ,
      (phi (j + 1) - phi j) • x = (phi (j + 1) - phi j - 1) • x + x := by
    intro j
    have h1 : 1 ≤ phi (j + 1) - phi j := by have := hmono j; omega
    conv_lhs => rw [show phi (j + 1) - phi j = (phi (j + 1) - phi j - 1) + 1 by omega]
    rw [add_nsmul, one_nsmul]
  have hneg : Tendsto (fun j => (phi (j + 1) - phi j - 1) • x) atTop (𝓝 (-x)) := by
    have hsub : Tendsto (fun j => (phi (j + 1) - phi j) • x - x) atTop (𝓝 (0 - x)) :=
      hzero.sub tendsto_const_nhds
    have hrw : ∀ j : ℕ,
        (phi (j + 1) - phi j) • x - x = (phi (j + 1) - phi j - 1) • x := by
      intro j
      rw [hstep j]
      abel
    simpa [hrw] using hsub
  refine hSclosed.mem_of_tendsto hneg ?_
  filter_upwards with j
  exact S.nsmul_mem hx _

/-- The forward hull is already the whole relation hull. -/
theorem screwForwardHull_coe_eq_screwHull [Countable I] (omega : I → ℝ) :
    (screwForwardHull omega : Set (I → UnitAddCircle)) = screwHull omega := by
  refine Set.Subset.antisymm ?_ ?_
  · rw [screwForwardHull_coe]
    refine closure_mono ?_
    rintro _ ⟨t, _, rfl⟩
    exact ⟨t, rfl⟩
  · refine closure_minimal ?_ (isClosed_screwForwardHull omega)
    rintro _ ⟨t, rfl⟩
    rcases le_or_gt 0 t with ht | ht
    · exact screwPhase_mem_screwForwardHull ht
    · have hnegt : screwPhase omega t = -screwPhase omega (-t) := by
        rw [screwPhase_neg, neg_neg]
      rw [hnegt]
      exact neg_mem_screwForwardHull
        (screwPhase_mem_screwForwardHull (by linarith : (0 : ℝ) ≤ -t))

/-- **Tail density.** Every cofinal tail of the screw line is dense in the relation
hull. -/
theorem closure_screwPhase_image_Ici [Countable I] (omega : I → ℝ) (T : ℝ) :
    closure (screwPhase omega '' Set.Ici T) = screwHull omega := by
  have himg : screwPhase omega '' Set.Ici T =
      (Homeomorph.addLeft (screwPhase omega T)) '' (screwPhase omega '' Set.Ici 0) := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨screwPhase omega (t - T), ⟨t - T, by simpa using ht, rfl⟩, ?_⟩
      show screwPhase omega T + screwPhase omega (t - T) = screwPhase omega t
      rw [← screwPhase_add]
      congr 1
      ring
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨T + s, by simpa using hs, ?_⟩
      show screwPhase omega (T + s) = screwPhase omega T + screwPhase omega s
      rw [screwPhase_add]
  rw [himg, ← (Homeomorph.addLeft (screwPhase omega T)).image_closure,
    ← screwForwardHull_coe, screwForwardHull_coe_eq_screwHull]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact add_mem_screwHull (screwPhase_mem_screwHull omega T) hw
  · intro hz
    refine ⟨z - screwPhase omega T, sub_mem_screwHull hz (screwPhase_mem_screwHull omega T), ?_⟩
    show screwPhase omega T + (z - screwPhase omega T) = z
    abel

/-! ## Cofinal value recurrence -/

private theorem closure_image_of_isCompact_closure {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {f : X → Y} (hf : Continuous f) {s : Set X}
    (hs : IsCompact (closure s)) :
    closure (f '' s) = f '' closure s := by
  refine Set.Subset.antisymm ?_ (image_closure_subset_closure_image hf)
  exact closure_minimal (Set.image_mono subset_closure) (hs.image hf).isClosed

/-- **No-gap cofinal value law.** After every time, the phase-defect energy of the screw
series accumulates exactly on `[0, M]`. -/
theorem closure_screwSeries_image_Ici [Countable I] {a omega : I → ℝ}
    (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a) (T : ℝ) :
    closure (screwSeries a omega '' Set.Ici T) = Set.Icc 0 (screwHullMax a omega) := by
  have himg : screwSeries a omega '' Set.Ici T =
      screwValue a '' (screwPhase omega '' Set.Ici T) := by
    rw [← Set.image_comp]
    exact Set.image_congr' (fun t => screwSeries_eq_screwValue a omega t)
  rw [himg,
    closure_image_of_isCompact_closure (screwValue_continuous hpos hsum)
      (by rw [closure_screwPhase_image_Ici]; exact isCompact_screwHull omega),
    closure_screwPhase_image_Ici, screwValue_image_screwHull hpos hsum]


/-! ## Extreme cofinal values -/

section Extremes

variable [Countable I] {a omega : I → ℝ}

omit [Countable I] in
theorem screwSeries_nonneg (hpos : ∀ i, 0 ≤ a i) (t : ℝ) :
    0 ≤ screwSeries a omega t := by
  rw [screwSeries_eq_screwValue]
  exact screwValue_nonneg hpos _

theorem screwSeries_le_screwHullMax (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a) (t : ℝ) :
    screwSeries a omega t ≤ screwHullMax a omega := by
  rw [screwSeries_eq_screwValue]
  exact screwValue_le_screwHullMax hpos hsum (screwPhase_mem_screwHull omega t)

private theorem frequently_near_of_mem_closure (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a)
    {c : ℝ} (hc : c ∈ Set.Icc 0 (screwHullMax a omega)) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ t in atTop, |screwSeries a omega t - c| < ε := by
  rw [Filter.frequently_atTop]
  intro T
  have hmem : c ∈ closure (screwSeries a omega '' Set.Ici T) := by
    rw [closure_screwSeries_image_Ici hpos hsum T]
    exact hc
  obtain ⟨y, ⟨t, ht, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
  exact ⟨t, ht, by rwa [Real.dist_eq, abs_sub_comm] at hdist⟩

/-- Every value of the closed interval is approached cofinally. -/
theorem screwSeries_frequently_near (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a)
    {c : ℝ} (hc : c ∈ Set.Icc 0 (screwHullMax a omega)) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ t in atTop, |screwSeries a omega t - c| < ε :=
  frequently_near_of_mem_closure hpos hsum hc hε

private theorem isBoundedUnder_le (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a) :
    IsBoundedUnder (· ≤ ·) atTop (screwSeries a omega) :=
  ⟨screwHullMax a omega, by
    rw [Filter.eventually_map]
    filter_upwards with t using screwSeries_le_screwHullMax hpos hsum t⟩

omit [Countable I] in
private theorem isBoundedUnder_ge (hpos : ∀ i, 0 ≤ a i) :
    IsBoundedUnder (· ≥ ·) atTop (screwSeries (omega := omega) a) :=
  ⟨0, by
    rw [Filter.eventually_map]
    filter_upwards with t using screwSeries_nonneg hpos t⟩

/-- **Vanishing lower limit.** The screw series returns arbitrarily close to zero,
without any simplicity or rational-independence premise. -/
theorem screwSeries_liminf_eq_zero (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a) :
    liminf (screwSeries a omega) atTop = 0 := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_
    refine Filter.liminf_le_of_frequently_le ?_ (isBoundedUnder_ge hpos)
    have hzero : (0 : ℝ) ∈ Set.Icc 0 (screwHullMax a omega) :=
      ⟨le_refl 0, screwHullMax_nonneg hpos hsum⟩
    have := frequently_near_of_mem_closure hpos hsum hzero hε
    refine this.mono fun t ht => ?_
    have := abs_lt.mp ht
    linarith [this.2]
  · refine Filter.le_liminf_of_le ((isBoundedUnder_le hpos hsum).isCoboundedUnder_ge) ?_
    filter_upwards with t using screwSeries_nonneg hpos t

/-- **Exact upper limit.** The cofinal supremum of the screw series is the maximal hull
energy, again with no simplicity or rational-independence premise. -/
theorem screwSeries_limsup_eq_screwHullMax (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a) :
    limsup (screwSeries a omega) atTop = screwHullMax a omega := by
  refine le_antisymm ?_ ?_
  · refine Filter.limsup_le_of_le ((isBoundedUnder_ge (omega := omega) hpos).isCoboundedUnder_le) ?_
    filter_upwards with t using screwSeries_le_screwHullMax hpos hsum t
  · refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
    refine Filter.le_limsup_of_frequently_le ?_ (isBoundedUnder_le hpos hsum)
    have hmax : screwHullMax a omega ∈ Set.Icc 0 (screwHullMax a omega) :=
      ⟨screwHullMax_nonneg hpos hsum, le_refl _⟩
    have hpos' : 0 < screwHullMax a omega - c := by linarith
    have := frequently_near_of_mem_closure hpos hsum hmax hpos'
    refine this.mono fun t ht => ?_
    have := abs_lt.mp ht
    linarith [this.1]

end Extremes


/-! ## Syndetic return times -/

section Syndetic

variable [Countable I] {a omega : I → ℝ}

omit [Countable I] in
theorem screwSeries_continuous (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a) :
    Continuous (screwSeries a omega) := by
  have hcomp : screwSeries a omega = screwValue a ∘ screwPhase omega := by
    funext t
    exact screwSeries_eq_screwValue a omega t
  rw [hcomp]
  exact (screwValue_continuous hpos hsum).comp (screwPhase_continuous omega)

/-- **Bounded-gap phase returns.** Every open set meeting the relation hull is entered by
the screw line within one fixed time window from any starting time. -/
theorem exists_window_screwPhase_mem_of_isOpen {U : Set (I → UnitAddCircle)}
    (hU : IsOpen U) (hne : (U ∩ screwHull omega).Nonempty) :
    ∃ L : ℝ, 0 < L ∧ ∀ tau : ℝ, ∃ t ∈ Set.Icc tau (tau + L), screwPhase omega t ∈ U := by
  classical
  obtain ⟨u, huU, huK⟩ := hne
  set c : ℝ → Set (I → UnitAddCircle) := fun s => {x | x + screwPhase omega s ∈ U} with hc
  have hcopen : ∀ s : ℝ, IsOpen (c s) := fun s => hU.preimage (by fun_prop)
  have hcover : screwHull omega ⊆ ⋃ s ∈ Set.Ici (0 : ℝ), c s := by
    intro x hx
    have hdiff : u - x ∈ screwHull omega := sub_mem_screwHull huK hx
    rw [← closure_screwPhase_image_Ici omega 0] at hdiff
    have hopen : IsOpen ((fun w : I → UnitAddCircle => x + w) ⁻¹' U) :=
      hU.preimage (by fun_prop)
    have hmem : u - x ∈ (fun w : I → UnitAddCircle => x + w) ⁻¹' U := by
      simp only [Set.mem_preimage]
      rwa [add_sub_cancel]
    obtain ⟨w, hw1, ⟨s, hs, rfl⟩⟩ := mem_closure_iff.mp hdiff _ hopen hmem
    exact Set.mem_biUnion hs hw1
  obtain ⟨F, hFsub, hFfin, hFcover⟩ :=
    (isCompact_screwHull omega).elim_finite_subcover_image (fun s _ => hcopen s) hcover
  obtain ⟨L0, hL0⟩ := hFfin.bddAbove
  refine ⟨max L0 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun tau => ?_⟩
  have hmem : screwPhase omega tau ∈ screwHull omega := screwPhase_mem_screwHull omega tau
  obtain ⟨s, hsF, hsmem⟩ := Set.mem_iUnion₂.mp (hFcover hmem)
  have hs0 : 0 ≤ s := hFsub hsF
  have hsL : s ≤ max L0 1 := le_trans (hL0 hsF) (le_max_left _ _)
  refine ⟨tau + s, ⟨by linarith, by linarith⟩, ?_⟩
  rw [screwPhase_add]
  exact hsmem

/-- **Relatively dense approximate returns.** Every value of `[0, M]` is approximated to
any accuracy within one fixed time window from any starting time. -/
theorem exists_window_screwSeries_near (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a)
    {y : ℝ} (hy : y ∈ Set.Icc 0 (screwHullMax a omega)) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧
      ∀ tau : ℝ, ∃ t ∈ Set.Icc tau (tau + L), |screwSeries a omega t - y| < ε := by
  have hUopen : IsOpen (screwValue a ⁻¹' Set.Ioo (y - ε) (y + ε)) :=
    isOpen_Ioo.preimage (screwValue_continuous hpos hsum)
  have hUne : ((screwValue a ⁻¹' Set.Ioo (y - ε) (y + ε)) ∩ screwHull omega).Nonempty := by
    rw [← screwValue_image_screwHull hpos hsum] at hy
    obtain ⟨z, hz, hzval⟩ := hy
    refine ⟨z, ?_, hz⟩
    simp only [Set.mem_preimage, Set.mem_Ioo, hzval]
    constructor <;> linarith
  obtain ⟨L, hL, hwin⟩ := exists_window_screwPhase_mem_of_isOpen hUopen hUne
  refine ⟨L, hL, fun tau => ?_⟩
  obtain ⟨t, ht, hmem⟩ := hwin tau
  refine ⟨t, ht, ?_⟩
  rw [screwSeries_eq_screwValue]
  simp only [Set.mem_preimage, Set.mem_Ioo] at hmem
  rw [abs_lt]
  constructor <;> linarith [hmem.1, hmem.2]

/-- **Relatively dense exact level sets.** Every interior value is attained exactly within
one fixed time window from any starting time. -/
theorem exists_window_screwSeries_eq (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a)
    {y : ℝ} (hy0 : 0 < y) (hyM : y < screwHullMax a omega) :
    ∃ L : ℝ, 0 < L ∧ ∀ tau : ℝ, ∃ t ∈ Set.Icc tau (tau + L), screwSeries a omega t = y := by
  have himg := screwValue_image_screwHull (a := a) (omega := omega) hpos hsum
  have hlow : (screwValue a ⁻¹' Set.Iio y ∩ screwHull omega).Nonempty := by
    have h0 : (0 : ℝ) ∈ Set.Icc 0 (screwHullMax a omega) := ⟨le_refl 0, by linarith⟩
    rw [← himg] at h0
    obtain ⟨z, hz, hzval⟩ := h0
    exact ⟨z, by simp only [Set.mem_preimage, Set.mem_Iio, hzval]; exact hy0, hz⟩
  have hhigh : (screwValue a ⁻¹' Set.Ioi y ∩ screwHull omega).Nonempty := by
    have h0 : screwHullMax a omega ∈ Set.Icc 0 (screwHullMax a omega) :=
      ⟨screwHullMax_nonneg hpos hsum, le_refl _⟩
    rw [← himg] at h0
    obtain ⟨z, hz, hzval⟩ := h0
    exact ⟨z, by simp only [Set.mem_preimage, Set.mem_Ioi, hzval]; exact hyM, hz⟩
  obtain ⟨L1, hL1, hwin1⟩ :=
    exists_window_screwPhase_mem_of_isOpen
      (isOpen_Iio.preimage (screwValue_continuous hpos hsum)) hlow
  obtain ⟨L2, hL2, hwin2⟩ :=
    exists_window_screwPhase_mem_of_isOpen
      (isOpen_Ioi.preimage (screwValue_continuous hpos hsum)) hhigh
  refine ⟨L1 + L2, by linarith, fun tau => ?_⟩
  obtain ⟨t1, ht1, hm1⟩ := hwin1 tau
  obtain ⟨t2, ht2, hm2⟩ := hwin2 t1
  have hv1 : screwSeries a omega t1 < y := by
    rw [screwSeries_eq_screwValue]; exact hm1
  have hv2 : y < screwSeries a omega t2 := by
    rw [screwSeries_eq_screwValue]; exact hm2
  have hle : t1 ≤ t2 := ht2.1
  have hiv :=
    intermediate_value_Icc hle
      (screwSeries_continuous (a := a) (omega := omega) hpos hsum).continuousOn
  obtain ⟨t, htmem, htval⟩ := hiv ⟨hv1.le, hv2.le⟩
  refine ⟨t, ⟨le_trans ht1.1 htmem.1, ?_⟩, htval⟩
  have h1 := htmem.2
  have h2 := ht2.2
  have h3 := ht1.2
  linarith

end Syndetic

end

end GaloisForLFunctions.HTGeometry
