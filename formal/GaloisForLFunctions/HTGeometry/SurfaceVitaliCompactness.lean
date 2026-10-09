import GaloisForLFunctions.HTGeometry.VitaliConvergence
import GaloisForLFunctions.HTGeometry.SurfaceLocalBoundPropagation

open Filter Topology Set Metric
namespace GaloisForLFunctions.HTGeometry

/-- Disk Vitali convergence is unchanged when holomorphy and the common bound hold only eventually. -/
theorem vitali_tendstoLocallyUniformlyOn_of_eventually
    {F : ℕ → ℂ → ℂ} {c : ℂ} {R C r : ℝ} {z₀ : ℂ} {Y : Set ℂ}
    (hr0 : 0 < r) (hrR : r < R / 2)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) (ball c R) ∧
      ∀ z ∈ ball c R, ‖F n z‖ ≤ C)
    (hYsub : Y ⊆ ball c r) (hz₀ : z₀ ∈ ball c r)
    (hacc : ∃ᶠ z in 𝓝[≠] z₀, z ∈ Y)
    (hconv : ∀ z ∈ Y, ∃ Lz : ℂ, Tendsto (fun n => F n z) atTop (𝓝 Lz)) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball c r) ∧
      TendstoLocallyUniformlyOn F G atTop (ball c r) := by
  classical
  let good (n : ℕ) := DifferentiableOn ℂ (F n) (ball c R) ∧
    ∀ z ∈ ball c R, ‖F n z‖ ≤ C
  let H : ℕ → ℂ → ℂ := fun n => if good n then F n else fun _ => 0
  have heq : ∀ᶠ n in atTop, H n = F n := hF.mono (fun n hn => by
    dsimp only [H]
    rw [if_pos (show good n from hn)])
  have hH : ∀ n, DifferentiableOn ℂ (H n) (ball c R) := by
    intro n
    dsimp [H]
    split_ifs with hn
    · exact hn.1
    · exact differentiableOn_const _
  have hHb : ∀ n, ∀ z ∈ ball c R, ‖H n z‖ ≤ max 0 C := by
    intro n z hz
    dsimp [H]
    split_ifs with hn
    · exact (hn.2 z hz).trans (le_max_right _ _)
    · simp only [norm_zero]
      exact le_max_left (0 : ℝ) C
  have hHconv : ∀ z ∈ Y, ∃ Lz : ℂ, Tendsto (fun n => H n z) atTop (𝓝 Lz) := by
    intro z hz
    obtain ⟨L, hL⟩ := hconv z hz
    exact ⟨L, hL.congr' (heq.mono fun n hn => congrFun hn.symm z)⟩
  obtain ⟨G, hG, hGH⟩ := vitali_tendstoLocallyUniformlyOn hr0 hrR hH hHb hYsub hz₀ hacc hHconv
  refine ⟨G, hG, hGH.congr_inseparable ?_⟩
  filter_upwards [heq] with n hn
  intro z _
  exact Inseparable.of_eq (congrFun hn z)

/-- Every point has a complex chart disk on which the late family is holomorphic and bounded. -/
def EventuallyAnalyticBoundedCharts {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X ℂ) (F : ℕ → X → ℂ) : Prop :=
  ∀ x, ∃ (i : ι) (R C : ℝ), x ∈ (e i).source ∧ 0 < R ∧
    ball ((e i) x) R ⊆ (e i).target ∧
    ∀ᶠ n in atTop, DifferentiableOn ℂ (F n ∘ (e i).symm) (ball ((e i) x) R) ∧
      ∀ z ∈ ball ((e i) x) R, ‖F n ((e i).symm z)‖ ≤ C

/-- Pointwise convergence is available throughout a neighborhood. -/
def LocallyPointwiseConvergent {X : Type*} [TopologicalSpace X]
    (F : ℕ → X → ℂ) (x : X) : Prop :=
  ∃ V ∈ 𝓝 x, ∀ y ∈ V, ∃ L : ℂ, Tendsto (fun n => F n y) atTop (𝓝 L)

theorem isOpen_locallyPointwiseConvergent {X : Type*} [TopologicalSpace X]
    (F : ℕ → X → ℂ) : IsOpen {x | LocallyPointwiseConvergent F x} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨V, hV, hC⟩
  obtain ⟨W, hWV, hWo, hxW⟩ := mem_nhds_iff.mp hV
  apply mem_of_superset (hWo.mem_nhds hxW)
  intro y hy
  exact ⟨V, mem_of_superset (hWo.mem_nhds hy) hWV, hC⟩

/-- Vitali propagation on a connected complex surface needs only one convergent neighborhood,
not a countable atlas. The family may become holomorphic on each chart only eventually. -/
theorem surface_vitali_of_locallyPointwiseConvergent {X ι : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (e : ι → OpenPartialHomeomorph X ℂ) (F : ℕ → X → ℂ)
    (hcontrol : EventuallyAnalyticBoundedCharts e F) (x₀ : X)
    (hseed : LocallyPointwiseConvergent F x₀) :
    ∃ G : X → ℂ, TendstoLocallyUniformly F G atTop ∧ Continuous G ∧
      ∀ x, ∃ i, x ∈ (e i).source ∧ AnalyticAt ℂ (G ∘ (e i).symm) ((e i) x) := by
  classical
  let W : Set X := {x | LocallyPointwiseConvergent F x}
  have hWo : IsOpen W := isOpen_locallyPointwiseConvergent F
  have hWc : closure W ⊆ W := by
    intro y hy
    obtain ⟨i, R, C, hyi, hR, htarget, hgood⟩ := hcontrol y
    let E := e i
    let c : ℂ := E y
    have hc : c ∈ E.target := E.map_source hyi
    have hV : E.source ∩ E ⁻¹' ball c (R / 6) ∈ 𝓝 y :=
      inter_mem (E.open_source.mem_nhds hyi)
        ((E.continuousAt hyi).preimage_mem_nhds (ball_mem_nhds c (by positivity)))
    obtain ⟨x, ⟨hxi, hxc⟩, hxW⟩ := mem_closure_iff_nhds.mp hy _ hV
    obtain ⟨V, hVx, hconv⟩ := hxW
    let Y : Set ℂ := ball c (R / 3) ∩ E.symm ⁻¹' V
    have hxsmall : E x ∈ ball c (R / 3) := by
      rw [mem_ball]
      have hh := mem_ball.mp hxc
      linarith
    have hYnhds : Y ∈ 𝓝 (E x) := by
      apply inter_mem (isOpen_ball.mem_nhds hxsmall)
      have hh : V ∈ 𝓝 (E.symm (E x)) := by rwa [E.left_inv hxi]
      exact (E.continuousAt_symm (E.map_source hxi)).preimage_mem_nhds hh
    obtain ⟨g, _, hg⟩ := vitali_tendstoLocallyUniformlyOn_of_eventually
      (F := fun n => F n ∘ E.symm) (r := R / 3) (by positivity) (by linarith)
      hgood (show Y ⊆ ball c (R / 3) from inter_subset_left) hxsmall
      (Filter.Eventually.frequently (nhdsWithin_le_nhds hYnhds))
      (fun z hz => hconv _ hz.2)
    change LocallyPointwiseConvergent F y
    refine ⟨E.symm '' ball c (R / 3), ?_, ?_⟩
    · have hh := E.symm.image_mem_nhds hc (ball_mem_nhds c (show 0 < R / 3 by positivity))
      simpa only [c, E.left_inv hyi] using hh
    · rintro z ⟨w, hw, rfl⟩
      exact ⟨g w, hg.tendsto_at hw⟩
  have hWclosed : IsClosed W := isClosed_of_closure_subset hWc
  have hW : W = univ := (show IsClopen W from ⟨hWclosed, hWo⟩).eq_univ ⟨x₀, hseed⟩
  have hpt (x : X) : ∃ L : ℂ, Tendsto (fun n => F n x) atTop (𝓝 L) := by
    have hx : x ∈ W := hW.symm ▸ mem_univ x
    obtain ⟨V, hV, hconv⟩ := hx
    exact hconv x (mem_of_mem_nhds hV)
  choose G hGpt using hpt
  have hlocal (x : X) : ∃ (i : ι) (r : ℝ) (g : ℂ → ℂ), x ∈ (e i).source ∧ 0 < r ∧
      ball ((e i) x) r ⊆ (e i).target ∧ DifferentiableOn ℂ g (ball ((e i) x) r) ∧
      TendstoLocallyUniformlyOn (fun n => F n ∘ (e i).symm) g atTop (ball ((e i) x) r) ∧
      EqOn g (G ∘ (e i).symm) (ball ((e i) x) r) := by
    obtain ⟨i, R, C, hxi, hR, htarget, hgood⟩ := hcontrol x
    obtain ⟨g, hga, hgc⟩ := vitali_tendstoLocallyUniformlyOn_of_eventually
      (F := fun n => F n ∘ (e i).symm) (r := R / 3)
      (Y := ball ((e i) x) (R / 3)) (z₀ := (e i) x) (by positivity) (by linarith)
      hgood Subset.rfl (mem_ball_self (by positivity))
      (Filter.Eventually.frequently (nhdsWithin_le_nhds
        (ball_mem_nhds ((e i) x) (show 0 < R / 3 by positivity))))
      (fun z _ => ⟨G ((e i).symm z), hGpt _⟩)
    refine ⟨i, R / 3, g, hxi, by positivity, ?_, hga, hgc, ?_⟩
    · exact (ball_subset_ball (by linarith)).trans htarget
    · intro z hz
      exact tendsto_nhds_unique (hgc.tendsto_at hz) (hGpt _)
  have hGa (x : X) : ∃ i, x ∈ (e i).source ∧ AnalyticAt ℂ (G ∘ (e i).symm) ((e i) x) := by
    obtain ⟨i, r, g, hxi, hr, _, hga, _, heq⟩ := hlocal x
    refine ⟨i, hxi, ?_⟩
    apply ((hga.analyticOnNhd isOpen_ball) _ (mem_ball_self hr)).congr
    filter_upwards [ball_mem_nhds ((e i) x) hr] with z hz
    exact heq hz
  have hGc : Continuous G := by
    apply continuous_iff_continuousAt.mpr
    intro x
    obtain ⟨i, hxi, hax⟩ := hGa x
    apply (hax.continuousAt.comp ((e i).continuousAt hxi)).congr_of_eventuallyEq
    filter_upwards [(e i).open_source.mem_nhds hxi] with y hy
    simp only [Function.comp_apply, (e i).left_inv hy]
  refine ⟨G, ?_, hGc, hGa⟩
  apply tendstoLocallyUniformly_of_forall_exists_nhds
  intro x
  obtain ⟨i, r, g, hxi, hr, htarget, _, hgc, heq⟩ := hlocal x
  let E := e i
  have hsub : closedBall (E x) (r / 2) ⊆ ball (E x) r := by
    intro z hz
    have hh := mem_closedBall.mp hz
    rw [mem_ball]
    linarith
  have huni : TendstoUniformlyOn (fun n => F n ∘ E.symm) (G ∘ E.symm) atTop
      (closedBall (E x) (r / 2)) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall (E x) (r / 2))).mp ((hgc.congr_right heq).mono hsub)
  refine ⟨E.source ∩ E ⁻¹' closedBall (E x) (r / 2), ?_, ?_⟩
  · exact inter_mem (E.open_source.mem_nhds hxi)
      ((E.continuousAt hxi).preimage_mem_nhds
        (closedBall_mem_nhds (E x) (show 0 < r / 2 by positivity)))
  · have hh : TendstoUniformlyOn F ((G ∘ E.symm) ∘ E) atTop
        (E.source ∩ E ⁻¹' closedBall (E x) (r / 2)) :=
      ((huni.comp E).mono inter_subset_right).congr
      (Filter.Eventually.of_forall fun n y hy => by
        simp only [Function.comp_apply, E.left_inv hy.1])
    exact hh.congr_right (fun y hy => by simp only [Function.comp_apply, E.left_inv hy.1])

/-- An increasing open exhaustion and eventual local bounds provide controlled chart disks. -/
theorem eventuallyAnalyticBoundedCharts_of_exhaustion {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X ℂ) (he : ∀ x, ∃ i, x ∈ (e i).source)
    (U : ℕ → Set X) (hUo : ∀ n, IsOpen (U n)) (hUm : Monotone U)
    (hUc : ∀ x, ∃ n, x ∈ U n) (F : ℕ → X → ℂ)
    (hFa : ∀ n i, DifferentiableOn ℂ (F n ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' U n))
    (hbd : ∀ x, EventuallyLocallyBounded F x) : EventuallyAnalyticBoundedCharts e F := by
  intro x
  obtain ⟨i, hxi⟩ := he x
  let E := e i
  obtain ⟨V, hV, C, hC⟩ := hbd x
  have hx : E x ∈ E.target := E.map_source hxi
  have hV' : V ∈ 𝓝 (E.symm (E x)) := by rwa [E.left_inv hxi]
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (E.open_target.mem_nhds hx) ((E.continuousAt_symm hx).preimage_mem_nhds hV'))
  have hclosed : closedBall (E x) (ε / 2) ⊆ E.target ∩ E.symm ⁻¹' V := by
    intro z hz
    apply hεsub
    rw [mem_ball]
    have hh := mem_closedBall.mp hz
    linarith
  let K : Set X := E.symm '' closedBall (E x) (ε / 2)
  have hK : IsCompact K :=
    (isCompact_closedBall (E x) (ε / 2)).image_of_continuousOn
      (E.symm.continuousOn.mono fun z hz => (hclosed hz).1)
  obtain ⟨N, hN⟩ := hK.elim_directed_cover U hUo
    (fun z _ => mem_iUnion.mpr (hUc z)) hUm.directed_le
  refine ⟨i, ε / 2, C, hxi, by positivity, ?_, ?_⟩
  · exact fun z hz => (hclosed (ball_subset_closedBall hz)).1
  · filter_upwards [hC, eventually_ge_atTop N] with n hn hnN
    refine ⟨(hFa n i).mono ?_, ?_⟩
    · intro z hz
      exact ⟨(hclosed (ball_subset_closedBall hz)).1,
        hUm hnN (hN ⟨z, ball_subset_closedBall hz, rfl⟩)⟩
    · intro z hz
      exact hn _ (hclosed (ball_subset_closedBall hz)).2

/-- One disk extraction and Vitali continuation give a global analytic subsequential limit.
No second-countability assumption or diagonal chart extraction is used. -/
theorem surface_montel_of_eventuallyAnalyticBoundedCharts {X ι : Type*}
    [TopologicalSpace X] [PreconnectedSpace X] (e : ι → OpenPartialHomeomorph X ℂ)
    (F : ℕ → X → ℂ) (hcontrol : EventuallyAnalyticBoundedCharts e F) (x₀ : X) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : X → ℂ,
      TendstoLocallyUniformly (fun n => F (φ n)) G atTop ∧ Continuous G ∧
      ∀ x, ∃ i, x ∈ (e i).source ∧ AnalyticAt ℂ (G ∘ (e i).symm) ((e i) x) := by
  obtain ⟨i, R, C, hxi, hR, _, hgood⟩ := hcontrol x₀
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgood
  obtain ⟨φ, g, hφ, hg, _⟩ := Bottcher.montel_subseq
    (F := fun n => F (n + N) ∘ (e i).symm) (c := (e i) x₀) (r := R / 3)
    (by positivity) (by linarith)
    (fun n => (hN (n + N) (by omega)).1)
    (fun n => (hN (n + N) (by omega)).2)
  let ψ : ℕ → ℕ := fun n => φ n + N
  have hψ : StrictMono ψ := fun a b hab => Nat.add_lt_add_right (hφ hab) N
  have hcontrolψ : EventuallyAnalyticBoundedCharts e (fun n => F (ψ n)) := by
    intro x
    obtain ⟨j, S, D, hxj, hS, ht, hlate⟩ := hcontrol x
    exact ⟨j, S, D, hxj, hS, ht, hψ.tendsto_atTop.eventually hlate⟩
  have hseed : LocallyPointwiseConvergent (fun n => F (ψ n)) x₀ := by
    refine ⟨(e i).symm '' ball ((e i) x₀) (R / 3), ?_, ?_⟩
    · have hh := (e i).symm.image_mem_nhds ((e i).map_source hxi)
        (ball_mem_nhds ((e i) x₀) (show 0 < R / 3 by positivity))
      simpa only [(e i).left_inv hxi] using hh
    · rintro z ⟨w, hw, rfl⟩
      exact ⟨g w, hg.tendsto_at (ball_subset_closedBall hw)⟩
  exact ⟨ψ, hψ, surface_vitali_of_locallyPointwiseConvergent e (fun n => F (ψ n))
    hcontrolψ x₀ hseed⟩

/-- Injective holomorphic exhaustion families with a fixed zero are normal once bounded near
that zero. This is a construction theorem for the compactness step, not an existence claim for
the exhaustion itself. -/
theorem surface_montel_of_injective_exhaustion {X ι : Type*} [TopologicalSpace X]
    [T1Space X] [PreconnectedSpace X] (e : ι → OpenPartialHomeomorph X ℂ)
    (he : ∀ x, ∃ i, x ∈ (e i).source) (U : ℕ → Set X)
    (hUo : ∀ n, IsOpen (U n)) (hUm : Monotone U) (hUc : ∀ x, ∃ n, x ∈ U n)
    (F : ℕ → X → ℂ) (hFi : ∀ n, InjOn (F n) (U n))
    (hFa : ∀ n i, DifferentiableOn ℂ (F n ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' U n))
    (x₀ : X) (hF0 : ∀ n, F n x₀ = 0) (hbase : EventuallyLocallyBounded F x₀) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : X → ℂ,
      TendstoLocallyUniformly (fun n => F (φ n)) G atTop ∧ Continuous G ∧
      ∀ x, ∃ i, x ∈ (e i).source ∧ AnalyticAt ℂ (G ∘ (e i).symm) ((e i) x) := by
  have hbd := eventuallyLocallyBounded_of_exhaustion e he U hUo hUm hUc F hFi hFa x₀ hF0 hbase
  exact surface_montel_of_eventuallyAnalyticBoundedCharts e F
    (eventuallyAnalyticBoundedCharts_of_exhaustion e he U hUo hUm hUc F hFa hbd) x₀

end GaloisForLFunctions.HTGeometry
