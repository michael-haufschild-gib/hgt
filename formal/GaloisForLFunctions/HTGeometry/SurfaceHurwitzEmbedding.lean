import GaloisForLFunctions.HTGeometry.SurfaceLocalBoundPropagation
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.LocallyUniformLimit
import GaloisForLFunctions.HTGeometry.HurwitzZeroLimit
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

open Filter Topology Set Metric
namespace GaloisForLFunctions.HTGeometry

/-- The scalar analytic-germ zero dichotomy transfers through any complex chart. -/
theorem chartwise_analytic_eventually_eq_or_ne {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X ℂ) {G : X → ℂ}
    (hG : ∀ x, ∃ i, x ∈ (e i).source ∧ AnalyticAt ℂ (G ∘ (e i).symm) ((e i) x))
    (x : X) (b : ℂ) :
    (∀ᶠ y in 𝓝 x, G y = b) ∨ (∀ᶠ y in 𝓝[≠] x, G y ≠ b) := by
  obtain ⟨i, hxi, hGa⟩ := hG x
  let E := e i
  have hgb : AnalyticAt ℂ (fun z => G (E.symm z) - b) (E x) := hGa.sub analyticAt_const
  rcases hgb.eventually_eq_zero_or_eventually_ne_zero with heq | hne
  · left
    filter_upwards [(E.continuousAt hxi).eventually heq, E.open_source.mem_nhds hxi] with y hy hys
    simpa only [Pi.sub_apply, Function.comp_apply, E.left_inv hys, sub_eq_zero] using hy
  · right
    apply eventually_nhdsWithin_iff.mpr
    have hne' := eventually_nhdsWithin_iff.mp hne
    filter_upwards [(E.continuousAt hxi).eventually hne', E.open_source.mem_nhds hxi] with y hy hys
    intro hyx
    have hey : E y ≠ E x := fun h => hyx (E.injOn hys hxi h)
    have hh := hy hey
    simpa only [Pi.sub_apply, Function.comp_apply, E.left_inv hys, sub_ne_zero] using hh

/-- A local scalar identity extends across a connected complex-charted source. -/
theorem chartwise_analytic_eq_const_of_eventuallyEq {X ι : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (e : ι → OpenPartialHomeomorph X ℂ) {G : X → ℂ}
    (hG : ∀ x, ∃ i, x ∈ (e i).source ∧ AnalyticAt ℂ (G ∘ (e i).symm) ((e i) x))
    (x₀ : X) (b : ℂ) (hbase : ∀ᶠ y in 𝓝 x₀, G y = b) : ∀ x, G x = b := by
  let S : Set X := {x | ∀ᶠ y in 𝓝 x, G y = b}
  have hSo : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp hx
    apply mem_of_superset (hVo.mem_nhds hxV)
    intro y hy
    exact mem_of_superset (hVo.mem_nhds hy) hV
  have hSc : closure S ⊆ S := by
    intro x hx
    rcases chartwise_analytic_eventually_eq_or_ne e hG x b with hlocal | hpunct
    · exact hlocal
    · by_contra hxS
      have hpunct' := eventually_nhdsWithin_iff.mp hpunct
      obtain ⟨y, hyne, hyS⟩ := mem_closure_iff_nhds.mp hx _ hpunct'
      have hyx : y ≠ x := fun h => hxS (h ▸ hyS)
      have heq : G y = b := (show ∀ᶠ z in 𝓝 y, G z = b from hyS).self_of_nhds
      exact hyne hyx heq
  have hall : S = univ :=
    (show IsClopen S from ⟨isClosed_of_closure_subset hSc, hSo⟩).eq_univ ⟨x₀, hbase⟩
  intro x
  have hx : x ∈ S := hall.symm ▸ mem_univ x
  exact (show ∀ᶠ z in 𝓝 x, G z = b from hx).self_of_nhds

/-- Analyticity in one local complex chart at each point implies continuity on the surface. -/
theorem continuous_of_chartwise_analytic {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X ℂ) {G : X → ℂ}
    (hG : ∀ x, ∃ i, x ∈ (e i).source ∧ AnalyticAt ℂ (G ∘ (e i).symm) ((e i) x)) :
    Continuous G := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨i, hxi, ha⟩ := hG x
  apply (ha.continuousAt.comp ((e i).continuousAt hxi)).congr_of_eventuallyEq
  filter_upwards [(e i).open_source.mem_nhds hxi] with y hy
  simp only [Function.comp_apply, (e i).left_inv hy]

/-- A nonconstant locally uniform limit of injective holomorphic maps on an open exhaustion
remains injective on the whole source. -/
theorem injective_of_exhaustion_locallyUniformLimit {X ι : Type*} [TopologicalSpace X]
    [T1Space X] [PreconnectedSpace X] (e : ι → OpenPartialHomeomorph X ℂ)
    (U : ℕ → Set X) (hUo : ∀ n, IsOpen (U n)) (hUm : Monotone U)
    (hUc : ∀ x, ∃ n, x ∈ U n) (F : ℕ → X → ℂ)
    (hFi : ∀ n, InjOn (F n) (U n))
    (hFa : ∀ n i, DifferentiableOn ℂ (F n ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' U n))
    {G : X → ℂ} (hlim : TendstoLocallyUniformly F G atTop)
    (hG : ∀ x, ∃ i, x ∈ (e i).source ∧ AnalyticAt ℂ (G ∘ (e i).symm) ((e i) x))
    (hnc : ¬ ∃ b, ∀ x, G x = b) : Function.Injective G := by
  classical
  intro x y hxy
  by_contra hne
  obtain ⟨i, hxi, hGa⟩ := hG x
  let E := e i
  let c : ℂ := E x
  let H : ℕ → ℂ → ℂ := fun n z => F n (E.symm z) - F n y
  let g : ℂ → ℂ := fun z => G (E.symm z) - G y
  have hc : c ∈ E.target := E.map_source hxi
  have hnot : ¬ ∀ᶠ z in 𝓝 c, g z = 0 := by
    intro hz
    apply hnc
    refine ⟨G y, chartwise_analytic_eq_const_of_eventuallyEq e hG x (G y) ?_⟩
    filter_upwards [(E.continuousAt hxi).eventually hz, E.open_source.mem_nhds hxi] with w hw hws
    simpa only [g, E.left_inv hws, sub_eq_zero] using hw
  have hga : AnalyticAt ℂ g c := hGa.sub analyticAt_const
  have hpunct := eventually_nhdsWithin_iff.mp
    (hga.eventually_eq_zero_or_eventually_ne_zero.resolve_left hnot)
  have havoid : ∀ᶠ z in 𝓝 c, E.symm z ≠ y :=
    (E.continuousAt_symm hc).eventually_ne (by simpa only [c, E.left_inv hxi] using hne)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (E.open_target.mem_nhds hc) (inter_mem havoid hpunct))
  let r : ℝ := ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hclosed : closedBall c (2 * r) ⊆
      E.target ∩ {z | E.symm z ≠ y} ∩ {z | z ≠ c → g z ≠ 0} := by
    intro z hz
    have hzε : z ∈ ball c ε := by
      rw [mem_ball]
      have hh := mem_closedBall.mp hz
      dsimp [r] at *
      linarith
    have hh := hεsub hzε
    exact ⟨⟨hh.1, hh.2.1⟩, hh.2.2⟩
  let K : Set X := E.symm '' closedBall c (2 * r)
  have hK : IsCompact K :=
    (isCompact_closedBall c (2 * r)).image_of_continuousOn
      (E.symm.continuousOn.mono fun z hz => (hclosed hz).1.1)
  obtain ⟨N, hN⟩ := hK.elim_directed_cover U hUo
    (fun z _ => mem_iUnion.mpr (hUc z)) hUm.directed_le
  obtain ⟨Ny, hNy⟩ := hUc y
  let L := max N Ny
  have hstage (n : ℕ) : K ⊆ U (n + L) := hN.trans (hUm (by dsimp [L]; omega))
  have hystage (n : ℕ) : y ∈ U (n + L) := hUm (by dsimp [L]; omega) hNy
  have hlocal (n : ℕ) : ball c (2 * r) ⊆ E.target ∩ E.symm ⁻¹' U (n + L) := by
    intro z hz
    exact ⟨(hclosed (ball_subset_closedBall hz)).1.1,
      hstage n ⟨z, ball_subset_closedBall hz, rfl⟩⟩
  have hH (n : ℕ) : DiffContOnCl ℂ (H (n + L)) (ball c r) := by
    have hh : DifferentiableOn ℂ (H (n + L)) (ball c (2 * r)) :=
      ((hFa (n + L) i).mono (hlocal n)).sub_const (F (n + L) y)
    refine ⟨hh.mono (ball_subset_ball (by linarith)), ?_⟩
    rw [closure_ball c hr.ne']
    exact hh.continuousOn.mono (closedBall_subset_ball (by linarith))
  have hGc : Continuous G := continuous_of_chartwise_analytic e hG
  have hgcont : ContinuousOn g (sphere c r) := by
    apply (hGc.continuousOn.comp (E.symm.continuousOn.mono ?_) (mapsTo_univ _ _)).sub continuousOn_const
    intro z hz
    apply (hclosed _).1.1
    exact (closedBall_subset_closedBall (by linarith : r ≤ 2 * r)) (sphere_subset_closedBall hz)
  have hcoordinate : TendstoLocallyUniformlyOn (fun n => F n ∘ E.symm) (G ∘ E.symm) atTop E.target :=
    hlim.tendstoLocallyUniformlyOn.comp E.symm (mapsTo_univ _ _) E.symm.continuousOn
  have hHlim : TendstoLocallyUniformlyOn H g atTop E.target :=
    hcoordinate.sub (((hlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ y)).tendstoUniformlyOn_const E.target).tendstoLocallyUniformlyOn)
  have hsmalltarget : closedBall c r ⊆ E.target := by
    intro z hz
    exact (hclosed (closedBall_subset_closedBall (by linarith : r ≤ 2 * r) hz)).1.1
  have huni : TendstoUniformlyOn H g atTop (closedBall c r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_closedBall c r)).mp
      (hHlim.mono hsmalltarget)
  have hshift : StrictMono (fun n : ℕ => n + L) := fun a b hab => Nat.add_lt_add_right hab L
  have htail : TendstoUniformlyOn (fun n => H (n + L)) g atTop (closedBall c r) :=
    fun u hu => hshift.tendsto_atTop.eventually (huni u hu)
  have hgc : g c = 0 := by simp only [g, c, E.left_inv hxi, hxy, sub_self]
  have hgsphere : ∀ z ∈ sphere c r, g z ≠ 0 := by
    intro z hz
    have hh := hclosed (closedBall_subset_closedBall (by linarith : r ≤ 2 * r)
      (sphere_subset_closedBall hz))
    apply hh.2
    intro heq
    have hz' := mem_sphere.mp hz
    rw [heq, dist_self] at hz'
    linarith
  obtain ⟨n, z, hz, hzero⟩ :=
    (eventually_exists_zero_of_tendstoUniformlyOn hr hH hgcont htail hgc hgsphere).exists
  have hzouter : z ∈ closedBall c (2 * r) :=
    closedBall_subset_closedBall (by linarith : r ≤ 2 * r) (ball_subset_closedBall hz)
  have heq : E.symm z = y := hFi (n + L) (hstage n ⟨z, hzouter, rfl⟩) (hystage n)
    (sub_eq_zero.mp hzero)
  exact (hclosed hzouter).1.2 heq

/-- Nonconstant chartwise analytic scalar maps on a connected source are open. -/
theorem isOpenMap_of_chartwise_analytic_nonconstant {X ι : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (e : ι → OpenPartialHomeomorph X ℂ) {G : X → ℂ}
    (hG : ∀ x, ∃ i, x ∈ (e i).source ∧ AnalyticAt ℂ (G ∘ (e i).symm) ((e i) x))
    (hnc : ¬ ∃ b, ∀ x, G x = b) : IsOpenMap G := by
  apply isOpenMap_iff_nhds_le.mpr
  intro x
  obtain ⟨i, hxi, ha⟩ := hG x
  let E := e i
  have hnot : ¬ ∀ᶠ z in 𝓝 (E x), G (E.symm z) = G (E.symm (E x)) := by
    intro hz
    apply hnc
    refine ⟨G x, chartwise_analytic_eq_const_of_eventuallyEq e hG x (G x) ?_⟩
    filter_upwards [(E.continuousAt hxi).eventually hz, E.open_source.mem_nhds hxi] with y hy hys
    simpa only [E.left_inv hxi, E.left_inv hys] using hy
  have hnh := ha.eventually_constant_or_nhds_le_map_nhds.resolve_left hnot
  change 𝓝 (G (E.symm (E x))) ≤ Filter.map (G ∘ E.symm) (𝓝 (E x)) at hnh
  rw [E.left_inv hxi, ← Filter.map_map, E.symm_map_nhds_eq hxi] at hnh
  exact hnh

/-- The nonconstant limit is a genuine global open embedding. -/
theorem isOpenEmbedding_of_exhaustion_locallyUniformLimit {X ι : Type*} [TopologicalSpace X]
    [T1Space X] [PreconnectedSpace X] (e : ι → OpenPartialHomeomorph X ℂ)
    (U : ℕ → Set X) (hUo : ∀ n, IsOpen (U n)) (hUm : Monotone U)
    (hUc : ∀ x, ∃ n, x ∈ U n) (F : ℕ → X → ℂ)
    (hFi : ∀ n, InjOn (F n) (U n))
    (hFa : ∀ n i, DifferentiableOn ℂ (F n ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' U n))
    {G : X → ℂ} (hlim : TendstoLocallyUniformly F G atTop)
    (hG : ∀ x, ∃ i, x ∈ (e i).source ∧ AnalyticAt ℂ (G ∘ (e i).symm) ((e i) x))
    (hnc : ¬ ∃ b, ∀ x, G x = b) : IsOpenEmbedding G :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_of_chartwise_analytic e hG)
    (injective_of_exhaustion_locallyUniformLimit e U hUo hUm hUc F hFi hFa hlim hG hnc)
    (isOpenMap_of_chartwise_analytic_nonconstant e hG hnc)

/-- A fixed chart derivative is preserved under locally uniform convergence, even when the
coordinate functions are holomorphic only eventually. -/
theorem deriv_chart_limit_eq_of_eventually {X : Type*} [TopologicalSpace X]
    (E : OpenPartialHomeomorph X ℂ) {F : ℕ → X → ℂ} {G : X → ℂ}
    (hlim : TendstoLocallyUniformly F G atTop) {s : Set ℂ} (hs : IsOpen s)
    (hst : s ⊆ E.target) {z : ℂ} (hz : z ∈ s) {a : ℂ}
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n ∘ E.symm) s)
    (hd : ∀ᶠ n in atTop, deriv (F n ∘ E.symm) z = a) :
    deriv (G ∘ E.symm) z = a := by
  have hc : TendstoLocallyUniformlyOn (fun n => F n ∘ E.symm) (G ∘ E.symm) atTop s :=
    hlim.tendstoLocallyUniformlyOn.comp E.symm (mapsTo_univ _ _) (E.symm.continuousOn.mono hst)
  have hdlim := (hc.deriv hF hs).tendsto_at hz
  have hconst : Tendsto (fun n => deriv (F n ∘ E.symm) z) atTop (𝓝 a) :=
    tendsto_const_nhds.congr' (hd.mono fun n hn => hn.symm)
  exact tendsto_nhds_unique hdlim hconst

end GaloisForLFunctions.HTGeometry
