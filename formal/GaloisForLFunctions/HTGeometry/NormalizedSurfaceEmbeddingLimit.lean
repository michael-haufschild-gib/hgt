import GaloisForLFunctions.HTGeometry.NormalizedEmbeddingDiskBound
import GaloisForLFunctions.HTGeometry.SurfaceVitaliCompactness
import GaloisForLFunctions.HTGeometry.SurfaceHurwitzEmbedding

open Filter Topology Set Metric
namespace GaloisForLFunctions.HTGeometry

/-- Normalization on one chart supplies the initial eventual local bound automatically. -/
theorem eventuallyLocallyBounded_of_normalized_exhaustion {X : Type*} [TopologicalSpace X]
    (E : OpenPartialHomeomorph X ℂ) (U : ℕ → Set X)
    (hUo : ∀ n, IsOpen (U n)) (hUm : Monotone U) (hUc : ∀ x, ∃ n, x ∈ U n)
    (F : ℕ → X → ℂ) (hFi : ∀ n, InjOn (F n) (U n))
    (hFa : ∀ n, DifferentiableOn ℂ (F n ∘ E.symm) (E.target ∩ E.symm ⁻¹' U n))
    (hFd : ∀ n z, z ∈ E.target ∩ E.symm ⁻¹' U n → deriv (F n ∘ E.symm) z ≠ 0)
    (x₀ : X) (hx₀ : x₀ ∈ E.source) (hE₀ : E x₀ = 0)
    (hF₀ : ∀ n, F n x₀ = 0) (hnorm : ∀ᶠ n in atTop, deriv (F n ∘ E.symm) 0 = 1) :
    EventuallyLocallyBounded F x₀ := by
  have h0 : (0 : ℂ) ∈ E.target := hE₀ ▸ E.map_source hx₀
  have hi0 : E.symm 0 = x₀ := by rw [← hE₀, E.left_inv hx₀]
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (E.open_target.mem_nhds h0)
  let R : ℝ := ε / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hclosed : closedBall (0 : ℂ) R ⊆ E.target := by
    intro z hz
    apply hεsub
    rw [mem_ball]
    have hh := mem_closedBall.mp hz
    dsimp [R] at *
    linarith
  let K : Set X := E.symm '' closedBall (0 : ℂ) R
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) R).image_of_continuousOn (E.symm.continuousOn.mono hclosed)
  obtain ⟨N, hN⟩ := hK.elim_directed_cover U hUo
    (fun z _ => mem_iUnion.mpr (hUc z)) hUm.directed_le
  obtain ⟨C, _, hC⟩ := exists_normalized_embedding_disk_bound
  refine ⟨E.symm '' ball 0 (R / 2), ?_, C * R, ?_⟩
  · have hh := E.symm.image_mem_nhds h0 (ball_mem_nhds 0 (show 0 < R / 2 by positivity))
    simpa only [hi0] using hh
  · filter_upwards [eventually_ge_atTop N, hnorm] with n hnN hdn
    have hlocal : ball (0 : ℂ) R ⊆ E.target ∩ E.symm ⁻¹' U n := by
      intro z hz
      exact ⟨hclosed (ball_subset_closedBall hz),
        hUm hnN (hN ⟨z, ball_subset_closedBall hz, rfl⟩)⟩
    have hfd : DifferentiableOn ℂ (F n ∘ E.symm) (ball 0 R) := (hFa n).mono hlocal
    have hfi : InjOn (F n ∘ E.symm) (ball 0 R) := by
      intro z hz w hw hzw
      exact E.symm.injOn (hlocal hz).1 (hlocal hw).1
        (hFi n (hlocal hz).2 (hlocal hw).2 hzw)
    have hf0 : (F n ∘ E.symm) 0 = 0 := by simp only [Function.comp_apply, hi0, hF₀ n]
    rintro y ⟨z, hz, rfl⟩
    exact hC (F n ∘ E.symm) R hR hfd hfi (fun w hw => hFd n w (hlocal hw)) hf0 hdn z
      (by simpa using (mem_ball.mp hz).le)

/-- A locally uniform exhaustion limit is analytic in every supplied complex chart. -/
theorem analyticOnNhd_chart_of_exhaustion_locallyUniformLimit {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X ℂ) (U : ℕ → Set X)
    (hUo : ∀ n, IsOpen (U n)) (hUm : Monotone U) (hUc : ∀ x, ∃ n, x ∈ U n)
    (F : ℕ → X → ℂ)
    (hFa : ∀ n i, DifferentiableOn ℂ (F n ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' U n))
    {G : X → ℂ} (hlim : TendstoLocallyUniformly F G atTop) (i : ι) :
    AnalyticOnNhd ℂ (G ∘ (e i).symm) (e i).target := by
  intro z hz
  obtain ⟨N, hN⟩ := hUc ((e i).symm z)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem ((e i).open_target.mem_nhds hz)
      (((e i).continuousAt_symm hz).preimage_mem_nhds ((hUo N).mem_nhds hN)))
  have hlate : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n ∘ (e i).symm) (ball z r) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    apply (hFa n i).mono
    exact fun w hw => ⟨(hrsub hw).1, hUm hn (hrsub hw).2⟩
  have hc : TendstoLocallyUniformlyOn (fun n => F n ∘ (e i).symm) (G ∘ (e i).symm)
      atTop (ball z r) :=
    hlim.tendstoLocallyUniformlyOn.comp (e i).symm (mapsTo_univ _ _)
      ((e i).symm.continuousOn.mono fun w hw => (hrsub hw).1)
  exact ((hc.differentiableOn hlate isOpen_ball).analyticOnNhd isOpen_ball) z (mem_ball_self hr)

/-- A normalized exhaustion by local analytic embeddings has a global analytic open-embedding
limit. This constructs the compactness handoff without a countable atlas or uniformization. -/
theorem exists_openEmbedding_limit_of_normalized_exhaustion {X ι : Type*}
    [TopologicalSpace X] [T1Space X] [PreconnectedSpace X]
    (e : ι → OpenPartialHomeomorph X ℂ) (he : ∀ x, ∃ i, x ∈ (e i).source)
    (U : ℕ → Set X) (hUo : ∀ n, IsOpen (U n)) (hUm : Monotone U)
    (hUc : ∀ x, ∃ n, x ∈ U n) (F : ℕ → X → ℂ)
    (hFi : ∀ n, InjOn (F n) (U n))
    (hFa : ∀ n i, DifferentiableOn ℂ (F n ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' U n))
    (hFd : ∀ n i z, z ∈ (e i).target ∩ (e i).symm ⁻¹' U n →
      deriv (F n ∘ (e i).symm) z ≠ 0)
    (x₀ : X) (i₀ : ι) (hx₀ : x₀ ∈ (e i₀).source) (hE₀ : (e i₀) x₀ = 0)
    (hF₀ : ∀ n, F n x₀ = 0)
    (hnorm : ∀ᶠ n in atTop, deriv (F n ∘ (e i₀).symm) 0 = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : X → ℂ,
      TendstoLocallyUniformly (fun n => F (φ n)) G atTop ∧ IsOpenEmbedding G ∧
      G x₀ = 0 ∧ deriv (G ∘ (e i₀).symm) 0 = 1 ∧
      ∀ i, AnalyticOnNhd ℂ (G ∘ (e i).symm) (e i).target := by
  have hbase := eventuallyLocallyBounded_of_normalized_exhaustion (e i₀) U hUo hUm hUc F hFi
    (fun n => hFa n i₀) (fun n => hFd n i₀) x₀ hx₀ hE₀ hF₀ hnorm
  obtain ⟨φ, hφ, G, hlim, _, hG⟩ :=
    surface_montel_of_injective_exhaustion e he U hUo hUm hUc F hFi hFa x₀ hF₀ hbase
  let E := e i₀
  have hi0 : E.symm 0 = x₀ := by rw [← hE₀, E.left_inv hx₀]
  have h0 : (0 : ℂ) ∈ E.target := hE₀ ▸ E.map_source hx₀
  obtain ⟨N, hN⟩ := hUc x₀
  have hUN : U N ∈ 𝓝 (E.symm 0) := by rw [hi0]; exact (hUo N).mem_nhds hN
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (E.open_target.mem_nhds h0) ((E.continuousAt_symm h0).preimage_mem_nhds hUN))
  have hlate : ∀ᶠ n in atTop, DifferentiableOn ℂ (F (φ n) ∘ E.symm) (ball 0 r) := by
    filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop N] with n hn
    apply (hFa (φ n) i₀).mono
    intro z hz
    exact ⟨(hrsub hz).1, hUm hn (hrsub hz).2⟩
  have hderiv : deriv (G ∘ E.symm) 0 = 1 :=
    deriv_chart_limit_eq_of_eventually E hlim isOpen_ball (fun z hz => (hrsub hz).1)
      (mem_ball_self hr) hlate (hφ.tendsto_atTop.eventually hnorm)
  have hnc : ¬ ∃ b, ∀ x, G x = b := by
    rintro ⟨b, hb⟩
    have hh : G ∘ E.symm = fun _ : ℂ => b := funext fun z => hb _
    rw [hh, deriv_const] at hderiv
    exact zero_ne_one hderiv
  have hUφ : ∀ x, ∃ n, x ∈ U (φ n) := by
    intro x
    obtain ⟨n, hn⟩ := hUc x
    exact ⟨n, hUm (hφ.id_le n) hn⟩
  have hemb : IsOpenEmbedding G :=
    isOpenEmbedding_of_exhaustion_locallyUniformLimit e (fun n => U (φ n))
      (fun n => hUo (φ n)) (hUm.comp hφ.monotone) hUφ (fun n => F (φ n))
      (fun n => hFi (φ n)) (fun n => hFa (φ n)) hlim hG hnc
  have hG0 : G x₀ = 0 := by
    have hh := hlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ x₀)
    have hh0 : Tendsto (fun n => F (φ n) x₀) atTop (𝓝 (0 : ℂ)) := by
      simpa only [hF₀] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    exact tendsto_nhds_unique hh hh0
  refine ⟨φ, hφ, G, hlim, hemb, hG0, hderiv, ?_⟩
  exact analyticOnNhd_chart_of_exhaustion_locallyUniformLimit e (fun n => U (φ n))
    (fun n => hUo (φ n)) (hUm.comp hφ.monotone) hUφ (fun n => F (φ n))
    (fun n => hFa (φ n)) hlim

end GaloisForLFunctions.HTGeometry
