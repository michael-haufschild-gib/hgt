import GaloisForLFunctions.HTGeometry.OneFiberDiskGrowth
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic

open Filter Topology Set Metric
namespace GaloisForLFunctions.HTGeometry

/-- A neighborhood has one common norm bound for all sufficiently late maps. -/
def EventuallyLocallyBounded {X : Type*} [TopologicalSpace X]
    (F : ℕ → X → ℂ) (x : X) : Prop :=
  ∃ V ∈ 𝓝 x, ∃ C : ℝ, ∀ᶠ n in atTop, ∀ y ∈ V, ‖F n y‖ ≤ C

/-- Eventual local boundedness is an open condition on the source point. -/
theorem isOpen_eventuallyLocallyBounded {X : Type*} [TopologicalSpace X] (F : ℕ → X → ℂ) :
    IsOpen {x | EventuallyLocallyBounded F x} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨V, hV, C, hC⟩
  obtain ⟨W, hWV, hWo, hxW⟩ := mem_nhds_iff.mp hV
  apply mem_of_superset (hWo.mem_nhds hxW)
  intro y hy
  exact ⟨V, mem_of_superset (hWo.mem_nhds hy) hWV, C, hC⟩

/-- On a connected complex surface, one bounded neighborhood propagates through an increasing
exhaustion of injective holomorphic maps sharing one fixed zero. No countable atlas is needed. -/
theorem eventuallyLocallyBounded_of_exhaustion {X ι : Type*} [TopologicalSpace X]
    [T1Space X] [PreconnectedSpace X] (e : ι → OpenPartialHomeomorph X ℂ)
    (he : ∀ x, ∃ i, x ∈ (e i).source) (U : ℕ → Set X)
    (hUo : ∀ n, IsOpen (U n)) (hUm : Monotone U) (hUc : ∀ x, ∃ n, x ∈ U n)
    (F : ℕ → X → ℂ) (hFi : ∀ n, InjOn (F n) (U n))
    (hFa : ∀ n i, DifferentiableOn ℂ (F n ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' U n))
    (x₀ : X) (hF0 : ∀ n, F n x₀ = 0) (hbase : EventuallyLocallyBounded F x₀) :
    ∀ x, EventuallyLocallyBounded F x := by
  classical
  obtain ⟨B, hB, hbound⟩ := exists_one_fiber_omitted_value_disk_bound
  let S : Set X := {x | EventuallyLocallyBounded F x}
  have hSo : IsOpen S := isOpen_eventuallyLocallyBounded F
  have hSc : closure S ⊆ S := by
    intro y hy
    by_cases hy0 : y = x₀
    · simpa [S, hy0] using hbase
    obtain ⟨i, hyi⟩ := he y
    let E := e i
    let c : ℂ := E y
    have hc : c ∈ E.target := E.map_source hyi
    have havoid : ∀ᶠ z in 𝓝 c, E.symm z ≠ x₀ :=
      (E.continuousAt_symm hc).eventually_ne (by simpa [c, E.left_inv hyi] using hy0)
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
      (inter_mem (E.open_target.mem_nhds hc) havoid)
    let r : ℝ := ε / 8
    have hr : 0 < r := by dsimp [r]; positivity
    have hball : closedBall c (4 * r) ⊆ E.target ∩ {z | E.symm z ≠ x₀} := by
      intro z hz
      apply hεsub
      rw [mem_ball]
      have hz' := mem_closedBall.mp hz
      dsimp [r] at *
      linarith
    let K : Set X := E.symm '' closedBall c (4 * r)
    have hK : IsCompact K :=
      (isCompact_closedBall c (4 * r)).image_of_continuousOn
        (E.symm.continuousOn.mono (fun z hz => (hball hz).1))
    obtain ⟨N, hN⟩ := hK.elim_directed_cover U hUo
      (fun z _ => mem_iUnion.mpr (hUc z)) hUm.directed_le
    obtain ⟨N₀, hN₀⟩ := hUc x₀
    have hV : E.source ∩ E ⁻¹' ball c (r / 2) ∈ 𝓝 y :=
      inter_mem (E.open_source.mem_nhds hyi)
        ((E.continuousAt hyi).preimage_mem_nhds (ball_mem_nhds c (by positivity)))
    obtain ⟨x, ⟨hxi, hxc⟩, hxS⟩ := mem_closure_iff_nhds.mp hy _ hV
    obtain ⟨V, hVx, C, hC⟩ := hxS
    have hCx : ∀ᶠ n in atTop, ‖F n x‖ ≤ C := hC.mono (fun n hn => hn x (mem_of_mem_nhds hVx))
    have hsmall : ball (E x) (2 * r) ⊆ closedBall c (4 * r) := by
      intro z hz
      have hzx := mem_ball.mp hz
      have hxc' := mem_ball.mp hxc
      rw [mem_closedBall]
      have hh := dist_triangle z (E x) c
      linarith
    refine ⟨E.symm '' ball c (r / 2), ?_, B * C, ?_⟩
    · have hh := E.symm.image_mem_nhds hc (ball_mem_nhds c (show 0 < r / 2 by positivity))
      simpa only [c, E.left_inv hyi] using hh
    · filter_upwards [hCx, eventually_ge_atTop N, eventually_ge_atTop N₀] with n hn hnN hnN₀
      have hstage : K ⊆ U n := hN.trans (hUm hnN)
      have hlocal : ball (E x) (2 * r) ⊆ E.target ∩ E.symm ⁻¹' U n := by
        intro z hz
        exact ⟨(hball (hsmall hz)).1, hstage ⟨z, hsmall hz, rfl⟩⟩
      have hdf : DifferentiableOn ℂ (F n ∘ E.symm) (ball (E x) (2 * r)) :=
        (hFa n i).mono hlocal
      have hsingle : ∀ z ∈ ball (E x) (2 * r),
          (F n ∘ E.symm) z = (F n ∘ E.symm) (E x) → z = E x := by
        intro z hz hsame
        have hxloc := hlocal (mem_ball_self (by positivity : 0 < 2 * r))
        have hxEq := hFi n (hlocal hz).2 hxloc.2 hsame
        exact E.symm.injOn (hlocal hz).1 hxloc.1 hxEq
      have homit : ∀ z ∈ ball (E x) (2 * r), (F n ∘ E.symm) z ≠ 0 := by
        intro z hz hz0
        have heq : E.symm z = x₀ := hFi n (hlocal hz).2 (hUm hnN₀ hN₀)
          (hz0.trans (hF0 n).symm)
        exact (hball (hsmall hz)).2 heq
      rintro w ⟨z, hz, rfl⟩
      have hdist : ‖z - E x‖ ≤ (2 * r) / 2 := by
        rw [← dist_eq_norm]
        have hzc := mem_ball.mp hz
        have hcx := mem_ball.mp hxc
        have hh := dist_triangle z c (E x)
        rw [dist_comm c (E x)] at hh
        linarith
      have hb := hbound (F n ∘ E.symm) (E x) 0 (2 * r) (by positivity) hdf hsingle homit z hdist
      simp only [Function.comp_apply, sub_zero, E.left_inv hxi] at hb
      exact hb.trans (mul_le_mul_of_nonneg_left hn (by linarith))
  have hclosed : IsClosed S := by
    have hh : closure S = S := subset_antisymm hSc subset_closure
    rw [← hh]
    exact isClosed_closure
  have hall : S = univ := (show IsClopen S from ⟨hclosed, hSo⟩).eq_univ ⟨x₀, hbase⟩
  intro x
  have hx : x ∈ S := hall.symm ▸ mem_univ x
  exact hx

end GaloisForLFunctions.HTGeometry
