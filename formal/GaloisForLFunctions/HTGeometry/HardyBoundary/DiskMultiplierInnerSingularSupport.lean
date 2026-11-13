import GaloisForLFunctions.HTGeometry.HardyBoundary.LocalPoissonMassVanishing
import GaloisForLFunctions.HTGeometry.HardyBoundary.DiskMultiplierInnerDefect

/-!
# Singular inner mass of a boundary-nonvanishing multiplier

Continuity and nonvanishing off one boundary point bound the inner log defect
on compact radial sectors. Its almost-everywhere radial limit is zero, so the
local Poisson mass estimate confines its representing measure to that point.
-/

noncomputable section
open Complex MeasureTheory Metric Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

private theorem exists_Icc_collar_subset {U : Set ℝ} (hU : IsOpen U)
    {α β : ℝ} (hαβ : α ≤ β) (hsub : Icc α β ⊆ U) :
    ∃ η : ℝ, 0 < η ∧ Icc (α - η) (β + η) ⊆ U := by
  obtain ⟨a, ha, hballa⟩ := Metric.isOpen_iff.mp hU α (hsub ⟨le_rfl, hαβ⟩)
  obtain ⟨b, hb, hballb⟩ := Metric.isOpen_iff.mp hU β (hsub ⟨hαβ, le_rfl⟩)
  let η := min a b / 2
  have hη : 0 < η := half_pos (lt_min ha hb)
  have hηa : η < a := (half_lt_self (lt_min ha hb)).trans_le (min_le_left a b)
  have hηb : η < b := (half_lt_self (lt_min ha hb)).trans_le (min_le_right a b)
  refine ⟨η, hη, ?_⟩
  intro θ hθ
  by_cases hleft : θ < α
  · apply hballa
    rw [mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith only [hθ.1, hηa], by linarith only [hleft, ha]⟩
  by_cases hright : β < θ
  · apply hballb
    rw [mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith only [hright, hb], by linarith only [hθ.2, hηb]⟩
  exact hsub ⟨le_of_not_gt hleft, le_of_not_gt hright⟩

/-- A bounded multiplier continuous and nonzero on the closed disk except at `1`
has no singular inner mass at any other boundary point. -/
theorem innerDefect_poissonMeasure_concentrated_at_one (φ : DiskMultiplier)
    (hφ : ∃ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0)
    (hc : ContinuousOn φ.fn {z : ℂ | ‖z‖ ≤ 1 ∧ z ≠ 1})
    (hne : ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 → φ.fn z ≠ 0)
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hrep : ∀ w ∈ ball (0 : ℂ) 1,
      ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν = diskMultiplierInnerDefect φ hφ w) :
    ν {θ : ℝ | circleMap 0 1 θ ≠ 1} = 0 := by
  have hU : IsOpen {θ : ℝ | circleMap 0 1 θ ≠ 1} :=
    isOpen_ne.preimage (continuous_circleMap 0 1)
  have hne' : ∀ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0 := by
    intro z hz
    have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    apply hne z hn.le
    intro he
    rw [he, norm_one] at hn
    exact (lt_irrefl (1 : ℝ)) hn
  have hharm := harmonicOnNhd_diskMultiplierInnerDefect φ hφ hne'
  have hcont : ContinuousOn (diskMultiplierInnerDefect φ hφ) (ball (0 : ℂ) 1) :=
    fun z hz => (hharm z hz).1.continuousAt.continuousWithinAt
  obtain ⟨ns, hns, hae⟩ := exists_diskMultiplierInnerDefect_angular_subseq_ae φ hφ
  apply measure_eq_zero_of_isOpen_of_rat_Icc hU
  intro p hp
  by_cases hporder : (p.1 : ℝ) ≤ (p.2 : ℝ)
  · obtain ⟨η, hη, hcollar⟩ := exists_Icc_collar_subset hU hporder hp
    obtain ⟨m, hm, hlower⟩ := exists_pos_norm_lower_bound_on_radial_arc hc hne
      (show (p.1 : ℝ) - η ≤ (p.2 : ℝ) + η by linarith only [hporder, hη]) hcollar
    have hmass : ν.real (Icc (p.1 : ℝ) (p.2 : ℝ)) = 0 := by
      apply measureReal_Icc_eq_zero_of_bounded_radial_ae_vanishing hrep hcont hη
        (r := fun i => hardyDiskAbelRadius (ns i))
        (fun i => hardyDiskAbelRadius_nonneg (ns i))
        (fun i => hardyDiskAbelRadius_lt_one (ns i))
        (tendsto_hardyDiskAbelRadius.mono_right nhdsWithin_le_nhds |>.comp hns.tendsto_atTop)
        (M := Real.log (diskMultiplierOuterFactor φ hφ).bd - Real.log m)
      · intro i θ hθ
        have hz : circleMap 0 (hardyDiskAbelRadius (ns i)) θ ∈ ball (0 : ℂ) 1 := by
          rw [mem_ball, dist_zero_right, norm_circleMap_zero,
            abs_of_nonneg (hardyDiskAbelRadius_nonneg (ns i))]
          exact hardyDiskAbelRadius_lt_one (ns i)
        rw [Real.norm_eq_abs, abs_of_nonneg (diskMultiplierInnerDefect_nonneg φ hφ hz)]
        exact diskMultiplierInnerDefect_le_of_norm_lower_bound φ hφ hz hm
          (hlower _ ⟨hardyDiskAbelRadius_nonneg (ns i),
            (hardyDiskAbelRadius_lt_one (ns i)).le⟩ θ hθ)
      · exact ae_restrict_of_ae hae
    exact ((ENNReal.toReal_eq_zero_iff (ν (Icc (p.1 : ℝ) (p.2 : ℝ)))).mp hmass).resolve_right
      (measure_ne_top ν _)
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hporder), measure_empty]

/-- The surviving inner defect is a single Poisson kernel, with nonnegative mass. -/
theorem innerDefect_eq_mass_mul_poissonKernel_of_rep (φ : DiskMultiplier)
    (hφ : ∃ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0)
    (hc : ContinuousOn φ.fn {z : ℂ | ‖z‖ ≤ 1 ∧ z ≠ 1})
    (hne : ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 → φ.fn z ≠ 0)
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hrep : ∀ w ∈ ball (0 : ℂ) 1,
      ∫ θ, poissonKernel 0 w (circleMap 0 1 θ) ∂ν = diskMultiplierInnerDefect φ hφ w)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    diskMultiplierInnerDefect φ hφ w = ν.real univ * poissonKernel 0 w 1 := by
  have hmass := innerDefect_poissonMeasure_concentrated_at_one φ hφ hc hne hrep
  have hae : ∀ᵐ θ ∂ν, circleMap 0 1 θ = 1 := ae_iff.mpr hmass
  rw [← hrep w hw]
  calc
    _ = ∫ _θ : ℝ, poissonKernel 0 w 1 ∂ν := integral_congr_ae (hae.mono fun _ hθ => by rw [hθ])
    _ = ν.real univ * poissonKernel 0 w 1 := by rw [integral_const, smul_eq_mul]

#print axioms innerDefect_poissonMeasure_concentrated_at_one
#print axioms innerDefect_eq_mass_mul_poissonKernel_of_rep

end GaloisForLFunctions.HTGeometry
