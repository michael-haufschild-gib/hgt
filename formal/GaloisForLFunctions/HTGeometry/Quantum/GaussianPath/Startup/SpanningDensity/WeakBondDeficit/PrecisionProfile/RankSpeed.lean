import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.PrecisionProfile.SingleBondSpeed
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.PrecisionProfile.RemovableRank
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion.InitialSpeed

/-! # Initial speed bracket from two physical bond thresholds -/
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
variable {n : ℕ}

/-- A lower rank among all bonds and an upper rank among removable
bonds squeeze the genuine two-sided initial speed. For one missing
bond the upper factor is ten, independent of the prefix. -/
theorem rank_initial_speed (ω : PathPauliDisorder) (d : ℕ) {h g : ℝ} (hh : 0<h) (hg : 0<g)
    (hd : d≤n+1) (hw : (weakEdges (pathPauliDisorderShell ω n) h).card<d)
    (hr : d≤(removable (pathPauliDisorderShell ω n) g).card) :
    let u := pathPauliDisorderShell ω n
    let H := (⟨_,isSelfAdjoint_pathHamiltonian u⟩ :
      selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ))
    ∃ v∈Icc (h/2) ((9*(d:ℝ)+1)*g),
      Tendsto (fun t => orbitCircuitDistance H (n+1-d) t/|t|) (𝓝[≠] 0) (𝓝 v) := by
  intro u H
  let B := 3348*(‖u‖+1)
  let M := 84*‖u‖^2+1
  have hB : 0<B := by dsimp only [B]; positivity
  have hM : 0<M := by dsimp only [M]; positivity
  let a := min (1/B) (g/M)
  have ha : 0<a := lt_min (one_div_pos.mpr hB) (div_pos hg hM)
  apply initial_speed_in_interval
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (lt_mem_nhds (neg_lt_zero.mpr ha))] with t ht hl
  have hp : 0< -t := neg_pos.mpr (show t<0 from ht)
  have ha' : -t≤a := by linarith only [hl]
  have h₁ := (le_div_iff₀ hB).mp (ha'.trans (min_le_left ..))
  have h₂ := (le_div_iff₀ hM).mp (ha'.trans (min_le_right ..))
  have hsmall : 3348*(-t)*‖u‖≤1 := by dsimp only [B] at h₁; linarith only [h₁,hp]
  have hlo := rank_single_signal_lower ω d hh hp hd hw hsmall
  have hup := rank_distance_upper u d hr (-t)
  rw [abs_of_pos hp] at hup
  change (-t)*h/2<orbitCircuitDistance H (n+1-d) (-t) at hlo
  change orbitCircuitDistance H (n+1-d) (-t)≤_ at hup
  rw [orbitCircuitDistance_neg_time] at hlo hup
  have hrem : (-t)*(84*‖u‖^2)≤g := by dsimp only [M] at h₂; linarith only [h₂,hp]
  refine ⟨(le_div_iff₀ hp).mpr ?_,(div_le_iff₀ hp).mpr ?_⟩
  · linarith only [hlo]
  · linarith only [hup,mul_le_mul_of_nonneg_left hrem hp.le]

#print axioms rank_initial_speed
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
