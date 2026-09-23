import GaloisForLFunctions.RHTower.EulerDeletionLogClockLocalization

noncomputable section
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
namespace RHTower.DeletionResidueMartingale

def lowClockProducerEnergy (N : ℕ) : ℝ :=
  ‖(historySpace 0).starProjection (predictableDrift N)‖ ^ (2 : ℕ) +
    ∑ l ∈ range (min (logarithmicClockThreshold N) N),
      ‖historyLayer l (predictableDrift N)‖ ^ (2 : ℕ)

theorem predictableDrift_norm_sq_eq_lowClock_add_highClock (N : ℕ) :
    ‖predictableDrift N‖ ^ (2 : ℕ) = lowClockProducerEnergy N +
      ∑ l ∈ Ico (logarithmicClockThreshold N) N,
        ‖historyLayer l (predictableDrift N)‖ ^ (2 : ℕ) := by
  have hfin : range N =
      range (min (logarithmicClockThreshold N) N) ∪
        Ico (logarithmicClockThreshold N) N := by
    ext l
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint
      (range (min (logarithmicClockThreshold N) N))
      (Ico (logarithmicClockThreshold N) N) := by
    simp only [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [predictableDrift_norm_sq_eq_historyLayer_sum, hfin, Finset.sum_union hdisj]
  unfold lowClockProducerEnergy
  ring

theorem predictableDrift_norm_sq_sub_lowClock_tendsto_zero :
    Tendsto (fun N : ℕ => ‖predictableDrift N‖ ^ (2 : ℕ) - lowClockProducerEnergy N)
      atTop (𝓝 0) := by
  convert predictableDrift_logarithmic_highClock_energy_tendsto_zero using 1
  funext N
  rw [predictableDrift_norm_sq_eq_lowClock_add_highClock]
  ring

end RHTower.DeletionResidueMartingale
