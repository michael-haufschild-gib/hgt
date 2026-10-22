import GaloisForLFunctions.RHTower.EulerDeletionLogClockLocalization

/-!
# Reduction of the predictable drift energy to its low-clock part

The squared norm of the predictable Möbius drift `predictableDrift N` splits orthogonally into
its projection onto `historySpace 0`, the history layers `l < min(K(N), N)` below the
logarithmic clock threshold `K(N) = 5(⌊log₂(N + 1)⌋ + 1)`, and the layers `K(N) ≤ l < N`.
The first two pieces form `lowClockProducerEnergy N`. Since the high-clock part tends to `0`,
`‖predictableDrift N‖² - lowClockProducerEnergy N → 0`.

## Main results

- `lowClockProducerEnergy`: `‖P_0 (drift N)‖² + ∑_{l < min(K(N), N)} ‖historyLayer l (drift N)‖²`.
- `predictableDrift_norm_sq_eq_lowClock_add_highClock`: the exact energy split.
- `predictableDrift_norm_sq_sub_lowClock_tendsto_zero`:
  `‖predictableDrift N‖² - lowClockProducerEnergy N → 0` as `N → ∞`.

## Hypotheses

All results are unconditional.
-/

noncomputable section
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
namespace RHTower.DeletionResidueMartingale

/-- Low-clock energy of the predictable drift: the squared projection onto `historySpace 0` plus the
layer energies for `l < min(K(N), N)`. -/
def lowClockProducerEnergy (N : ℕ) : ℝ :=
  ‖(historySpace 0).starProjection (predictableDrift N)‖ ^ (2 : ℕ) +
    ∑ l ∈ range (min (logarithmicClockThreshold N) N),
      ‖historyLayer l (predictableDrift N)‖ ^ (2 : ℕ)

/-- Exact orthogonal split: `‖predictableDrift N‖²` equals the low-clock energy plus the layer energies
for `K(N) ≤ l < N`. -/
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

/-- The full drift energy is asymptotically carried by the low clocks:
`‖predictableDrift N‖² - lowClockProducerEnergy N → 0`. -/
theorem predictableDrift_norm_sq_sub_lowClock_tendsto_zero :
    Tendsto (fun N : ℕ => ‖predictableDrift N‖ ^ (2 : ℕ) - lowClockProducerEnergy N)
      atTop (𝓝 0) := by
  convert predictableDrift_logarithmic_highClock_energy_tendsto_zero using 1
  funext N
  rw [predictableDrift_norm_sq_eq_lowClock_add_highClock]
  ring

end RHTower.DeletionResidueMartingale
