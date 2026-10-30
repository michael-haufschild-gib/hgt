import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheBoundedCompleteWeilSpectrumIsTheCompletedShellSpectrum
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleConductorMinimizesTheCompletedEnergy
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapPositivityAtEveryOverlap

/-!
# The bottom of the complete Weil spectrum is the completed shell energy

For the tilted unit spline and every fixed overlap `c > 0` the low spectrum of the complete Weil
matrix is the completed conductor spectrum, with multiplicity
(`tiltedUnitSpline_spectral_count_eq`). Its bottom converges to the conductor-one energy, the
completed shell energy
`E(c) = (2/M) Σ_{k ≥ 1} (1/k) ∫_{kc}^∞ |φ̂(2πt)|² dt`
(`tiltedUnitSpline_spectrum_bottom`), which is positive and tends to `0` as `c → ∞`: Weil
positivity on the atomic families holds at every bounded overlap with exactly this margin, and the
margin vanishes at infinite overlap. Beyond `(log N)^{1/4}` positivity is the Riemann hypothesis
(`tiltedUnitSpline_overlap_window`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis CompletedShell CriticalArithmeticCorrelationTheory

/-- The bottom of the completed conductor spectrum is the conductor-one energy. -/
theorem completedEnergyFloor_eq_completedShellEnergy {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) :
    completedEnergyFloor φ c = completedShellEnergy φ c := by
  rw [← completedConductorEnergy_one]
  exact le_antisymm (completedEnergyFloor_le hφ hsupp hM hc one_pos)
    (le_ciInf fun m => completedConductorEnergy_one_le hφ hsupp hM hc m.property)

/-- **Exact low spectral counts at every overlap.** -/
theorem tiltedUnitSpline_spectral_count_eq {c : ℝ} (hc : 0 < c) (T : ℝ)
    (hT : ∀ m : ℕ, 0 < m → completedConductorEnergy tiltedUnitSpline c m ≠ T) :
    ∀ᶠ N : ℕ in atTop, (completeWeilSpectralSublevel tiltedUnitSpline c N T).card =
      (completedEnergySublevel tiltedUnitSpline hc T).card := by
  obtain ⟨a, β, hβ, hres⟩ := exists_tiltedUnitSpline_completeWeilEnergy_reserve hc
  exact eventually_completeWeil_spectral_count_eq_of_reserve_quasimodes hc hβ hres
    (fun _ hm => tendsto_completeWeilMatrix_ramanujan_quasimode_norm contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc hm) T hT

/-- **The bottom of the spectrum at every overlap** converges to the completed shell energy. -/
theorem tiltedUnitSpline_spectrum_bottom {c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∀ i, completedShellEnergy tiltedUnitSpline c - ε < completeWeilEigenvalue tiltedUnitSpline c N i) ∧
        ∃ i, |completeWeilEigenvalue tiltedUnitSpline c N i -
          completedShellEnergy tiltedUnitSpline c| < ε := by
  obtain ⟨a, β, hβ, hres⟩ := exists_tiltedUnitSpline_completeWeilEnergy_reserve hc
  have h := eventually_completeWeil_spectrum_bottom_of_reserve_quasimodes contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc hβ hres
    (fun _ hm => tendsto_completeWeilMatrix_ramanujan_quasimode_norm contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc hm) hε
  rwa [completedEnergyFloor_eq_completedShellEnergy contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc] at h

/-- **The margin vanishes at infinite overlap.** -/
theorem tendsto_tiltedUnitSpline_completedShellEnergy_atTop :
    Tendsto (completedShellEnergy tiltedUnitSpline) atTop (𝓝 0) := by
  simpa only [completedConductorEnergy_one] using
    tendsto_completedConductorEnergy_atTop contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      integral_tiltedUnitSpline_sq_pos 1

/-- **The overlap window of the Riemann hypothesis.** For the tilted unit spline the complete Weil
matrix is eventually positive definite at every fixed overlap, unconditionally, while eventual
positivity at overlap `2(log N)^α`, `α > 1/4`, is equivalent to RH. -/
theorem tiltedUnitSpline_overlap_window :
    (∀ c : ℝ, 0 < c → ∀ᶠ N : ℕ in atTop, (completeWeilMatrix tiltedUnitSpline c N).PosDef) ∧
      ∀ α : ℝ, 1 / 4 < α → (RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop,
        ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
          0 ≤ completeWeilEnergy tiltedUnitSpline (2 * Real.log N ^ α) N x) :=
  ⟨fun _ hc => eventually_tiltedUnitSpline_completeWeilMatrix_posDef hc,
    fun _ hα => riemannHypothesis_iff_tiltedUnitSpline_completeWeil_nonneg_log hα⟩

/-- **An unbounded schedule of unconditional positivity.** Diagonalizing the fixed-overlap
theorem gives overlap ratios `c_N → ∞` along which the complete Weil matrix of the tilted unit
spline is eventually positive definite. Hence a proof that every unbounded growth of the overlap
decides RH would prove RH: the critical growth lies strictly above some unbounded schedule. -/
theorem exists_unbounded_overlap_schedule_posDef :
    ∃ s : ℕ → ℕ, Tendsto s atTop atTop ∧
      ∀ᶠ N : ℕ in atTop, (completeWeilMatrix tiltedUnitSpline ((s N : ℝ) + 1) N).PosDef := by
  have h : ∀ k : ℕ, ∃ M : ℕ, ∀ N, M ≤ N →
      (completeWeilMatrix tiltedUnitSpline ((k : ℝ) + 1) N).PosDef := fun k =>
    eventually_atTop.mp (eventually_tiltedUnitSpline_completeWeilMatrix_posDef (by positivity))
  choose M hM using h
  -- a monotone majorant of the horizons, at least the index
  set M' : ℕ → ℕ := fun k => (∑ j ∈ range (k + 1), M j) + k with hM'
  have hle : ∀ k, M k ≤ M' k := fun k => by
    have : M k ≤ ∑ j ∈ range (k + 1), M j :=
      single_le_sum (f := M) (fun _ _ => Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_self k))
    simp only [hM']; omega
  have hmono : Monotone M' := by
    intro a b hab
    simp only [hM']
    have : ∑ j ∈ range (a + 1), M j ≤ ∑ j ∈ range (b + 1), M j :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun _ _ _ =>
        Nat.zero_le _
    omega
  refine ⟨fun N => Nat.findGreatest (fun k => M' k ≤ N) N, ?_, ?_⟩
  · refine tendsto_atTop_atTop.mpr fun K => ⟨M' K, fun N hN => ?_⟩
    have hKN : K ≤ N := (show K ≤ M' K by simp only [hM']; omega).trans hN
    exact Nat.le_findGreatest hKN hN
  · filter_upwards [eventually_ge_atTop (M' 0)] with N hN
    have hspec : M' (Nat.findGreatest (fun k => M' k ≤ N) N) ≤ N :=
      Nat.findGreatest_spec (P := fun k => M' k ≤ N) (Nat.zero_le N) hN
    exact hM _ N ((hle _).trans hspec)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
