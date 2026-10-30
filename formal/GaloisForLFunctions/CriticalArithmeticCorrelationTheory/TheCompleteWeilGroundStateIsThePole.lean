import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleConductorMinimizesTheCompletedEnergy
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilFormIsPositiveAtEveryFixedOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheBoundedCompleteWeilSpectrumIsTheCompletedShellSpectrum

/-!
# The complete Weil ground state is the pole

Reduced-residue block comparison identifies conductor one as the unique completed ground
energy, separated from all other conductors by a positive Fourier-tail gap. The actual complete
matrix has the same bounded spectral counts. Exactly one eigenvalue eventually lies below the
midpoint of that gap; it tends to the pole energy, and its spectral line captures the normalized
pole vector in Euclidean norm. All statements hold at every fixed positive overlap.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open CompletedShell

/-- The infimum of all completed conductor energies is attained at the pole conductor. -/
theorem completedEnergyFloor_eq_conductor_one {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) :
    completedEnergyFloor φ c = completedConductorEnergy φ c 1 := by
  refine le_antisymm (completedEnergyFloor_le hφ hsupp hM hc one_pos) ?_
  exact le_ciInf fun m => completedConductorEnergy_one_le hφ hsupp hM hc m.property

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- The Fourier-tail gap separating every nonpolar completed conductor from conductor one. -/
def tiltedUnitSplineGroundGap (c : ℝ) : ℝ :=
  2 / (∫ u, tiltedUnitSpline u ^ 2) * ∫ t in Set.Ioi c, shellSpectrum tiltedUnitSpline t

theorem tiltedUnitSplineGroundGap_pos (c : ℝ) : 0 < tiltedUnitSplineGroundGap c :=
  mul_pos (div_pos zero_lt_two integral_tiltedUnitSpline_sq_pos)
    (integral_shellSpectrum_tiltedUnitSpline_pos c)

/-- The actual bounded complete-Weil spectral counts equal the completed conductor counts,
with every quasimode and reserve input discharged for the explicit profile. -/
theorem eventually_tiltedUnitSpline_completeWeil_spectral_count_eq {c : ℝ} (hc : 0 < c)
    (T : ℝ) (hT : ∀ m : ℕ, 0 < m → completedConductorEnergy tiltedUnitSpline c m ≠ T) :
    ∀ᶠ N : ℕ in atTop,
      (completeWeilSpectralSublevel tiltedUnitSpline c N T).card =
        (completedEnergySublevel tiltedUnitSpline hc T).card := by
  obtain ⟨a, β, hβ, hres⟩ := exists_tiltedUnitSpline_completeWeilEnergy_reserve hc
  exact eventually_completeWeil_spectral_count_eq_of_reserve_quasimodes hc hβ hres
    (fun m hm => tendsto_completeWeilMatrix_completedConductor_residual_norm
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc hm)
    T hT

/-- Exactly one actual complete-Weil eigenvalue lies below the midpoint of the conductor gap. -/
theorem eventually_tiltedUnitSpline_completeWeil_ground_count_one {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      (completeWeilSpectralSublevel tiltedUnitSpline c N
        (completedConductorEnergy tiltedUnitSpline c 1 + tiltedUnitSplineGroundGap c / 2)).card = 1 := by
  let T := completedConductorEnergy tiltedUnitSpline c 1 + tiltedUnitSplineGroundGap c / 2
  have hδ := tiltedUnitSplineGroundGap_pos c
  have hgap : ∀ m : ℕ, 1 < m →
      completedConductorEnergy tiltedUnitSpline c 1 + tiltedUnitSplineGroundGap c ≤
        completedConductorEnergy tiltedUnitSpline c m := fun m hm =>
    completedConductorEnergy_nonpolar_gap contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      integral_tiltedUnitSpline_sq_pos hc hm
  have hT : ∀ m : ℕ, 0 < m → completedConductorEnergy tiltedUnitSpline c m ≠ T := by
    intro m hm heq
    by_cases hm1 : m = 1
    · subst m
      dsimp only [T] at heq
      linarith only [heq, hδ]
    · have h := hgap m (by omega)
      dsimp only [T] at heq
      linarith only [h, heq, hδ]
  have hset : completedEnergySublevel tiltedUnitSpline hc T = {1} := by
    ext m
    rw [mem_completedEnergySublevel, mem_singleton]
    constructor
    · rintro ⟨hm, hmT⟩
      by_contra hm1
      have h := hgap m (by omega)
      dsimp only [T] at hmT
      linarith only [h, hmT, hδ]
    · rintro rfl
      refine ⟨one_pos, ?_⟩
      dsimp only [T]
      linarith only [hδ]
  filter_upwards [eventually_tiltedUnitSpline_completeWeil_spectral_count_eq hc T hT] with N hN
  rw [hset, card_singleton] at hN
  exact hN

/-- At every fixed overlap, the actual bottom eigenvalue tends to the pole conductor energy. -/
theorem eventually_tiltedUnitSpline_completeWeil_ground_near_pole {c : ℝ} (hc : 0 < c)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∀ i : PrimeHorizonIndex N, completedConductorEnergy tiltedUnitSpline c 1 - ε <
        completeWeilEigenvalue tiltedUnitSpline c N i) ∧
      ∃ i : PrimeHorizonIndex N,
        |completeWeilEigenvalue tiltedUnitSpline c N i -
          completedConductorEnergy tiltedUnitSpline c 1| < ε := by
  obtain ⟨a, β, hβ, hres⟩ := exists_tiltedUnitSpline_completeWeilEnergy_reserve hc
  have h := eventually_completeWeil_spectrum_bottom_of_reserve_quasimodes
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
    hc hβ hres
    (fun m hm => tendsto_completeWeilMatrix_completedConductor_residual_norm
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc hm)
    hε
  simpa only [completedEnergyFloor_eq_conductor_one contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc] using h


/-- Projection of the normalized pole vector onto the unique eventual ground window. -/
def tiltedUnitSplineGroundProjection (c : ℝ) (N : ℕ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  HTGeometry.hermitianEigenProjection (completeWeilMatrix_isHermitian tiltedUnitSpline c N)
    (completeWeilSpectralSublevel tiltedUnitSpline c N
      (completedConductorEnergy tiltedUnitSpline c 1 + tiltedUnitSplineGroundGap c / 2))
    (normalizedRamanujanHorizonVector 1 N)

/-- The actual complete-Weil ground line captures the normalized pole vector in norm. -/
theorem tendsto_tiltedUnitSpline_groundProjection_error_sq {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ =>
      ‖normalizedRamanujanHorizonVector 1 N - tiltedUnitSplineGroundProjection c N‖ ^ 2)
      atTop (𝓝 0) := by
  let δ := tiltedUnitSplineGroundGap c / 2
  have hδ : 0 < δ := half_pos (tiltedUnitSplineGroundGap_pos c)
  have hbound (N : ℕ) :
      ‖normalizedRamanujanHorizonVector 1 N - tiltedUnitSplineGroundProjection c N‖ ^ 2 ≤
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector 1 N) -
            completedConductorEnergy tiltedUnitSpline c 1 • normalizedRamanujanHorizonVector 1 N‖ ^ 2 /
          δ ^ 2 := by
    have hgap : ∀ i ∉ completeWeilSpectralSublevel tiltedUnitSpline c N
        (completedConductorEnergy tiltedUnitSpline c 1 + δ),
        δ ≤ |(completeWeilMatrix_isHermitian tiltedUnitSpline c N).eigenvalues i -
          completedConductorEnergy tiltedUnitSpline c 1| := by
      intro i hi
      have hval : completedConductorEnergy tiltedUnitSpline c 1 + δ ≤
          completeWeilEigenvalue tiltedUnitSpline c N i := by
        simpa only [completeWeilSpectralSublevel, mem_filter, mem_univ, true_and, not_lt] using hi
      apply le_trans _ (le_abs_self _)
      change δ ≤ completeWeilEigenvalue tiltedUnitSpline c N i -
        completedConductorEnergy tiltedUnitSpline c 1
      linarith only [hval]
    have h := HTGeometry.gap_sq_mul_eigenProjection_error_le_residual_sq
      (completeWeilMatrix_isHermitian tiltedUnitSpline c N)
      (completeWeilSpectralSublevel tiltedUnitSpline c N
        (completedConductorEnergy tiltedUnitSpline c 1 + δ))
      (normalizedRamanujanHorizonVector 1 N)
      (completedConductorEnergy tiltedUnitSpline c 1) δ hδ.le hgap
    rw [le_div_iff₀ (sq_pos_of_pos hδ)]
    simpa only [tiltedUnitSplineGroundProjection, δ, mul_comm] using h
  have hlim := ((tendsto_completeWeilMatrix_completedConductor_residual_norm
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
    hc (m := 1) one_pos).pow 2).div_const (δ ^ 2)
  apply squeeze_zero (fun N => sq_nonneg _) hbound
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div] using hlim

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.completedEnergyFloor_eq_conductor_one
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeil_spectral_count_eq
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeil_ground_count_one
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeil_ground_near_pole

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_tiltedUnitSpline_groundProjection_error_sq

