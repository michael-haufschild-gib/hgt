import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ThePlateauShapeAndChargeHaveTheirIndicatorLimits
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheBoundedCompleteWeilSpectrumIsTheAdjunctionSpectrum
import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive complete Weil matrices throughout strict separation

The pole charge compensates the conductor-one loss for a smooth plateau.
Every arithmetic energy then lies above a fixed positive floor. Exhaustion of
the complete bounded spectrum transfers this floor to the whole finite matrix,
for each fixed width ratio below one. No horizon uniformity in that ratio is asserted.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity

/-- Below unit width, the completed conductor-one energy exceeds its endpoint value. -/
theorem completed_shape_le_completeWeilAdjunctionEnergy_one
    {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    bumpRobin φ 1 / (∫ u, φ u ^ 2) + completeWeilPoleShift φ 1 - Real.log (2 * Real.pi) ≤
      completeWeilAdjunctionEnergy φ c 1 := by
  have hq := completeWeilPoleShift_le hφ hsupp hM (c := 1) zero_le_one
  have hmul := mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hc1)
  have hlog := Real.log_le_sub_one_of_pos hc0
  have hp : completeWeilPoleShift φ c = c * completeWeilPoleShift φ 1 := by
    unfold completeWeilPoleShift
    ring
  rw [completeWeilAdjunctionEnergy, ramanujanAdjunctionEnergy_one, if_pos rfl,
    completeWeilSelfFinitePart, Real.log_div one_ne_zero (by positivity), Real.log_one,
    Real.log_mul (by positivity) hc0.ne', hp]
  nlinarith only [hmul, hlog]

/-- A threshold below conductor one eventually bounds every actual eigenvalue. -/
theorem eventually_completeWeil_eigenvalues_ge_of_lt_one
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {T : ℝ}
    (hT : T < completeWeilAdjunctionEnergy φ c 1) :
    ∀ᶠ N : ℕ in atTop, ∀ i : PrimeHorizonIndex N, T ≤ completeWeilEigenvalue φ c N i := by
  have hall : ∀ m : ℕ, 0 < m → T < completeWeilAdjunctionEnergy φ c m := by
    intro m hm
    by_cases hm1 : m = 1
    · simpa only [hm1] using hT
    · exact hT.trans (completeWeilAdjunctionEnergy_one_lt hφ.continuous hsupp hM hc0.le hc1
        (by omega : 2 ≤ m))
  have hempty : completeWeilEnergySublevel φ c T = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro m hm
    have hm' := (mem_completeWeilEnergySublevel φ c T m).mp hm
    exact (not_lt_of_gt (hall m hm'.1)) hm'.2
  filter_upwards [eventually_completeWeil_spectral_count_eq hφ hsupp hM hc0 hc1 T
    (fun m hm => ne_of_gt (hall m hm))] with N hN
  have hzero : completeWeilSpectralSublevel φ c N T = ∅ := by
    apply card_eq_zero.mp
    simpa only [hempty, card_empty] using hN
  intro i
  by_contra hi
  have himem : i ∈ completeWeilSpectralSublevel φ c N T := by
    exact mem_filter.mpr ⟨mem_univ _, lt_of_not_ge hi⟩
  simp [hzero] at himem

/-- Almost all of the unit support's mass can be retained with any strict spectral
floor below `2 - log (2π)`. The profile is independent of the width ratio. -/
theorem exists_near_unit_plateau_eventually_completeWeil_eigenvalues_ge {b ε : ℝ}
    (hb : b < 2 - Real.log (2 * Real.pi)) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
      1 - ε < (∫ u, plateau η u ^ 2) ∧
      ∀ c : ℝ, 0 < c → c < 1 →
        ∀ᶠ N : ℕ in atTop, ∀ i : PrimeHorizonIndex N,
          b ≤ completeWeilEigenvalue (plateau η) c N i := by
  have hshape := tendsto_plateau_completed_margin.eventually (lt_mem_nhds hb)
  have hmass := tendsto_integral_plateau_sq.eventually
    (lt_mem_nhds (show 1 - ε < 1 by linarith only [hε]))
  have hsmall : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1 / 2 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num))
  obtain ⟨η, hmargin, hmassη, hη2, hη⟩ :=
    (hshape.and (hmass.and (hsmall.and self_mem_nhdsWithin))).exists
  refine ⟨η, hη, hη2, hmassη, fun c hc0 hc1 => ?_⟩
  have hM : 0 < ∫ u, plateau η u ^ 2 :=
    lt_of_lt_of_le (by linarith only [hη2]) (integral_plateau_sq_ge hη hη2.le)
  apply eventually_completeWeil_eigenvalues_ge_of_lt_one (contDiff_plateau η)
    (fun _ hu => plateau_eq_zero hη hu) hM hc0 hc1
  have hfloor := completed_shape_le_completeWeilAdjunctionEnergy_one
    (contDiff_plateau η).continuous (fun _ hu => plateau_eq_zero hη hu) hM hc0 hc1.le
  simp only [completeWeilPoleShift, one_mul] at hfloor
  linarith only [hmargin, hfloor]

/-- A single smooth plateau gives the same spectral floor at every fixed separated
width ratio. The horizon may depend on that ratio. -/
theorem exists_plateau_eventually_completeWeil_eigenvalues_ge {b : ℝ}
    (hb : b < 2 - Real.log (2 * Real.pi)) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
      ∀ c : ℝ, 0 < c → c < 1 →
        ∀ᶠ N : ℕ in atTop, ∀ i : PrimeHorizonIndex N,
          b ≤ completeWeilEigenvalue (plateau η) c N i := by
  obtain ⟨η, hη, hη2, _, hall⟩ :=
    exists_near_unit_plateau_eventually_completeWeil_eigenvalues_ge hb (ε := 1) zero_lt_one
  exact ⟨η, hη, hη2, hall⟩

/-- The same margin controls every vector of the literal completed quadratic form. -/
theorem exists_plateau_eventually_completeWeilEnergy_ge {b : ℝ}
    (hb : b < 2 - Real.log (2 * Real.pi)) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
      ∀ c : ℝ, 0 < c → c < 1 →
        ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
          b * ‖x‖ ^ 2 ≤ completeWeilEnergy (plateau η) c N x := by
  obtain ⟨η, hη, hη2, hall⟩ := exists_plateau_eventually_completeWeil_eigenvalues_ge hb
  refine ⟨η, hη, hη2, fun c hc0 hc1 => ?_⟩
  filter_upwards [hall c hc0 hc1] with N hN
  intro x
  rw [completeWeilEnergy,
    HTGeometry.hermitianEnergy_eq_sum (completeWeilMatrix_isHermitian (plateau η) c N),
    ← (completeWeilMatrix_isHermitian (plateau η) c N).eigenvectorBasis.sum_sq_inner_left x,
    mul_sum]
  exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hN i) (sq_nonneg _)

/-- The literal complete Weil matrix is eventually positive definite at every fixed
strictly separated width, for one nonnegative smooth compact profile. -/
theorem exists_plateau_eventually_completeWeilMatrix_posDef :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
      ∀ c : ℝ, 0 < c → c < 1 →
        ∀ᶠ N : ℕ in atTop, (completeWeilMatrix (plateau η) c N).PosDef := by
  let b : ℝ := (2 - Real.log (2 * Real.pi)) / 2
  have hb0 : 0 < b := by
    dsimp [b]
    linarith only [RHTower.log_two_pi_lt_two]
  have hb : b < 2 - Real.log (2 * Real.pi) := by
    dsimp [b] at *
    linarith only [hb0]
  obtain ⟨η, hη, hη2, hall⟩ := exists_plateau_eventually_completeWeil_eigenvalues_ge hb
  refine ⟨η, hη, hη2, fun c hc0 hc1 => ?_⟩
  filter_upwards [hall c hc0 hc1] with N hN
  apply (completeWeilMatrix_isHermitian (plateau η) c N).posDef_iff_eigenvalues_pos.mpr
  intro i
  exact hb0.trans_le (hN i)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_plateau_eventually_completeWeilMatrix_posDef
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_plateau_eventually_completeWeilEnergy_ge
