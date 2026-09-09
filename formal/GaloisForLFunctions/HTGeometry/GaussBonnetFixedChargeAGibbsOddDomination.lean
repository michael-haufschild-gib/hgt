import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsOddKernelLimit

/-!
# Uniform domination of the divided Gibbs force difference

The exact four-term decomposition controls the correction on the entire
phase interval. Its bound depends only on the fixed critical prefactor,
not the coordinate or sufficiently near-critical coexistence state.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAGibbsOddKernel_dominated (w φ : ℝ) :
    ∀ᶠ τ in atBot, ∀ t ∈ Icc (-1 : ℝ) 1,
      |egbFixedChargeAGibbsOddKernel w φ τ t| ≤ 80 * (egbFixedChargeAGibbsCriticalPrefactor w φ + 1) := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have hAhi := (egbFixedChargeAGibbsPrefactor_critical_limit w φ).eventually_lt_const
    (show egbFixedChargeAGibbsCriticalPrefactor w φ < egbFixedChargeAGibbsCriticalPrefactor w φ + 1 by linarith)
  have hEAhi := (egbFixedChargeAGibbsPrefactor_linear_limit w φ).eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  have hEAlo := (egbFixedChargeAGibbsPrefactor_linear_limit w φ).eventually_const_lt (by norm_num : (-1 : ℝ) < 0)
  have hELhi := (egbFixedChargeAGibbsLinear_linear_limit φ).eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  have hELlo := (egbFixedChargeAGibbsLinear_linear_limit φ).eventually_const_lt (by norm_num : (-1 : ℝ) < 0)
  have hLhi := (egbFixedChargeAGibbsLinear_critical_limit φ).eventually_lt_const
    (show 4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) < 5 by linarith)
  have hLlo := (egbFixedChargeAGibbsLinear_critical_limit φ).eventually_const_lt
    (show -5 < 4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) by linarith)
  have hNhi := (egbFixedChargeAMeanPressureNumerator_critical_limit φ).eventually_lt_const
    (show 3 - 2 * egbFixedChargeACriticalCouplingWeight φ < 4 by linarith)
  have hRhi := (egbFixedChargeAGibbsResidual_critical_limit φ).eventually_lt_const
    (show 1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5 < 2 by linarith)
  have hRlo := (egbFixedChargeAGibbsResidual_critical_limit φ).eventually_const_lt
    (show -2 < 1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5 by linarith)
  filter_upwards [hAhi, hEAhi, hEAlo, hELhi, hELlo, hLhi, hLlo, hNhi, hRhi, hRlo,
    egbFixedChargeAGibbsReciprocal_uniform_bounds] with τ hAhi hEAhi hEAlo hELhi hELlo hLhi hLlo hNhi hRhi hRlo hEall
  intro t ht
  let A0 := egbFixedChargeAGibbsCriticalPrefactor w φ
  let A := egbFixedChargeAGibbsPrefactor w φ τ
  let EA := (A - A0) / egbCoexistenceASymmetricRatio τ
  let L := egbFixedChargeAGibbsLinear τ φ
  let L0 := 4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ)
  let EL := (L - L0) / egbCoexistenceASymmetricRatio τ
  let E := egbFixedChargeAGibbsReciprocal τ t
  let ER := (E - 1) / egbCoexistenceASymmetricRatio τ
  let N := egbFixedChargeAMeanPressureNumerator τ φ
  let R := egbFixedChargeAGibbsResidual τ φ
  have hA0 : 0 < A0 := egbFixedChargeAGibbsCriticalPrefactor_pos w φ
  have hA : 0 < A := egbFixedChargeAGibbsPrefactor_pos w φ τ
  have hN : 0 < N := egbFixedChargeAMeanPressureNumerator_pos τ φ
  have hL0 : 0 < L0 := by dsimp [L0]; linarith
  have hL04 : L0 ≤ 4 := by dsimp [L0]; linarith
  change A < A0 + 1 at hAhi
  change EA < 1 at hEAhi
  change -1 < EA at hEAlo
  change EL < 1 at hELhi
  change -1 < EL at hELlo
  change L < 5 at hLhi
  change -5 < L at hLlo
  change N < 4 at hNhi
  change R < 2 at hRhi
  change -2 < R at hRlo
  have hE : (0 < E ∧ E ≤ 4) ∧ |ER| ≤ 12 := hEall t ht
  have hAabs : |A| ≤ A0 + 1 := by rw [abs_of_pos hA]; exact hAhi.le
  have hA0abs : |A0| ≤ A0 := by rw [abs_of_pos hA0]
  have hEAabs : |EA| ≤ 1 := abs_le.mpr ⟨hEAlo.le, hEAhi.le⟩
  have hELabs : |EL| ≤ 1 := abs_le.mpr ⟨hELlo.le, hELhi.le⟩
  have hLabs : |L| ≤ 5 := abs_le.mpr ⟨hLlo.le, hLhi.le⟩
  have hL0abs : |L0| ≤ 4 := by rw [abs_of_pos hL0]; exact hL04
  have hEabs : |E| ≤ 4 := by rw [abs_of_pos hE.1.1]; exact hE.1.2
  have hNabs : |N| ≤ 4 := by rw [abs_of_pos hN]; exact hNhi.le
  have hRabs : |R| ≤ 2 := abs_le.mpr ⟨hRlo.le, hRhi.le⟩
  have htabs : |t| ≤ 1 := abs_le.mpr ht
  have ht2 : t ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - t by linarith [ht.2]) (show 0 ≤ t + 1 by linarith [ht.1])]
  have htf : |t ^ 2 - 1| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg t]
  have hterm1 : |EA * E * L * t| ≤ 20 := by
    simp only [abs_mul]
    calc
      _ ≤ ((1 * 4) * 5) * 1 :=
        mul_le_mul (mul_le_mul (mul_le_mul hEAabs hEabs (abs_nonneg _) (by norm_num)) hLabs (abs_nonneg _) (by norm_num))
          htabs (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hterm2 : |A0 * EL * E * t| ≤ 4 * A0 := by
    simp only [abs_mul]
    calc
      _ ≤ ((A0 * 1) * 4) * 1 :=
        mul_le_mul (mul_le_mul (mul_le_mul hA0abs hELabs (abs_nonneg _) hA0.le) hEabs (abs_nonneg _) (by positivity))
          htabs (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hterm3 : |A0 * L0 * t * ER| ≤ 48 * A0 := by
    simp only [abs_mul]
    calc
      _ ≤ ((A0 * 4) * 1) * 12 :=
        mul_le_mul (mul_le_mul (mul_le_mul hA0abs hL0abs (abs_nonneg _) hA0.le) htabs (abs_nonneg _) (by positivity))
          hE.2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hNr : |N * t ^ 2 + R| ≤ 6 := by
    have hNt : |N * t ^ 2| ≤ 4 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
      calc
        _ ≤ 4 * 1 := mul_le_mul hNabs ht2 (sq_nonneg t) (by norm_num)
        _ = _ := by norm_num
    calc
      _ ≤ |N * t ^ 2| + |R| := abs_add_le _ _
      _ ≤ 4 + 2 := add_le_add hNt hRabs
      _ = _ := by norm_num
  have hterm4 : |A * E * (N * t ^ 2 + R)| ≤ 24 * (A0 + 1) := by
    simp only [abs_mul]
    calc
      _ ≤ ((A0 + 1) * 4) * 6 :=
        mul_le_mul (mul_le_mul hAabs hEabs (abs_nonneg _) (by positivity)) hNr (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hsum : |EA * E * L * t + A0 * EL * E * t + A0 * L0 * t * ER + A * E * (N * t ^ 2 + R)| ≤
      80 * (A0 + 1) := by
    calc
      _ ≤ |EA * E * L * t + A0 * EL * E * t + A0 * L0 * t * ER| + |A * E * (N * t ^ 2 + R)| := abs_add_le _ _
      _ ≤ (|EA * E * L * t + A0 * EL * E * t| + |A0 * L0 * t * ER|) + |A * E * (N * t ^ 2 + R)| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ ((|EA * E * L * t| + |A0 * EL * E * t|) + |A0 * L0 * t * ER|) + |A * E * (N * t ^ 2 + R)| :=
        add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
      _ ≤ ((20 + 4 * A0) + 48 * A0) + 24 * (A0 + 1) :=
        add_le_add (add_le_add (add_le_add hterm1 hterm2) hterm3) hterm4
      _ ≤ _ := by linarith
  rw [egbFixedChargeAGibbsOddKernel_decomposition]
  change |(t ^ 2 - 1) * (EA * E * L * t + A0 * EL * E * t + A0 * L0 * t * ER + A * E * (N * t ^ 2 + R))| ≤ 80 * (A0 + 1)
  rw [abs_mul]
  calc
    _ ≤ 1 * (80 * (A0 + 1)) := mul_le_mul htf hsum (abs_nonneg _) (by norm_num)
    _ = _ := by ring

end GaloisForLFunctions.HTGeometry
