import GaloisForLFunctions.HTGeometry.Thermodynamics.FiniteCanonicalHeat
import GaloisForLFunctions.HTGeometry.ChargedStringGibbsVariance
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Sharp spectral bounds on canonical heat capacity

The fluctuation identity turns a finite spectral range into a heat-capacity
bound. The exact defect classifies saturation: every level is an endpoint
and the Gibbs mean is the midpoint. Applied to charged-string potential
samples, the existing strict electrostatic variance bound becomes a strict
canonical response bound.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.Thermodynamics
open _root_.HTGeometry
variable {A : Type*} [Fintype A] [Nonempty A]

def finiteSpectrumMin (E : A → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty E
def finiteSpectrumMax (E : A → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty E

theorem finiteSpectrum_bounds (E : A → ℝ) (a : A) :
    finiteSpectrumMin E ≤ E a ∧ E a ≤ finiteSpectrumMax E :=
  ⟨Finset.inf'_le E (Finset.mem_univ a), Finset.le_sup' E (Finset.mem_univ a)⟩

/-- Both defects are retained, making the sharp bound and its equality case explicit. -/
theorem finiteGibbsVariance_range_decomposition (β : ℝ) (E : A → ℝ) :
    finiteGibbsEnergyVariance β E = (finiteSpectrumMax E - finiteSpectrumMin E) ^ 2 / 4 -
      (finiteGibbsEnergyMean β E - (finiteSpectrumMin E + finiteSpectrumMax E) / 2) ^ 2 -
      ∑ a, finiteGibbsStateWeight β E a * (E a - finiteSpectrumMin E) *
        (finiteSpectrumMax E - E a) := by
  have hsum : (∑ a, finiteGibbsStateWeight β E a * (E a - finiteSpectrumMin E) *
        (finiteSpectrumMax E - E a)) =
      (finiteSpectrumMin E + finiteSpectrumMax E) * finiteGibbsEnergyMean β E -
        (∑ a, finiteGibbsStateWeight β E a * E a ^ 2) - finiteSpectrumMin E * finiteSpectrumMax E := by
    calc
      _ = ∑ a, (finiteSpectrumMin E + finiteSpectrumMax E) * (finiteGibbsStateWeight β E a * E a) -
          finiteGibbsStateWeight β E a * E a ^ 2 -
          (finiteSpectrumMin E * finiteSpectrumMax E) * finiteGibbsStateWeight β E a := by
            apply Finset.sum_congr rfl
            intro a _
            ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, sum_finiteGibbsStateWeight_eq_one, mul_one]
        rfl
  rw [hsum]
  unfold finiteGibbsEnergyVariance
  ring

theorem finiteGibbsRangeDefect_nonneg (β : ℝ) (E : A → ℝ) (a : A) :
    0 ≤ finiteGibbsStateWeight β E a * (E a - finiteSpectrumMin E) *
      (finiteSpectrumMax E - E a) :=
  mul_nonneg (mul_nonneg (finiteGibbsStateWeight_pos β E a).le
    (sub_nonneg.mpr (finiteSpectrum_bounds E a).1)) (sub_nonneg.mpr (finiteSpectrum_bounds E a).2)

theorem finiteGibbsVariance_range_bound (β : ℝ) (E : A → ℝ) :
    finiteGibbsEnergyVariance β E ≤ (finiteSpectrumMax E - finiteSpectrumMin E) ^ 2 / 4 := by
  have hd := finiteGibbsVariance_range_decomposition β E
  have hs := Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => finiteGibbsRangeDefect_nonneg β E a)
  nlinarith only [hd, hs,
    sq_nonneg (finiteGibbsEnergyMean β E - (finiteSpectrumMin E + finiteSpectrumMax E) / 2)]

/-- The variance bound is saturated exactly by a balanced two-endpoint Gibbs law. -/
theorem finiteGibbsVariance_range_equality_iff (β : ℝ) (E : A → ℝ) :
    finiteGibbsEnergyVariance β E = (finiteSpectrumMax E - finiteSpectrumMin E) ^ 2 / 4 ↔
      finiteGibbsEnergyMean β E = (finiteSpectrumMin E + finiteSpectrumMax E) / 2 ∧
        ∀ a, E a = finiteSpectrumMin E ∨ E a = finiteSpectrumMax E := by
  have hd := finiteGibbsVariance_range_decomposition β E
  have hs := Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => finiteGibbsRangeDefect_nonneg β E a)
  constructor
  · intro heq
    have hsq : (finiteGibbsEnergyMean β E -
        (finiteSpectrumMin E + finiteSpectrumMax E) / 2) ^ 2 = 0 := by
      nlinarith only [hd, hs, heq,
        sq_nonneg (finiteGibbsEnergyMean β E - (finiteSpectrumMin E + finiteSpectrumMax E) / 2)]
    have hzero : (∑ a, finiteGibbsStateWeight β E a * (E a - finiteSpectrumMin E) *
        (finiteSpectrumMax E - E a)) = 0 := by linarith only [hd, hsq, heq]
    refine ⟨sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hsq), ?_⟩
    intro a
    have ha := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b (_ : b ∈ Finset.univ) => finiteGibbsRangeDefect_nonneg β E b)).mp hzero a
        (Finset.mem_univ a)
    rcases mul_eq_zero.mp ha with hleft | hright
    · exact Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp hleft).resolve_left
        (finiteGibbsStateWeight_pos β E a).ne'))
    · exact Or.inr (sub_eq_zero.mp hright).symm
  · rintro ⟨hm, he⟩
    have hzero : (∑ a, finiteGibbsStateWeight β E a * (E a - finiteSpectrumMin E) *
        (finiteSpectrumMax E - E a)) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      rcases he a with ha | ha <;> rw [ha] <;> ring
    rw [finiteGibbsVariance_range_decomposition, hm, sub_self, zero_pow (by norm_num : 2 ≠ 0),
      hzero, sub_zero, sub_zero]

theorem canonicalHeatCapacity_range_bound (u : ℝ) (E : A → ℝ) :
    canonicalHeatCapacity E (Real.exp u) ≤
      (finiteSpectrumMax E - finiteSpectrumMin E) ^ 2 / (4 * Real.exp u ^ 2) := by
  rw [canonicalHeatCapacity_eq_variance]
  calc
    _ ≤ ((finiteSpectrumMax E - finiteSpectrumMin E) ^ 2 / 4) / Real.exp u ^ 2 :=
      div_le_div_of_nonneg_right (finiteGibbsVariance_range_bound _ E) (sq_nonneg _)
    _ = _ := by ring

/-- The charged-string geometry gives a strict bound on its finite Gibbs heat response. -/
theorem stringPotentialSpectrum_heat_bound {n : ℕ} (u ell tau : ℝ) (x : Fin (n + 1) → ℝ) :
    4 * Real.exp u ^ 2 * canonicalHeatCapacity (CPV.stringPotentialSpectrum ell tau x) (Real.exp u) <
      1 - 4 * Real.pi * CPV.stringBlackHoleTemperature ell tau / Real.exp ell := by
  have hv := CPV.stringPotentialSpectrum_variance_temperature_bound (Real.exp u)⁻¹ ell tau x
  have hheat : Real.exp u ^ 2 *
      canonicalHeatCapacity (CPV.stringPotentialSpectrum ell tau x) (Real.exp u) =
      finiteGibbsEnergyVariance (Real.exp u)⁻¹ (CPV.stringPotentialSpectrum ell tau x) := by
    rw [canonicalHeatCapacity_eq_variance]
    field_simp
  linarith only [hv, hheat]

#print axioms finiteGibbsVariance_range_equality_iff
#print axioms canonicalHeatCapacity_range_bound
#print axioms stringPotentialSpectrum_heat_bound

end GaloisForLFunctions.HTGeometry.Thermodynamics
