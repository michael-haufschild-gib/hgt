import GaloisForLFunctions.HTGeometry.ChargedStringThermalOccupation
import GaloisForLFunctions.HTGeometry.FiniteGibbsDifferentialBoundary

/-!
# Charged horizon potential in finite Gibbs variance geometry

The mean and variance in equations (68)--(74) of arXiv:2608.21406v1 are
instantiated with the corpus's normalized Gibbs weights and the charged string
potential sampled at positive exterior radii. Completing the square retains an
explicit strictly positive defect in the electrostatic variance bound.

The final exclusions concern the displayed finite variance budget. They do not
identify a finite Gibbs sample with an exact solution of the continuum cavity PDE.
-/

noncomputable section
open scoped BigOperators
open _root_.HTGeometry
namespace GaloisForLFunctions.HTGeometry.CPV

def stringPotentialSpectrum {n : ℕ} (ell tau : ℝ) (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i => stringBlackHolePotential ell tau (Real.exp (x i))

theorem stringPotentialSpectrum_mean_bounds {n : ℕ}
    (β ell tau : ℝ) (x : Fin (n + 1) → ℝ) :
    0 < finiteGibbsEnergyMean β (stringPotentialSpectrum ell tau x) ∧
      finiteGibbsEnergyMean β (stringPotentialSpectrum ell tau x) < coherentRadius tau := by
  let V := stringPotentialSpectrum ell tau x
  have hb (i : Fin (n + 1)) : 0 < V i ∧ V i < coherentRadius tau :=
    stringBlackHolePotential_exterior_bounds ell tau (x i)
  constructor
  · exact Finset.sum_pos (fun i _ => mul_pos (finiteGibbsStateWeight_pos β V i) (hb i).1)
      Finset.univ_nonempty
  · calc finiteGibbsEnergyMean β V < ∑ i, finiteGibbsStateWeight β V i * coherentRadius tau := by
           apply Finset.sum_lt_sum
           · intro i _
             exact (mul_lt_mul_of_pos_left (hb i).2 (finiteGibbsStateWeight_pos β V i)).le
           · exact ⟨0, Finset.mem_univ _, mul_lt_mul_of_pos_left (hb 0).2 (finiteGibbsStateWeight_pos β V 0)⟩
         _ = coherentRadius tau := by rw [← Finset.sum_mul, sum_finiteGibbsStateWeight_eq_one, one_mul]

theorem stringPotentialSpectrum_variance_decomposition {n : ℕ}
    (β ell tau : ℝ) (x : Fin (n + 1) → ℝ) :
    finiteGibbsEnergyVariance β (stringPotentialSpectrum ell tau x) =
      coherentRadius tau ^ 2 / 4 -
        (finiteGibbsEnergyMean β (stringPotentialSpectrum ell tau x) - coherentRadius tau / 2) ^ 2 -
        ∑ i, finiteGibbsStateWeight β (stringPotentialSpectrum ell tau x) i *
          stringPotentialSpectrum ell tau x i * (coherentRadius tau - stringPotentialSpectrum ell tau x i) := by
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  unfold finiteGibbsEnergyVariance finiteGibbsEnergyMean
  simp_rw [mul_assoc, ← sq]
  ring

theorem stringPotentialSpectrum_variance_bound {n : ℕ}
    (β ell tau : ℝ) (x : Fin (n + 1) → ℝ) :
    finiteGibbsEnergyVariance β (stringPotentialSpectrum ell tau x) < coherentRadius tau ^ 2 / 4 := by
  rw [stringPotentialSpectrum_variance_decomposition]
  have hs : 0 < ∑ i, finiteGibbsStateWeight β (stringPotentialSpectrum ell tau x) i *
      stringPotentialSpectrum ell tau x i * (coherentRadius tau - stringPotentialSpectrum ell tau x i) := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro i _
    have hb := stringBlackHolePotential_exterior_bounds ell tau (x i)
    exact mul_pos (mul_pos (finiteGibbsStateWeight_pos β _ i) hb.1) (sub_pos.mpr hb.2)
  nlinarith [sq_nonneg (finiteGibbsEnergyMean β (stringPotentialSpectrum ell tau x) - coherentRadius tau / 2)]

theorem stringPotentialSpectrum_variance_temperature_bound {n : ℕ}
    (β ell tau : ℝ) (x : Fin (n + 1) → ℝ) :
    finiteGibbsEnergyVariance β (stringPotentialSpectrum ell tau x) <
      (1 - 4 * Real.pi * stringBlackHoleTemperature ell tau / Real.exp ell) / 4 := by
  have h := stringPotentialSpectrum_variance_bound β ell tau x
  have ht := stringBlackHole_charge_temperature ell tau
  linarith

/-- The variance term of the cavity identity with an explicit positive energy cost. -/
def stringCavityVarianceBudget {n : ℕ}
    (e k β ell tau : ℝ) (x : Fin (n + 1) → ℝ) : ℝ :=
  e ^ 2 * finiteGibbsEnergyVariance β (stringPotentialSpectrum ell tau x) - Real.exp k

/-- The neutral variance budget excludes every positive real squared growth rate. -/
theorem stringCavity_neutral_no_growth {n : ℕ}
    (k β ell tau : ℝ) (x : Fin (n + 1) → ℝ) :
    ¬ ∃ g : ℝ, 0 < g ∧ g ^ 2 = stringCavityVarianceBudget 0 k β ell tau x := by
  rintro ⟨g, _, hg⟩
  simp only [stringCavityVarianceBudget, zero_pow (by omega : 2 ≠ 0), zero_mul, zero_sub] at hg
  nlinarith [sq_nonneg g, Real.exp_pos k]

/-- A realized barrier above the sharp electrostatic budget excludes growth at any charge. -/
theorem stringCavity_above_threshold_no_growth {n : ℕ}
    (e k β ell tau : ℝ) (x : Fin (n + 1) → ℝ) :
    ¬ ∃ g : ℝ, g ^ 2 =
      e ^ 2 * finiteGibbsEnergyVariance β (stringPotentialSpectrum ell tau x) -
        (e ^ 2 * coherentRadius tau ^ 2 / 4 + Real.exp k) := by
  rintro ⟨g, hg⟩
  have hv := mul_le_mul_of_nonneg_left
    (stringPotentialSpectrum_variance_bound β ell tau x).le (sq_nonneg e)
  nlinarith [sq_nonneg g, Real.exp_pos k]

end GaloisForLFunctions.HTGeometry.CPV
