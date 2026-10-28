import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFullPrimeMatrixHasRamanujanSpectralPoints
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanAdjunctionEnergiesAreDistinct
import GaloisForLFunctions.ArithmeticIncidencePositivity.ArchimedeanBumpBridgeAndSelfEnergyAsymptotic

/-!
# Every finite adjunction packet occurs in the full prime spectrum

Distinct arithmetic energies have positive separation on each fixed finite
conductor set. Their Ramanujan residuals therefore force distinct actual matrix
eigenvalues in arbitrarily small translated energy windows.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- Each fixed finite packet of positive conductors gives distinct actual spectral
points, with any prescribed accuracy, at every sufficiently large horizon. -/
theorem eventually_fullPrimeMatrix_finite_adjunction_packet
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ eig : S → ℝ, Function.Injective eig ∧
      (∀ m, eig m ∈ spectrum ℝ (fullPrimeMatrix N)) ∧
      ∀ m, |eig m - (Real.log N - ramanujanAdjunctionEnergy m)| < ε := by
  classical
  obtain ⟨s, hs, _, hsep⟩ := ArithmeticIncidencePositivity.exists_separation_finset
    (S.image ramanujanAdjunctionEnergy)
  let δ : ℝ := min ε (s / 4)
  have hδ : 0 < δ := lt_min hε (div_pos hs (by norm_num))
  have hδeps : δ ≤ ε := min_le_left _ _
  have hδs : δ ≤ s / 4 := min_le_right _ _
  have hevent : ∀ᶠ N : ℕ in atTop, ∀ m : S, ∃ i : PrimeHorizonIndex N,
      |(fullPrimeMatrix_isHermitian N).eigenvalues i -
        (Real.log N - ramanujanAdjunctionEnergy m)| < δ := by
    rw [Filter.eventually_all]
    intro m
    exact eventually_fullPrimeMatrix_eigenvalue_near (hS m m.property) hδ
  filter_upwards [hevent] with N hN
  choose i hi using hN
  let eig : S → ℝ := fun m => (fullPrimeMatrix_isHermitian N).eigenvalues (i m)
  refine ⟨eig, ?_, ?_, ?_⟩
  · intro a b hab
    by_contra hne
    have hEne : ramanujanAdjunctionEnergy a ≠ ramanujanAdjunctionEnergy b := by
      intro h
      exact hne (Subtype.ext (ramanujanAdjunctionEnergy_injectiveOn
        (hS a a.property) (hS b b.property) h))
    have habsep := hsep _ (mem_image.mpr ⟨a, a.property, rfl⟩)
      _ (mem_image.mpr ⟨b, b.property, rfl⟩) hEne
    have hclose : |ramanujanAdjunctionEnergy a - ramanujanAdjunctionEnergy b| < 2 * δ := by
      calc
        _ = |(eig a - (Real.log N - ramanujanAdjunctionEnergy a)) -
              (eig b - (Real.log N - ramanujanAdjunctionEnergy b))| := by
          rw [hab]
          congr 1
          ring
        _ ≤ |eig a - (Real.log N - ramanujanAdjunctionEnergy a)| +
              |eig b - (Real.log N - ramanujanAdjunctionEnergy b)| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            abs_add_le (eig a - (Real.log N - ramanujanAdjunctionEnergy a))
              (-(eig b - (Real.log N - ramanujanAdjunctionEnergy b)))
        _ < δ + δ := add_lt_add (hi a) (hi b)
        _ = 2 * δ := by ring
    linarith only [habsep, hclose, hδs, hs]
  · intro m
    exact (fullPrimeMatrix_isHermitian N).eigenvalues_mem_spectrum_real (i m)
  · intro m
    exact (hi m).trans_le hδeps

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

