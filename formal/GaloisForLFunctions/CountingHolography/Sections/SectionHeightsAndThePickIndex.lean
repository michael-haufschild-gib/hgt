import GaloisForLFunctions.CountingHolography.Sections.SignedSplineSmallSections
import GaloisForLFunctions.CountingHolography.TheIntegerProbesAreNotIntegerValued
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheRealProbeKernelCountsTheZerosRightOfTheLine

/-!
# The negative index read from rational lattice sections

Subtract the dual logarithmic count from the original count and polarize on
pairs of integer atoms. Their mixed Tate limits give the Hermitian spline
matrix at every horizon. The supremum of its negative indices is also the
index measured by the integer Pick tests.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology ArithmeticScatteringHolography HTGeometry
open ArithmeticCastelnuovoSeveri Zeta23 ExclusionOfTheCriticalState

/-- The signed normalized height before taking the limit along a divisor ray. -/
def rayHeight {N : ℕ} (a : Fin N → ℤ) (m : ℕ) : ℝ :=
  ((splineCount (m • a) : ℝ) - dualCount (m • a)) / (m : ℝ)^2

/-- Polarization uses two single divisors and their sum, including when the atoms coincide. -/
def mixedRayHeight {N : ℕ} (i j : Fin N) (m : ℕ) : ℝ :=
  (rayHeight (Pi.single i 1 + Pi.single j 1) m -
    rayHeight (Pi.single i 1) m - rayHeight (Pi.single j 1) m) / 2

theorem mixedRayHeight_tendsto {N : ℕ} (i j : Fin N) :
    Tendsto (mixedRayHeight i j) atTop (𝓝 (atomGram N i j).re) := by
  have h (a : Fin N → ℤ) : Tendsto (rayHeight a) atTop (𝓝 (integerProbe N a)) :=
    splineCount_sub_dualCount_tateLimit a
  have hm := (((h (Pi.single i 1 + Pi.single j 1)).sub (h (Pi.single i 1))).sub
    (h (Pi.single j 1))).div_const 2
  rw [integerProbe_pair, integerProbe_single, integerProbe_single] at hm
  have he (x y z : ℝ) : (x + y + 2*z - x - y) / 2 = z := by ring
  simpa only [he] using hm

/-- The matrix specified solely by counts of sections on rational lattices. -/
def sectionMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ((limUnder atTop (mixedRayHeight i j) : ℝ) : ℂ)

theorem sectionMatrix_eq_atomGram (N : ℕ) : sectionMatrix N = atomGram N := by
  ext i j : 1
  change ((limUnder atTop (mixedRayHeight i j) : ℝ) : ℂ) = atomGram N i j
  rw [(mixedRayHeight_tendsto i j).limUnder_eq]
  exact Complex.ext rfl (atomGram_im N i j).symm

/-- The matrix at finite multiplicity, before taking a Tate limit. -/
def finiteSectionMatrix (N m : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (mixedRayHeight i j m : ℂ)

/-- Each strictly negative direction persists at sufficiently large finite
multiplicity. No sign or nonsingularity condition is imposed on the nullspace. -/
theorem eventually_le_finiteSectionIndex (N : ℕ) :
    ∀ᶠ m : ℕ in atTop, hermNegIndex (sectionMatrix N) ≤ hermNegIndex (finiteSectionMatrix N m) := by
  rw [sectionMatrix_eq_atomGram]
  apply HeckeKreinToeplitz.eventually_le_hermNegIndex (atomGram_isHermitian N)
  intro i j
  have he : ((atomGram N i j).re : ℂ) = atomGram N i j :=
    Complex.ext rfl (atomGram_im N i j).symm
  rw [← he]
  exact (Complex.continuous_ofReal.tendsto _).comp (mixedRayHeight_tendsto i j)

/-- Distinct right zeros, with infinite cardinality allowed, are exactly the
supremal negative index recovered by polarizing the two section counts. -/
theorem rightZeros_encard_eq_sectionIndex :
    (rightZeros zetaZeroConfig).encard = ⨆ N : ℕ, (hermNegIndex (sectionMatrix N) : ℕ∞) := by
  simp only [sectionMatrix_eq_atomGram]
  exact HeckeKreinToeplitz.negIndex_zetaKernel_eq_iSup_integerAtoms

/-- An integer Pick witness of index at least `r` exists exactly up to the
index of the polarized section heights. The two Gram matrices have different entries. -/
theorem integerPick_iff_le_sectionIndex (r : ℕ) :
    (∃ (N : ℕ) (p : Fin N → ℕ), (∀ i, 2 ≤ p i) ∧ r ≤ hermNegIndex (integerPickMatrix p)) ↔
      (r : ℕ∞) ≤ ⨆ N : ℕ, (hermNegIndex (sectionMatrix N) : ℕ∞) := by
  rw [← rightZeros_encard_eq_sectionIndex]
  exact integerProbeIndex_law r

/-- Outside RH one fixed horizon has at least two negative squares at every
sufficiently large finite multiplicity. Thus a cofinal ceiling of one at each
horizon would settle the sign, even without matching indices on null modes. -/
theorem rh_or_eventually_two_finiteSectionIndex :
    RiemannHypothesis ∨ ∃ N : ℕ, ∀ᶠ m : ℕ in atTop, 2 ≤ hermNegIndex (finiteSectionMatrix N m) := by
  by_cases h : RiemannHypothesis
  · exact Or.inl h
  right
  have htwo : (2 : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := two_le_rightZeros_encard_of_not_RH h
  have hN : ∃ N : ℕ, 2 ≤ hermNegIndex (sectionMatrix N) := by
    by_contra! hn
    have hle : (rightZeros zetaZeroConfig).encard ≤ 1 := by
      rw [rightZeros_encard_eq_sectionIndex]
      apply iSup_le
      intro N
      exact_mod_cast (show hermNegIndex (sectionMatrix N) ≤ 1 by have := hn N; omega)
    exact (by norm_num : ¬ (2 : ℕ∞) ≤ 1) (htwo.trans hle)
  obtain ⟨N, hN⟩ := hN
  exact ⟨N, (eventually_le_finiteSectionIndex N).mono fun _ hm => hN.trans hm⟩

#print axioms integerPick_iff_le_sectionIndex
#print axioms rh_or_eventually_two_finiteSectionIndex

end GaloisForLFunctions.CountingHolography.Sections
