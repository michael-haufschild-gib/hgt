import GaloisForLFunctions.HilbertMetric.SymmetricFockShadow

/-!
# Fabri--Picasso applications in symmetric Fock geometry

The one-mode Fock tower supplies a closed finite-sector exhaustion: normalized states exist at
every particle number while lowering and adjoint-raising charge escape every finite bound.
-/

noncomputable section

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

/-- Canonical unit vector in the one-mode degree-`n` Fock sector. -/
def oneModeFockUnit (n : ℕ) : EuclideanSpace ℝ (Sym Unit n) :=
  EuclideanSpace.single (Sym.replicate n ()) 1

@[simp]
theorem norm_oneModeFockUnit (n : ℕ) : ‖oneModeFockUnit n‖ = 1 := by
  simp [oneModeFockUnit]

/-- The squared lowering charge of the canonical one-mode state is exactly `n+1`. -/
theorem fabriPicasso_oneModeLoweringCharge (n : ℕ) :
    ∑ i : Unit,
        ‖(symmetricFockAnnihilation n i) (oneModeFockUnit (n + 1))‖ ^ (2 : ℕ) =
      (n : ℝ) + 1 := by
  rw [symmetricFockAnnihilation_energy]
  simp

/-- Finite-sector lowering charges escape every real bound with particle number. -/
theorem fabriPicasso_oneModeLoweringCharge_unbounded :
    ∀ B : ℝ, ∃ n : ℕ,
      B < ∑ i : Unit,
        ‖(symmetricFockAnnihilation n i) (oneModeFockUnit (n + 1))‖ ^ (2 : ℕ) := by
  intro B
  obtain ⟨n, hn⟩ := exists_nat_gt B
  refine ⟨n, ?_⟩
  rw [fabriPicasso_oneModeLoweringCharge]
  exact hn.trans (by norm_num)

/-- The squared adjoint-raising charge of the canonical one-mode state is also `n+1`. -/
theorem fabriPicasso_oneModeRaisingCharge (n : ℕ) :
    ∑ i : Unit,
        ‖(symmetricFockAnnihilation n i).adjoint (oneModeFockUnit n)‖ ^ (2 : ℕ) =
      (n : ℝ) + 1 := by
  rw [symmetricFockAnnihilation_adjoint_energy]
  simp

/-- Finite-sector raising charges escape every real bound with particle number. -/
theorem fabriPicasso_oneModeRaisingCharge_unbounded :
    ∀ B : ℝ, ∃ n : ℕ,
      B < ∑ i : Unit,
        ‖(symmetricFockAnnihilation n i).adjoint (oneModeFockUnit n)‖ ^ (2 : ℕ) := by
  intro B
  obtain ⟨n, hn⟩ := exists_nat_gt B
  refine ⟨n, ?_⟩
  rw [fabriPicasso_oneModeRaisingCharge]
  exact hn.trans (by norm_num)

end GaloisForLFunctions.HilbertMetric
