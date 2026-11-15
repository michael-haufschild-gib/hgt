import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovFiniteProfiles
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Uniform Fourier bounds for normalized covering weights

The fixed cutoff profiles are Schwartz functions in Euclidean coordinates,
so their inverse Fourier transforms are integrable. Summing their finitely
many integral norms gives a bound for every covering weight in its own
normalized frame, independently of scale, direction, and center index.
-/

open scoped BigOperators FourierTransform
open MeasureTheory

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- A fixed profile in the Euclidean coordinates used by the Fourier transform. -/
def cutoffProfileEuclideanSchwartz (r k q : ℕ) (N : ℤ) :
    SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r k)) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : AffineAxisIndex r k => ℝ))
      (cutoffProfileSchwartz r k q N)

/-- The inverse Fourier kernel of a fixed normalized profile. -/
def inverseCutoffProfile (r k q : ℕ) (N : ℤ) :
    SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r k)) ℂ :=
  𝓕⁻ (cutoffProfileEuclideanSchwartz r k q N)

theorem integrable_inverseCutoffProfile (r k q : ℕ) (N : ℤ) :
    Integrable (inverseCutoffProfile r k q N) := (inverseCutoffProfile r k q N).integrable

/-- The integral norm of the inverse Fourier kernel of a fixed profile. -/
def inverseCutoffProfileMass (r k q : ℕ) (N : ℤ) : ℝ :=
  ∫ x, ‖inverseCutoffProfile r k q N x‖

theorem inverseCutoffProfileMass_nonneg (r k q : ℕ) (N : ℤ) :
    0 ≤ inverseCutoffProfileMass r k q N := integral_nonneg (fun _ => norm_nonneg _)

/-- A single positive bound controls every inverse kernel in the finite profile family. -/
theorem exists_cutoffProfileMass_bound (r k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N ∈ cutoffProfileIndices q, inverseCutoffProfileMass r k q N ≤ C := by
  refine ⟨1 + ∑ N ∈ cutoffProfileIndices q, inverseCutoffProfileMass r k q N, ?_, ?_⟩
  · have hs : 0 ≤ ∑ N ∈ cutoffProfileIndices q, inverseCutoffProfileMass r k q N :=
      Finset.sum_nonneg (fun N _ => inverseCutoffProfileMass_nonneg r k q N)
    linarith only [hs]
  · intro N hN
    have h := Finset.single_le_sum
      (fun M _ => inverseCutoffProfileMass_nonneg r k q M) hN
    linarith only [h]

/-- A physical ordered cutoff pulled back to its own Euclidean frame coordinates. -/
def normalizedCoveringWeight (r k q : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) (i : ℤ)
    (x : EuclideanSpace ℝ (AffineAxisIndex r k)) : ℂ :=
  coveringWeight r k q ε δ i
    (momentFrame r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ)) (WithLp.ofLp x))

/-- Every normalized ordered cutoff is one of the fixed Euclidean Schwartz profiles. -/
theorem exists_normalizedCoveringWeight_profile (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (i : ℤ) (hi : i ∈ dimensionCoveringGrid r q ε) :
    ∃ N ∈ cutoffProfileIndices q,
      normalizedCoveringWeight r (k + 1) q ε δ i =
        (cutoffProfileEuclideanSchwartz r (k + 1) q N :
          EuclideanSpace ℝ (AffineAxisIndex r (k + 1)) → ℂ) := by
  obtain ⟨N, hN, he⟩ := exists_cutoffProfile_of_coveringWeight r k q ε hε δ i hi
  refine ⟨N, hN, ?_⟩
  funext x
  change (coveringWeight r (k + 1) q ε δ i
      (momentFrame r (k + 1) ε δ (ε * (i : ℝ) / (q + 1 : ℝ)) (WithLp.ofLp x)) : ℂ) =
    (cutoffProfile r (k + 1) q N (WithLp.ofLp x) : ℂ)
  rw [he]

/-- The inverse Fourier transforms of all normalized covering weights have a uniform integral norm. -/
theorem exists_uniform_normalizedCoveringWeight_fourierL1 (r k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), ε ≠ 0 → ∀ (δ : Fin (r + 1) → ℝ) (i : ℤ),
      i ∈ dimensionCoveringGrid r q ε →
      Integrable (𝓕⁻ (normalizedCoveringWeight r (k + 1) q ε δ i)) ∧
        (∫ x, ‖𝓕⁻ (normalizedCoveringWeight r (k + 1) q ε δ i) x‖) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_cutoffProfileMass_bound r (k + 1) q
  refine ⟨C, hC, ?_⟩
  intro ε hε δ i hi
  obtain ⟨N, hN, he⟩ := exists_normalizedCoveringWeight_profile r k q ε hε δ i hi
  have hF : 𝓕⁻ (normalizedCoveringWeight r (k + 1) q ε δ i) =
      (inverseCutoffProfile r (k + 1) q N :
        EuclideanSpace ℝ (AffineAxisIndex r (k + 1)) → ℂ) := by
    rw [he, ← SchwartzMap.fourierInv_coe]
    rfl
  rw [hF]
  exact ⟨integrable_inverseCutoffProfile r (k + 1) q N, hbound N hN⟩

#print axioms cutoffProfileEuclideanSchwartz
#print axioms integrable_inverseCutoffProfile
#print axioms inverseCutoffProfileMass_nonneg
#print axioms exists_cutoffProfileMass_bound
#print axioms exists_normalizedCoveringWeight_profile
#print axioms exists_uniform_normalizedCoveringWeight_fourierL1

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
