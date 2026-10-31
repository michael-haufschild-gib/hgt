import GaloisForLFunctions.HeckeKreinToeplitz.Index.HermitianFiniteSums
import GaloisForLFunctions.HeckeKreinToeplitz.KernelsOnGroupsAndTheirNegativeIndex

/-!
# Positive group coefficients from invariant forms

An invariant nonnegative Hermitian form produces a positive-definite group kernel on each orbit, without completing the representation space.
-/

open Complex Module Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

/-- An invariant form reads every orbit pairing from a single group coefficient. -/
theorem invariantHermitianForm_orbit_pairing (ρ : G →* End ℂ V) (H : V → V → ℂ)
    (hinv : ∀ g x y, H (ρ g x) (ρ g y) = H x y) (v : V) (g h : G) :
    H (ρ h v) (ρ g v) = H (ρ (g⁻¹ * h) v) v := by
  have he := hinv g⁻¹ (ρ h v) (ρ g v)
  have hleft : ρ g⁻¹ (ρ h v) = ρ (g⁻¹ * h) v := by
    rw [map_mul, Module.End.mul_apply]
  have hright : ρ g⁻¹ (ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hleft, hright] at he
  exact he.symm

/-- A nonnegative invariant Hermitian form gives a positive-definite group coefficient. -/
theorem isPosDefKernel_of_invariantHermitianForm (ρ : G →* End ℂ V)
    {H : V → V → ℂ} (hH : IsHermitianForm H) (hpos : ∀ x, 0 ≤ (H x x).re)
    (hinv : ∀ g x y, H (ρ g x) (ρ g y) = H x y) (v : V) :
    IsPosDefKernel (fun g => H (ρ g v) v) := by
  have hpair := invariantHermitianForm_orbit_pairing ρ H hinv v
  refine ⟨?_, ?_⟩
  · intro g
    calc
      H (ρ g⁻¹ v) v = H v (ρ g v) := by
        simpa only [map_one, Module.End.one_apply, mul_one] using (hpair g 1).symm
      _ = (starRingEnd ℂ) (H (ρ g v) v) := hH.symm (ρ g v) v
  · intro n x c
    have hp := hpos (∑ i, c i • ρ (x i) v)
    rw [hermitianForm_fin_synthesis hH] at hp
    have he : (∑ i : Fin n, ∑ j : Fin n, c i * star (c j) * H (ρ (x i) v) (ρ (x j) v)) =
        ∑ i : Fin n, ∑ j : Fin n, conj (c i) * H (ρ ((x i)⁻¹ * x j) v) v * c j := by
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      rw [hpair, Complex.star_def]
      ring
    rw [he] at hp
    rw [hermQuad_gram]
    exact hp

#print axioms isPosDefKernel_of_invariantHermitianForm
end GaloisForLFunctions.HeckeKreinToeplitz
