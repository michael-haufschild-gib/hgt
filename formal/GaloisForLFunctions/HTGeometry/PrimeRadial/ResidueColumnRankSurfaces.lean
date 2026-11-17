import GaloisForLFunctions.HTGeometry.PrimeRadialIntrinsicTrdegSurfaceUniversalityLaw
import GaloisForLFunctions.ArithmeticEffectivityTheory.Semigroups.GapDensity

/-!
# Kunz coordinates classify prime-radial rank defects

The finite residue-column inequalities characterize exactly which column
spectra occur as prime-radial fusion algebras. Past twice the genus, their
finite-jet transcendence degrees have the exact constant deficit prescribed
by the missing exponents.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open ArithmeticEffectivityTheory.ResidueColumns

/-- The positive-order census loses exactly the genus once the conductor is passed. -/
theorem columnSubmonoid_positive_count (m : ℕ) (k : ℕ → ℕ)
    (h0 : k 0 = 0) (hK : Kunz m k) {N : ℕ} (hN : 2 * genus m k ≤ N) :
    primeRadialAddSubmonoidCount (columnSubmonoid m k h0 hK) N = N - genus m k := by
  classical
  have hp := prefix_count_of_two_genus_le m k hK (N := N + 1) (by omega)
  have hc : (allowedBelow m k (N + 1)).card =
      primeRadialAddSubmonoidCount (columnSubmonoid m k h0 hK) N + 1 := by
    unfold primeRadialAddSubmonoidCount
    change (allowedBelow m k (N + 1)).card =
      ((Finset.range N).filter (fun j => j + 1 ∈ carrier m k)).card + 1
    simp only [allowedBelow, Finset.card_eq_sum_ones, Finset.sum_filter,
      Finset.sum_range_succ', (zero_mem_iff m k).mpr h0, if_true]
  omega

/-- A finite criterion realizes the full column spectrum and its eventual trdeg deficit. -/
theorem exists_primeRadial_column_genus_surface_iff (m : ℕ) (k : ℕ → ℕ) :
    (∃ A : NonUnitalSubalgebra ℂ PrimeRadialProfile,
      PrimeRadialCarrierFusionClosed A.toSubmodule ∧
      (primeRadialOrderSubmonoid A : Set ℕ) = carrier m k ∧
      ∀ N : ℕ, 2 * genus m k ≤ N → ∀ r : ℕ,
        Algebra.trdeg (primeRadialTailDifferentialField A.toSubmodule N)
            (primeRadialFiniteJetField A.toSubmodule N r) =
          (((r + 1) * (N - genus m k) : ℕ) : Cardinal)) ↔
      k 0 = 0 ∧ Kunz m k := by
  constructor
  · rintro ⟨A, _, hA, _⟩
    exact (exists_submonoid_iff m k).mp ⟨primeRadialOrderSubmonoid A, hA⟩
  · rintro ⟨h0, hK⟩
    obtain ⟨A, hfusion, horder, _, htrdeg⟩ :=
      primeRadialIntrinsicJetTrdegSurface_realizes_addSubmonoid (columnSubmonoid m k h0 hK)
    refine ⟨A, hfusion, ?_, ?_⟩
    · rw [horder]
      rfl
    · intro N hN r
      rw [htrdeg N r, columnSubmonoid_positive_count m k h0 hK hN]

#print axioms columnSubmonoid_positive_count
#print axioms exists_primeRadial_column_genus_surface_iff

end GaloisForLFunctions.HTGeometry
