import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.CoxResidualClassification
import GaloisForLFunctions.HTGeometry.FiniteMomentDivisorReconstruction

/-!
# Gamma–Cox reconstruction of finite spectral multisets

A finite sum of squared moment discrepancies detects equality of complex
multisets, including multiplicities. The zeroth moment also compares cardinality,
so neither equal degrees nor a chosen matching of roots is assumed.
-/

open Filter Topology Finset
open scoped Classical
open GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Moment discrepancy through the sum of the two cardinalities. -/
def spectralMomentEnergy (M N : Multiset ℂ) : ℝ :=
  ∑ k ∈ range (M.card + N.card + 1),
    ‖(M.map (fun x => x ^ k)).sum - (N.map (fun x => x ^ k)).sum‖ ^ 2

/-- Finite moment energy detects the full multiset, not merely its support. -/
theorem spectralMomentEnergy_zero_iff (M N : Multiset ℂ) :
    spectralMomentEnergy M N = 0 ↔ M = N := by
  constructor
  · intro h
    have hm (k : ℕ) (hk : k ≤ M.card + N.card) :
        (M.map (fun x => x ^ k)).sum = (N.map (fun x => x ^ k)).sum := by
      have hz := (sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg
        ‖(M.map (fun x => x ^ k)).sum - (N.map (fun x => x ^ k)).sum‖)).mp h k
        (mem_range.mpr (Nat.lt_succ_iff.mpr hk))
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
    have hcard : M.card = N.card := by
      have h0 := hm 0 (Nat.zero_le _)
      have hc : (M.card : ℂ) = (N.card : ℂ) := by simpa using h0
      exact_mod_cast hc
    exact multiset_eq_of_powerSum_eq_le hcard (fun k hk => hm k (by omega))
  · rintro rfl
    simp [spectralMomentEnergy]

/-- Scalar detection distinguishes complete finite spectra with multiplicity. -/
theorem cox_spectral_equality (M N : Multiset ℂ) :
    Tendsto (fun K => detection K (spectralMomentEnergy M N)) atTop
      (𝓝 (if M = N then 1 else 0)) := by
  simpa only [spectralMomentEnergy_zero_iff] using
    tendsto_detection (spectralMomentEnergy M N)

/-- Simultaneous exact classification of finitely many pairs of spectra. -/
theorem cox_spectral_equality_family {ι : Type*} [Fintype ι]
    (M N : ι → Multiset ℂ) :
    Tendsto (fun K => (binaryLaw K (fun i => spectralMomentEnergy (M i) (N i))).real
      {b | b ≠ fun i => decide (M i = N i)}) atTop (𝓝 0) := by
  exact tendsto_classification_error (fun i => spectralMomentEnergy (M i) (N i))
    (fun i => M i = N i) fun i => by
    simp only [spectralMomentEnergy_zero_iff]

end
end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.spectralMomentEnergy_zero_iff
#print axioms GaloisForLFunctions.HTGeometry.cox_spectral_equality
#print axioms GaloisForLFunctions.HTGeometry.cox_spectral_equality_family
