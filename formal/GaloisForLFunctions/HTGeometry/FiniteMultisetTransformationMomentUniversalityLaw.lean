import GaloisForLFunctions.HTGeometry.PowerSumTorelli

/-!
# Finite multiset transformation--moment universality

Sharp finite power-sum Torelli applies uniformly to every point transformation.  An `n`-point
complex multiset is fixed by an arbitrary map `τ : ℂ → ℂ` exactly when its first `n` power sums
are fixed after applying `τ`.  Conjugation self-duality, reciprocal self-duality, and weighted
function-field duality are all instances of the same finite law.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions

noncomputable section

/-- **Universal finite transformation criterion.**  For any transformation of the complex plane,
an enumerated `n`-point multiset is invariant under that transformation exactly when the power
sums through order `n` are invariant. -/
theorem finiteMultiset_map_fixed_iff_firstPowerSums_fixed
    {n : ℕ} (f : Fin n → ℂ) (τ : ℂ → ℂ) :
    (univ.val.map f).map τ = univ.val.map f ↔
      ∀ k ≤ n,
        (univ.val.map (fun i => (τ (f i)) ^ k)).sum =
          (univ.val.map (fun i => f i ^ k)).sum := by
  constructor
  · intro hfixed k _
    have h := congrArg
      (fun S : Multiset ℂ => (S.map (fun z => z ^ k)).sum) hfixed
    simpa only [Multiset.map_map, Function.comp_apply] using h
  · intro hmoments
    have h := powerSum_torelli_finite (fun i => τ (f i)) f hmoments
    rw [Multiset.map_map]
    simpa only [Function.comp_apply] using h

/-- Reciprocal self-duality of a finite spectrum is exactly invariance of its first `n` power sums
under reciprocal transformation. -/
theorem finiteReciprocal_spectralClosure_iff_firstPowerSums
    {n : ℕ} (f : Fin n → ℂ) :
    (univ.val.map f).map (fun z => z⁻¹) = univ.val.map f ↔
      ∀ k ≤ n,
        (univ.val.map (fun i => (f i)⁻¹ ^ k)).sum =
          (univ.val.map (fun i => f i ^ k)).sum :=
  finiteMultiset_map_fixed_iff_firstPowerSums_fixed f (fun z => z⁻¹)

/-- Weighted reciprocal closure `z ↦ q / z` is exactly invariance of the first `n` secular
moments under that transformation. -/
theorem finiteWeightedReciprocal_spectralClosure_iff_firstPowerSums
    {n : ℕ} (q : ℂ) (f : Fin n → ℂ) :
    (univ.val.map f).map (fun z => q / z) = univ.val.map f ↔
      ∀ k ≤ n,
        (univ.val.map (fun i => (q / f i) ^ k)).sum =
          (univ.val.map (fun i => f i ^ k)).sum :=
  finiteMultiset_map_fixed_iff_firstPowerSums_fixed f (fun z => q / z)

end

end GaloisForLFunctions
