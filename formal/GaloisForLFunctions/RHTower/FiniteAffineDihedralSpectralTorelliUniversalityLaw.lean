import GaloisForLFunctions.HTGeometry.FiniteAffineCyclicMomentSymmetryUniversalityLaw
import GaloisForLFunctions.RHTower.FiniteSatakeRealityTorelliUniversalityLaw

/-!
# Finite affine-dihedral spectral Torelli universality

For a finite complex spectrum and a real center, the full affine dihedral generator pair is
visible in one sharp finite packet of centered power sums. Conjugation closure is exactly reality
of the first cardinality-many centered moments, while invariance under a primitive affine rotation
is exactly vanishing in its nontrivial character sectors through the same threshold.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions

noncomputable section

/-- Translation by a conjugation-fixed center intertwines conjugation closure of a finite spectrum
with conjugation closure of its centered translate. -/
private theorem conjugationClosed_centered_iff
    {n : ℕ} (f : Fin n → ℂ) (c : ℂ) (hc : (starRingEnd ℂ) c = c) :
    (univ.val.map f).map (starRingEnd ℂ) = univ.val.map f ↔
      (univ.val.map (fun i => f i - c)).map (starRingEnd ℂ) =
        univ.val.map (fun i => f i - c) := by
  constructor
  · intro h
    have hm := congrArg (Multiset.map (fun z : ℂ => z - c)) h
    simpa only [Multiset.map_map, Function.comp_apply, map_sub, hc] using hm
  · intro h
    have hm := congrArg (Multiset.map (fun z : ℂ => z + c)) h
    simpa only [Multiset.map_map, Function.comp_apply, map_sub, map_add, hc,
      sub_add_cancel] using hm

/-- **Finite affine-dihedral spectral Torelli universality law.** Let `c` be a real center and
`ζ` a primitive `d`th root. An `n`-point complex spectrum is simultaneously closed under
conjugation and fixed by `z ↦ c + ζ(z-c)` exactly when its centered power sums through order `n`
are real and all those in nontrivial cyclic-character sectors vanish. The common threshold `n`
is the sharp finite power-sum Torelli threshold; no labelled orbit decomposition is required. -/
theorem finiteAffineDihedralSpectrum_fixed_iff_firstCenteredDihedralMoments
    {n d : ℕ} (f : Fin n → ℂ) (c : ℂ) (hc : (starRingEnd ℂ) c = c)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d) :
    ((univ.val.map f).map (starRingEnd ℂ) = univ.val.map f ∧
        (univ.val.map f).map (fun z => c + ζ * (z - c)) = univ.val.map f) ↔
      (∀ k, k ≤ n →
        (starRingEnd ℂ) (∑ i, (f i - c) ^ k) = ∑ i, (f i - c) ^ k) ∧
      (∀ k, k ≤ n → ¬ d ∣ k → ∑ i, (f i - c) ^ k = 0) := by
  rw [conjugationClosed_centered_iff f c hc]
  rw [finiteSatake_conjugationClosed_iff_firstMoments_real
    (fun i => f i - c)]
  rw [finiteAffineCyclicSpectrum_fixed_iff_firstCenteredCharacterMoments_vanish
    f c hζ]
  simp only [Finset.sum_eq_multiset_sum Finset.univ]

end

end GaloisForLFunctions
