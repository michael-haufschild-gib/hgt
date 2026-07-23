import GaloisForLFunctions.HTGeometry.FiniteMultisetTransformationMomentUniversalityLaw
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Finite affine cyclic moment-symmetry universality

For an `n`-point complex multiset and a primitive `d`th root `ζ`, invariance under scalar
rotation by `ζ` is equivalent to vanishing of precisely the first `n` power sums lying outside
the trivial cyclic-character sector.  Translating the spectrum gives the corresponding sharp
criterion for rotation about an arbitrary center.

The order-two case recovers the odd-moment reflection criterion, while the statement and its
finite threshold are uniform in the cyclic order.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions

noncomputable section

/-- **Finite cyclic character criterion.**  An `n`-point spectrum is fixed by multiplication by
a primitive `d`th root exactly when all of its nontrivial-character power sums through order `n`
vanish. -/
theorem finiteCyclicScaling_fixed_iff_firstCharacterMoments_vanish
    {n d : ℕ} (f : Fin n → ℂ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d) :
    (univ.val.map f).map (fun z => ζ * z) = univ.val.map f ↔
      ∀ k, k ≤ n → ¬ d ∣ k → ∑ i, f i ^ k = 0 := by
  rw [finiteMultiset_map_fixed_iff_firstPowerSums_fixed]
  constructor
  · intro h k hk hdk
    have heq := h k hk
    rw [← Finset.sum_eq_multiset_sum Finset.univ,
      ← Finset.sum_eq_multiset_sum Finset.univ] at heq
    simp_rw [mul_pow] at heq
    rw [← Finset.mul_sum] at heq
    have hne : ζ ^ k ≠ 1 := fun hone =>
      hdk ((hζ.pow_eq_one_iff_dvd k).mp hone)
    have hzero : (ζ ^ k - 1) * ∑ i, f i ^ k = 0 := by
      linear_combination heq
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)
  · intro h k hk
    rw [← Finset.sum_eq_multiset_sum Finset.univ,
      ← Finset.sum_eq_multiset_sum Finset.univ]
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    by_cases hdk : d ∣ k
    · rw [(hζ.pow_eq_one_iff_dvd k).mpr hdk, one_mul]
    · rw [h k hk hdk, mul_zero]

/-- **Finite affine cyclic moment-symmetry law.**  An `n`-point spectrum is invariant under
rotation `z ↦ c + ζ(z-c)` about an arbitrary center exactly when its centered power sums in
all nontrivial cyclic-character sectors vanish through the sharp Torelli threshold `n`. -/
theorem finiteAffineCyclicSpectrum_fixed_iff_firstCenteredCharacterMoments_vanish
    {n d : ℕ} (f : Fin n → ℂ) (c : ℂ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d) :
    (univ.val.map f).map (fun z => c + ζ * (z - c)) = univ.val.map f ↔
      ∀ k, k ≤ n → ¬ d ∣ k → ∑ i, (f i - c) ^ k = 0 := by
  rw [← finiteCyclicScaling_fixed_iff_firstCharacterMoments_vanish
    (fun i => f i - c) hζ]
  constructor
  · intro hfixed
    have hm := congrArg (Multiset.map (fun z : ℂ => z - c)) hfixed
    simp only [Multiset.map_map, Function.comp_apply] at hm ⊢
    convert hm using 1
    apply Multiset.map_congr rfl
    intro i hi
    ring
  · intro hfixed
    have hm := congrArg (Multiset.map (fun z : ℂ => c + z)) hfixed
    simp only [Multiset.map_map, Function.comp_apply] at hm ⊢
    convert hm using 1
    apply Multiset.map_congr rfl
    intro i hi
    ring

end

end GaloisForLFunctions
