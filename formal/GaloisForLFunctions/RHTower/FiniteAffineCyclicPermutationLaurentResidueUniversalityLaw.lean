import GaloisForLFunctions.HTGeometry.FiniteShiftedLaurentCyclicDivisorMomentUniversalityLaw
import GaloisForLFunctions.RHTower.FiniteAffineCyclicMomentResidueCharacterUniversalityLaw

/-!
# Finite affine cyclic permutation Laurent-residue universality law

An explicit primitive cyclic permutation of distinct, center-free affine spectral nodes controls
two levels of data simultaneously.  After forgetting labels it forces the sharp centered moments,
characteristic-product covariance, cyclic character, and logarithmic residue.  With arbitrary
labels retained, the same permutation detects invariant complex weights in every consecutive
Laurent window, including windows of negative orders.
-/

open scoped BigOperators
open Complex Filter Topology Finset

namespace GaloisForLFunctions

noncomputable section

/-- **Finite affine cyclic permutation Laurent-residue universality law.**  A primitive affine
cyclic permutation of an injective center-free spectrum produces the full unlabeled
moment/product/order/residue certificate and, uniformly for every weight vector and integer
window, the labeled shifted-Laurent character certificate. -/
theorem finiteAffineCyclicPermutationLaurentResidueUniversality
    {n d : ℕ} (f : Fin n → ℂ) (hf : Function.Injective f) (c : ℂ)
    (σ : Equiv.Perm (Fin n)) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d) (hd : d ≠ 0)
    (hcenter : ∀ i, f i ≠ c)
    (hσ : ∀ i, f (σ i) = c + ζ * (f i - c)) :
    (Finset.univ.val.map f).map (fun z => c + ζ * (z - c)) =
        Finset.univ.val.map f ∧
      (∀ k, k ≤ n → ¬ d ∣ k → ∑ i, (f i - c) ^ k = 0) ∧
      (∀ z, finiteCenteredSpectralProduct f c (ζ * z) =
        ζ ^ n * finiteCenteredSpectralProduct f c z) ∧
      Nat.ModEq d (Finset.univ.filter fun i => f i = c).card n ∧
      ζ ^ ((Finset.univ.filter fun i => f i = c).card : ℤ) = ζ ^ n ∧
      Tendsto
        (fun z => z * logDeriv (finiteCenteredSpectralProduct f c) z)
        (𝓝[≠] 0)
        (𝓝 (((Finset.univ.filter fun i => f i = c).card : ℕ) : ℂ)) ∧
      ∀ (e : Fin n → ℂ) (b : ℤ),
        (fun i => e (σ.symm i)) = e ↔
          ∀ k : Fin n, ¬ (d : ℤ) ∣ b + (k : ℕ) →
            signedLaurentMoment (fun i => f i - c) e (b + (k : ℕ)) = 0 := by
  have hσmap : Multiset.map (⇑σ) Finset.univ.val = Finset.univ.val := by
    have h := congrArg Finset.val (Finset.map_univ_equiv σ)
    simpa only [Finset.map_val, Equiv.coe_toEmbedding] using h
  have hfixed :
      (Finset.univ.val.map f).map (fun z => c + ζ * (z - c)) =
        Finset.univ.val.map f := by
    rw [Multiset.map_map]
    have hfun : (fun z => c + ζ * (z - c)) ∘ f = f ∘ σ := by
      funext i
      exact (hσ i).symm
    rw [hfun, ← Multiset.map_map, hσmap]
  have hmoments :
      ∀ k, k ≤ n → ¬ d ∣ k → ∑ i, (f i - c) ^ k = 0 :=
    (finiteAffineCyclicSpectrum_fixed_iff_firstCenteredCharacterMoments_vanish
      f c hζ).mp hfixed
  have hresidue :=
    (finiteAffineCyclicMomentResidueCharacterUniversality f c hζ hd).mp hmoments
  refine ⟨hfixed, hmoments, hresidue.2.1, hresidue.2.2.1,
    hresidue.2.2.2.1, hresidue.2.2.2.2, ?_⟩
  have hlam : Function.Injective (fun i => f i - c) := by
    intro i j hij
    apply hf
    have := congrArg (fun z : ℂ => z + c) hij
    simpa only [sub_add_cancel] using this
  have hlam0 : ∀ i, f i - c ≠ 0 := fun i => sub_ne_zero.mpr (hcenter i)
  have hσlam : ∀ i, f (σ i) - c = ζ * (f i - c) := by
    intro i
    rw [hσ i]
    ring
  intro e b
  exact cyclicPushWeight_fixed_iff_shiftedSignedLaurentCharacterMoments_vanish
    hlam hlam0 e σ hζ hσlam b

end

end GaloisForLFunctions
