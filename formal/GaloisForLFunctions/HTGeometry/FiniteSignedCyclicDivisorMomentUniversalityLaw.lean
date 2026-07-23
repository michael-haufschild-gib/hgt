import GaloisForLFunctions.HTGeometry.SignedMomentSeparation
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Finite signed cyclic-divisor moment universality

Let distinct complex nodes be permuted by multiplication with a primitive root of unity.  A
complex weight vector on those nodes is invariant under cyclic pushforward exactly when its first
full Vandermonde block of signed moments vanishes in every nontrivial character sector.

This is the signed-divisor companion of finite unweighted cyclic spectral Torelli: node positions
are fixed, arbitrary complex weights replace multiplicities, and the sharp finite threshold is the
number of distinct nodes.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- Pushing weights forward along a cyclic node permutation multiplies the `k`th signed moment by
the corresponding cyclic character. -/
theorem signedMoment_cyclicPushWeight
    {r : ℕ} (lam : Fin r → ℂ) (e : Fin r → ℂ)
    (σ : Equiv.Perm (Fin r)) {ζ : ℂ} (hσ : ∀ i, lam (σ i) = ζ * lam i) (k : ℕ) :
    signedMoment lam (fun i => e (σ.symm i)) k = ζ ^ k * signedMoment lam e k := by
  unfold signedMoment
  calc
    ∑ i, e (σ.symm i) * lam i ^ k =
        ∑ i, e (σ.symm (σ i)) * lam (σ i) ^ k :=
      (σ.bijective.sum_comp (fun i => e (σ.symm i) * lam i ^ k)).symm
    _ = ∑ i, e i * (ζ * lam i) ^ k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [σ.symm_apply_apply, hσ]
    _ = ζ ^ k * ∑ i, e i * lam i ^ k := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- **Finite signed cyclic-divisor moment law.**  A signed divisor on distinct nodes cyclically
permuted by a primitive root has invariant weights exactly when its first full Vandermonde block
vanishes in every nontrivial character sector. -/
theorem cyclicPushWeight_fixed_iff_firstSignedCharacterMoments_vanish
    {r d : ℕ} {lam : Fin r → ℂ} (hlam : Function.Injective lam)
    (e : Fin r → ℂ) (σ : Equiv.Perm (Fin r)) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ d) (hσ : ∀ i, lam (σ i) = ζ * lam i) :
    (fun i => e (σ.symm i)) = e ↔
      ∀ k : Fin r, ¬ d ∣ (k : ℕ) → signedMoment lam e (k : ℕ) = 0 := by
  constructor
  · intro hfixed k hdk
    have heq := congrArg (fun w => signedMoment lam w (k : ℕ)) hfixed
    change signedMoment lam (fun i => e (σ.symm i)) (k : ℕ) =
      signedMoment lam e (k : ℕ) at heq
    rw [signedMoment_cyclicPushWeight lam e σ hσ] at heq
    have hne : ζ ^ (k : ℕ) ≠ 1 := fun hone =>
      hdk ((hζ.pow_eq_one_iff_dvd (k : ℕ)).mp hone)
    have hzero : (ζ ^ (k : ℕ) - 1) * signedMoment lam e (k : ℕ) = 0 := by
      linear_combination heq
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)
  · intro h
    apply signedMoment_injective hlam
    funext k
    change signedMoment lam (fun i => e (σ.symm i)) (k : ℕ) =
      signedMoment lam e (k : ℕ)
    rw [signedMoment_cyclicPushWeight lam e σ hσ]
    by_cases hdk : d ∣ (k : ℕ)
    · rw [(hζ.pow_eq_one_iff_dvd (k : ℕ)).mpr hdk, one_mul]
    · rw [h k hdk, mul_zero]

end

end GaloisForLFunctions
