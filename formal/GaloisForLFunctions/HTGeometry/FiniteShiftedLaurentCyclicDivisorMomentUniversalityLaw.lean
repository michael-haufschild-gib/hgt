import GaloisForLFunctions.HTGeometry.FiniteSignedCyclicDivisorMomentUniversalityLaw

/-!
# Finite shifted-Laurent cyclic-divisor moment universality

For distinct nonzero complex nodes, every consecutive block of as many Laurent moments as nodes
determines an arbitrary complex weight vector.  If multiplication by a primitive root of unity
permutes the nodes, the pushforward fixes the weights exactly when the moments belonging to
nontrivial characters vanish in any such shifted block.

This strengthens the initial natural-moment criterion to arbitrary integer windows, including
windows containing negative orders.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- Signed Laurent moment of integer order `q` of a weight vector `e` against nodes `lam`. -/
def signedLaurentMoment {r : ℕ} (lam : Fin r → ℂ) (e : Fin r → ℂ) (q : ℤ) : ℂ :=
  ∑ i, e i * lam i ^ q

/-- A shifted Laurent moment is an ordinary moment of the diagonally rescaled weight vector. -/
lemma signedLaurentMoment_eq_shiftedSignedMoment
    {r : ℕ} (lam : Fin r → ℂ) (hlam0 : ∀ i, lam i ≠ 0)
    (e : Fin r → ℂ) (b : ℤ) (k : ℕ) :
    signedLaurentMoment lam e (b + (k : ℤ)) =
      signedMoment lam (fun i => e i * lam i ^ b) k := by
  unfold signedLaurentMoment signedMoment
  apply Finset.sum_congr rfl
  intro i hi
  rw [zpow_add₀ (hlam0 i), zpow_natCast]
  ring

/-- **Shifted Laurent Vandermonde separation.** Every consecutive length-`r` integer-moment
window separates arbitrary complex weights on `r` distinct nonzero nodes. -/
theorem signedLaurentMoment_shiftedBlock_injective
    {r : ℕ} {lam : Fin r → ℂ} (hlam : Function.Injective lam)
    (hlam0 : ∀ i, lam i ≠ 0) (b : ℤ) :
    Function.Injective
      (fun e : Fin r → ℂ =>
        fun k : Fin r => signedLaurentMoment lam e (b + (k : ℕ))) := by
  intro e e' h
  have hscaled :
      (fun i => e i * lam i ^ b) = (fun i => e' i * lam i ^ b) := by
    apply signedMoment_injective hlam
    funext k
    change signedMoment lam (fun i => e i * lam i ^ b) (k : ℕ) =
      signedMoment lam (fun i => e' i * lam i ^ b) (k : ℕ)
    rw [← signedLaurentMoment_eq_shiftedSignedMoment lam hlam0 e b (k : ℕ)]
    rw [← signedLaurentMoment_eq_shiftedSignedMoment lam hlam0 e' b (k : ℕ)]
    exact congrFun h k
  funext i
  exact mul_right_cancel₀ (zpow_ne_zero b (hlam0 i)) (congrFun hscaled i)

/-- Cyclic pushforward multiplies every integer Laurent moment by its cyclic character. -/
theorem signedLaurentMoment_cyclicPushWeight
    {r : ℕ} (lam : Fin r → ℂ) (e : Fin r → ℂ)
    (σ : Equiv.Perm (Fin r)) {ζ : ℂ}
    (hσ : ∀ i, lam (σ i) = ζ * lam i) (q : ℤ) :
    signedLaurentMoment lam (fun i => e (σ.symm i)) q =
      ζ ^ q * signedLaurentMoment lam e q := by
  unfold signedLaurentMoment
  calc
    ∑ i, e (σ.symm i) * lam i ^ q =
        ∑ i, e (σ.symm (σ i)) * lam (σ i) ^ q :=
      (σ.bijective.sum_comp (fun i => e (σ.symm i) * lam i ^ q)).symm
    _ = ∑ i, e i * (ζ * lam i) ^ q := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [σ.symm_apply_apply, hσ]
    _ = ζ ^ q * ∑ i, e i * lam i ^ q := by
      simp_rw [mul_zpow]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- **Finite shifted-Laurent cyclic-divisor moment law.** On distinct nonzero nodes cyclically
permuted by a primitive root, invariant weights are detected by the nontrivial-character moments
in every consecutive length-`r` integer window. -/
theorem cyclicPushWeight_fixed_iff_shiftedSignedLaurentCharacterMoments_vanish
    {r d : ℕ} {lam : Fin r → ℂ} (hlam : Function.Injective lam)
    (hlam0 : ∀ i, lam i ≠ 0) (e : Fin r → ℂ)
    (σ : Equiv.Perm (Fin r)) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ d) (hσ : ∀ i, lam (σ i) = ζ * lam i)
    (b : ℤ) :
    (fun i => e (σ.symm i)) = e ↔
      ∀ k : Fin r, ¬ (d : ℤ) ∣ b + (k : ℕ) →
        signedLaurentMoment lam e (b + (k : ℕ)) = 0 := by
  constructor
  · intro hfixed k hdk
    have heq := congrArg
      (fun w => signedLaurentMoment lam w (b + (k : ℕ))) hfixed
    change signedLaurentMoment lam (fun i => e (σ.symm i)) (b + (k : ℕ)) =
      signedLaurentMoment lam e (b + (k : ℕ)) at heq
    rw [signedLaurentMoment_cyclicPushWeight lam e σ hσ] at heq
    have hne : ζ ^ (b + (k : ℕ)) ≠ 1 := fun hone =>
      hdk ((hζ.zpow_eq_one_iff_dvd (b + (k : ℕ))).mp hone)
    have hzero :
        (ζ ^ (b + (k : ℕ)) - 1) *
          signedLaurentMoment lam e (b + (k : ℕ)) = 0 := by
      linear_combination heq
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)
  · intro h
    apply signedLaurentMoment_shiftedBlock_injective hlam hlam0 b
    funext k
    change signedLaurentMoment lam (fun i => e (σ.symm i)) (b + (k : ℕ)) =
      signedLaurentMoment lam e (b + (k : ℕ))
    rw [signedLaurentMoment_cyclicPushWeight lam e σ hσ]
    by_cases hdk : (d : ℤ) ∣ b + (k : ℕ)
    · rw [(hζ.zpow_eq_one_iff_dvd (b + (k : ℕ))).mpr hdk, one_mul]
    · rw [h k hdk, mul_zero]

end

end GaloisForLFunctions
