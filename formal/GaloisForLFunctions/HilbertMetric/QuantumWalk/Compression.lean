import GaloisForLFunctions.HTGeometry.TwoProjectionQuantumWalk
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Chebyshev compression of reflection walks

The compressed-power identity in Bhakta–Bhattacharjya, Lemma 2.2,
extends from graph boundary matrices to any pair of orthogonal projections.
For `W=(2P-1)(2Q-1)` and `A=Q(2P-1)Q`, it reads
`Q W^n Q = T_n(A) Q`. The rightmost `Q` gives the identity of the
compressed space, including at time zero.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric.QuantumWalk
open Polynomial

private theorem compression_recurrence {R : Type*} [Ring R]
    (P Q : R) (hP : P * P = P) (hQ : Q * Q = Q) (n : ℕ) :
    Q * ((P + P - 1) * (Q + Q - 1)) ^ (n + 2) * Q =
      2 * (Q * (P + P - 1) * Q) *
        (Q * ((P + P - 1) * (Q + Q - 1)) ^ (n + 1) * Q) -
      Q * ((P + P - 1) * (Q + Q - 1)) ^ n * Q := by
  let W := (P + P - 1) * (Q + Q - 1)
  let V := (Q + Q - 1) * (P + P - 1)
  have hPa (x : R) : P * (P * x) = P * x := by rw [← mul_assoc, hP]
  have hQa (x : R) : Q * (Q * x) = Q * x := by rw [← mul_assoc, hQ]
  have hVW : V * W = 1 := by dsimp [V, W]; noncomm_ring [hP, hQ, hPa, hQa]
  have hs : Q * (W + V) = 2 * (Q * (P + P - 1) * Q) := by
    dsimp [W, V]
    noncomm_ring [hQ, hQa]
  have hVpow : V * W ^ (n + 1) = W ^ n := by
    rw [pow_succ', ← mul_assoc, hVW, one_mul]
  have h := congrArg (fun Z : R => Z * W ^ (n + 1) * Q) hs
  have hleft : Q * (W + V) * W ^ (n + 1) * Q =
      Q * W ^ (n + 2) * Q + Q * W ^ n * Q := by
    rw [mul_add, add_mul, add_mul]
    simp only [mul_assoc, hVpow, ← pow_succ']
  rw [hleft] at h
  have hright : 2 * (Q * (P + P - 1) * Q) * (Q * W ^ (n + 1) * Q) =
      2 * (Q * (P + P - 1) * Q) * W ^ (n + 1) * Q := by
    noncomm_ring [hQ, hQa]
  change Q * W ^ (n + 2) * Q = _
  rw [hright]
  exact eq_sub_of_add_eq h

/-- Algebraic compression identity; idempotence alone supplies the walk recurrence. -/
theorem compressed_reflection_pow {𝕜 R : Type*} [CommRing 𝕜] [Ring R] [Algebra 𝕜 R]
    (P Q : R) (hP : P * P = P) (hQ : Q * Q = Q) (n : ℕ) :
    Q * ((P + P - 1) * (Q + Q - 1)) ^ n * Q =
      aeval (Q * (P + P - 1) * Q) (Chebyshev.T 𝕜 (n : ℤ)) * Q := by
  induction n using Nat.twoStepInduction with
  | zero => simpa only [Nat.cast_zero, Chebyshev.T_zero, map_one, pow_zero, mul_one,
      one_mul] using hQ
  | one =>
    simp only [Nat.cast_one, Chebyshev.T_one, aeval_X, pow_one]
    noncomm_ring [hQ]
  | more n ih0 ih1 =>
    rw [compression_recurrence P Q hP hQ, ih1, ih0]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Chebyshev.T_add_two,
      map_sub, map_mul, map_ofNat, aeval_X]
    noncomm_ring

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Every pair of orthogonally complemented subspaces has an exact compressed walk calculus. -/
theorem starProjection_walk_pow (P Q : Submodule 𝕜 E)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection] (n : ℕ) :
    Q.starProjection * HTGeometry.twoProjectionQuantumWalk P.starProjection Q.starProjection ^ n *
        Q.starProjection =
      aeval (Q.starProjection * HTGeometry.projectionReflection P.starProjection * Q.starProjection)
        (Chebyshev.T 𝕜 (n : ℤ)) * Q.starProjection :=
  compressed_reflection_pow P.starProjection Q.starProjection
    P.isIdempotentElem_starProjection Q.isIdempotentElem_starProjection n

end GaloisForLFunctions.HilbertMetric.QuantumWalk

#print axioms GaloisForLFunctions.HilbertMetric.QuantumWalk.starProjection_walk_pow
