import GaloisForLFunctions.RHTower.Sieve.FareyCoprime
import GaloisForLFunctions.RHTower.Sieve.CoefficientExpansion

/-!
# The large sieve as a bound on exponential sums

The statements of this folder are inner products against exponential rows.  Their classical form is
a bound on the trigonometric polynomial

`S(θ) = ∑_{n < N} c_n e(nθ)`,

which is the same quantity read through `⟪expRow N e(θ), ·⟫` with conjugated coefficients.  Making
that identification explicit gives the large sieve in the shape it is used:

`∑_{q ≤ Q} ∑_{(a,q) = 1} |S(a/q)|² ≤ (N + Q²(1 + log(Q²/2 + 1))) ∑_n |c_n|²`.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- The trigonometric polynomial with coefficients `c`. -/
noncomputable def expSum (N : ℕ) (c : Fin N → ℂ) (θ : ℝ) : ℂ :=
  ∑ n : Fin N, c n * (circleFreq θ) ^ (n : ℕ)

/-- The coefficient vector of a trigonometric polynomial, as a Euclidean vector. -/
noncomputable def conjVec (N : ℕ) (c : Fin N → ℂ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun n : Fin N => (starRingEnd ℂ) (c n))

/-- The exponential coefficient is the trigonometric polynomial, up to conjugation. -/
theorem norm_inner_expRow_conjVec (N : ℕ) (θ : ℝ) (c : Fin N → ℂ) :
    ‖⟪expRow N (circleFreq θ), conjVec N c⟫_ℂ‖ = ‖expSum N c θ‖ := by
  rw [inner_expRow_apply]
  have hsum : ∑ n : Fin N, (starRingEnd ℂ) ((circleFreq θ) ^ (n : ℕ)) * (conjVec N c) n
      = (starRingEnd ℂ) (expSum N c θ) := by
    rw [expSum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [conjVec, mul_comm]
  rw [hsum]
  simp

/-- The energy of the coefficient vector. -/
theorem norm_sq_conjVec (N : ℕ) (c : Fin N → ℂ) :
    ‖conjVec N c‖ ^ (2 : ℕ) = ∑ n : Fin N, ‖c n‖ ^ (2 : ℕ) := by
  rw [conjVec, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp

/-- **The large sieve for trigonometric polynomials at Farey points.** -/
theorem largeSieve_expSum_farey (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (s : Finset (ℕ × ℕ))
    (hmem : ∀ p ∈ s, 0 < p.2 ∧ p.2 ≤ Q ∧ 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ Nat.Coprime p.1 p.2)
    (c : Fin N → ℂ) :
    ∑ p ∈ s, ‖expSum N c ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ (2 : ℕ)
      ≤ ((N : ℝ) + (Q : ℝ) ^ (2 : ℕ) * (1 + Real.log ((Q : ℝ) ^ (2 : ℕ) / 2 + 1)))
          * ∑ n : Fin N, ‖c n‖ ^ (2 : ℕ) := by
  have hbase := largeSieve_farey_reduced N hQ s hmem (conjVec N c)
  rw [norm_sq_conjVec] at hbase
  refine le_trans (le_of_eq ?_) hbase
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [norm_inner_expRow_conjVec]

end RHTower.Sieve
