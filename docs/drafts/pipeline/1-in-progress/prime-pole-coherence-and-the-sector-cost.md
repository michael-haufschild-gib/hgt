# Prime-pole coherence and the sector cost

- **ID:** critical-rigidity-prime-pole-coherence
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Determine the exact norm of the pole reading of the actual prime generator on prime-supported packets, and identify the mandatory conductor cost in relative prime estimates.

## Candidate sharp law

For normalized packets supported on primes `p≤Q`, the proposed pole response is

`P_Q(a)=Σ_p log p / sqrt(p−1) · a_p`.

The exact adjunction weight is `L_p=p log p/(p−1)`. Weighted Cauchy–Schwarz predicts the sharp law

`P_Q(a)² ≤ B_Q Σ_p L_p a_p²`, where `B_Q=Σ_(p≤Q)log p/p`.

The coefficient choice `a_p=sqrt(p−1)/p` gives both `P_Q(a)=B_Q` and adjunction mass `B_Q`, so the constant cannot be reduced. Mertens' theorem gives `B_Q=log Q+O(1)`.

## Source identification to formalize

The packet itself has zero constant mode. The complete prime generator is the divisor jet minus diagonal adjunction. Its constant mode should be exactly `P_Q(a)`, since the period mean of the divisor jet is `Λ(m)`. Thus pole-neutral input can generate a coherent pole output whose squared norm has a mandatory logarithmic cost.

## Positive content and scope

The survivor is the exact optimal pole-response inequality, its explicit extremizer, and its logarithmic scale. This would identify the source of a necessary loss, rather than discard relative control. It does not obstruct cancellation with the global pole or Gamma terms in the complete form; it explains why that coupling must be retained.

## Corpus leads

- `SuccessorShellArithmetic.TopBand.RamanujanDivisorMoments.periodMean_ramanujanLogDivisorJet`.
- `ArithmeticIntersectionTheory.TheDifferentOfATorsionOrbit.tameDifferent_prime_pow`.
- `RHTower.MertensFirst`: `RHTower.Mertens.mertens_first_prime` gives an explicit bounded difference between `B_Q` and `log Q`.
- Current relative prime-head bound is `A_Q L_Q(a)`, where `A_Q=Σ_(p≤Q)log p/(p−1)`. The candidate lower bound has the same logarithmic order.

No Lean theorem or completed no-go is claimed yet.
