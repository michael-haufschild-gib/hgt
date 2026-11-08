# The domain of the completed prime boundary

- **ID:** RIAC-completed-boundary
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [RIAC](renormalized-intersection-arithmetic-counts.md), completed topology
- **Statement:** Classify boundedness and closability of the actual Dirichlet augmentation on weighted prime chains.

## Exact candidate

On finite prime coefficients, `d_s x=Σ_p p^(−s)x_p`. Complete degree one
using `Σ_p p^δ |x_p|²`. Determine whether this functional has a bounded
extension, or even a closable densely defined extension, exactly when
`2 Re(s)+δ>1`. In the bounded range, identify its norm squared with
`Σ_p p^(−2 Re(s)−δ)`.

At the proposed boundary, seek explicit finite probes with boundary one
and arbitrarily small weighted norm. Such probes would obstruct closability,
not merely boundedness. A further question is whether coning with prime two
extends to the higher-degree domains and contracts the completed complex.

## Existing work and distinction

ESG already proves that multiplication of each prime vertex by `p^s`
conjugates the finite-cutoff boundary to the ordinary augmentation, naturally
in height. This is an algebraic statement. No assertion about closed graph
domains follows without a norm and a domain comparison.

## Audit and completion standard

Search existing Hilbert/Koszul and prime-boundary results before claiming
novelty. Verify the exact exponent including the square of the coefficient.
Do not replace closability by boundedness without proof. Preserve the
augmented degree zero and distinguish ordinary from reduced homology.
Any obstruction must retain the exact extension range, explicit boundary
representative and norm formula as positive survivors. No theorem is yet
claimed on this card.

## Verified source inputs

`Nat.Primes.summable_rpow` gives the exact reciprocal-prime power boundary.
`RHTower.Sieve.norm_prime_cpow_sq_eq` identifies the squared complex
coefficient with `p^(−2 Re(s))`. The existing Hilbert basis and
`summable_norm_apply_sq` provide the necessity mechanism for bounded
extensions. Actual extension, finite-chain comparison and nonclosability
still require their own proofs.
