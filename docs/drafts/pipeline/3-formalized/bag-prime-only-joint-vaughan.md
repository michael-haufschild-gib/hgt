# BAG prime-only joint Vaughan source

- **ID:** BAG-C28.56c
- **Stage:** 3-formalized
- **Type:** LEAN PROVED (exact source construction)
- **Source:** Sieve/VaughanIdentity.lean; Sieve/VaughanBlockDecomposition.lean; mathlib VonMangoldt and Nat/Squarefree; ChiPrimeGaussianCubicMain.lean
- **Statement:** Remove proper prime powers exactly from the joint cubic factorization, preserving all signed weights and exposing a prime-only long Type-II factor.

## Hard target and scope

BAG C28.44 still requires full joint signed Gaussian cubic cancellation at N/log²N. The naive prime-to-von-Mangoldt replacement introduces a correction whose absolute bound is too large. This construction removes that correction pointwise; it does not assert the missing signed estimate.

## Corpus-derived paper proof

Write sf(n)=1 when n is squarefree and 0 otherwise. The actual von Mangoldt definition and Nat.squarefree_and_prime_pow_iff_prime give sf(n)Λ(n)=1_prime(n)log n exactly. Multiply the actual four-term Vaughan identity by sf(n), retaining each term and its sign. In a factorization n=dm, squarefreeness is equivalent to sf(d)=sf(m)=1 and gcd(d,m)=1. Therefore the long Type-II factor sf(d)(Λ(d)-Λ_≤U(d)) is exactly log d on primes d>U and zero otherwise. The remaining signed coefficient is sf(m)(1-ζ*μ_≤V)(m), with the coprimality condition retained.

If n≤U², every contributing prime d>U has m<d. As m>0, d cannot divide m, so the coprimality condition disappears without an error term. This yields an independent signed cofactor coefficient in the entire square-root-cutoff Type-II branch, rather than replacing prime powers by a large error. The two Type-I terms still contain their exact squarefree masks; none is silently treated as a free integer sum.

Substitute the complete actual q,r cubic row, divided by log n, as weight. The prime logarithm cancels exactly on primes. Every q,r, coupled W/V factor, denominator and noncontraction mask remains. No analytic or prime-distribution estimate is assumed. The remaining task is cancellation of these actual signed source terms jointly; their separate norms do not suffice.

## Status

Paper construction dependency-closed on the named corpus identities. `ChiPrimeGaussianCubicPrimeOnlyVaughan.lean` supplies the complete coefficient identity, the prime-only Type-II factorization, automatic coprimality below U², and the actual full Gaussian cubic substitution. Direct production49037 using `lake --old env lean <leaf> -o <olean>` passed without diagnostics. All11 public axiom queries19626 passed with only propext, Classical.choice and Quot.sound. Leaf wired into RHTower; no umbrella/full build. Lint56927 reports13 unrelated unreachable leaves, none in this construction. No claim of full cubic asymptotics, growing moments, self-target recurrence or RH.

The precise advance is removal of the proper-prime-power correction branch without an estimate. The full signed cancellation problem remains in the exact Type-I/II source. In particular, the Type-I squarefree masks and Type-II near-fraction correlations remain mathematical obligations, not supplied hypotheses.

## Log

- 2026-10-03 — Prime-power search9453 and squarefree search50969 both nonpartial65041/65041, source/compiler metadata mostly pending; all candidates/source/ideas/ingredients inspected. No matching prime-only Vaughan producer found in those hits or targeted source search. Beginning exact construction.
- 2026-10-03 — Scratch6239, production49037 and all11-public-declaration axiom audit19626 exit0. Full coefficient equality and Gaussian substitution hold for every cutoff pair U,V, with no analytic premise. The range condition n≤U² in the separate simplification lemma only removes its explicit coprimality test.
