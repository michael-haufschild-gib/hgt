# Pre-registered predictions — Weil-form / signature-cancellation falsification test
Registered BEFORE running. Object: symmetric completions of truncated carriers.
  A(s)     = (1/2) s (s-1) π^{-s/2} Γ(s/2)                     (archimedean factor)
  SUM   Ξ_N^S(s) = A(s)·Σ_{n≤N} n^{-s}       + A(1-s)·Σ_{n≤N} n^{-(1-s)}   (additive truncation)
  PROD  Ξ_P^P(s) = A(s)·∏_{p≤P}(1-p^{-s})^{-1} + A(1-s)·∏_{p≤P}(1-p^{-(1-s)})^{-1}  (multiplicative truncation)
Both are real on Re=1/2 and symmetric under s↦1-s. Off-line zeros come in quadruples;
count M = #zeros in {Re>1/2, Im>0} up to height T via the argument principle; off-line = 4M.

## The question
Does the FINITE arithmetic (finitely many primes / terms) cancel off-line-zero mass — i.e. pin
zeros onto the line — at finite truncation, or only in the limit? "Signature cancellation" (#1,
Hodge/Weil) reachable at finite N ⟺ off-line zeros suppressed by finite arithmetic.

## Predictions (P = prediction, with rough confidence)
- P-A (~80%): the SUM completion Ξ_N^S has NO off-line zeros below height T*(N) ≈ 2πN² (the
  approximate-functional-equation horizon) and off-line zeros appear/proliferate ABOVE it.
  → T*(N) tracks 2πN². (If it tracks log N or N instead: surprise.)
- P-B, THE REAL TEST (~60%): the PRODUCT (multiplicative) truncation SUPPRESSES off-line zeros
  relative to the SUM truncation at matched arithmetic content, but does NOT eliminate them at
  finite P. → finite-range cancellation is real but partial; complete pinning is infinitary.
  Falsification-Mirage: product ≈ sum (no suppression) ⟹ cancellation is TOTALLY infinitary,
    #1 is a mirage at finite N.
  Falsification-Reachable: product has ZERO off-line zeros in a growing range ⟹ finite Euler
    product FULLY pins, #1 reachable at finite P (surprising, very encouraging).
- P-C (~70%): "cancellation length" (height to which the object is pinned on-line) is
  COEXTENSIVE with the AFE range ~2πN² for the sum; the product's cancellation length is
  LONGER at matched term-count (multiplicative structure buys extra range).

## What the outcome decides (goal part 2)
- If product ≫ sum in pinning: signature cancellation IS a finite-N construction target → build #1.
- If product ≈ sum: cancellation is infinitary → #1 needs the limit object; finite carriers only
  ever speak the count/parity register.

## OUTCOME (resolved by the multiplicative principle, not by scaling up numerics)
v1 census (recorded, then STOPPED as theatre): additive SUM truncation scatters off-line zeros
(count grows with N, onset ~T=20 regardless of N); multiplicative PRODUCT truncation shows ~0
off-line zeros even at one prime. This is KNOWN (Euler product is the arithmetic; partial products
are zero-free, partial sums scatter). No v2.

The sharp resolution (user's steer "always multiplicative, never additive"):
- A FINITE Euler product ∏_{p≤P}(1-p^{-s})^{-1} is ZERO-FREE (finite product of nonvanishing
  factors). So there is NO off-line mass at any finite multiplicative truncation — nothing to cancel.
- Off-line zeros (hence RH, hence any signature defect) are created ONLY in the analytic
  continuation of the DIVERGENT product past Re=1. Signature cancellation is therefore INFINITARY.
- P-B verdict: NOT the "weak finite cancellation" I guessed — stronger: there is nothing to cancel
  until the product diverges and is continued. Prediction (infinitary) CONFIRMED, via the correct frame.

Decision for #1: the naive "finite-N signature-with-cancellation" is a mirage — and MORE so than I
guessed. The Weil form W = P∞ + Arch − Prime splits, but the ARCH/SEAM half is NOT positive
(windingRate(0) ≈ −2.7 < 0; the arch density is indefinite, negative core + log-growing tail). So the
positivity — the actual RH content — is the WHOLE-form balance, and it is infinitary through and
through; no finite piece carries it. Finite N supplies only the explicit ingredients (Arch = the banked
winding form; Prime_X = truncated von Mangoldt), never the positivity. Payoff: Arch = (1/π)∫ĥ·windingRate
exactly, so the winding-floor machinery IS the explicit archimedean term of the Weil/Hodge form. See
construction note.
