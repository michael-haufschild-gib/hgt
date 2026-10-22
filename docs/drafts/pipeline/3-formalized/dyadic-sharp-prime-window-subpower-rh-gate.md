# Dyadic sharp prime-window subpower upper bound forces RH

- **ID:** `dyadic-sharp-prime-window-subpower-rh-gate`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / VALUE-RELATION RH GATE
- **Scientific status:** `[FORMALIZATION] [POSITIVE STATEMENT] [NOVELTY AUDIT REQUIRED] [NOT AN RH PROOF]`
- **Statement:** If, from any fixed index onward and for every `epsilon>0`,
  the dyadic weighted von-Mangoldt window is at most its exact square-root main term plus
  `C_epsilon n^epsilon`, then RH holds.

## Main theorem

For

```text
W(n) = sum_{n/2 < k <= n} Lambda(k) / sqrt(k),
```

the Lean theorem

```text
riemannHypothesis_of_eventually_dyadicWeightedPrimeWindow_upper
```

proves directly, without a bundled proposition interface,

```text
(exists N, for every epsilon>0, exists C_epsilon>=0,
  for every n>=N,
    W(n) <= 2*(1-1/sqrt(2))*sqrt(n) + C_epsilon*n^epsilon)
  -> RH.
```

The theorem is conditional as a criterion: the displayed prime inequality remains the source
obligation. No right-half zero, `not RH` witness, divisor hypothesis, or test-function regularity
appears in its premise.

The stronger fixed-exponent theorem

```text
xiRightCenteredZero_re_le_of_eventually_dyadicWeightedPrimeWindow_upper
```

shows that one eventual error exponent `alpha>=0` already forces every nontrivial zero on the
right of the critical line into

```text
Re(rho) <= 1/2 + alpha.
```

Thus the all-epsilon theorem is not an isolated contradiction argument: it is the cofinal limit of
an explicit exponent-to-zero-free-region law.

## Exact value relations

Define the finite sharp source coefficient

```text
S(n) = 4*(1-1/sqrt(2))*sqrt(n) - 2*W(n).
```

Then the requested inequality is pointwise equivalent to

```text
S(n) + 2*C_epsilon*n^epsilon >= 0.
```

The ordinary Dirichlet series of `S(n)` is exactly the pole-filled continued sharp source on its
initial half-plane:

```text
sum_{n>=1} S(n)*n^(-s) = dyadicSharpPrimeContinuedSource(s),  Re(s)>3/2.
```

There is also an exact Abel value relation

```text
W(n) = 2*(1-1/sqrt(2))*sqrt(n) + dyadicCriticalMellinErrorIncrement(n),
```

so the prime inequality is exactly the one-sided subpower upper bound on the endpoint-plus-
primitive increment of `psi(x)-x` over `[n/2,n]`.

## Proof architecture

Assume RH is false and let `delta_* > 0` be the supremum of positive transverse Xi displacement.
Set `alpha=delta_*/4`. The assumed inequality makes

```text
S(n) + D*n^alpha
```

nonnegative after absorbing the finite prefix. Its Dirichlet series continues as

```text
dyadicSharpPrimeContinuedSource(s) + D*zeta(s-alpha).
```

Two local Landau transfers are used. The first moves convergence from `Re(s)>3/2` to just right of
`1+delta_*` through the zero-free real corridor. The second crosses that boundary inside the
unconditional zero-height-gap ball. After subtracting the summable power correction, the original
sharp source series converges at some `sigma<1+delta_*`.

Multiplying this analytic L-series by the shifted pole-filled zeta must reproduce the globally
holomorphic cancelled sharp source. At every right Xi zero, however, the cancelled source has
vanishing order exactly one less than that zeta factor. An analytic L-series cannot supply a
negative order. Hence every shifted right Xi pole has real part at most `sigma`, contradicting the
definition of `delta_*`.

## Verification

The implementation is in

```text
GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowDirichlet
GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowSubpowerGate
```

The touched modules compile. The formal lint gate passes. `#print axioms` for the capstone reports
only Lean/mathlib's standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`; there
is no project `axiom`, `sorry`, `admit`, `opaque`, or `unsafe` declaration.

## Scientific boundary

The classical relation

```text
RH <-> psi(x) = x + O(x^(1/2+epsilon)) for every epsilon>0
```

is standard. A targeted literature search did not locate this exact one-sided fixed-dyadic
weighted-window criterion, but absence from that search is not a novelty proof. The exact criterion
therefore remains outside `new_scientific_knowledge` until a dedicated literature audit clears the
novelty gate.

The closest primary-source comparison located in the 2026-07-13 audit is Gonek--Graham--Lee,
*The Lindelöf hypothesis for primes is equivalent to the Riemann hypothesis*, Proc. AMS 148
(2020), DOI `10.1090/proc/14974`: it uses uniform oscillatory von-Mangoldt sums with a two-sided
error. Banks--Sinha, *The Riemann Hypothesis via the generalized von Mangoldt function*,
arXiv:`2209.11768` (revised 2026), develops related two-sided twisted-sum equivalences. Neither
source states the present one-sided, untwisted, fixed-dyadic weighted-window inequality in the form
formalized here. This comparison narrows the audit but does not establish novelty.

The converse direction is not yet formalized here. Classically it follows from an RH-quality
Chebyshev error estimate inserted into the exact Abel relation. Until that analytic estimate is
present axiom-free in Lean, this card claims only the implication displayed above.

## Gates

- [x] 0 -> 1 in-progress: exact source coefficient and Landau mechanism isolated
- [x] 1 -> 2 fully-proven: complete proof with the open source obligation stated explicitly
- [x] 2 -> 3 formalized: capstone compiles, lint passes, axioms audited
- [ ] Novelty gate: exact fixed-dyadic criterion checked against the primary literature
- [ ] Converse gate: RH-quality Chebyshev estimate formalized and transported through Abel
- [ ] 3 -> 4 publication-ready: not eligible before both remaining gates

## Log

- 2026-07-13 — Repaired and verified the sharp Dirichlet source identity; formalized the two-step
  Landau transfer, cancelled-source order contradiction, fixed-exponent zero-free law, and direct
  prime-window-to-RH theorem.
