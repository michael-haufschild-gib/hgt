# BAG complete arithmetic Mellin pairing and exterior vanishing

- **Stage:** 3-formalized

2026-10-06,01ax. Dependency-closed paper proof and production closure.
ChiCubicMellinArithmeticPairing674lines/API5. All four public theorem proofs
passed scratch73591/log09 standard3. Production93958/log01 emptyPASS:
lake --old env lean with explicit leaf olean. All five imported declarations
passed axiom43754/log01 with onlypropext,Classical.choice,Quot.sound.
Index96945/log01PASS/API5; RHTower importonce23598; scoped diffcheckPASS.
No admissions, new axioms or resource increases. Authoritative lint83875/log01
terminal1:362warnings19unrelated unreachable modules, noownedfinding.
Global lint is NOT clean. Exact errors:
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.KuznetsovUniformBounds
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergCoefficient
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergFactorization
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergForms
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergGcdLog
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergGcdLogForms
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergRatioForms
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergSummability
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionFarey
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionOffResonance
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionRatioFibers
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionRatioForm
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionResonantBounds
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionResonantCount
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionResonantSmall
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionSecondMomentExpansion
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.ComplexMeasurePairing
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.MultiplicativeConvolutionDomain
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PermutationAveragedFirstFailure

Audit logs /tmp/bag-mellin-pairing-*01ax.log and scratch01–09 retained.

The literal source is the ORIGINAL complete growing labelled Euler source,
with both cofactors, both exclusions, allowed first/second collision and all
valuation sectors, evaluated on1+rho_i/logN+2*pi*i*xi_i and divided bylogN.
The native2*pi frequencies are explicit in its public definition.

1. Every exact difference of localized Mellin profiles, including different
parametersq,r in[1,2]^2 and arbitrary Schwartz inputsf,g, has an admitted full
arithmetic pairing bounded by ONE constant times the square root of its own
H^(5/4) energy, uniformly in all sufficiently largeN. No trace, norm or
uniform Schwartz budget is a premise.
2. Every Schwartz frequency test has an admitted complete source pairing
bounded byC sqrt(1+logN) times its H2 energy root.
3. The literal selected physical Mellin exterior has pairing norm<=C/N,
uniformly in the entire Mellin parameter square, with integrability proved.
4. Its full arithmetic pairing tends to zero for EVERY moving parameter
sequence in that square. No convergence of the parameter sequence is needed.

Proof. The closed subpower envelope at exponent1/8 and native2*pi scaling
give, forL=logN>=1, the normalized bound
|Z_N(2*pi*xi)/L|<=C w(xi)^(1/8)*(1+k_L(xi0)+k_L(xi1)),
w=1+|xi0|+|xi1|, k_L(t)=L/(1+L|t|)^2.
The original complete cofactor series proves source measurability directly.
Both bounded background and shrinking axes remain in the estimate.

The background pairs by weighted Cauchy–Schwarz: w^(1/8)|G| is the product
ofw^(5/4)|G| andw^(-9/8). The latter squarew^(-9/4) is integrable on the
full plane because9/4>2. Admission follows from native polynomial Schwartz
moments and the Euclidean norm/coordinate weight comparison.

For localized profile differences, the closed common-support reproducing
trace theorem givesw^(5/4)|G|<=T sqrt(E_(5/4)(G)). Thusw^(1/8)|G| is bounded
by that constant times(1+|otheraxis|)^(-9/8). Each transverse kernel k_L has
EXACT constant mass after one-dimensional dilation; the unpaired coordinate
weight is integrable because9/8>1. Euclidean/product volume transport is
exact. Adding the background and both axes proves the complete uniform
operator estimate and its integrability, with no frequency truncation.

For unrestricted Schwartz tests, multiply the source envelope byw^-2.
Its squared frequency weight isw^(-15/4). The inequalities0<=k_L<=L,
k_L²<=L*k_L and(1+k0+k1)²<=3(1+k0²+k1²) reduce the full squared dual norm
to an integrable planar background plusL times the same two admitted axis
majorants. Consequently that norm squared is<=C(1+L). Weighted Holder2
admits the complex pairing and gives the second theorem.

Apply the closed actual exteriorH2 energy law withk=2: energy<=B/N^4,
uniformlyq. Its root is<=sqrt(B)/N². The elementary symbolic inequality
sqrt(1+logN)<=N forN>=2 absorbs the complete dual cost, provingC/N. The
native constant-over-natural limit and the complex norm squeeze prove zero
for everyq_N. These results make no numerical experiments or asymptotic
Schwartz-limit identification.

Hard frontier remaining: actual physicalHs Cauchy transfer, fixed-input
Mellin parameter continuity, and fixed-late-test comparison with the proved
signed fixed-Schwartz source law. Full original sharp-action bridge,
growing moments/cofactors/common-height return and RH remain open.
P1 bag-moving-mellin-trace-transfer records the active proof loop.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiCubicMellinArithmeticPairing` | `bagLocalizedMellin_difference_arithmetic_pairing_bound`, `bagMellinNormalizedArithmeticSource_H2_pairing_bound`, `bagCubicSelectedExteriorMellin_arithmetic_pairing_decay`, `bagCubicSelectedExteriorMellin_arithmetic_pairing_tendsto` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
