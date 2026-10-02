# Theta endpoint-commutator comparisons

- **Route:** RN, full theta tail-kernel positivity.
- **Status:** both CP-3 comparisons falsified in Lean, 2026-10-02.
- **Scope:** auxiliary comparisons only; neither RN nor RH is falsified.
- **Lean:** `formal/GaloisForLFunctions/RHTower/ThetaTailEndpointCommutatorObstruction.lean`.

## Exact failed claims

For the literal complete source `k`, put

    C_j(x,y) = integral_(s>0) s^j k(x+s) k(y+s) ds,
    D_0(x,y) = (sqrt(x)-sqrt(y))^2 C_0(x,y).

CP-3 proposed `2 C_1 >= D_0` in matrix order. Its original sufficiency
argument had the wrong sign. The exact decomposition is

    H = 2 sqrt(X) C_0 sqrt(X) + D_0 + 2 C_1.

The corrected sufficient comparison, CP-3′, is `2 C_1 >= -D_0`.
Both comparisons fail on positive nodes `(r,r+1)` for every sufficiently
large `r`. Coefficients are respectively

    (1/k(r),  1/k(r+1)),
    (1/k(r), -1/k(r+1)).

This is a theorem about the complete theta source, not a counterexample
from a replacement source or a finite theta truncation.

## Dependency-closed paper proof

For fixed `x,y`, write `A=pi*(exp(2x)+exp(2y))`,
`E(r)=exp(-2r)`, `P(r)=k(x+r)k(y+r)`, and `N(r)=E(r)P(r)`.
The existing complete-source score theorem gives

    (baseSlope(r)+2A)/E(r) -> 7.

Differentiating the tail mass and applying l'Hopital gives the new law

    (C_0(x+r,y+r)/N(r) - 1/(2A))/E(r) -> 7/(4A^2).

Combine it with the corpus's first correction for `H` and the exact identity

    H(x+r,y+r) = (x+y+2r) C_0(x+r,y+r) + 2 C_1(x+r,y+r).

The polynomially weighted exponential limits then imply
`r C_1(x+r,y+r)/N(r) -> 0`. No numerical approximation is used.
For `r>=1`, rationalizing the square-root gap bounds
`r (sqrt(r)-sqrt(r+1))^2` away from zero. Since `C_0/N -> 1/(2A)>0`,
the normalized endpoint commutator stays bounded away from zero.
Multiplying either displayed packet form by the positive scalar `r/E(r)`
therefore gives a quantity strictly below zero eventually.

## Positive survivor and new insight

The **full** `H` matrix on these same nodes is positive definite eventually.
This uses the corpus's fixed-pattern Cauchy-limit theorem, together with
injectivity of the two-node pattern. Thus a full positive kernel can have
both endpoint commutator remainders indefinite: removing the leading
endpoint Gram term destroys precisely the interaction needed here.

The new positive analytic statement is the exact tail-mass first correction;
the exact moment decomposition and separation of scales are also formalized.
The joint survivor theorem is
`full_kernel_positive_with_negative_endpoint_comparisons`.
The negative theorem is `endpoint_comparisons_eventually_negative`.
The `*_commonShift` lemmas identify the moving-cut definitions with the
literal zero-cut orbit moments above.

Paper proof and Lean leaf proof are complete. Targeted `lake --old build`
and final `lake env lean` passed; the final leaf audit had no warnings.
The leaf is wired into `RHTower.lean`. The `/tmp` axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound` for all four audited main
theorems. Repository lint reports twelve unrelated unreachable modules;
their names and exact audit commands are in the RN working log.

## Remaining hard problem

Prove positivity of the complete mixed form uniformly over arbitrary finite
test families. The fixed two-node survivor does not supply that theorem.
Any further comparison must retain the leading Gram term and its interaction
with the remainder; neither CP-3 sign is an available positivity producer.
