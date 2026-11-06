# Arithmetic symmetric-group positivity is equivalent to RH

- **ID:** w2-arithmetic-character-rh-criterion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W2 representation construction](../../1-in-progress/w2-representation-construction.md)
- **Statement:** Every finite Gram matrix of the canonical completed-arithmetic symmetric-group class function is positive semidefinite iff RH.

## Arithmetic definition and exact cycles

Put `M=2+γ−log(4π)>0` and
`F(X)=logDeriv xi(1/2+√X)/√X`. Define the value of a cycle of length `n+1` by

`c_n = Re[(-1)^n F^(n)(1/4)/n!]/M^(n+1)`.

The class function is the product of these values over nontrivial cycles. The proved endpoint
resolvent identity and conjugation symmetry give the exact complex formula

`c_n = Σ_ρ (1/(ρ(1−ρ)))^(n+1)/M^(n+1)`.

All divisor sums converge absolutely. Their first sum is `M`, so `c_0=1`. Conjugation,
inversion and adjoining fixed points preserve the class function.

## Positivity implies RH

Choose cycles sharing one pivot and otherwise disjoint arms. Arms of lengths `r_i,r_j`
give entry `c_(r_i+r_j)`. Replicate each arm `N` times. The resulting Gram matrix is
`H_ij + δ_((i,a),(j,b))(1−H_ii)`, where `H_ij=c_(r_i+r_j)`.

Its quadratic form on block-constant vectors is
`N² Q_H(v)+N Σ_i(1−H_ii)v_i²`. Positivity for every `N` forces `Q_H(v)≥0`.
Consequently every endpoint Hankel matrix is positive. Removing normalization is an
invertible positive diagonal congruence. The corpus endpoint-resolvent Hankel criterion
then gives RH.

## RH implies positivity

Under RH each endpoint weight is positive real. Divide by `M` to obtain a summable probability
alphabet. Independent coloring produces a positive character on every finite symmetric
group. A cycle fixes exactly the constant words on its support; disjoint cycles factor.
Thus its character is exactly the prescribed arithmetic class function.

## Lean and open source obligation

`RHTower/Representation/EndpointCharacterCriterion.lean` proves
`xiEndpointArithmeticCharacter_posSemidef_iff_rh`, normalized identity, conjugation and
restriction, and `xiEndpointArithmeticCharacter_formPerm_eq_moment` for arbitrary nonempty
nodup cycle lists. Its direct leaf check passes and its umbrella import is present.

The proof uses the project's endpoint Hankel receiver, replicated Gram classification, cycle
identification and arithmetic derivative identities. This is a receiver equivalence, not an
independent positive arithmetic representation. Constructing that representation remains open.
