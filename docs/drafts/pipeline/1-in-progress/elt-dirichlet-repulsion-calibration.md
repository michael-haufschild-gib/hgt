# Dirichlet exceptional-zero repulsion calibration

- **ID:** ELT-DH
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / FORMALIZATION TARGET
- **Target:** A complete Deuring–Heilbronn law for the actual infinite divisor of `ζ(s)L(s,χ)`, with χ primitive, real and nonprincipal. A real zero β₁ near 1 forces every other zero ρ near 1 to satisfy
  `1−Re ρ ≥ log(1/[C(1−β₁)log(q(|Im ρ|+3))])/[C log(q(|Im ρ|+3))]`
  for an absolute positive constant C.

## Mechanism to validate

Positive coefficients `(1+χ(n))(1+cos(t log n))Λ(n)` control all even
reciprocal moments of the complete divisor at `σ` and `σ+it`.
Removing β₁ from both copies pairs its moments with the pole at 1;
their difference is bounded by `4k(1−β₁)/(σ−1)^(2k+1)`.

An infinite power-sum lemma must detect a remaining zero with order
`k≤C M`, where M is the total normalized reciprocal-square mass.
Put `L=log(q(|t|+3))`. For a target at `1−δ+it`, choose
`σ=1+δ+1/L`; the required mass bound is `M≤C(1+δL)`.
The moment comparison then gives `1≤C(1−β₁)L exp(CδL)`,
which yields the stated logarithmic repulsion.
All nontrivial and trivial zeros, multiplicities, and Gamma terms must
be retained. No finite truncation may replace the divisor.

## Status and role

This is the classical calibration required by §2.10, not a claim of new
repulsion for ζ. Corpus search found Siegel's theorem and the two-torsion
positivity exception; no declaration named Deuring–Heilbronn was found.
Exact divisor identities, the infinite power-sum lemma, and the target
statement remain under audit. No proof or formalization is claimed.

The ζ analogue must explain how to replace real pole–zero cancellation
when the isolated layer is a nonreal conjugate pair.

## Infinite power-sum argument

Normalize a summable sequence by its attained maximal modulus. Write
`M=Σ|z_j|`, `|z_j|≤1`, and choose `|w|=1` among its terms.
For `P_N(z)=Σ_{j<N}Σ_{k<j}z^(k+1)`, the Fejér square identity gives
`Re P_N(z)≥−N/2`. For `|z|≤1/2`, geometric summation gives the
stronger summable majorant `Re P_N(z)≥−2N|z|`; together these give
that majorant on the whole unit disc.

The weighted polynomial
`U_N(z)=Re[P_N(z)+(P_N(zw)+P_N(z conj(w)))/2]`
has nonnegative moment weights `1+Re(w^k)≤2`, satisfies
`U_N(z)≥−4N|z|`, and at the selected term satisfies
`U_N(w)≥N(N−4)/4`. If every real power sum through order `N−1`
were at most `1/8`, summing would give `N−7≤32M`.
Choose `N=ceil(32M)+9`. Since `M≥1`, some `1≤k≤64M` has
`Re Σ z_j^k>1/8`. Absolute summability justifies every exchange;
no gap below the maximal modulus or finite-support premise is needed.

This argument is being formalized as a component of the full calibration,
not as a completed repulsion result.
