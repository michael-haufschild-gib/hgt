# Exact coefficient repair by real local factors

- **ID:** local-divisor-coefficient-repair
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** arithmetic-local-divisor-geometry; Astra §§8.1, 9.4
- **Statement:** Classify exactly how adjoining real divisor factors can conceal an off-real pair in the coefficient cone, and price the necessary multiplicity.

## Mathematical statement and paper proof

Write `y=x²`. A conjugate spectral pair at offsets `u±iδ` gives

`Q(y)=y²+2(u²−δ²)y+(u²+δ²)²`.

It satisfies `Q(x²)=(x²+u²−δ²)²+4u²δ²≥0`, while its coefficients are all nonnegative exactly when `δ²≤u²`.

Adjoining one real zero at squared offset `c≥0` multiplies by `y+c`. The resulting coefficients, in descending order, are

`1, c+2(u²−δ²), (u²+δ²)²+2c(u²−δ²), c(u²+δ²)²`.

For an adverse pair `δ²>u²`, set `b=2(δ²−u²)>0` and `r=u²+δ²`. Such a factor repairs the pair exactly when `b≤c` and `bc≤r²`. A choice exists iff `b²≤r²`, equivalently `δ²≤3u²`; `c=r` is a valid choice throughout that range. Thus coefficient positivity of a larger head does not imply coefficient positivity of its factors. At the boundary, `Q(y)(y+4u²)=y³+64u⁶`. This is an exact positive survivor: the one-factor repair region, not merely a counterexample to cancellation.

For arbitrary multiplicity, normalize by `r>0`, put `z=y/r`, and set `α=(δ²−u²)/r`. The multiplier `(y+r)^n` gives the normalized polynomial

`(1+z)^n(z²−2αz+1)=(1+z)^(n+2)−2(α+1)z(1+z)^n`.

Its interior coefficient at `k`, divided by the positive `binomial(n,k−1)`, is

`(n+2)(n+1)/(k(n+2−k))−2(α+1)`.

The maximum of `k(n+2−k)` over integer `1≤k≤n+1` occurs at the middle integer(s). Consequently:

- for `n=2m`, coefficient nonnegativity holds iff `α≤m/(m+1)`;
- for `n=2m+1`, it holds iff `α≤(m+1)/(m+2)`.

Equivalently, the exact geometric bounds are `δ²≤(2m+1)u²` and `δ²≤(2m+3)u²`, respectively. This prices the degree needed to mask a nearby pair: as the center approaches its ordinate, required multiplicity grows like `δ²/u²`. At its own ordinate (`u=0`, `δ≠0`), no nonzero polynomial multiplier can repair the pair: its positive root survives multiplication, whereas a nonzero polynomial with nonnegative coefficients is positive at every positive argument.

Central divisor factors `y^a` preserve and reflect coefficient nonnegativity exactly; they shift indices without changing signs. No division by a vanishing central value is needed.

## Novelty and source audit

This is local polynomial geometry, not an arithmetic selection theorem. It measures why degree and centering cannot be omitted from a source certificate. Pólya multiplier positivity is classical; no worldwide novelty is claimed. The intended contribution is an exact sharp multiplicity law tied to the WD local pair and its singular central limit.

Primary literature inspected: Powers–Reznick, *A quantitative Pólya's theorem with corner zeros*, https://www.math.emory.edu/~vicki/pub/polya2.pdf; their general multiplier theorem is stronger in scope but does not make the local-factor sign an arithmetic theorem. The argument above is independent and elementary.

Motzkin–Straus, *Divisors of polynomials and power series with positive coefficients* (1969), https://msp.org/pjm/1969/29-3/pjm-v29-n3-p13-p.pdf, Theorem 2.6 already gives `α≤n/(n+2)` as a sufficient equal-factor bound; Theorem 2.1 gives the optimal degree for arbitrary quadratic multiples. Our contribution is exact parity-sensitive necessity and sufficiency in WD coordinates. Kepka–Korbelář, https://arxiv.org/abs/1210.6868, reviews quadratic multiples and develops cubic and multiplicity bounds. General root-angle degree bounds are classical, not a new programme theorem.

Corpus searches: `finiteHead`, `CoeffNonneg`, `"Polya" "coeff"`, `"negative coefficients" "root"`, `binomial multiplier coefficient`. Existing positive-shell and polynomial-heat product laws are inputs, not new results.

## Gates

- [x] Dependency-closed symbolic paper argument; no numerical experiments.
- [x] Formalize pair geometry and exact one-factor repair; foreground check passed.
- [x] Formalize the sharp arbitrary-multiplicity law.
- [x] Formalize central shifts and impossibility of repair at the adverse ordinate.
- [x] Final foreground module checks, umbrella wiring and `#print axioms` audit.

Lean declarations: `coeffNonneg_pairFactor_iff`, `exists_linear_repair_iff`,
`pairFactor_boundary_repair`, `coeffNonneg_geometricRepair_even_iff` and
`coeffNonneg_geometricRepair_odd_iff`. Modules `LocalFactors`, `DivisorTransitions`,
`BinomialMultipliers` and `GeometricMultipliers` passed plain `lake --old env lean` checks.
Transitive audits use only `propext`, `Classical.choice` and `Quot.sound`.

## Limits

Real factors in these models are not asserted to occur in the actual Xi head. A source certificate must constrain actual local divisors. The programme's arithmetic endpoint remains open.
