# Complete fifth even native source from scale five

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Σ6
- **Lean:** `ThetaCuspSections/FifthEvenNativeRay.lean`, `FifthEvenThreeAtomRemainder.lean`

For every real center `x` with `q=π exp(2x)≥5`, the complete native
matrix `Hᵢⱼ(x)=(-1)^(i+j) J_(2(i+j))(x)`, `i,j<5`, is positive definite.
Its normalized Gaussian form has quadratic floor `49/4000`.
Retaining the leading mass strengthens this to the scale-dependent floor
`(2q−3)²/1000−147/4000`.
More precisely, the full leading-pair Gaussian form survives with quadratic
loss at most `(147/4000)‖v‖²`.
In particular, the unique positive zero of the compensation source has
a strict native fifth even section. Every constant matrix correction
`H+GV` equals `H` at this center.

**Proof.** Divide moment `k` by `Kq^k`, where `K=4q² exp(x−2q)>0`,
and apply the fixed Gaussian basis. The first atom and its two ordered
cross pairs with atom two retain `(49/1000)I`. The two remaining unequal
pairs have entry bounds `1/160` and `1/1000`; the entire reflected tail
beyond three atoms has bound `1/10000`. These follow from exact shifted
radial coefficients, stationary exponential bounds and the three-atom
Cauchy estimate. Their total entry budget is `147/20000`, hence their
quadratic loss is at most `147/4000` times the squared Euclidean norm.
The other pure atoms are positive semidefinite, leaving `(49/4000)I`.
The leading-pair reserve also retains one thousandth of its zeroth moment,
which is at least `(2q−3)²`; this gives the growing floor.
The triangular coordinate map has positive diagonal, so its inverse
congruence transfers strict positivity to `H`. The compensation zero
satisfies `5<q<45/8`, placing it inside this ray.

Public certificates:

- `FifthRemainder.remainderGram_bound`
- `FifthNativeRay.sourceGram_retained_lower`
- `FifthNativeRay.sourceGram_coercive`
- `FifthNativeRay.sourceGram_growing_coercive`
- `FifthNativeRay.native_even_five_posDef`
- `FifthNativeRay.exists_strict_compensation_neutral_center`

Canonical Lean checks and transitive axiom audits pass; only `propext`,
`Classical.choice`, and `Quot.sound` occur.

This closes the compensation-zero source condition. Global positivity of
the fixed cross-load, and the full rank-nine source argument, remain open.
