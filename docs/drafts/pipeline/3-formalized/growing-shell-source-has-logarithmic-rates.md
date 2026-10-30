# Growing shell sources have logarithmic rates

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** fixed-conductor-packets-remain-positive-at-growing-overlap

## Statement

Fix a positive modulus and a smooth unit-supported profile with positive
squared mass. One constant `C>0` has the following property for every
natural `k`: beyond one base horizon `Y₀`, all `c≥1`, `Y≥Y₀`,
`X≥2cY`, affine multipliers and shell shifts satisfy

`|actual shell correction − signed shell mean| ≤ C c³/(log Y)^k`.

## Proof

The exact finite-part Abel identity is
`weighted error = W(1)E_F(X)−∫_0^1 W′(u)E_F(Xu)du`.
If `W` vanishes for `|u|<a`, `|W(1)|≤B` and `|W′|≤D`, the
quantitative residue Mertens bound gives error at most
`2(B+D)/(log Y)^k · Σ_r|F(r)|`, provided `X≥Y` and `Xa≥Y`.

Let `M=∫φ²` and let `L` be a Lipschitz constant for its autocorrelation.
For each active shell, `a_h=h/c∈[1/c,1]`. The reciprocal weight
`W(u)=G(a_h/u)` vanishes for `|u|<1/(2c)`, satisfies `|W(1)|≤M`,
and has derivative bounded by `4Lc²`: outside the flat interval,
`|W′(u)|≤La_h/u²≤4Lc²`.

The affine Ramanujan residue pattern has `Σ_r|F(r)|≤qϕ(q)`.
There are at most `2c` shells, and the correction multiplies their sum
by `2/M`. Since `M+4Lc²≤(M+4L)c²`, the result follows with
`C=8qϕ(q)(M+4L)/M`. This is the literal signed source, including
all prime powers and arbitrary reflected or positive shifts.

## Lean status

`GrowingShellSourcesHaveLogarithmicRates.lean` proves
`exists_affineShellCorrection_polynomial_log_rate`. Final direct Lean audit
passed; transitive axioms are `propext`, `Classical.choice`, `Quot.sound`.
Supporting quantitative source estimate; no separate contribution count.
