# Weighted prime shells are uniform on bounded overlap

- **ID:** weighted-prime-shells-are-uniform-on-bounded-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** one-horizon-makes-every-bounded-overlap-positive

## Statement

For every fixed conductor `q≥1`, nonzero compact `C²` unit profile, finite
shell range `1≤h≤H`, and `K≥1`, the literal weighted affine prime shell
converges to its signed Ramanujan mean uniformly in `1≤c≤K`, `h`, and both
affine parameters. All prime powers are retained. Consequently the full
finite shell correction converges uniformly for `1≤c≤K`.

## Proof [PROVED HERE]

Write `G=φ⋆φ`, `M=∫φ²`. The reciprocal weights `W_a(t)=G(a/t)`, extended by
zero at zero, have `a=h/c∈[1/K,H]`. They vanish on one common neighborhood
of zero. Since `G` is globally Lipschitz with constant `L`, their derivatives
on `[0,1]` are bounded uniformly: below `τ=min(1/(2K),1/2)` they vanish;
above it, the chain rule gives `|W_a′(t)|≤LH/τ²`. Also `|W_a(1)|≤M`.

The exact finite-part Abel identity is

`weightedReading_F(W,X)−κ_F∫_0^1W(u)/u du`
`=W(1)e_F(X)−∫_0^1W′(u)e_F(Xu)du`.

Each residue indicator has `e_r(Y)→0`. The finite residue basis provides
one horizon above which every `e_r` is small. On the derivative support,
`Xu≥τX`; hence the display is uniformly small for all these weights.
Summing with signed residue coefficients bounds the error by
`ε Σ_r|F(r)|`. For the affine Ramanujan pattern this norm is at most
`qϕ(q)`, independent of its two affine parameters. The proved reciprocal
change of variables supplies the desired shell integral. Finally sum at
most `⌈K⌉` shells; the varying endpoint creates no loss of uniformity.

## Lean formalization

`CriticalArithmeticCorrelationTheory/TheWeightedPrimeShellsAreUniformOnBoundedOverlap.lean`:

- `eventually_weightedResiduePrimeReading_uniform_weights`
- `eventually_affineRamanujanPrimeShell_uniform_overlap`
- `eventually_affinePrimeShellCorrectionOfShift_uniform_overlap`
- `eventually_tiltedUnitSpline_affineShellCorrection_uniform_overlap`

Direct Lean audit passed. All four transitive axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`. Supporting source estimate;
no separate contribution count.
