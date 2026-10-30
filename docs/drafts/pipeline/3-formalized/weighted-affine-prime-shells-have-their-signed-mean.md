# Weighted affine prime shells have their signed mean

- **ID:** weighted-affine-prime-shells-have-their-signed-mean
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Fix `q≥1`, `c>0`, `h≥1`, and a real `C²` profile `φ` supported in `[0,1]`.
Write `G(u)=∫φ(v)φ(v+u)dv` and `c_q` for the Ramanujan coefficient. Then

`Σ_{1≤k≤⌊X⌋} Λ(k)c_q(kn+b)G(hX/(ck))/k`

converges, uniformly over natural `n,b`, to

`[c_q(n)c_q(b)/ϕ(q)] ∫_(h/c)^1 G(u)/u du`.

Every prime power is retained. No prime-distribution premise is added.
The explicit tilted unit spline is included.

## Proof [PROVED HERE]

For any residue function `F`, the proved residue Mertens finite part gives
`R_F(T)=κ_F log T+C_F+e_F(T)`, where `e_F(T)→0`. The same formula holds at real
endpoints using `⌊T⌋/T→1`. Let `W` be `C¹` and vanish on a neighborhood of zero.
Real-endpoint Abel summation and integration by parts give the exact identity

`Σ_{k≤X} Λ(k)F(k)W(k/X)/k − κ_F∫_0^1 W(u)/u du`
`= W(1)e_F(X) − ∫_0^1 W′(u)e_F(Xu)du`.

Indeed, `∫W′=W(1)` cancels both `κ_F log X` and `C_F`, while
`∫W′ log u=−∫W/u`. Choose `α>0` below the zero neighborhood. The derivative
vanishes for `u<α`; on `[α,1]`, `Xu→∞` uniformly. Boundedness of `W′` therefore
makes the displayed error tend to zero.

Apply this to each of the finitely many residue indicators. Once their
errors have size at most `ε`, every signed `F` has error at most
`εΣ_r|F(r)|`. For `F(r)=c_q(rn+b)`, the proved unit-average identity is
`κ_F=c_q(n)c_q(b)/ϕ(q)`, and `Σ_r|F(r)|≤qϕ(q)`, independently of `n,b`.
This proves one common horizon for all affine parameters.

Set `a=h/c` and `W(t)=G(a/t)` for `t≠0`, with `W(0)=0`. Autocorrelation
support gives `W(t)=0` for `|t|<a`; thus the extension is `C²`. Put
`δ=a/(1+a)`. Its Mellin integral below `δ` vanishes. The proved reciprocal
shell substitution, after scaling, gives

`∫_δ^1 W(t)/t dt = ∫_a^(1+a) G(u)/u du = ∫_a^1 G(u)/u du`.

The last equality uses `G(u)=0` for `u≥1`. Substitution of `t=k/X` yields
the literal weighted prime source in the statement.

## Significance and status

This identifies the profile-weighted upward shell source with its signed
Ramanujan mean, uniformly in moving affine parameters. The existing
unweighted integer-window theorem does not identify this source or integral.
Full bounded-overlap norm quasimodes remain separate.

Summing all `1≤h<c` with shift `b=h` gives the literal source correction
`2/M Σ_h affineRamanujanPrimeShell`. Uniformly in `n`, it tends to
`c_q(n)[completeWeilAdjunctionEnergy − completedConductorEnergy]`.
The explicit tilted spline satisfies this law without a profile premise.

## Lean verification

Leaf: `CriticalArithmeticCorrelationTheory/TheWeightedAffinePrimeShellsHaveTheirSignedMean.lean`.

- `eventually_affineRamanujanPrimeShell_uniform`;
- `eventually_tiltedUnitSpline_affinePrimeShell_uniform`;
- `eventually_affinePrimeShellCorrection_energy_uniform`;
- `eventually_tiltedUnitSpline_affineShellCorrection_energy`.

Final direct no-olean check passed without warnings. All four axiom audits
report only `propext`, `Classical.choice`, and `Quot.sound`. CACT umbrella
import registered. Counted as one source contribution, including the Abel
transfer and finite-shell consequence.
