# Rational band poles survive the infinite affine Weyl sum

- **ID:** loop-eisenstein-rational-band-pole-noncancellation
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-0111/walls-ledger.md`, Σ19
- **Statement:** One rotation threshold preserves every zero of `Λ(s+1)` in `−1/2<Re s<0`, with its full multiplicity, in the level-four rational affine Weyl sum.

## Exact source
Let `λ(s)=(4−s,s)` and `c_w(λ)=Π_(β∈I(w)) Λ(λ(β∨))/Λ(λ(β∨)+1)`.
Use the existing affine Weyl group and degree exponent, with torus coordinates zero
and rotation coordinate `log R`, `R>0`:
`E_R(s)=Σ_w c_w(λ(s)) exp(weylExponent(λ(s),0,0,log R,w))`.
This is the full infinite Weyl expansion. Identifying it with an arithmetic
loop-group Eisenstein integral is a separate, still unfinished construction.

## Proof [PROVED HERE]
On `−1<Re s<2`, the root arguments are `4n+s` for positive roots `α+nδ`,
and `4n−s` for `−α+nδ`. Except for `α`, every argument has real part greater
than two. Its completed-zeta quotient is therefore analytic, nonzero and
bounded by `exp 2`, using the corpus's uniform right-half-plane quotient bound.

Remove `α` from each inversion product. Split the resulting Weyl terms into
`P_R(s)`, whose inversion set contains `α`, and `Q_R(s)`, whose set does not.
Exact finite-product factorization gives
`E_R(s)=Q_R(s)+[Λ(s)/Λ(s+1)]P_R(s)`.
Each remaining product has norm at most `exp(2 #I(w))`.
For `w=r_n` or `sr_n`, `#I(w)≤2|n|+1`, while the degree factor is
`exp(−R(4n²+ns))`, of norm at most `exp(−2Rn²)` on the strip.
The majorant `exp(2+4|n|−2Rn²)` is summable. It proves absolute and locally
uniform convergence, so both sectors are analytic on the entire strip.
It also dominates the strong-rotation limit for `R≥1`.
Only the identity and finite simple reflection have degree index zero;
they belong to opposite sectors and their remaining products equal one.
The remainder of each sector is bounded, uniformly on the entire strip, by
`2Σ_(n≠0) exp(2+4|n|−2Rn²)`. Dominated convergence makes this bound tend to zero.
Consequently `P_R→1` and `Q_R→1` uniformly on the strip as `R→∞`.
For one sufficiently large threshold, both sectors stay within distance one
of `1` everywhere on the strip and therefore have no zeros there.

Fix a band zero `s₀` of `Λ(s+1)`. Both completed-zeta factors are analytic
near `s₀`. The numerator `Λ(s₀)=Λ(1−s₀)` is nonzero by Euler-product
nonvanishing, since `Re(1−s₀)>1`. Above the uniform rotation threshold,
`P_R(s₀)≠0`; hence the cleared numerator
`Λ(s+1)Q_R(s)+Λ(s)P_R(s)` is nonzero at `s₀`.
The meromorphic order of `E_R` is exactly minus the zero order of `Λ` at
`s₀+1`, simultaneously at every band zero and every height.
Conversely, away from these denominator zeros the two-sector expression is
analytic. Thus every sufficiently strongly rotated Weyl sum has actual band-pole
support exactly `reflectionPoles`; its cardinal is the renormalized Hodge defect.

## Gates
- [x] Exact rational source and infinite sum; no assumed noncancellation.
- [x] Dependency-closed proof from the corpus's quotient bound and Gaussian degree series.
- [ ] Lean convergence, sector identity, full pole multiplicity and axiom audit.

## Boundary
The existing `reflectionPoles` definition counts denominator zeros. This theorem
supplies actual poles of the infinite rational Weyl expansion. It does not prove
that the band is empty, nor identify the expansion with the unipotent integral of
an arithmetic loop-group series. The function-field noncancellation proof supplies
the rotation mechanism; the rational continuation and two analytic sectors are the
missing bridge addressed here.
