# Receiver Abel escape detects effective pole order

- **ID:** receiver-abel-escape-detects-effective-pole-order
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** review-2610 B3.2; the simple-zero restriction in actual receiver atom laws
- **Statement:** At a zero on the actual rightmost line, the finite-height Abel mass is governed by the positive difference between denominator and numerator vanishing orders. Unbounded effective pole orders force every compact window's normalized spectral mass to vanish.

## Exact target

Fix positive damping ε below Θ−1/2 and put θ=Θ−ε−1/2. At a zero
ρ with Re ρ=Θ, let m be the order of ζ at ρ minus the order at ρ−ε.
When m>0 and a is the leading Laurent coefficient of the centered receiver
symbol at ρ−ε, conjecture

`e^(2m−1) ∫window |Gε(θ+e+iy)|² w(y) dy → cm |a|² w(Im ρ)`,

where `cm=∫ℝ(1+x²)^(-m) dx>0`. For nonpositive order difference the local
mass remains bounded. On a compact height interval, the largest positive
order controls its growth. If effective pole orders on the rightmost line
are unbounded, global Abel mass grows faster than every fixed pole scale,
so each compact window has normalized mass tending to zero.

## Significance gate

The target removes simplicity and accounts for cancellation with multiplicity
in the actual source, then gives an infinite-height escape mechanism distinct
from nonsummability of simple residues. Count the whole classification at most
once, only after corpus novelty, paper proof, Lean, and significance audits.
The already drafted energy upper bound is infrastructure, not a separate
credited contribution. No claim about RH, bounded multiplicities, or residue
summability is made.

Audit decision: retain this as uncredited supporting mathematics. It removes
the simplicity restriction and makes the normalization and coefficients exact,
but its mechanism is local analytic factorization, rescaling, and finite gluing.
The review already places finite-height pole classification on the known side
of B3.2; its hard residue-summability and infinite-height tail questions remain.
The new multiplicity alternative alone does not establish a significant closing
input under the user's contribution standard.

## Gates

- [x] Precise source and missing restriction identified.
- [x] Initial corpus audit: existing ACP atom and capacity laws assume simple zeros;
  AOT already defines the effective order but does not supply this Abel classification.
- [x] Dependency-closed paper proof, including compact-window upper bounds.
- [ ] Exact Lean formalization and transitive axiom audit.

## Initial proof route

Use the actual-abscissa energy estimate to obtain the receiver's Laplace
symbol on every line to the right. Factor numerator and denominator at a
zero by their exact analytic orders. Rescale `y−Im ρ=e x`; the leading
pole gives the integrable kernel `(1+x²)^(-m)`, while lower Laurent powers
and holomorphic remainders disappear after scaling. Cover compact height
intervals by finitely many such neighborhoods and a regular complement.
A higher-order pole outside the interval provides a global lower bound
that dominates the interval's upper bound.

## Corpus findings

Reuse `ArithmeticOrientationTheory.visibleTranslatedZetaOrder`; do not introduce
a renamed invariant. `PaidKernelsCoverVisibleTranslatedZeroOrders` proves that
repairing kernels must supply this order. `PowerLogEigenstatesOfTheCofactorCountZetaMultiplicity`
classifies model power-log eigenspaces. Neither identifies the actual receiver's
Abel mass at multiple poles. Existing ACP `tendsto_window_atom` and capacity
laws use a simple-pole expansion.

For the local limit, a full Laurent expansion is unnecessary. Factor
`G(z0+z)=H(z)/z^m` with H continuous and H(0) nonzero. Substitution `y−y0=e x`
turns the scaled integrand into
`1_{|ex|≤δ}|H(e(1+ix))|²(1+x²)^(-m)w(y0+ex)`.
Its bound is a constant times `(1+x²)^(-1)` for m≥1; dominated convergence
gives the limit for every continuous locally bounded weight. This also removes
the Lipschitz restriction of the previous simple-pole proof.

Unbounded effective orders should imply the stronger assertion
`e^N A_{θ+e}(0,0) → +∞` for every natural N. A pole with `2m−1>N` supplies
the lower bound. Compact-window mass has some fixed polynomial upper bound,
obtained by a finite cover of analytic factorization neighborhoods. Its share
then tends to zero. Endpoint poles affect the exact atom weight of a clipped
window, but not this upper-bound argument.

## Status

Proof architecture and exact new consequence identified. Compact-cover
formalization and local rescaling theorem remain to be checked. No theorem or
contribution credited.

## Exact factor and compact control

Put `s₀=ρ−ε`, `D=ordρ ζ`, `N=ords₀ ζ`. Local analytic factorization gives
`ζ(s₀+z)=z^N u(z)` and `ζ(ρ+z)=z^D v(z)`, with `u(0)v(0)≠0`.
For `D=N+m`, `m>0`, the centered symbol is exactly

`Qε(s₀+z)=H(z)/z^m`,
`H(z)=u(z)(1−mε ζ(ρ+z))/((s₀+z)v(z))`.

The numerator is analytic, and `H(0)=u(0)/(s₀v(0))≠0` because ζ(ρ)=0.
Thus centering cannot cancel the surviving principal part. For `D≤N`, the
same quotient multiplied by `z^(N−D)` gives a bounded analytic extension.

For a fixed height window, apply
`HTGeometry.exists_finset_zeroFree_factorization` to the entire residue unit
on a larger ball. Every extracted zero has real part at most Θ. On
`Re s=Θ+e`, each factor `|s−ρ|` is at least e. The zero-free analytic factor
has a positive lower bound on the smaller compact ball. Hence the reciprocal
residue unit is at most `C e^(−K)` for a finite K. The receiver numerator and
the factors `1/s`, `1/(s−1)` are bounded on its translated compact rectangle,
chosen below `Re s=1`. Thus compact spectral mass is at most `C' e^(−2K)`.

The generic atom and compact inverse bounds are being formalized in
`TheAbelMassDetectsThePoleOrder.lean` and
`CompactWindowsHavePolynomialPoleGrowth.lean`. These are infrastructure for
the actual-source statement; neither has completed its audit.

## Global consequence and unconditional alternative

Let `T(e)=∫ℝ|Gε(θ+e+iy)|²dy=2π Aθ+e(0,0)`. A pole of effective order m
has a small window W with
`e^(2m−1)W(e)→cm|a|²>0`, and `0≤W(e)≤T(e)` by Plancherel and positivity.
For every integer `N<2m−1`,

`e^N W(e)=e^(−(2m−1−N))[e^(2m−1)W(e)]→∞`.

If effective orders are unbounded, choose such an m for each N. Then
`e^N T(e)→∞` and `e^N Aθ+e(0,0)→∞` for every natural N. For a fixed
compact interval J, the proved compact control gives `e^K WJ(e)≤C` for
some K. Therefore

`0≤WJ(e)/T(e)≤C/[e^K T(e)]→0`.

This produces an unconditional alternative for the actual source: its effective
orders on the rightmost line are bounded, or its Abel mass diverges at every
polynomial scale and its normalized spectral mass leaves every compact window.
The bounded-order branch does not assert tightness. Lower-order atoms vanish
at every higher pole scale by multiplying their finite scaled limit by a
positive power of e; no claim about summing infinitely many top-order atoms
is made without proof.

Formalization status: generic arbitrary-order atom and scaling/share lemmas
passed Lean with standard axioms only. Generic compact inverse bound passed.
Actual factorization, actual compact mass bounds, atom application, and global
alternative remain under verification. No contribution credited.

## Remaining sharp classification obligations

The polynomial compact bound suffices for unbounded-order escape, but it does
not identify the sharp largest order on a given compact interval. Finish that
part of the stated target: choose an interval whose endpoints are not boundary
zeros, list its finitely many boundary zeros, and partition into disjoint small
windows plus a compact complement. The complement has a uniform bound by
nonvanishing of the residue unit. At scale `e^(2M−1)`, poles of order M give
their atoms and lower orders vanish. Full cancellation gives a bounded analytic
extension. This proves the finite-height classification without a tail premise.

Use Mathlib's `meromorphicTrailingCoeffAt` to identify the canonical leading
coefficient, rather than leave the nonzero amplitude as an unnamed existential.
Its characterization by a nonvanishing analytic local factor was located and
read. The minimal scratch proof transporting `F(s+z)=H(z)/z^m` to the canonical
coefficient passed Lean and is included in the actual atom draft. This is
precision within the same contribution, not new contribution credit.

## Sharp compact law: complete paper argument

Take an interval `[a,b]` whose endpoints are not ordinates of boundary zeros.
The entire residue unit is not identically zero, so its zeros in a ball
containing the boundary segment form a finite set. Let Z be exactly those
with real part Θ and ordinate in `[a,b]`. Distinct points of Z have distinct
ordinates. Write `mρ=max(0,ordρ ζ−ordρ−ε ζ)` and `M=max(1,maxρ∈Z mρ)`.

Choose one positive δ smaller than every local factorization radius, every
distance to the endpoints, and half every distinct ordinate gap. The closed
windows `[Imρ−δ,Imρ+δ]` are disjoint and contained in `[a,b]`. At a point
with `mρ=M`, the local mass theorem gives
`cM |aρ|² w(Imρ)` at scale `e^(2M−1)`, with aρ the canonical coefficient.
When `0<mρ<M`, multiply its finite local limit by `e^(2(M−mρ))`, obtaining
zero. When `mρ=0`, the analytic extension gives a uniform bound on that box;
its finite-length integral tends to zero after the positive power scaling.

On the complementary rectangle, including `e=0`, the shifted residue unit
is nonzero: for `e>0` this is the defining zero-free half-plane of Θ; for
`e=0` a zero would belong to Z and violate the removed-neighborhood condition.
The numerator and `1/s` are continuous there. Compactness gives a uniform
bound B for the centered symbol. Thus the complementary weighted integral
has absolute value at most `B² sup|w| (b−a)`, and its normalized value tends
to zero. Add the finitely many local limits to get exactly

`e^(2M−1) ∫[a,b] |Gε(θ+e+iy)|²w(y)dy → Σρ∈Z,mρ=M cM|aρ|²w(Imρ)`.

For any continuous w, compactness bounds `|w|` on `[a,b]` by some W≥0.
Clipping w to `[-W,W]` gives a globally bounded continuous function equal to
w throughout the interval and at every atom. Apply the bounded-weight proof
to this clipping. Thus the final compact law has no global weight bound as a
premise and applies to every continuous test function.

No infinite sum, tail estimate, simplicity assumption, or noncancellation
assumption enters this argument. The draft formalization is
`CompactReceiverWindowsSelectTheMaximalVisibleOrder.lean`, supported by the
finite-boundary and finite-window integration modules. Its source check and
transitive axiom audit remain outstanding.

### Removing the abscissa-below-one restriction

The compact proof draft initially assumed Θ<1 to keep the shifted denominator
away from its removable pole at 1. That assumption must not remain an analytic
premise of the final classification. Since Θ≤1, split into Θ<1 and Θ=1.
In the second case, the known zero-free line Re s=1 makes Z empty. The residue
unit is nonzero on Re s≥1, including its value at 1. For `0<e<ε/2`, the
receiver's numerator stays in Re s<1 while its shifted denominator stays in
Re s>1. The same Mellin identity therefore holds; compactness bounds the
symbol down to e=0. Every compact mass multiplied by e tends to zero. This
is exactly the maximal-order formula for the empty zero set, M=1.

Implement and audit this case before stating the compact law without an
abscissa restriction. It does not assert divergence or tightness of total mass.
