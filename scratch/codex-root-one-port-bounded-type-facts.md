# One-port bounded-type fact (paper proof; Lean and novelty audits open)

Let `k` be the completed even theta source in `theta-one-port-variogram-pencil.md`,
`H(z)=∫₀∞ k(x)e^{izx} dx`, and `B(z)=-H(-z)/H(z)` for `Im z>0`. The corpus's
strict decrease of `k` on the positive ray proves `H` zero-free in the upper
half-plane; hence `B` is analytic there. The identity `Xi=H+H∘(-)` means `B=1`
is precisely the off-real connection collision. This is occurrence, not a
noncollision theorem.

## Fact: the literal connection map lies beyond bounded type

The first theta atom on `x≥0` is

`h(x)=4π² exp(9x/2)(1-(3/(2π))exp(-2x)) exp(-π exp(2x))`, and `k(x)≥h(x)>0`.
For `v→∞`, take `x_v=(1/2)log(v/(2π))`. Integrating on
`[x_v,x_v+1/v]` gives

`log H(-iv) ≥ (v/2)log v - O(v)`.

Indeed, the interval has length `1/v`; on it `v x≥v x_v`,
`πe^{2x}≤(v/2)e^{2/v}`, and the remaining first-atom factors are bounded
below by a positive constant for large `v`. Strict decrease gives
`0<H(iv)≤k(0)/v`. Thus

`log |B(iv)| ≥ (v/2)log v - O(v)`, so `log |B(iv)|/v→+∞`.

The same atom formula gives a matching leading upper scale. For `x≥0`,
`k(x)≤C exp(9x/2-π exp(2x))`: bound each higher atom by its first-atom
Gaussian and sum `n⁴ exp(-π(n²-1))`. Substitution `t=π exp(2x)` reduces the
majorant's Laplace transform to an incomplete Gamma integral with parameter
`(v+9/2)/2`. Stirling and the first-atom lower bound yield the sharper
paper-level limit

`lim_{v→∞} log |B(iv)| / (v log v) = 1/2`.

An analytic function of bounded type on the upper half-plane has a positive
harmonic majorant `u` for `log⁺|f|`. The positive harmonic representation (or
Harnack along the imaginary ray) yields `u(iv)≤v u(i)` for `v≥1`. Therefore
`B` is **not of bounded type**. Boundary `|B(u)|=1` does not put the actual
source connection in a Schur/inner/Smirnov class.

The one-sided `H` is entire of order at most one: the same Gaussian upper
envelope gives `log max_{|z|≤r}|H(z)|=O(r log r)`. If it had finitely many
zeros, the subquadratic finite-zero Hadamard theorem already in
`FiniteZeroSubquadraticRigidity.lean` would make it a polynomial times one
exponential character, contradicting the superlinear growth of `H(-iv)`.
Because `H` is zero-free on the closed upper half-plane, it has **infinitely
many zeros in the lower half-plane**. Consequently `B` has infinitely many
zeros in the upper half-plane. This is a paper deduction, not a new Lean
theorem; it has not been literature-audited.

For the finite exponential gauge `E_a(z)=exp(-iaz)H(z)`, the Hermite--Biehler
inequality at `z=iv` requires
`2av>log|B(iv)|`. Hence every fixed `a` fails; a height-dependent gauge
would need `a(v)≥(1/4+o(1))log v` even at this single ray. This does not
construct a lawful moving gauge or imply RH. It quantifies why fixed-aperture
one-port phase domination cannot be the missing source producer.

## Whole-route consequence and limits

This rules out a boundary-only inner-function or finite-harmonic-majorant
argument for the one-port connection. A lawful analytic strategy must retain
the source-selected superlinear interior growth, e.g. through an explicit
weighted/Carleman normalization, and then prove a theta-arithmetic constraint
on the value `1`. The result does **not** show `B≠1`; it is a no-go for a
method, not an RH proof. The analogous non-Nevanlinna ceiling for a different
Dirichlet seam is already noted in `goldilocks-divisor-rigidity.md`; this
source-specific one-port statement should not be called a literature-new
theorem before a proper novelty audit. No Lean theorem has been added.

**Decisive corpus falsifier:**
`docs/drafts/pipeline/2-fully-proven/theta-compact-critical-strip-zero-engineering.md`
constructs arbitrarily small positive, strongly log-concave perturbations
equal to `k` outside a fixed compact interval, preserving finite anchors and
all finite-prime-deletion right-ray positivity, but with a prescribed off-line
zero inside the Xi strip. Those perturbations have the *same first-atom tail*,
the same leading `log|B(iv)|/(v log v)=1/2`, and the same fixed-gauge barrier.
Therefore the growth/zero-infinitude theorem is **not a source-specific RH
producer**. Any proposed normalization based only on this asymptotic is
falsified by the same family; exact modular/Euler assembly is indispensable.
