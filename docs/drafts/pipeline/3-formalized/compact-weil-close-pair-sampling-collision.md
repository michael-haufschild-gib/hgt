# Compact-Weil close-pair sampling collision

## Status

Formalized in Lean 4. `GaloisForLFunctions.RHTower.CompactWeilClosePairSamplingCollision`
contains the universal Hilbert-space split, exact collision identities, normalized-difference
identity, and mathematically sharp derivative implication. No analytic claim is assumed there:
the derivative premise is exactly the conditional clause stated below.

`GaloisForLFunctions.RHTower.CompactWeilConcreteProfileCollision` discharges all Hilbert and
differentiability structure for the corpus-owned profile
`ccmGuinandWeilPolarCompactLaplace 1` on the real spectral axis. The codomain is concretely `ℂ`;
differentiability is derived from the compact-support integral; and
`ccmGuinandWeilPolarCompactLaplaceReal_closePairCollision_closed` packages split, collision,
differentiability, and normalized quadratic limit without structural or differentiability
premises. Both modules are umbrella-wired. Direct checks, targeted builds, and `#print axioms`
audits pass; every exported theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Statement

For any real Hilbert-valued profile `f`, base point `x`, and separation `h`, two point-sampling
energies split exactly as

\[
\|f(x)\|^2+\|f(x+h)\|^2
=\frac12\|f(x)+f(x+h)\|^2+
 \frac12\|f(x+h)-f(x)\|^2.
\]

At `h=0`, the difference channel vanishes and the pair is one reporter with doubled weight. If
`f` is differentiable at `x` with derivative `d`, then

\[
\frac{\|f(x+h)-f(x)\|^2}{h^2}\longrightarrow\|d\|^2.
\]

Thus unrenormalized scalar point sampling loses one independent close-pair channel quadratically.

## Proof

First identity is parallelogram law. Collision statement is substitution. Last statement is norm
squared of derivative difference quotient.

## Research consequence

Compact-Weil ground calculations can lock many isolated ordinates while becoming ill-conditioned
on a coalescing pair. Separation-uniform multiplicity resolution cannot come from unrenormalized
point values alone; it needs derivative/divided-difference sampling, a multiplicity jet, or another
source law that pays the `h^-2` renormalization. This conclusion is symbolic and independent of
all computed zeta data.
