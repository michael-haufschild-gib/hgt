# Compact-Weil close-pair sampling collision

## Status

Paper proof and unconditional Lean formalization complete:
`GaloisForLFunctions.RHTower.CompactWeilClosePairSamplingCollision`.

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
