# Compact-Weil close-pair sampling collision

## Status

Paper proof complete. Lean formalization of the algebraic split and collision identities is
unconditional in `GaloisForLFunctions.RHTower.CompactWeilClosePairSamplingCollision`, but the
quadratic derivative law still takes `hf : HasDerivAt f d x`. Under the pipeline's strict
no-premise gate this hypothesis must be produced for a concrete compact-Weil profile inside Lean;
Hilbert structure alone cannot imply differentiability of an arbitrary function. Stage 3 remains
open until that concrete profile and its differentiability are constructed.

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
