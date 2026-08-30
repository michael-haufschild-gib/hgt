# Compact-Weil close-pair sampling collision

## Status

Paper proof complete. Lean formalization of the algebraic split and collision identities is
unconditional in `GaloisForLFunctions.RHTower.CompactWeilClosePairSamplingCollision`, but the
quadratic derivative law still takes `hf : HasDerivAt f d x`. Under the pipeline's strict
no-premise gate, Hilbert structure alone cannot imply differentiability of an arbitrary function.
The generic quantifier and a hypothesis-free derivative conclusion are incompatible, so this
exact generic card cannot enter Stage 3 under that gate.

The corpus-owned profile `ccmGuinandWeilPolarCompactLaplace 1`, restricted to the real spectral
axis, is now handled in
`GaloisForLFunctions.RHTower.CompactWeilConcreteProfileCollision`. Its exported split, collision,
differentiability, and normalized quadratic-limit theorems have no Hilbert or differentiability
premises: the codomain is concretely `ℂ`, and differentiability is proved from the compact-support
integral. The closed capstone
`ccmGuinandWeilPolarCompactLaplaceReal_closePairCollision_closed` packages all four conclusions in
one premise-free theorem. All five declarations are targeted-built and depend only on `propext`,
`Classical.choice`, and `Quot.sound`. This discharges the structural hypotheses for that actual
profile. It does not prove arbitrary functions differentiable, so the generic card remains at
Stage 2 rather than silently replacing its quantifier by a special case.

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
