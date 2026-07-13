# First RH ladder--Hedenmalm simplicity collision

- **ID:** `rh-ladder-hedenmalm-simplicity-collision`
- **Stage:** 3-formalized
- **Type:** TOP-DOWN RH CHAIN / MULTIPLICITY COLLISION
- **Scientific status:** `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean parents:** `RHLadderTheory`, `XiHedenmalmEigenbasis`, `XiHedenmalmValueConstraint`
- **Lean module:** `formal/GaloisForLFunctions/RHTower/RHLadderHedenmalmSimplicityCollision.lean`

## Statement

The first RH ladder and simplicity of the centered Xi divisor are incompatible with any
right-half Xi zero:

\[
\texttt{RHLadder 1}+\texttt{XiZerosSimple}\Longrightarrow \mathrm{RH}.
\]

Indeed, the ladder forces every right-half Xi zero to have even positive analytic order, while
centered Xi simplicity forces the same order to equal one after the affine centered-coordinate
change.

The existing Hedenmalm corpus gives two source-facing entrances:

```text
first Hedenmalm quotient nonzero at every Xi divisor point
  -> XiZerosSimple
  + RHLadder 1
  -> RH,

Hedenmalm theta evaluation span dense in the Xi Hilbert carrier
  -> XiZerosSimple
  + RHLadder 1
  -> RH.
```

There is also a concrete source-to-source value relation.  Let `C` be the Hilbert closure of the
analytically continued prime--Gamma Cauchy source core and `H` the closure of the Hedenmalm theta
evaluation span.  Lean proves

\[
C\subseteq H\iff \texttt{XiZerosSimple}.
\]

The reason is local but not divisor-selective: `C` unconditionally contains the indicator of every
complete multiplicity fiber, whereas a multiple zero forces `H` into the coordinate hyperplane
annihilating that fiber.  Consequently

```text
continued Cauchy source closure contained in Hedenmalm theta closure
  -> XiZerosSimple
  + RHLadder 1
  -> RH.
```

## Attack and non-circularity

`RHLadder 1` alone permits right-half zeros of even order.  `XiZerosSimple` alone permits
off-critical simple zeros.  The contradiction is their intersection, not either premise renamed.

An unrestricted holomorphic Bezout certificate

\[
A\,\Xi C+B\,(\Xi C+i\Xi C')=1
\]

is not a stronger scientific input: over the holomorphic function ring of the upper half-plane it
is a reformulation of the absence of common zeros, hence of simplicity there.  It becomes a
genuine source construction only if `A` and `B` are produced in a specified prime--Gamma or theta
source algebra before reading the Xi divisor.  The present chain therefore reuses the already
formalized Hedenmalm simplicity interfaces instead of adding an unrestricted Bezout hypothesis.

## Open core

`[OPEN CORE]` Prove `RHLadder 1` from a source constraint, and independently prove one existing
Hedenmalm simplicity interface from source data.  The most concrete new value-relation target is
the inclusion of the analytically continued Cauchy source closure in the Hedenmalm theta closure.
Equivalently, prove that every continued-Cauchy multiplicity-fiber indicator can be approximated by
Hedenmalm theta evaluations.  The shorter pointwise interface is
`XiThetaFirstQuotientValueConstraint`.

Finite local jet algebra cannot be the whole provider: the current `HTGeometry` corpus proves
constrained Cauchy-jet controllability and positive polynomial escape after any disjoint finite
packet is frozen.  A successful proof must therefore use a cofinal/global closure constraint or a
source identity coupling infinitely many fibers.

## Gates

- [x] identify the even-versus-one multiplicity collision
- [x] identify existing Hedenmalm value and density interfaces for simplicity
- [x] formalize the direct collision and both source-facing corollaries
- [x] verify the exact Lean dependency and axiom surface
- [ ] construct the two independent source premises
- [ ] RH

## Formal verification

Lean proves the general positive-rung theorem
`riemannHypothesis_of_rhLadder_of_xiZerosSimple`, its first-rung specialization, the static
Hedenmalm-value corollary, and the theta-density corollary.  It also proves
`xiContinuedCauchyToHedenmalmClosure_iff_simple` and the resulting ladder-to-RH capstone.  The named
module build passes in the repository toolchain.  The declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.
