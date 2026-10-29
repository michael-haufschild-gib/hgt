# Hecke theta Mellin continuation and unit unfolding

- **ID:** hecke-theta-mellin-continuation-and-unit-unfolding
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke and class-field programme](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md), HL7
- **Statement:** The actual Hecke theta Mellin integral unfolds over global units into the ideal-class series with its exact Gamma normalization, giving global continuation without class field theory.

## Actual theta and unit average

The finite-character theta inversion has the arithmetic trace dual,
explicit zero modes, and uniform exponential tails on bounded place
profiles. Summable Gaussian majorants prove joint continuity and local
integrability. These actual data discharge every field of the Mellin
pair; no abstract functional-equation or convergence premise is assumed.

Mathlib's actual weighted unit logarithms supply the lattice and torsion
kernel. The completed profile divides retained coordinates by their
place multiplicities and reconstructs the omitted coordinate from the
weighted-zero sum. Its actual fundamental domain has regulator volume,
compact closure, and bounded profiles. Integration gives the averaged
Poisson identity, both regulator-scaled zero modes, and Mellin continuation.

- [Actual theta Mellin pair](actual-hecke-theta-mellin-continuation.md)
- [Joint continuity](hecke-theta-joint-continuity-on-positive-parameters.md)
- [Actual unit domain](actual-unit-log-domain-and-regulator-volume.md)
- [Actual averaged Mellin pair](actual-unit-averaged-hecke-theta-mellin-continuation.md)

## Absolute orbit unfolding

Nonzero elements of a base ideal are indexed by actual global units and
integral ideals in its inverse ordinary class. The constructed generators
have principal ideal `I*b` and absolute field norm `Norm(I)Norm(b)`.
The actual units split as torsion times their logarithmic lattice.

This identifies the unit-orbit theta sums with logarithmic
periodizations. A summable paired Gaussian majorant proves finite
whole-space norm integrals by nonnegative unfolding before complex
integration. It then justifies both infinite exchanges. The average
minus its regulator-scaled zero mode equals the torsion order times the
sum of whole-log-space class integrals.

- [Ideal elements as unit orbits](hecke-ideal-elements-as-unit-orbits.md)
- [Actual torsion/log-lattice decomposition](global-units-as-torsion-times-log-lattice.md)
- [Logarithmic periodizations](hecke-theta-unit-orbits-as-logarithmic-periodizations.md)
- [Absolute unit unfolding](hecke-unit-domain-unfolding-is-absolutely-integrable.md)

## Exact Gamma and ideal-series normalization

The radial/log map `(q,l) ↦ q-P(l)` has measure pushforward density
`2^r2/[K:Q]`. The substitution `t=exp(2q)` contributes another factor two.
Each real logarithmic integral gives `GammaR(s+epsilon)/2`; each complex
one gives `GammaC(s)/4`, with Mathlib's convention
`GammaC(s)=2*(2*pi)^(-s)*Gamma(s)`.
Thus the actual scalar, including torsion, is

```
torsionOrder K / ([K:Q] * 2^(Units.rank K)).
```

The finite residue and real sign weights equal the principal-ideal
character, including noncoprime zeros. The exact norm integral separates
as the ideal-term norm times one finite archimedean mass. Absolute ideal
series convergence therefore permits the Mellin/class exchange on
`Re(s)>1`. Summing over actual coprime ordinary-class representatives with
inverse base weights gives Gamma times the full Hecke series.

- [Exact radial logarithmic Jacobian](hecke-radial-logarithmic-jacobian.md)
- [Archimedean Mellin integrals and arithmetic coefficients](hecke-archimedean-mellin-integrals.md)
- [Finite class recombination](hecke-l-series-as-finite-class-theta-sums.md)

## Continuation and closure

Actual ordinary-class descent and orthogonality cancel nontrivial
residues. Entire divided differences fill removable values, producing
ordinary global continuation and the proper Gamma completion. The
trivial ordinary L-function has exactly its positive simple pole at one;
nontrivial characters have entire ordinary and completed functions.

- [Global ordinary continuation](hecke-global-continuation-from-ordinary-classes.md)
- [Raw completed residues and removable values](hecke-unramified-character-descent-and-residue-cancellation.md)
- [Primitive arithmetic and dual character](hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- [Actual dual Mellin unfolding](hecke-dual-theta-unfolding-over-fractional-ideal-classes.md)
- [Primitive completed functional equation](primitive-hecke-l-functions-have-completed-functional-equation.md)

Every stated proof is formalized. Final direct source audits pass without
warnings, recorded main transitive axioms are only `propext`,
`Classical.choice`, and `Quot.sound`, and modules are wired into their
umbrellas without compiling them. The earlier provisional Jacobians,
normalizations, and scratch queues are superseded by these exact proofs.
No unfinished proof or scratch remains on this card. CFT remains paused.
