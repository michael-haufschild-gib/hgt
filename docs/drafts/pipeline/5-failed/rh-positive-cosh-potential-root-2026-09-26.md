# Literal theta potential versus positive hyperbolic modes

- Owner: root, 2026-09-26.
- Stage: 5-failed. Conjecture refuted in Lean; strongest positive survivor paper-proved and Lean-closed. Not an RH proof.
- Goal: test an exact global source construction that could precede an all-order sign argument.
- Classification: [BRIDGE / REPRESENTATION TEST]. No Lee–Yang closure theorem for this entire class is assumed.

## Frozen conjecture C3

For `Phi=thetaCuspFullSource`, put `V(x)=log(Phi(0))-log(Phi(x))`.
Test whether there exist `q>=0`, summable nonnegative weights `a_n`, and frequencies `b_n>=0`, with every displayed series convergent, such that

`V(x)=q*x^2+sum_n a_n*(cosh(b_n*x)-1)` for every `x>=0`.

This is the positive independent-hyperbolic-mode ansatz, not the general interacting Ising programme. Corpus inputs: literal source envelope and first-atom lower bound; the open ferromagnetic source-incidence problem. No source match or stability-preserving implication is inferred from positivity of individual modes.

## Scientific test and paper proof

The literal complete source satisfies, for constants `C1,C2`,

`pi*exp(2x)-(9/2)*x+C1 <= V(x) <= pi*exp(2x)-(9/2)*x+C2` (`x>0`).

Indeed its first positive atom is a lower bound and the complete theta envelope is an upper bound, both with the same exponential and linear exponents. Thus `exp(-2x)*V(x)->pi`, while

`V(x)-2*pi*(cosh(2x)-1)->-infinity`.

For any positive-mode representation, a positive weight at `b>2` contradicts the finite scaled limit: its individual nonnegative mode grows faster than `exp(2x)`. Hence only frequencies at most 2 survive. Dominated convergence, using summability of the weights and `0<=exp(-2x)*(cosh(bx)-1)<=1` for `0<=b<=2`, gives the exact edge law

`lim exp(-2x)*V(x) = (1/2)*sum_(b_n=2) a_n`.

The quadratic term has zero scaled limit. Therefore the total weight at frequency 2 is exactly `2*pi`. Positivity of all remaining terms then forces

`V(x)>=2*pi*(cosh(2x)-1)` for every `x>=0`, contradicting the actual source's negative linear remainder. C3 fails.

## Strongest positive survivor and route consequence

The spectral-edge mass law and the resulting sharp pointwise floor are the nontrivial positive survivor. They expose which source datum a positive-mode construction loses: the actual negative linear correction, invisible after division by the leading exponential. A more general interacting or signed construction remains possible; no claim about all Ising realizations or RH follows.

All listed proof obligations are closed: literal logarithmic bounds, positive-series edge classification, source specialization, exact linear residual, and the stronger no-sublinear-repair theorem. No numerical experiment.

## Derived sharper survivor [BRIDGE; dependency-closed paper proof]

The same envelope sandwich proves the exact literal linear charge

`(V(x)-2*pi*(cosh(2*x)-1))/x -> -9/2` as `x->infinity`.

This follows by expanding `2*pi*cosh(2*x)=pi*exp(2*x)+pi*exp(-2*x)`: both bounding constants vanish after division by `x`, as does the decaying exponential.

Suppose an exact repaired representation is `V=P+r`, where `P` has the positive quadratic/mode form above and `exp(-2*x)*r(x)->0`. Then `P` has the same leading coefficient `pi`. The proved edge-mass argument forces `P>=2*pi*(cosh(2*x)-1)`, hence

`r(x)<=V(x)-2*pi*(cosh(2*x)-1)`.

Therefore, for every `eps>0`, eventually

`r(x)/x < -9/2+eps`.

This is an unavoidable signed correction of at least linear size, not a proposed sufficient condition for RH. In particular a bounded or sublinear correction cannot repair this positive-mode construction. Interacting constructions, nonsummable mode measures, and constructions with a different leading sector remain outside the tested class. No blanket Lee–Yang failure is asserted.


## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/ThetaPositiveCoshPotentialObstruction.lean`.

| Result | Declaration |
|---|---|
| No active frequency above the finite leading rate | `PositiveCoshEdge.active_frequency_le` |
| Exact edge mass and pointwise floor | `PositiveCoshEdge.edge_mass_and_floor` |
| Actual source logarithmic envelope | `ThetaCoshPotential.potential_bounds` |
| Actual leading exponential coefficient | `ThetaCoshPotential.scaled_potential_limit` |
| Closed C3 refutation | `ThetaCoshPotential.no_positive_cosh_representation` |
| Exact negative linear charge | `ThetaCoshPotential.potential_edge_linear_limit` |
| Necessary charge of any subleading correction | `ThetaCoshPotential.correction_eventually_le_linear` |
| Closed exclusion of every sublinear repair | `ThetaCoshPotential.no_sublinear_positive_cosh_representation` |

Namespaces have prefix `RHTower`. The two existential no-go statements have no input hypotheses. The general edge and correction laws explicitly expose their representation and convergence assumptions.

Verification: full scratch check passed; named leaf build passed (9109 jobs); all 16 public theorem axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`; none missing. Umbrella wired; corpus index refreshed; `scripts/formal_tools.py lint --check-generated` passed with existing large-file warnings. All owned proof/search/index/lint jobs exited. No git command or numerical experiment.

Internal audit: corpus deep searches for the positive-cosh source representation and spectral-edge mechanism inspected candidate lemmas, source arguments, ingredient suggestions and coverage. They found no ready literal-source representation or this complete test. Several retrievals were partial; complete source inventory does not imply complete proof applicability. General dominated-convergence edge extraction is a standard method; no global novelty or Lee–Yang closure claim is made. This card records the exact formal source obstruction and its quantitative survivor.
