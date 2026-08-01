# Replica-collision Hamming tomography law

- **Stage:** 3-formalized
- **Status:** paper proof and Lean proof complete; external novelty audit open
- **Target:** universal-quantum-recurrence-anatomy master paper
- **Claim class:** exact finite-dimensional theorem

## Jump

Completed recurrence may contain more than a scalar moment law.  Its order-two
collision classes may reconstruct the product geometry of noninteracting
quantum components.

Let \(X=\prod_{c\in C}I_c\).  For \(x,y\in X\), let
\(\mathcal R(x,y)\) be the ordered pairs \((z,w)\) whose two-point histogram
agrees with that of \((x,y)\) in every component.  Conjecture:

\[
  \mathcal R(x,y)\simeq
  \{0,1\}^{\{c:x_c\ne y_c\}},
  \qquad
  |\mathcal R(x,y)|=2^{d_H(x,y)}.
\]

For arbitrary additive component spectra, the Boolean cube always injects
into the equal-energy class, so
\[
  |\{(z,w):E_z+E_w=E_x+E_y\}|\ge 2^{d_H(x,y)}.
\]
Mutual projective independence is the sharpness condition giving equality,
not a premise needed for the universal lower bound.

Thus order-two recurrence-collision multiplicity is exactly exponential in
component Hamming distance.  Minimal nontrivial classes recover Hamming-graph
adjacency; the maximal class exposes component count when every component has
at least two levels.

## Why this is not assembly

Existing ingredients show that factorization creates replica collisions.  The
new target turns those collisions into tomography: recurrence classes encode
the product metric between eigenvalue labels.  It upgrades
“factorization affects return” to “return collision structure measures how
many independent pieces distinguish two spectral states.”

## Falsifiers

1. A recombination satisfying every component histogram that is not obtained
   by independent component swaps.
2. Two swap choices on differing components producing the same ordered pair.
3. Failure when a component coordinate agrees; these coordinates must be
   removed from the Boolean choice set.
4. Literature already stating the exact recurrence-to-Hamming equivalence.
5. Inability to connect component-histogram classes to the formally proved
   spectral collision law without extra hypotheses.

## Proof route

1. Define componentwise recombination directly as coordinatewise identity or
   swap.
2. Construct explicit forward and inverse maps between Boolean choices on
   differing coordinates and recombination pairs.
3. Prove both inverse laws.
4. Take finite cardinalities to obtain \(2^{d_H}\).
5. Combine with component projective independence to identify these classes
   with exact equal-energy two-replica collisions.

All five steps are proved in
`formal/GaloisForLFunctions/HTGeometry/ComponentReplicaCollisionLaw.lean`.
The capstone theorem is `card_factorizedPairEnergyCollision`.

## Scope boundary

The theorem concerns exact additive component factorization and completed
finite-spectrum recurrence.  It does not infer a tensor decomposition from a
single scalar spectral-form-factor trace, nor claim feasible resolution time
without a detuning bound.

## Proof result

For every additive component spectrum,

\[
\#\{(z,w):E(z)+E(w)=E(x)+E(y)\}
  \ge 2^{d_H(x,y)}.
\]

For mutually projectively independent component spectra this is sharp:

\[
\#\{(z,w):E(z)+E(w)=E(x)+E(y)\}
  =2^{d_H(x,y)}.
\]

The proof first identifies equal two-copy energy with equality of every
component two-point multiplicity.  Equality of two-point multiplicities is
equivalent to unchanged-or-swapped labels in each component.  Independent
choices on precisely the differing coordinates give a Boolean cube, and its
cardinality is \(2^{d_H(x,y)}\).

This is stronger than scalar moment factorization: the collision class of
each spectral pair recovers its component Hamming distance exactly.

The operational bridge is also proved.  Every pair-resolved centered-time
phase kernel converges to the \(0/1\) indicator of componentwise
recombination:

\[
\lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}
 e^{it[(E_z+E_w)-(E_x+E_y)]}\,dt
=\mathbf 1_{\{(z,w)\in\mathcal R(x,y)\}}.
\]

Thus the Boolean cube is the support of an exact completed-recurrence
kernel, not a combinatorial analogy attached after the fact.

## External priority status

Initial exact-phrase and mechanism searches found literature on SFF moments,
independent-phase limits, quasi-free product spectra, partial SFFs and
Hamiltonian learning, but no source stating the recurrence-kernel/Hamming
equivalence or the bound \(2^{d_H}\).  In particular,
Campos Venuti--Odavić--Hamma derive exact SFF moments and quasi-free
product/log-normal laws
(<https://arxiv.org/abs/2505.05199>), but do not formulate pair-resolved
collision classes as a Hamming metric.

This is not yet a complete priority clearance.  The cardinality proof is
elementary once additive factorization is written in component coordinates;
a hostile reviewer may classify it as an unstated corollary unless the
pair-resolved recurrence observable, inverse-factorization consequence and
experimental distinction are made central and the ancestry search remains
negative.
