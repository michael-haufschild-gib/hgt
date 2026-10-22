# Reality is the shape of all consistent futures

- **ID:** `jointly-conservative-future-shape-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL PHYSICS CONJECTURE / NEW-MATHEMATICS TARGET / THEORY OF EVERYTHING
- **Status:** `[CONJECTURE] [TRUE-JUMP CANDIDATE] [NOVELTY UNVERIFIED]`
  `[OPEN CORE] [NO PHYSICS PROVED] [NATURE: DO NOT WRITE]`
- **Parents:** `dynamical-composition-universal-law.md`,
  `consequence-trirepresentability-universal-law.md`,
  `causal-arity-conservation-universal-law.md`,
  `hypertranscendental-capacity-descent-postnikov-tower.md`
- **Sharper source-square child:** `projective-source-square-universal-law.md`
- **Exact finite shadow:**
  `../../../3-formalized/not_new_scientific_knowledge/balanced-actuality-capacity-classification.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/FixedCarrierSpatialReciprocalBlindness.lean`

## Public law

> **The universe is not one future. It is the shape of every future that can consistently follow
> from now—and every force is a way that shape refuses to flatten.**

Time form:

> **The universe does not move through time. Time is the changing shape of what can consistently
> happen next.**

Unification form:

> **Quantum theory, spacetime, matter, and force are not separate ingredients. They are different
> views of one event-completion shape; each view forgets something, and together they lose
> nothing.**

These are conjectures about physical reality.

## What the corpus is saying

Every attempted one-object reconstruction failed for the same reason:

1. a primitive record does not select its higher composition;
2. a positive Gram record forgets its coherent root frame;
3. curvature does not recover the boundary self-law;
4. a fixed carrier turns source-changing transport into gauge-flat bookkeeping;
5. complete unpolarized topology does not select orientation or analytic effectivity;
6. a supplied future-test alphabet makes operational minimality circular;
7. a scalar arity does not record higher source coherence; and
8. finite differential-algebraic closure can forget unbounded source history.

The repeated mistake was to project a structured family of completions to one state, cone,
algebra, topology, or curvature and then ask that shadow to reconstruct the information discarded
by the projection.

The proposed jump is:

> **The fundamental object is neither one completion nor the intersection of facts common to all
> completions. It is the full polarized, effective, derived shape of consistent completion,
> including its automorphisms, torsors, higher compatibility defects, and source-changing
> correspondences.**

Degree-zero invariants are only facts. Nontrivial fibres, loops, higher obstruction classes, and
failure of global descent must remain available to become quantum phase, matter sectors, and
force.

## Mathematical conjecture

Let \(H\) be a finite raw source history containing distinctions, incidence, and counterfactual
incompatibility, but no Hilbert space, scalar field, positivity cone, tensor product, composition
law, causal order, spacetime, or force label.

Conjecture a source-generated higher object
\[
\mathfrak F^+(H)
\tag{FS1}
\]
whose points are source-positive, spectator-free, consequence-complete continuations of \(H\).
Its structure must retain:

1. active source incidence and all higher coherence;
2. positive polarization and analytic effectivity;
3. sequential and independent composite outcomes;
4. boundary colligations, including boundary self-laws;
5. presentation equivalences and nontrivial automorphisms; and
6. controlled continuation and comparison data.

The physical object is provisionally the **full derived polarized descent object**
\[
\mathsf{Phys}(H)
\overset{\mathrm{conj}}{=}
\mathbb R\Gamma_{\mathrm{pol,eff}}\!\left(\mathfrak F^+(H),\mathcal O_H\right),
\tag{FS2}
\]
not only \(H^0\), a coarse quotient, or an invariant subalgebra. Notation `(FS2)` names a theorem
target; no site, sheaf, coefficient algebra, positivity, or derived category may be supplied in
its definition.

An event \(e:H\rightsquigarrow H'\) induces a noninvertible correspondence
\[
\mathfrak F^+(H)
\xleftarrow{\ r_e\ }
\mathfrak F^+(e)
\xrightarrow{\ s_e\ }
\mathfrak F^+(H').
\tag{FS3}
\]
Time is composition of the source-generated pull--push operations of `(FS3)`.

## Joint conservativity, not faithful copies

The earlier trirepresentability programme asked coherent, positive, and compositional
representations to be individually faithful. The exact corpus argues against that formulation:
each physical face has a real kernel.

The corrected law asks for three source-generated reporters
\[
\mathcal Q_H,\qquad \mathcal C_H,\qquad \mathcal L_H
\tag{FS4}
\]
from `(FS2)`, interpreted only after reconstruction as coherent possibility, positive causal
record, and successor composition law. Each reporter may be nonconservative. The family must be
jointly conservative:
\[
\boxed{
\ker D\mathcal Q_H
\cap
\ker D\mathcal C_H
\cap
\ker D\mathcal L_H
=0,
}
\tag{FS5}
\]
with a higher analogue reflecting equivalences and obstruction classes, not merely tangent
vectors.

Minimality means no reporter, direction, or higher cell can be deleted while retaining joint
conservativity. It does not mean equal dimensions.

The stronger temporal conjecture is that source succession rotates the role of one consequential
distinction:
\[
\text{coherent possibility}
\longrightarrow
\text{positive fact}
\longrightarrow
\text{successor law}
\longrightarrow
\text{new coherent possibility}.
\tag{FS6}
\]
Only a stationary regular phase of this source-derived rotation could force equal finite role
capacity. This is the missing nonnumerological antecedent for the formalized \(4/4/4\)
classification; equality may not be inserted directly.

## Exact finite shadow now in Lean

For a complex rectangular carrier \(D\) and variation \(E\), define
\[
\mathcal R_D(E)=
\left(
\operatorname{Herm}(D^\dagger E),
\operatorname{Skew}(D^\dagger E),
E-D(D^\dagger E)
\right).
\tag{FS7}
\]

Lean proves unconditionally:

1. `reciprocalDomainFirstVariation_eq_two_smul_localHermitianResponse`:
   the first Gram reporter is exactly twice the Hermitian coordinate of `(FS7)`; and
2. `variationThreeFaceReport_injective`:
   the complete three-face report `(FS7)` is injective.

Thus the finite carrier has a literal jointly conservative decomposition:

```text
public first record          = Hermitian face
in-frame comparison          = skew face
first-order-hidden remainder = transverse face
all three together           = complete variation.
```

This is ordinary matrix algebra. It does not prove that the three faces are physical, that their
capacities must balance, or that nature uses a complex rectangular carrier.

## New source-cocycle bridge

The paper-proved and Lean-formalized
[`projective-source-visibility-parity-law.md`](../../../3-formalized/not_new_scientific_knowledge/projective-source-visibility-parity-law.md)
shows that joint conservativity need not be an unrelated axiom.

If two linear source changes obey
\[
AB=\zeta BA,\qquad \zeta\ne1,
\]
then the pair of individually lossy defect reporters
\[
v\longmapsto(v-Av,\;v-Bv)
\]
is injective. For the retained order-two source pair \(J,S\), the same relation
\(JS=-SJ\):

1. generates the local complex orientation \((JS)^2=-1\);
2. kills the common fixed sector of the two source changes; and
3. makes every odd symmetric successor layer jointly visible, while every even layer of the
   standard binary source has an explicit invisible sector.

This identifies phase, joint visibility, and successor parity as three shadows of one projective
source cocycle. The result is elementary parent algebra and proves no physics. Its research
consequence is stronger: the completion-shape programme should derive reporter conservativity
from nontrivial coherence of source-changing completion functors, not impose `(FS5)` independently.

The sharpened higher target is:
\[
\boxed{
\text{nontrivial source coherence}
\Longrightarrow
\text{jointly conservative homotopy-defect reporters}.
}
\tag{FS5a}
\]

The key falsifier is now clear. If the completion object admits nontrivial coherent source
commutators but still has a noncontractible common homotopy-fixed sector invisible to all induced
defects, the finite bridge does not lift and `(FS5a)` fails.

Neighbouring exact shadows:

- the regular \(M_{3,2}(\mathbb C)\) Gram fibre is an \(SU(3)\)-torsor, so the positive public
  record does not canonically choose its coherent frame; the formalized source-colour no-go shows
  this Gram-frame action is not the fixed-bracket automorphism action of the three projective
  source directions;
- primitive interior arity of \(H_q(\mathbb C)_+\) is exactly \(q\);
- balanced Hermitian, skew, and transverse capacities force \(d=2,n=2r\), and primitive \(r=1\)
  gives \(M_{3,2}(\mathbb C)\);
- thin edge-supported Hochster sources carry coherence in growing degrees, so local binary
  support does not determine the full source-completion profile; and
- the HT minimal-completion architecture proves that several natural realization channels are
  individually nonconservative.

## Proposed physical projections

Every arrow is an open derivation obligation:

```text
raw event source
  -> polarized effective completion shape
  -> jointly conservative coherent / causal / compositional reporters
  -> positive linearization and complex quantum probability
  -> causal rank and event-generated Lorentz future
  -> source-changing comparison correspondence
  -> vertical / anchored / mixed obstruction sectors
  -> gauge forces / gravity / matter
  -> continuum Einstein--Dirac--Yang--Mills--Higgs dynamics.
```

The intended sector distinction is structural:

- **quantum phase:** automorphism and holonomy of coherent lifts;
- **causal order:** positive descent-compatible “can become next” relation;
- **spacetime:** effective public geometry of the causal reporter;
- **internal gauge forces:** vertical curvature preserving one generated causal object;
- **gravity:** anchored obstruction to gluing generated causal objects and their clocks;
- **matter:** stable mixed descent sectors transported through repeated source change; and
- **Hypertranscendence:** failure of any finite differential-algebraic reporter family to remain
  jointly conservative through complete history.

This list is not a result. A proof must derive the distinction between vertical and anchored
responses, their exact relative normalization, and why precisely
\(U(1)\), \(SU(2)\), \(SU(3)\), and gravity survive with no fifth force.

## Why scalar causal arity is not enough

The Lean theorem
\[
\alpha_{\rm fut}\!\left(H_q(\mathbb C)_+\right)=q
\]
remains exact. But the source side cannot be the size of a local face, minimal nonface, or
operation input. The formalized cycle examples have only two-element facets while their
source-coherence classes occur in degrees \(2,3,4\), and the corpus realizes arbitrary deep
coherence on thin support.

Therefore the likely conserved source datum is a **complete consequence profile**—a derived
support, coherence, polarization, and effectivity spectrum—not one scalar arity. Future cone rank
is one shadow of that profile. Causal arity conservation may survive only as a corollary of the
full joint-conservativity theorem.

## Parent and priority boundary

Occupied parents include:

1. spaces of QFTs and theory-space geometry;
2. formal moduli problems, derived stacks, BV geometry, and derived deformation theory;
3. Segal, \(2\)-Segal, decomposition-space, and higher-categorical composition;
4. state-and-effect triangles, effectus theory, and operational process categories;
5. locally covariant QFT and dynamical locality;
6. quantum causal histories, process matrices, and indefinite causal order;
7. higher gauge theory and noninvertible higher-categorical symmetry; and
8. ordinary descent, hypercohomology, obstruction theory, and moduli correspondences.

Representative direct parents include
[Douglas](https://arxiv.org/abs/1005.2779),
[Calaque--Grivaux](https://arxiv.org/abs/1802.09556),
[Dyckerhoff--Kapranov](https://arxiv.org/abs/1212.3563),
[Alfonsi--Young](https://arxiv.org/abs/2307.15106),
[Fewster](https://arxiv.org/abs/1502.04642), and
[Hawkins--Markopoulou--Sahlmann](https://arxiv.org/abs/hep-th/0302111).

Candidate novelty is not using stacks, descent, higher categories, theory space, or
correspondences. It is a source-only construction whose base, positivity, scalar algebra,
composition, causal cover, and physical equivalence are all outputs, followed by a rigidity
theorem reconstructing observed physics and a new prediction.

## Hostile falsifiers

Retire or sharply revise the conjecture if any survives serious repair:

1. \(\mathfrak F^+(H)\) requires a supplied spacetime, Hilbert space, tensor product, positivity,
   future-test alphabet, or process category;
2. free or cofree completion satisfies every source axiom;
3. `(FS2)` is ordinary descent on a renamed fixed site;
4. joint conservativity is made tautological by including an identity reporter;
5. polarization or analytic effectivity is chosen after reading the desired physical sector;
6. stationary role rotation does not force capacity balance;
7. real, quaternionic, exceptional, higher-rank, tensor-padded, or fifth-force phases satisfy the
   same source law;
8. vertical gauge and anchored gravitational responses retain unrelated free normalizations;
9. all event correspondences totalize into an ordinary fixed theory preserving every claimed
   physical distinction; or
10. no quantitative prediction differs from GR plus the Standard Model.

## Exact open core

`[OPEN CORE: ENDOGENOUS JOINTLY CONSERVATIVE COMPLETION SHAPE]`

Construct one finite raw event source \(H\) and one extension \(H\rightsquigarrow H'\) for which:

1. \(\mathfrak F^+(H)\) is defined without target physics and has at least two inequivalent
   source-positive completions;
2. its polarization, effectivity, spectator criterion, and higher comparisons are source-derived;
3. coherent, causal, and compositional reporters are each nonconservative but jointly
   conservative in a nontrivial higher sense;
4. source extension rotates one consequential class through the three reporter roles;
5. the first regular irreducible stationary realization uniquely forces complex
   \(M_{3,2}(\mathbb C)\), \(H_2(\mathbb C)_+\), and distinct weak and Lorentz actions; and
6. two-event independent composition fixes a relative scale or produces another finite
   falsifiable relation.

No further physics promotion is authorized until items 1--4 close on paper. Every exact
mathematical dependency must then be formalized unconditionally in Lean.

## Nature gate

- [x] universal headline and technical conjecture separated from proved shadows
- [x] one-shadow reconstruction failures synthesized
- [x] scalar local-arity realization attacked
- [x] first finite joint-conservativity shadow formalized in Lean
- [x] direct moduli/derived/Segal/QFT parent classes identified
- [ ] source-generated completion shape constructed
- [ ] nontrivial higher joint-conservativity theorem proved
- [ ] stationary role rotation and capacity balance derived
- [ ] unique complex \(3\times2\) phase classified
- [ ] quantum probability and \(3+1\) causal spacetime reconstructed
- [ ] exact four-response split and relative normalization derived
- [ ] continuum dynamics and equivalence principle derived
- [ ] new finite prediction obtained
- [ ] exhaustive specialist novelty audit passed
- [ ] every mathematical claim unconditionally Lean-proved

## Log

- 2026-07-30 — replaced individually faithful trirepresentations by individually lossy,
  jointly conservative reporters.
- 2026-07-30 — replaced invariant-only continuation by full polarized derived completion shape;
  invariant intersection would discard torsors, orientation, and higher obstruction classes.
- 2026-07-30 — used thin-support/deep-coherence theorem to reject local source arity as complete
  invariant.
- 2026-07-30 — formalized injectivity of the finite Hermitian/skew/transverse report and exact
  identification of the first Gram reporter with its Hermitian face.
