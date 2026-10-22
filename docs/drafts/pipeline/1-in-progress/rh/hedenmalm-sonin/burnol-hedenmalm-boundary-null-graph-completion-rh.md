# Burnol--Hedenmalm boundary-null graph completion for RH

- **ID:** `burnol-hedenmalm-boundary-null-graph-completion-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]` / CONTRADICTION ROUTE
- **Scientific status:** `[OPEN] [ROUTE C1 SURVIVOR] [CONDITIONAL RH ENDPOINT] [GENERIC GRAPH SUBROUTE RETIRED]`
- **Frontier owner:** Route C1 — complete Xi-Weil/Hedenmalm-form positivity
- **Statement:** A source-defined singular graph completion of Burnol's critical Sonine carrier
  which adjoins the completed common source as a null boundary vector, retains the divided-zero
  family faithfully, and makes centered coordinate multiplication symmetric proves RH and the
  simplicity of every nontrivial zeta zero.

## Goal

Construct the missing carrier rather than assume a spectral list.  The input space must be defined
from the Sonine/co-Poisson and archimedean theta sources before its zero vectors are enumerated.
Burnol then supplies completeness and minimality of the divided family; Hedenmalm supplies the
completed coordinate recurrence.  The only open theorem is the singular boundary-null graph
construction joining them.

## 1. Desired source-side object `[CONJECTURE]`

Let `E` be a source-defined linear core obtained from Burnol's critical extended Sonine space by
the archimedean completion multiplier, enlarged only as needed to contain the common source `XiC`
and the first two removable divided levels.  Construct:

```text
J:E -> H,
S:dom(S) subset H -> H,                                  (1)
```

where `H` is a Hilbert space and `S` is closed and symmetric, such that:

```text
(G1) J(XiC)=0;
(G2) J(Q_(alpha,1))!=0 for every XiC zero alpha;
(G3) J(Q_(alpha,1)),J(Q_(alpha,2)) are in dom(S)
     whenever those levels exist;
(G4) S J(Q_(alpha,k+1))
       =alpha J(Q_(alpha,k+1))+J(Q_(alpha,k)),  k=0,1;
(G5) E, J, the graph norm, and positivity are defined from
     theta/Sonine/co-Poisson data, not from the Xi divisor.           (2)
```

Condition `(G5)` is the anti-circularity gate.  A direct sum indexed by zeros, a metric whose
weights are assigned after listing the divisor, or the declaration `XiC=0` does not discharge it.

## 2. Contradiction endpoint `[PROVED CONDITIONALLY]`

Assume `(G1)`--`(G5)`.  If RH is false, functional-equation and Schwarz symmetry give a nonreal
centered Xi zero `alpha`.  Put

```text
v=J(Q_(alpha,1)).                                        (3)
```

By `(G2)`, `v!=0`; by `(G1)` and `(G4)`,

```text
S v=alpha v.                                             (4)
```

Symmetry gives

```text
alpha ||v||^2=<S v,v>=<v,S v>=conj(alpha)||v||^2,         (5)
```

contradicting `alpha` nonreal.  Hence every centered zero is real and RH follows.

If a zero has multiplicity at least two, set `w=J(Q_(alpha,2))`.  The second recurrence gives

```text
(S-alpha)w=v,
(S-alpha)v=0.                                            (6)
```

Symmetry then yields

```text
||v||^2=<(S-alpha)w,v>=<w,(S-alpha)v>=0,                 (7)
```

again contradicting `(G2)`.  Thus the same carrier also proves simplicity.

Both ends of the contradiction chain are closed.  The route stops at one construction theorem,
not at an unspecified appeal to self-adjointness.

## 3. What the parent theories discharge

Burnol's source-defined Sonine space discharges:

1. Hilbert membership of `zeta(s)/(s-rho)^k` for every required multiplicity level;
2. completeness and minimality of that divided family;
3. a complete triangular biorthogonal evaluator system;
4. co-Poisson source presentations for prime-dilation defects.

Archimedean completion and Hedenmalm's theta problem discharge:

1. rapid decay of `XiC` and every fixed removable quotient on the real axis;
2. maximal-domain membership for centered coordinate multiplication;
3. the exact common-source recurrence;
4. the symmetric-eigenvector contradiction once the source is null and the quotient is faithful.

The proved domain--radical exchange law shows why neither parent alone closes the route.

## 4. Exact open core

> **[OPEN CORE]** Construct a positive singular boundary form `q` on a source-defined completion
> of the completed Burnol carrier such that `q(XiC,XiC)=0`, every first divided vector has positive
> norm, and centered coordinate multiplication is symmetric and graph-closed on the first two
> divided levels.

The form must be singular relative to ordinary `L^2`.  Existing corpus theorems rule out every
nonzero absolutely continuous Fourier multiplier, finite-order local metric, and closable
translation-stable `L^2` realization.  That no-go has a positive consequence: the search is
reduced to boundary forms or rigged completions whose null relation is imposed by a source trace,
not by an `L^2` density.

## 5. Candidate construction tests

Any proposed provider must pass all five tests before Lean work begins:

1. **Critical-aperture test:** obtain the null relation as a boundary term of Burnol's nested
   Sonine/co-Poisson apertures, rather than as an imposed quotient.
2. **Archimedean graph test:** prove the completion multiplier sends the boundary graph into a
   closed centered-coordinate graph and identify its defect exactly with `XiC`.
3. **Faithfulness test:** use Burnol minimality or the biorthogonal evaluator system to prove that
   no first divided vector enters the radical, without choosing per-zero weights.
4. **Symmetry test:** make the two coordinate boundary terms cancel on the source core; formal
   symmetry only on the already selected eigenfunction span is insufficient.
5. **Multiplicity test:** retain the second divided level so that a multiple zero produces the
   forbidden Jordan step rather than disappearing from the carrier.

After the detour audit below, the only provider still specific enough to remain live is a
**Burnol-specific critical-aperture trace identity**.  A generic renormalized graph limit,
boundary-triplet/Weyl function, de Branges extension, or functional-calculus regularization merely
repackages the already classified translation-defect form.  The live theorem must use a concrete
co-Poisson/Sonine aperture relation that is absent from the generic entire-function model, with
Gamma completion performed before the boundary limit.

## 6. Long-detour audit

Four substantially different constructions were tested against `(G1)--(G5)`.

### Critical-aperture graph limits

A positive `L^2` graph limit on the real boundary sees only the real divisor measure.  Its radical
contains precisely the analytic fibres not represented on that real boundary.  Requiring the
completed Burnol quotient family to survive faithfully is therefore equivalent to requiring that
there be no off-real fibre.  This is the same faithfulness gate already proved for the theta
convolution cokernel and the translation-invariant defect form.

**Positive statement:** a critical-aperture construction can be a genuine provider only if it
proves a new source trace identity before passing to the real-boundary Hilbert completion.  Mere
existence or closability of the graph is insufficient.

### de Branges and boundary-triplet extensions

In a de Branges model, coordinate multiplication is symmetric, but the reproducing kernels at
nonreal points are deficiency vectors of the adjoint rather than eigenvectors of a self-adjoint
extension.  Making the Xi divisor the spectrum of one self-adjoint extension requires exactly the
Hermite--Biehler orientation that the construction is meant to prove.

**Positive statement:** the missing datum is one source-selected self-adjoint boundary condition
whose Weyl function has the Xi numerator; abstract extension theory and the completed divisor do
not select it.

### Green and Moore--Penrose regularizations

Functional calculus can close the real coordinate graph and can annihilate a prescribed range,
but any positive regularization commuting with real translation factors through a positive real
spectral measure.  It therefore loses the off-real primary fibres or imports their absence as
faithfulness.

**Positive statement:** a successful Green operator must fail ordinary translation invariance in
one explicit, source-controlled boundary term.  That boundary term, rather than the regularized
inverse, is the actual theorem to construct.

### Burnol mixed systems and hereditary completeness

Burnol's 2011 theorem says that every admissible mixture of divided-zeta vectors and dual zero-jet
evaluators has closed-span codimension at most one.  An off-line functional-equation quartet does
not force a nonzero mixed-system complement: the complement conditions require a function that is
simultaneously orthogonal to the selected divided vectors and zero to the prescribed orders at the
unselected fibres, and divisor location alone constructs no such function.  If a complement does
exist, Schwarz and functional-equation symmetries act on it by involutions; a one-dimensional
invariant complement is compatible with both because the antiunitary squares to `+1`, not `-1`.

This is not merely a missing trick.  Baranov--Belov--Borichev prove the same codimension-at-most-one
phenomenon for broad exact systems of reproducing kernels in de Branges spaces, where a
one-dimensional defect genuinely occurs and is not a real-spectrum criterion.  Therefore
near-hereditary completeness is divisor-location blind unless an additional source relation
constructs a nonzero complement from an off-line orbit.

**Positive statement:** Burnol's mixed-system theorem reduces any hereditary-completeness RH route
to one sharp new lemma:

```text
off-line Xi orbit
  -> two linearly independent source-constructed mixed complements.          (13)
```

The codimension theorem would then give an immediate contradiction.  No current Sonine,
co-Poisson, functional-equation, or conjugation identity supplies even the first complement, so
`(13)` is a strictly stronger and more honest target than “use hereditary completeness.”

## 7. Failed shortcuts and positive residues

- **Ordinary completed `L^2`:** coordinate multiplication is self-adjoint but `XiC` is nonzero,
  so divided quotients are defect vectors rather than eigenvectors.  **Positive residue:** the
  operator-domain half of the construction is already solved.
- **Quotient by `span(XiC)`:** that span is not invariant under coordinate multiplication, so the
  quotient operator is not defined.  **Positive residue:** use a graph quotient whose boundary
  relation, not merely its vector quotient, is invariant.
- **Translation-invariant positive metric:** killing `XiC` forces the spectral measure onto the
  real Xi divisor and makes positivity RH-bearing.  **Positive residue:** a successful metric must
  be singular and boundary-generated; this sharply identifies its allowed category.
- **Burnol completeness alone:** the first divided vectors lie outside the uncompleted coordinate
  domain.  **Positive residue:** the complete/minimal system is a ready-made faithfulness detector
  after archimedean graph completion.

## Literature calibration

- J.-F. Burnol, *On the system of the functions zeta(s)/(s-rho)^k*,
  [arXiv:1106.4751](https://arxiv.org/abs/1106.4751), Theorems 1--2.
- A. Baranov, Yu. Belov, and A. Borichev, *Hereditary completeness for systems of exponentials and
  reproducing kernels*, [arXiv:1112.5551](https://arxiv.org/abs/1112.5551).

## Dependencies

- `../2-fully-proven/not_new_scientific_knowledge/burnol-hedenmalm-archimedean-completion-domain-radical-exchange.md`.
- `../2-fully-proven/not_new_scientific_knowledge/burnol-prime-dilation-copoisson-quotient-law.md`.
- `../2-fully-proven/new_scientific_knowledge/hedenmalm-pair-weil-polarization-law.md`.
- `../2-fully-proven/new_scientific_knowledge/hedenmalm-theta-pair-divisor-supported-metric-law.md`.
- `../../../3-formalized/not_new_scientific_knowledge/hedenmalm-divided-chain-symmetric-carrier-law.md`.

## Gates

- [x] well-posed contradiction chain
- [x] both logical endpoints proved
- [x] operator-domain and metric-radical defects separated
- [x] source-purity and non-circularity tests explicit
- [x] positive statements extracted from every failed shortcut
- [x] critical-aperture, de Branges, Green-regularization, and hereditary-completeness detours
      tested
- [x] generic boundary-null graph route identified with the existing real-boundary faithfulness
      obstruction
- [x] Burnol-specific positive successor isolated as an aperture trace identity or the
      two-complement implication `(13)`
- [ ] construct the critical-aperture boundary-null graph form
- [ ] prove source-side positivity without Weil/RH input
- [ ] prove faithfulness on the first divided family
- [ ] close and symmetrize centered coordinate multiplication
- [ ] formalize only after the analytic construction exists on paper
