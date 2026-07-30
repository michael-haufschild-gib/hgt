# Faithful reflection-Tate conormal localization and RH

- **ID:** `faithful-reflection-tate-conormal-localization-rh`
- **Stage:** 5-failed
- **Type:** RETIRED RH ROUTE / REUSABLE SUPPORT REDUCTION
- **Scientific status:** `[PAPER-PROVED REDUCTION] [LEAN-FORMALIZED]`
  `[ROUTE RETIRED: CORPUS-EQUIVALENT] [PARITY-BLIND] [NOT RH]`
- **Parents:**
  - `../3-formalized/gamma-dihedral-orbifold-bulk-mirror-anomaly.md`;
  - `../3-formalized/clock-compass-noncommutative-tomography.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/source-face-observation-cohomology-transmutation.md`;
  - `../2-fully-proven/prime-winning-cech-divisor-resolution.md`;
  - `source-localization-modular-defect-conservation-law.md`;
  - `polarized-critical-rees-corona-transgression-rh.md`.

## Corrected verdict

This reduction is valid, but it is not an independent source mechanism.  The required
left-invertible reporter is exactly the already isolated
`[XI_INTERNAL_REFLECTION_RANK_NONCREATION]` hypothesis in different language: it assumes that an
individual principal-conormal ray cannot become a free reflection pair.  That is the
RH-bearing statement, not a consequence of Tate cohomology.

The corpus gives two sharper falsifiers.

1. `RHTower/WeightMismatchRefutation.lean` proves that every off-line Xi quartet has even total
   reflection weight.  Mod-two orbit data do not distinguish the critical line.
2. `RHTower/HalfChargeConservation.lean` and `RHTower/HalfChargeSeamCompat.lean` prove that an
   off-line conjugate pair can deposit an even seam order while preserving every parity
   constraint.  Endpoint parity cannot distinguish a genuine on-line zero from a deposited
   pair-collision residue.

Therefore no reflection-Tate or parity reporter can *construct* the required left inverse from
the source.  The formal theorem survives only as a terminal fixed-support lemma: if some stronger
source-history invariant has already reconstructed every individual conormal charge from the fixed
locus, then RH follows immediately.

## Corpus correction

Positivity is not the missing selector. The corpus already proves explicit off-line Euler systems
with positive source, functional equation, entire completion, hypertranscendence, and positive
unsquared orientation. It also proves that generic normality, hyperrigidity, one faithful positive
split, and finite Hermiticity do not supply RH.

The corpus also rules out the naive formulation of a single “third completion.” Every finite
prime-winning source fibre is a full simplex. The normalized augmented-simplex contraction and
arbitrary direct-sum exactness are already formalized in
`HTGeometry/SimplexAugmentedContraction.lean`. An additive functor preserving that homotopy also
preserves its contractibility. Exact derived Cartier base change cannot then create a nonzero
conormal fibre. This is the same obstruction proved abstractly by the source-face observation
transmutation theorem: derived specialization preserves homotopy fibres; the nonzero class can
only occur when ordinary cohomology, a topology, a domain, or a truncation fails to commute with
specialization.

Therefore the missing object is not one Hausdorff completion simultaneously preserving the full
contraction and a nonzero Xi fibre. It must be a **fracture square of incompatible realizations**,
with the conormal carried by their comparison anomaly.

## Fixed-locus anomaly law

Let \(I\) be a label set with involution \(r\). On the finitely supported integral permutation
lattice, give reflection the signed action \(C=-r\). A degree-one cocycle is an invariant finite
charge \(q=rq\), while a boundary is
\[
q=g+rg.
\tag{1}
\]

Orbitwise:

- on a free pair \(\{i,r(i)\}\), every invariant charge \((m,m)\) is the boundary of \((m,0)\);
- at a fixed label, boundaries are exactly the even charges.

Hence the already formalized theorem gives
\[
\widehat H^1(C_2,\mathbf Z^{(I)}\otimes\mathrm{sgn})
\cong
(\mathbf Z/2)^{(I^r)}.
\tag{2}
\]

This changes the interpretation of reflection. Functional equation alone permits free pairs.
Reflection **anomaly** does not: free pairs are homological gauge, while genuine degree-one
anomaly is supported only at the fixed locus.

## Faithful anomaly-localization theorem `[PROVED + LEAN]`

Let \(B\subseteq(\mathbf Z/2)^{(I)}\) be a source-defined charge lattice. Suppose there is a
reporter
\[
\tau:B\longrightarrow
\widehat H^1(C_2,\mathbf Z^{(I)}\otimes\mathrm{sgn})
\tag{3}
\]
such that extension by zero from \(I^r\) reconstructs every charge:
\[
\operatorname{ext}_{I^r\hookrightarrow I}
\bigl(\operatorname{parity}(\tau(q))\bigr)=q
\qquad(q\in B).
\tag{4}
\]
Then
\[
\operatorname{supp}q\subseteq I^r
\qquad(q\in B).
\tag{5}
\]

### Proof

The left side of `(4)` vanishes at every nonfixed label by `(2)`. Equality `(4)` makes \(q\)
vanish there as well. This proves `(5)`.

This is the anomaly analogue of the clock-compass theorem: a left-invertible complete reporter
cannot lose a nonzero polarization. Here it cannot lose a nonzero conormal point-charge into a
free reflection boundary.

Lean formalizes `(3)`--`(5)` in
`formal/GaloisForLFunctions/RHTower/XiReflectionTateConormalLocalization.lean` as:

- `reflectionFixedExtension`;
- `reflectionTateFixedSupport`;
- `IsReflectionTateConservative`;
- `support_fixed_of_reflectionTateConservative`;
- `fixed_of_single_mem_reflectionTateConservative`.

## RH reduction `[PROVED + LEAN]`

Let
\[
\iota(\rho)=1-\overline\rho.
\tag{6}
\]
Its fixed locus is \(\operatorname{Re}\rho=1/2\). Let \(B_{\rm ar}\) be a source-constructed
mod-two principal-jet charge lattice. Assume:

1. **Xi landing:** for every Xi zero \(\rho\), the individual principal-conormal jet charge
   \(e_\rho\) belongs to \(B_{\rm ar}\);
2. **reflection-Tate conservativity:** one reporter `(3)`, constructed before choosing a zero,
   satisfies `(4)` on all of \(B_{\rm ar}\).

Then \(e_\rho\) is supported on the fixed locus by `(5)`, so
\[
\rho=1-\overline\rho,\qquad \operatorname{Re}\rho=\frac12.
\tag{7}
\]
Thus RH follows.

Lean formalizes the unconditional implication as
`riemannHypothesis_of_reflectionTate_conormal_localization`. Its hypotheses are explicit; no
source reporter or Xi landing theorem is asserted.

Multiplicity is not collapsed to total parity. The intended lattice carries one integral
generator for each principal jet grade \(1,\ldots,d_\rho\); reduction mod two happens after
separating those grades. Every jet then contributes a unit charge even when \(d_\rho\) is even.

## Surviving universal meaning

The proved support lemma says:

> **Conservative anomaly localization.** In an involutive infinite source, paired defects on free
> orbits are boundaries. A defect can represent physical/arithmetic information only if the
> source supplies a conservative reporter that reconstructs it from the anomaly quotient.
> Conservativity forces genuine defects onto isotropy.

It usefully repackages:

- why functional equation alone permits off-line quartets: it supplies an involution, not a
  conservative anomaly reporter;
- why scalar positivity and orientation fail: they read representatives, not whether a free pair
  is a boundary;
- why finite exactness and infinite leakage coexist: nonzero information is a comparison anomaly,
  not homology of either exact realization;
- why adelic \(L^2\) loses divisor fibres: it preserves the contraction but not the singular
  conormal reporter;
- why finite divisor completions lose covariance: they retain point charges without the complete
  reflection-Tate comparison;
- why generalized-prime off-line models are decisive falsifiers: their off-line pair must map to a
  Tate boundary, so any claimed reporter is not left-invertible;
- why duality versus adjunction is the correct fracture: inverse duality moves the label by
  \(\iota\), while adjunction is fibrewise; a conservative identification can live only on the
  equalizer.

## Why the proposed open core is retired

`[RETIRED CORE] [XI_SOURCE_REFLECTION_TATE_LEFT_INVERSE]`

Construct from the ordinary-prime Euler--Gamma source, before divisor specialization:

1. an integral, jet-graded Bockstein charge lattice \(B_{\rm ar}\) inside the comparison cone of
   the two incompatible completions;
2. a chain-level signed \(C_2\)-action induced by functional-equation/Gamma reflection;
3. a transgression \(\tau\) from \(B_{\rm ar}\) to reflection-Tate cohomology;
4. a source-defined synthesis map proving `(4)` on the whole lattice;
5. a conservative Bockstein identification placing every Xi principal conormal jet in
   \(B_{\rm ar}\), with the standard Xi determinant and all multiplicities.

Constructing these clauses would still prove RH, but reflection-Tate theory supplies none of
them.  In particular, Bockstein naturality cannot create the required fracture, and parity erases
the relative half-seam ancestry that must be retained.  The live successor is the source-selected
closed multiplication-graph problem in
`../1-in-progress/mobius-incidence-curvature-gamma-sonin-pole-divisor-transfer-rh.md`: it keeps the
prime-current numerator, overlap, and completion history before scalarization.

## Hostile audit

1. Group cohomology, Tate cohomology, fixed-point localization, and the support proof are parent
   mathematics. No novelty is claimed for them.
2. The abstract hypotheses imply RH. They are useful only if both maps are constructed from source
   data before reading Xi zeros.
3. Taking \(B_{\rm ar}\) to be the span of already critical zeros, or defining \(\tau\) from the
   fixed locus, is circular.
4. Reflection invariance of the Xi divisor proves only that zeros form fixed points or free pairs.
   It does not prove `(4)`.
5. Aggregating multiplicities mod two loses even-order zeros. Jet grades must remain separate
   until after integral landing.
6. A reporter that is merely injective as an abstract group map is insufficient. Reconstruction
   must use the canonical extension into the same spectral label space; otherwise arbitrary
   relabelling can fake conservativity.
7. The current corpus does not construct the required source reporter. This card is not an RH
   proof.
8. Targeted corpus search found the reflection-Tate fixed-locus theorem and clock-compass
   faithfulness separately, but not this exact RH reduction. Targeted arXiv search found general
   equivariant/fixed-point localization, not an Xi-conormal reflection-Tate construction. This is
   noncollision evidence, not a priority certificate.
9. The later hostile audit found the stronger internal collision with
   `XI_INTERNAL_REFLECTION_RANK_NONCREATION` and the explicit half-charge seam-deposit falsifier.
   Hence the route is retired even though its conditional implication remains correct.

## Gates

- [x] positivity/normality/orientation loop rejected
- [x] single-completion incompatibility identified from existing exactness theorems
- [x] reflection-Tate fixed-locus calculation already Lean-formalized
- [x] faithful anomaly-localization theorem Lean-formalized
- [x] RH implication from landing plus conservativity Lean-formalized
- [x] collision with internal reflection-rank noncreation identified
- [x] parity-blind seam-deposit countermechanism identified
- [x] route retired; formal fixed-support lemma retained
