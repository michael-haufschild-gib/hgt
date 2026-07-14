# Summable orientation nodal-collapse law

- **ID:** `summable-orientation-nodal-collapse-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / GENERAL HT SINGULARITY GEOMETRY / RH ROUTE CONSTRAINT
- **Scientific status:** `[PROVED] [FORMALIZED] [BRIDGE] [NOT NEW IN ISOLATION]`
- **Parent:** `../../1-in-progress/vanishing-mass-finite-residue-projective-rigidity.md`
- **Formal module:**
  `formal/GaloisForLFunctions/HTGeometry/OrientationNodalCollapse.lean`

## Statement

Let `P` be an infinite set of pole labels, let `w_p>0`, and encode an orientation by
`epsilon_p in {+1,-1}`.  For a coordinatewise-continuous residue path `r_p(t)`, `0<=t<=1`, joining

```text
r_p(0)=epsilon_p w_p,       r_p(1)=delta_p w_p,
```

put

```text
N(r)={p : r_p(t)=0 for some t in [0,1]}.
```

Then

```text
{p : epsilon_p != delta_p} subset N(r).                       (1)
```

Consequently finite nodal support forces eventual equality.  On an infinite label set,
eventually opposite endpoints force `N(r)` to be infinite.

The affine coefficient chord

```text
r_p(t)=(1-t) epsilon_p w_p+t delta_p w_p                       (2)
```

is sharp: at `t=1/2` its zero-coordinate set is exactly the disagreement set.  Under global
complement, every coordinate vanishes simultaneously.

For the actual universal prime carrier `C_epsilon`, complement and the affine chord satisfy

```text
C_(!epsilon)=-C_epsilon,
Chord(epsilon,!epsilon;t)=(1-2t) C_epsilon,
Chord(epsilon,!epsilon;1/2)=0.                                 (3)
```

Despite this total nodal collapse, complement has finite exact coefficient distance

```text
d_1(epsilon,!epsilon)=2 sum_p universalPrimeWeight(p)<infinity. (4)
```

Thus finite metric cost and infinite nodal complexity coexist.

## Proof

For every changed coordinate the endpoint residues have opposite strict signs.  The intermediate
value theorem gives a zero on `[0,1]`, proving `(1)`.  The finite and infinite support conclusions
are set-theoretic consequences.

At `t=1/2`, equation `(2)` is half the sum of the two endpoint residues.  Because `w_p` is nonzero,
this vanishes exactly when the two signs differ.  Boolean complement negates each universal prime
weight, and linearity of the normally convergent Cauchy series gives `(3)`.  Each complemented
coordinate changes by absolute amount `2w_p`; summability and termwise equality give `(4)`.

## Geometric and physical verdict

The naive infinite-energy/topological-barrier interpretation is false.  Ordinary coefficient
`ell-one` or compact-open continuity does not protect a tail orientation: opposite carriers are
joined by a finite-cost chord.  What is protected is the fixed nonzero-simple-pole stratum.

The positive law is stratified:

> A deformation with finite nodal support preserves the orientation tail.  Changing an infinite
> tail requires entering an infinite divisor-deletion stratum; global reversal passes through
> total carrier collapse.

The physical analogue is therefore not an energetic barrier but a singularity-sector constraint.
Finite local defect processes remain in one tail sector.  A global sector change requires a
collective nodal event at which infinitely many response channels lose their residues.

## HT relevance

Hypertranscendental information is not protected by metric distance alone.  Its robust datum is
preservation of the singularity constraint: nonzero pole support, residue quantization, and the
generated differential field away from the collapse locus.  At the complement midpoint the
carrier is zero, so its nontrivial differential information collapses simultaneously.

## RH relevance

Any RH route using only norm continuity of a summable prime carrier is blind to the projective tail
sector.  A viable orientation route must instead prove that the source-selected family cannot enter
the infinite divisor-deletion locus.  Such an exclusion must come from Herglotz positivity, fixed
simple-pole support, reflection positivity, or a differential-field constraint; topology of the
ambient completion cannot supply it.

## Parent-theory and novelty boundary

The coordinate walls and their sign chambers are the Boolean hyperplane arrangement, and the
crossing lower bound is the intermediate value theorem applied coordinatewise.  Finite sign-vector
and tope geometry belongs to oriented-matroid theory; see, for example, the topological
representation framework in Matthew Stamps,
<https://doi.org/10.1007/s10801-012-0366-0>, and the oriented-matroid Varchenko arrangement in
Winfried Hochstaettler and Volkmar Welker, <https://arxiv.org/abs/1805.07183>.  The summable-distance
identity is elementary `ell-one` geometry.  Their combination is useful for the HT carrier but does
not clear the scientific-novelty gate.

## Formal theorem surface

`OrientationNodalCollapse.lean` proves:

- `orientation_disagreement_subset_residuePathNodalSupport`;
- `primeOrientationsEventuallyEqual_of_finite_residuePathNodalSupport`;
- `residuePathNodalSupport_infinite_of_eventuallyOpposite`;
- `orientationResidueChord_midpoint_nodalSupport`;
- `universalPrimeOrientationWeight_complement`;
- `universalPrimeOrientationLimit_complement`;
- `universalPrimeOrientationChord_complement_half`;
- `universalPrimeOrientationCoefficientDistance_complement`.

## Gates

- [x] naive infinite-energy/topological barrier falsified
- [x] arbitrary-path nodal-support lower bound formalized
- [x] sharp affine-chord law formalized
- [x] actual universal prime carrier complement collapse formalized
- [x] finite exact coefficient-distance law formalized
- [x] targeted module build passed
- [x] parent-theory audit completed; classified as bridge
