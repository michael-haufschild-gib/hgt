# Vanishing-mass finite-residue projective rigidity

- **ID:** `vanishing-mass-finite-residue-projective-rigidity`
- **Stage:** 1-in-progress
- **Type:** THEOREM CANDIDATE / GENERAL HT SINGULARITY-CONSTRAINT LAW / RH ROUTE CONSTRAINT
- **Scientific status:** `[CONJECTURE: FULL DIFFERENTIAL-BIRATIONAL LAW] [FORMALIZED: AFFINE FINITE-RESIDUE CORE] [NOVELTY UNVERIFIED]`
- **Parent:** `../2-fully-proven/needs-audit/coherence-end-projective-ht-tail-reconstruction.md`

## Constraint

Let `l` be a nontrivial asymptotic filter, let positive pole masses `w_i` tend to zero along `l`,
and let `epsilon_i,delta_i` be Boolean residue orientations.  Suppose a transformation changes the
signed residues by

```text
sign(delta_i) w_i = a sign(epsilon_i) w_i + q_i,          (1)
```

where `a` is one constant scalar and the correction sequence `q_i` takes values in a finite set.
The finite-range hypothesis is the residue shadow of a finite collection of logarithmic
derivatives whose pole orders range over bounded integer sets.

## Theorem target: vanishing-mass residue screening

Equation `(1)` forces

```text
q_i = 0 eventually,
```

and exactly one of

```text
a = +1 and epsilon_i = delta_i eventually,
a = -1 and epsilon_i != delta_i eventually.              (2)
```

Thus a vanishing simple-pole palette screens every finite quantized residue correction.  The only
asymptotic affine symmetry preserving the palette is its global projective sign.

For the universal prime-log carrier, summability of the positive masses supplies `w_p -> 0` on the
cofinite prime filter.  Hence `(2)` becomes exactly the existing eventual-equality/eventual-opposite
prime-tail relation.

## Proof

Rearranging `(1)` gives

```text
q_i = (sign(delta_i) - a sign(epsilon_i)) w_i.
```

The coefficient in parentheses is uniformly bounded because both signs have absolute value one.
Therefore `q_i -> 0`.  A finite-range function converging to zero in a Hausdorff topological group
is eventually zero: remove the finite set of its nonzero values to obtain a neighborhood of zero.
After cancellation of the eventually nonzero mass `w_i`, `(1)` becomes

```text
sign(delta_i) = a sign(epsilon_i).
```

At any tail point this forces `a` to be `+1` or `-1`; the same global value then forces eventual
agreement or eventual opposition throughout the tail.

## Open core

`[OPEN CORE]` Prove that every element of the differential field of a generic summable simple-pole
carrier which again has the same pole locations, only simple poles, and the same unsigned
vanishing residue palette has residue action of the form `(1)` with finite-range `q`.  This is the
missing local-to-global differential-birational rigidity statement.  It would replace the much
stronger all-orientations joint differential-independence hypothesis in the parent card.

The completed affine finite-range and finite-quantized theorem is recorded separately at stage 3
in `../3-formalized/vanishing-mass-finite-residue-affine-projective-rigidity.md`.

The unrestricted statement is not assumed here.  Logarithmic derivatives show why finite
quantized corrections must be allowed: their residues are integral pole orders.  The vanishing
mass law says positively that all such corrections must disappear asymptotically.  The analytic
producer is now formalized for arbitrary meromorphic germs: the punctured logarithmic derivative
has residue equal to the integer meromorphic order, and finite real-linear logarithmic gauges
produce exactly `finiteQuantizedResidueCorrection`.

## RH relevance

Any RH route encoding prime information in a summable signed simple-pole carrier and allowing only
affine changes plus finitely generated logarithmic gauge corrections must preserve the prime
orientation tail up to one global sign.  Such a route can change finitely many local prime residues,
but it cannot implement an independent asymptotic sign surgery.  A viable route outside this class
must therefore introduce a genuinely infinite residue palette or a non-affine singularity action.

## Gates

- [x] exact residue constraint isolated without a flow parameter
- [x] false unrestricted affine-variable version rejected
- [x] finite-quantized correction class identified
- [x] abstract finite-range screening theorem formalized
- [x] universal prime-weight corollary formalized
- [x] bounded quantized pole-order finite-palette producer formalized
- [x] analytic logarithmic-derivative residue producer formalized
- [ ] full differential-birational local-to-global rigidity proved or falsified
- [ ] parent-theory and literature novelty audit completed
