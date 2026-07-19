# Xi aperture--Poisson response signature parity

- **ID:** `xi-aperture-poisson-response-signature-parity`
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM (Lean) / no-go with positive survivor
- **Source:** `XiMobiusContinuousApertureDyadicProjection.lean`,
  `PoissonCoarseGrainingEnergy.lean`, `XiSquaredEulerRayTwoPointPositivity.lean`,
  `XiSquaredEulerRayCubicAmplification.lean`, HTGeometry `PoissonRadialChamber.lean`, and
  *Finite Fusion Forces Infinite Hypertranscendence*
- **Scientific status:** `[LEAN-PROVED] [CANDIDATE NEW RH-PROOF-SHAPE KNOWLEDGE]`
  `[EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Statement:** A nontrivial slab Poisson coarsening increment has signature `(1+,2-)` on three
  distinct nodes, but the actual fine-minus-coarse response refinement has signature `(2+,1-)`,
  exactly matching one off-line squared-Xi orbit and giving an eventual negative cubic amplifier.
  The refinement is nevertheless not a Hilbert Gram, so the remaining theorem is a completed
  signature-converting intertwiner from the positive true-aperture source to this indefinite
  response.

## Goal

Determine whether the positive dyadic innovations of the true Möbius aperture can be sent directly
to the finite-resolution slab response and thereby supply the unbounded transverse amplifier left
open by the three-node Xi response theorem.

The answer is no for every fixed linear Hilbert/Gram intertwiner.  Direct positive amplification
by the **coarsening** increment also has the wrong cubic sign.  But orienting the same response in
the actual refinement direction reverses its odd-dimensional inertia and produces exactly the
negative cubic required by the Xi orbit theorem.  The positive survivor is therefore stronger
than a no-go: the target response amplifier already exists.  The companion valuation-clock
shuttle theorem now supplies its exact source multiplier coefficientwise; analytic completion of
the source-to-response signature conversion remains open.

## Exact kernels

For `a > 0`, put

```text
L_a(x)=a^2/(a^2+x^2).
```

For `0<a<b`, define the response increment

```text
S_(a,b)(x)=L_b(x)-L_a(x).
```

Direct denominator clearing gives

```text
S_(a,b)(x)
 =x^2(b^2-a^2)/((b^2+x^2)(a^2+x^2)).                 (SP1)
```

Hence

```text
S_(a,b)(0)=0,
S_(a,b)(x)>0  iff  x!=0.                               (SP2)
```

This is the spatial form of the scale shuttle.  In the spectral form of the Poisson energy, the
normalized half-line density is

```text
w_a(t)=a exp(-a t),  t>=0.
```

Both `w_a` and `w_b` have integral one.  Their difference has exactly one switch at

```text
tau(a,b)=log(b/a)/(b-a)>0:                             (SP3)

w_b(t)-w_a(t)>0  for 0<=t<tau(a,b),
w_b(t)-w_a(t)=0  for t=tau(a,b),
w_b(t)-w_a(t)<0  for t>tau(a,b).                       (SP4)
```

Indeed

```text
w_b(t)/w_a(t)=(b/a) exp(-(b-a)t),
```

which is strictly decreasing and equals one exactly at `(SP3)`.  The zero total integral says the
scale step redistributes spectral weight from the high-frequency tail into the low-frequency
sector.  It is not the addition of a positive spectral band.  This is the real-line analogue of
the exact one-threshold radial orientation chambers already formalized in HTGeometry
`PoissonRadialChamber.lean`.

## The two-channel mirror law `[PROVED HERE]`

Take two distinct displacements `d_0,d_1` and put `c=S_(a,b)(d_0-d_1)>0`.  The scale-increment
matrix is

```text
A_2=[[0,c],[c,0]].                                     (SP5)
```

Therefore its mirror-even and mirror-odd vectors are exact eigenchannels:

```text
A_2(1,1)= c(1,1),
A_2(1,-1)=-c(1,-1).                                    (SP6)
```

For a mass amplitude `m`,

```text
q_A(m,m)= 2c m^2>=0,
q_A(m,-m)=-2c m^2<=0,                                  (SP7)
```

with strict signs when `m!=0`.  A Schwarz mirror pair of actual Xi zeros has equal positive
multiplicity, so its physical vector is `(m,m)`.  In the coarsening orientation the completed
response correlation selects the positive mirror-even channel and excludes the negative
mirror-odd signed-Jordan channel.  In the actual fine-minus-coarse refinement orientation the
matrix is `-A_2`, so the signs reverse:

```text
q_(-A)(m,m)=-2c m^2<0,
q_(-A)(m,-m)=2c m^2>0.                                (SP7r)
```

Thus response correlation does not make either scale difference positive semidefinite.  It fixes
the parity channel: the Schwarz-even physical divisor is positive under coarsening and negative
under refinement.  This is the exact cancellation/selection statement exposed by the
separate-Jordan no-go.

## The three-node signature theorem `[PROVED HERE]`

Let `d_0,d_1,d_2` be pairwise distinct and write

```text
c_ij=S_(a,b)(d_i-d_j)>0.
```

Then

```text
A_3=
 [[0,    c_01,c_02],
  [c_01,0,    c_12],
  [c_02,c_12,0    ]],                                  (SP8)

det(A_3)=2 c_01 c_02 c_12>0,                           (SP9)
det(A_3[{i,j}])=-c_ij^2<0.                              (SP10)
```

The matrix is real symmetric, nondegenerate, and has trace zero.  Since its determinant is
positive, its eigenvalue product is positive; trace zero rules out three positive eigenvalues.
The strictly positive quadratic value on `(1,1,1)` rules out three negative eigenvalues.  Thus

```text
signature(A_3)=(1+,2-).                                (SP11)
```

By contrast, the existing squared-Euler orbit theorem gives, at every ordered positive triple,
positive diagonal, positive two-node minors, and strictly negative three-node determinant for an
off-line Xi orbit.  Sylvester elimination therefore gives

```text
signature(off-line orbit response)=(2+,1-).            (SP12)
```

The coarsening increment and the required orbit selector have opposite negative-index parity.
However, the actual response refinement is

```text
R_3=-A_3,
det(R_3)=-2 c_01 c_02 c_12<0,
signature(R_3)=(2+,1-).                                (SP12r)
```

Therefore the fine-minus-coarse response has exactly the same negative-index parity as an off-line
orbit.  The orientation reversal is the pivotal positive survivor.

## Oriented cubic classification and positive survivor

For any fixed background kernel `B`, the existing mixed-discriminant identity gives

```text
det(B+lambda A_3)
 =det(B)+lambda M_1+lambda^2 M_2+lambda^3 det(A_3).     (SP13)
```

Because `det(A_3)>0`, `(SP13)` is strictly positive for every sufficiently large positive
`lambda`.  Thus direct amplification by the **coarsening** increment eventually forces the wrong
cubic sign.

For the refinement kernel `R_3=-A_3`, the same identity has negative leading coefficient:

```text
det(B+lambda R_3)
 =det(B)+lambda N_1+lambda^2 N_2
   -lambda^3 det(A_3)<0                                (SP13r)
```

for every sufficiently large positive `lambda`.  Hence the actual fine-minus-coarse Poisson
response is an unbounded negative cubic amplifier against every fixed background.  The target
amplifier demanded by `XiSquaredEulerRayCubicAmplification.lean` is present on the response side.

The strongest positive survivor is the oriented three-way classification:

```text
true-aperture refinement       : positive-semidefinite Hilbert innovation,
slab Poisson refinement       : (2+,1-) on three distinct nodes,
off-line Xi orbit response    : (2+,1-) on three positive Euler nodes.   (SP14)
```

A fixed linear transport of a positive Gram increment remains positive semidefinite under
congruence, so it cannot produce the middle line of `(SP14)`.  But no target-sign obstruction
remains: the middle and last lines now have the same index and the same eventual negative cubic.
A successful source-to-zero construction must therefore perform one genuine signature conversion,
from the positive all-valuation aperture innovation to the index-one response refinement.  The
functional-equation mirror already selects the relevant even physical channel.  The companion
`xi-aperture-poisson-valuation-clock-shuttle` theorem identifies the scale-dependent multiplier as
an Euler-aperture derivative of the actual normalized Xi source.  What remains is to complete that
coefficientwise map through the infinite Euler--Gamma assembly and quadratic response.

## Hypertranscendental source consequence

The finite-fusion theorem proves that valuation depth is not redundant: every complete next layer
is differentially independent over the field generated by all preceding layers, and fusion closure
forces the whole countably free tower.  `XiShiftPrimeHypertranscendence.lean` places the actual
filtered von Mangoldt source in this upper-end differential geometry.

Together with `(SP14)`, this rules out the following proof shape:

```text
independent valuation layers
  -> sum their positive Hilbert innovation Grams
  -> identify that sum by fixed congruence with one slab Poisson refinement
  -> amplify an off-line orbit.
```

The first arrow loses the relative HT information by quadratic Gram compression, and fixed
congruence cannot change its positive inertia into the index-one response refinement.  The
response target itself has the correct cubic parity, so the surviving proof shape is sharper: fuse
unbounded valuation layers before the quadratic response is formed, then complete the exact
Euler-aperture derivative shuttle as a nonlinear/indefinite intertwiner into the Poisson refinement
channel.  Hypertranscendence is
therefore relevant not as a generic complexity certificate but as the obstruction to replacing
this infinite pre-response fusion by any finite differential prefix.

## Hostile audit

1. **Not generic positivity.**  Entrywise monotonicity of `L_a` on positive masses does not imply
   Loewner monotonicity; `(SP5)` supplies a strict negative signed direction.
2. **Not an RH proof.**  The refinement supplies the correct target cubic, and the companion
   shuttle supplies its coefficientwise source multiplier, but no completed analytic intertwiner.
3. **Not a finite-coordinate amplifier.**  Positive congruence preserves inertia, and the existing
   aperture cubic curvature is already an invertible dressing of its positive Cauchy tangent.  The
   needed conversion must occur before or outside finite Hilbert Gram compression.
4. **Not merely the old separate-Jordan no-go.**  The old result says the low/high cutoff Jordan
   pieces are gauge-dependent.  Here the joined finite-resolution response itself has an exact
   parity-split scale signature, and the actual mirror mass lies in the coarsening-positive /
   refinement-negative even channel.
5. **Literature boundary.**  Poisson kernels, their Fourier transforms, one-switch exponential
   densities, and the finite-matrix inertia calculations are standard ingredients.  A targeted
   search found no source stating the combined signature-parity obstruction for the actual Xi
   aperture, slab response, and squared-Euler orbit.  External specialist novelty review remains
   required; the scientific claim is presently corpus-new RH-proof-shape knowledge, not a claim
   that `(SP1)`--`(SP4)` are new analysis.

## Lean status

`RHTower/XiAperturePoissonResponseSignature.lean` formalizes:

1. the exact positive formula `(SP1)` and strictness `(SP2)`;
2. the two-node even/odd quadratic identities and strict signs `(SP5)`--`(SP7)`;
3. the exact three-node determinant `(SP9)` and its strict positivity;
4. non-positive-semidefiniteness / no Gram realization at two nodes;
5. eventual positivity under positive cubic amplification, and the specialization showing that a
   Poisson coarsening increment cannot be the existing Xi negative amplifier;
6. strict even-negative / odd-positive parity for the actual refinement orientation;
7. the refinement no-Gram theorem, its strict negative three-node determinant, and its eventual
   negative amplification against every fixed background.

The spectral threshold `(SP3)`--`(SP4)` is a second formalization target after the algebraic
signature core; it is not needed for the no-go dependency closure.

The direct leaf compilation passes.  `#print axioms` for the strict channel laws, the no-Hilbert-
Gram theorem, the three-node determinant, and the eventual cubic specialization reports only
`propext`, `Classical.choice`, and `Quot.sound`, for both coarsening and refinement orientations.
No umbrella or full project build was used.

## Gates

- [x] 0 -> 1: exact actual kernels, source/response objects, and attack class identified
- [x] 1 -> 2: dependency-closed proof of the oriented signature and cubic classification
- [x] hostile internal corpus audit: no duplicate exact Xi/slab/aperture signature theorem found
- [ ] external specialist novelty audit
- [x] 2 -> 3: Lean algebraic signature core, targeted leaf check, and axiom audit
- [ ] completed source-to-zero signature-converting intertwiner

## Log

- 2026-07-19 — extracted from the signed-Jordan, true-aperture martingale, slab coarse-graining,
  squared-Euler cubic, and finite-fusion HT surfaces.  The direct Hilbert-martingale route was
  falsified; the mirror-parity cancellation and opposite three-node signature were retained as the
  first positive survivor.  Lean then exposed the orientation pivot: fine-minus-coarse reverses
  the cubic, exactly matches the off-line orbit's `(2+,1-)` signature, and is an eventual negative
  amplifier.  The open core narrowed to the source-pure signature-converting map.
- 2026-07-19 — the completed source-to-response target was narrowed by
  `XiCompletedApertureReflectionKernel.lean`.  The critical seam and the entire reflection-even
  aperture sector annihilate every odd determinant, not only the three-node cubic.  The unique
  surviving completed sector is the nonzero transverse aperture-odd kernel
  `2 Re[-xi'/xi(1/2+u+i(x-y))]`; its three-node sign and identification with the Poisson refinement
  are now the exact open source gates.
