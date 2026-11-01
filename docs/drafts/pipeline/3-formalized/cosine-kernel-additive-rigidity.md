# Cosine-kernel zeros cannot form additive triples

- **Stage:** 3-formalized
- **Type:** THEOREM / PINCHING SOURCE
- **Routes:** Argon §4.1 and §4.3.
- **Corpus:** `IncommensurableGaborPinching/CosineKernelNonLatticeFloor` proves explicit short-span floors only near bandwidth one.

## Theorem

For `θ sin θ≠0`, the cosine-window transform
`Kθ(y)=∫_{−1/2}^{1/2} cos(2θv) cos(2yv) dv`
has no zeros at all three points x, y, x+y. Consequently every compact set of gap pairs
has a strictly positive floor for `max(|Kθ(x)|,|Kθ(y)|,|Kθ(x+y)|)`.
This is qualitative and applies beyond bandwidth one; it supplies no numerical 75% gain by itself.

## Paper mechanism

The exact identity `(y²−θ²)Kθ(y)=y cosθ sin y−θ sinθ cos y` holds also at the removable frequencies:
integrate the derivative of `y cos(2θv)sin(2yv)−θ sin(2θv)cos(2yv)`.
A kernel zero therefore obeys `cos y=c y sin y`, with `c=cosθ/(θ sinθ)`.
Such a root has nonzero sine. If x,y,x+y all obey this equation, angle addition gives

`[1+c²(x²+xy+y²)] sin x sin y=0`,

impossible because the bracket is positive and both sine factors are nonzero.
Continuity and compactness then give the triple floor. No trigonometric interval subdivision is needed.

The excluded box limit is sharp: at θ=0, frequencies π, π, 2π are kernel zeros.
At nonzero θ with sinθ=0 the normalizing mean vanishes. For the corpus's totalized normalized
kernel this makes every frequency zero. Thus the normalized kernel admits an additive zero triple
exactly when `θ sinθ=0`. The exact classification is also formalized.

## Actual Gram transport

[Positive cosine pinching](trans-threshold-cosine-pinching-credit.md) transfers this
floor to the actual finite evaluation Gram at every fixed positive bandwidth,
including `4/3`. The cosine window still needs its matching prime-side certificate
and signed discrepancy estimate before yielding a trans-threshold zero proportion.

## Lean

`IncommensurableGaborPinching/CosineKernelAdditiveRigidity.lean` proves
`mtKernelNum_closed_form_global`, `mtKernel_no_additive_zero_triple`,
`mtKernel_compact_triple_floor`, `mtKernel_fourThirds_triple_floor`,
`mtKernel_boxcar_additive_zeros`, and `mtKernel_additive_zero_triple_iff`.
All six public theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`.
The exact production leaf passes `lake --old env lean` without warnings and is wired
into `IncommensurableGaborPinching.lean`. No proof-resource limit was raised.

## Gates

- [x] Corpus search for additive kernel-zero rigidity.
- [x] Paper algebra for sum-free zeros.
- [x] Exact kernel identity at all frequencies, compact floor, and degeneracy classification formalized.
- [ ] Literal trans-threshold Gram transport and positive-density pair packing.
- [ ] Combined arithmetic calibration; actual prime-phase discrepancy remains open.
