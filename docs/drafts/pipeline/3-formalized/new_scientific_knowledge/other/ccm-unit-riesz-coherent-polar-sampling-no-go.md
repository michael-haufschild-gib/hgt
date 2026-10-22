# CCM unit-Riesz coherent polar sampling no-go

- **ID:** `ccm-unit-riesz-coherent-polar-sampling-no-go`
- **Stage:** 3-formalized
- **Type:** NO-GO + exact positive survivor / cross-route operator classification
- **Scientific status:** `[PROVED HERE] [LEAN-PROVED, UNCONDITIONAL] [NOVELTY UNVERIFIED] [NO RH CLAIM]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CCM/CCMUnitRieszCoherentPolarSamplingNoGo.lean`
- **Parent:** `ccm-unit-riesz-exponential-coherent-trace`

## Question decided

The literal unit-Riesz source is atomic coherent energy minus continuous polar energy of the same
increment frame. A tempting closure is therefore a finite Loewner comparison

```text
atomic coherent projector <= C * continuous polar frame.          (1)
```

This card proves that `(1)` is impossible even for one fixed lag projector, even on finite linear
combinations of actual coherent increment columns. It then identifies and proves the exact positive
replacement: one first-order lag-generator/source-Gram channel.

## Four-lag packet

Put

```text
K(p,u)=1-exp(-p/2)-exp(-u/2)+exp(-|p-u|/2),
q=exp(h/2),  r=exp(-h/2),  A=1+q+r,
p_j=a+jh,
c=(-1,A,-A,1),
g_(a,h)(u)=sum_(j=0)^3 c_j K(p_j,u).               (2)
```

`K` is the proved `L2` Gram kernel of the actual increments `v_0-v_(-p)`. Hence `(2)` is a genuine
finite source-span response, not an arbitrary continuous bump.

The coefficients have three exact moment cancellations:

```text
sum c_j = 0,
sum c_j exp(-p_j/2) = 0,
sum c_j exp(+p_j/2) = 0.                            (3)
```

The constant part and both exponential tails therefore vanish. Lean proves the full piecewise law

```text
g(u)=0,                                                        u<=a,
g(u)=exp((u-a)/2)-exp(-(u-a)/2),                    a<=u<=a+h,
g(u)=(1+q)(exp((a+h-u)/2)-exp((u-a-2h)/2)),       a+h<=u<=a+2h,
g(u)=exp((u-a-3h)/2)-exp((a+3h-u)/2),             a+2h<=u<=a+3h,
g(u)=0,                                                        a+3h<=u. (4)
```

In particular,

```text
g(a)=g(a+3h)=0,
g(a+h)=q-r,
g(a+2h)=-(q-r),
|g(u)|<=q-r.                                                   (5)
```

This is a compact exponential spline manufactured inside the literal coherent source span.

## Fixed-sample polar no-go

Define bare continuous polar-frame energy

```text
P(a,h)=integral_(0,infinity) exp(-u) g_(a,h)(u)^2 du.            (6)
```

From `(4)`--`(5)`, for `a>=0` and `h>=0`,

```text
0<=P(a,h)<=3h(q-r)^2.                                          (7)
```

Fix sample lag `u=1` by taking `a=1-h`. Then `g(1)=q-r>0`. For any proposed finite nonnegative
constant `C`, choose

```text
h=1/(6(C+1)).                                                   (8)
```

This has `0<h<1`, and `(7)` gives

```text
C P(1-h,h) <= 3Ch g(1)^2 < g(1)^2.                             (9)
```

Replacing an arbitrary signed proposed constant by `max(C,0)` strengthens the contradiction. Lean
therefore proves the closed theorem

```text
not exists C, forall a h,
  0<=a -> 0<h -> a+h=1 -> g_(a,h)(1)^2 <= C P(a,h).             (10)
```

Thus no finite Loewner domination of the fixed lag-one projector by the bare polar continuum can
hold on the coherent source span. The failure is local and source-native; primes, asymptotics, and
the `N -> infinity` limit are not involved.

## Exact positive survivor: generator/source-Gram energy

The source-Gram quadratic of the same packet is

```text
Q(a,h)=c^T K c=sum_j c_j g(p_j)=2A(q-r)>0.                      (11)
```

On the three open cells in `(4)`, Lean differentiates the response and defines its piecewise weak
lag generator `g'`. Direct exponential integration proves the exact graph-energy law

```text
G(a,h)=sum_cells integral (4 g'(u)^2+g(u)^2) du
      =4 Q(a,h)
      =8A(q-r).                                                 (12)
```

Consequently fixed sampling has the exact source-Gram and generator representation

```text
g_(1-h,h)(1)^2
  =(q-r)/(2A) Q(1-h,h)
  =(q-r)/(8A) G(1-h,h).                                        (13)
```

This is the strongest positive statement exposed by the obstruction. Bare polar `L2` response
energy loses two localization orders, while the first-order graph energy is exactly the original
coherent source norm. Any valid CCM transport must carry this generator/source-Gram channel or an
equivalent boundary flux; scalar polar averaging alone cannot work.

## Proof spine

1. Expand the four increment kernels and use `qr=1` to prove `(3)`.
2. Resolve four absolute values on each lag cell, yielding `(4)` and `(5)`.
3. Use support width `3h`, `exp(-u)<=1`, and `(5)` to prove `(7)` without computing `(6)`.
4. Use the explicit scale `(8)` to prove `(9)` and then the unconditional no-go `(10)`.
5. Evaluate the response at its four nodes to obtain `(11)`.
6. Differentiate the three formulas in `(4)`. On each cell, `4g'^2+g^2` collapses to a sum of two
   exponentials. Integrate the three cells exactly and use `qr=1` to obtain `(12)`.
7. Combine `(5)`, `(11)`, and `(12)` to obtain `(13)`.

## Route consequences

- **CCM-UR:** the remaining source inequality cannot be a bare atomic-projector versus polar-frame
  Loewner bound. Any successful unit-Riesz inequality must retain a first-order lag graph norm,
  signed arithmetic cancellation, or both.
- **CCM-FU:** Cesaro smoothing cannot manufacture the missing point control from polar `L2` mass.
  A valid FU merger must transport the generator/source-Gram term through the cumulative source,
  not estimate prime and polar channels separately.
- **CCM-HG:** the Hankel boundary slope is no longer an optional interpretation. Formula `(12)`
  proves a source-side boundary/generator channel is exactly what repairs the failed polar
  domination. Open task is to identify this graph energy with the literal HG relative-trace slope.
- **CCM-EP:** dephased boundary transport must converge in a graph norm strong enough to preserve
  `(12)`. Strong convergence only in the bare polar `L2` response norm is provably insufficient.
- **CCM-GS:** generic separation does not control localized leverage. Cofinal ground separation
  must be quantitative in source-Gram/generator norm; pointwise nonvanishing alone misses `(10)`.
- **Route O:** opposite Rayleigh control cannot come from scalar coherent restriction plus polar
  mass. The required near-ground intertwiner must be graph-bounded and preserve the generator
  channel, or Route O repeats `(10)` inside the restricted-Weil space.
- **Route G:** source admission into Suzuki form must retain first-order lag energy. A trace-only or
  diagonal-only admission destroys precisely the survivor `(12)`.

## Hostile novelty and theatre audit

- Exponential covariance kernels, their Sobolev/RKHS interpretation, and generic point-evaluation
  inequalities are classical. No novelty claim is made for those ingredients.
- Corpus already contains `L2PointSamplingNoGo.lean` and `HTGeometry/SpikeSobolev.lean`. Neither
  applies to the source-selected exponential Gram range, constructs a compact packet inside that
  range, fixes the sample at lag one, or proves the exact graph-energy identity `(12)`.
- Connes--Consani scaling-Hamiltonian and archimedean Weil-positivity papers describe compressed
  scaling, prolate, and trace-formula positivity. Riesz-criterion literature describes other
  smoothing criteria. Targeted search did not expose `(2)`--`(13)` for the literal unit-Riesz CCM
  current. Absence is not established; novelty remains unverified.
- A generic statement that `L2` does not control points would be theatre. New content is an
  explicit counterpacket lying in the actual coherent source span, at a fixed sample, plus exact
  identification of the positive surviving norm.
- This does **not** estimate the von-Mangoldt coefficients, construct the CCM ground intertwiner,
  identify the HG/EP boundary generator, or prove RH.

## Open core exposed

Construct one literal CCM boundary/ground transport `T_N` for which the source graph identity
survives:

```text
G_source(f)=4 ||f||_source^2,
G_boundary(T_N f) <= or = G_source(f),
and T_N preserves the signed prime-minus-polar completed trace.  (14)
```

Then prove the arithmetic completed source has the required cofinal graph bound. A transport
controlled only by bare polar `L2` mass is now formally excluded.

## Index of the formalization

Modules: `RHTower/CCM/CCMUnitRieszCoherentPolarSamplingNoGo.lean`,
`RHTower/CCM/CCMUnitRieszCoherentGeneratorSampling.lean`.  All declarations are unconditional;
`#print axioms` returns only `propext, Classical.choice, Quot.sound`.

| Card item | Lean declaration |
|---|---|
| `(2)` four-lag packet in the source span | `unitExponentialThirdDifferenceResponse`, `unitExponentialThirdDifferenceResponse_eq_gramPacket` |
| `(3)` moment cancellations | `unitExponentialThirdDifferenceResponse_eq_zero_of_le`, `unitExponentialThirdDifferenceResponse_eq_zero_of_ge` |
| `(4)` piecewise law | `unitExponentialThirdDifferenceResponse_eq_first`, `unitExponentialThirdDifferenceResponse_eq_middle`, `unitExponentialThirdDifferenceResponse_eq_last` |
| `(5)` node values and sup bound | `unitExponentialThirdDifferenceResponse_at_leftNode`, `unitExponentialThirdDifferenceResponse_at_firstNode`, `unitExponentialThirdDifferenceResponse_at_secondNode`, `unitExponentialThirdDifferenceResponse_at_rightNode`, `abs_unitExponentialThirdDifferenceResponse_le` |
| `(6)`, `(7)` polar energy bound | `unitExponentialThirdDifferencePolarEnergy_eq_interval`, `unitExponentialThirdDifferencePolarEnergy_nonneg`, `unitExponentialThirdDifferencePolarEnergy_le` |
| `(8)`, `(9)` explicit scale | `exists_unitExponentialThirdDifference_fixedSample_gt_polarEnergy` |
| `(10)` the no-go | `no_unitExponentialCoherent_fixedSample_polarDomination` |
| `(11)` source-Gram quadratic | `unitExponentialThirdDifferenceSourceGram_eq`, `unitExponentialThirdDifferenceSourceGram_pos` |
| `(12)` graph-energy law | `unitExponentialThirdDifference_first_graphDensity`, `unitExponentialThirdDifference_middle_graphDensity`, `unitExponentialThirdDifference_last_graphDensity`, `unitExponentialThirdDifferenceGeneratorEnergy_eq_sourceGram` |
| `(13)` fixed-sample representation | `unitExponentialThirdDifference_fixedSample_eq_sourceGram`, `unitExponentialThirdDifference_fixedSample_eq_generatorEnergy` |
