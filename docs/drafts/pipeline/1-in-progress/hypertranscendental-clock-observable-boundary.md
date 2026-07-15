# Hypertranscendence has an exact clock-observable boundary

- **ID:** `hypertranscendental-clock-observable-boundary`
- **Stage:** 1-in-progress
- **Type:** GENERAL HT THEOREM / STATIC OBSERVABILITY GEOMETRY
- **Scientific status:** `[PAPER PROOF COMPLETE MODULO ONE CLASSICAL RATIONAL-DERIVATION LEMMA] [LEAN OPEN] [NOVELTY PROVISIONAL]`
- **Originating conjecture:** **Hypertranscendence is infinite algebraic clock capacity concentrated
  on a thin constraint boundary.**
- **Statement:** For a hypertranscendental element, the largest part of a finite jet-observable
  field which remains inside that field for `r` successive applications of the derivation is
  exactly the prefix obtained by deleting its outer `r` jet layers.

## Static setup

Let `(K, delta) subset (L, delta)` be an ordinary differential-field extension of characteristic
zero and let `f in L` be hypertranscendental over `K`. Put

```text
j_m = delta^m f,
P_N = K(j_0,...,j_(N-1)),   P_0=K.                         (1)
```

The integer `N` is observational resolution, not time. The derivation is called the algebraic
clock only because it tests whether a finite observable field contains the derivative of each of
its observables. It is not a flow or a generative law for `f`.

For `0 <= r <= N`, define the `r`-tick internal observable core

```text
C_r(P_N)={a in P_N : delta^q a in P_N for every 0 <= q <= r}. (2)
```

## The clock-boundary theorem `[PROVED MODULO CLASSICAL LEMMA]`

For every `N` and `0 <= r <= N`,

```text
C_r(P_N)=P_(N-r).                                          (3)
```

In particular, for `N>=1`,

```text
{a in P_N : delta a in P_N}=P_(N-1).                       (4)
```

Thus the entire failure of the actual derivation to close on `P_N` is supported on its single
outer algebraic coordinate `j_(N-1)`. The next value `j_N` is transcendental over `P_N`; no finite
jet field is a differential field. Nevertheless, deleting one boundary layer gives the maximal
domain whose one-step clock remains observable at resolution `N`.

Equation (3) is the precise meaning of a thin constraint boundary. Requiring `r` successive clock
tests erodes exactly `r` outer layers, independently of the bulk size. At `r=N`, only the base
field remains:

```text
C_N(P_N)=K.                                                 (5)
```

## Proof

Hypertranscendence makes the complete jet family `(j_m)_(m>=0)` algebraically independent over
`K`. Hence

```text
j_N is transcendental over P_N                             (6)
```

and `P_N=P_(N-1)(j_(N-1))` is a one-variable rational function field over `P_(N-1)`.

### One-step boundary localization

The ambient derivation maps `P_(N-1)` into `P_N`. On the rational extension
`P_N=P_(N-1)(j_(N-1))`, let

- `D_0` be the extension of this coefficient derivation with `D_0(j_(N-1))=0`;
- `partial_top` be the relative coordinate derivation with
  `partial_top(j_(N-1))=1` and `partial_top(P_(N-1))=0`.

Both are obtained first on the polynomial ring and then by the quotient rule. As derivations from
`P_N` to `P_(N+1)`, equality on the coefficient field and the top generator gives

```text
delta a = D_0 a + j_N partial_top(a),   a in P_N.           (7)
```

This is the exact boundary-localization formula. If `delta a in P_N`, then the first two terms in
`(7)` show that `j_N partial_top(a) in P_N`. By `(6)`, this forces
`partial_top(a)=0`. In characteristic zero the kernel of the coordinate derivation on a
one-variable rational function field `F(t)` is exactly `F`; therefore `a in P_(N-1)`.

Conversely, differentiating a rational expression in `j_0,...,j_(N-2)` introduces jets only
through `j_(N-1)`, so `delta(P_(N-1)) subset P_N`. This proves `(4)`.

### Iterated erosion

The inclusion `P_(N-r) subset C_r(P_N)` follows because `q` derivatives of an observable using
jets below `N-r` use jets only below `N-r+q <= N`.

For the reverse inclusion, suppose all derivatives of `a` through order `r` lie in `P_N`. Apply
`(4)` first to `delta^(r-1)a`, then to `delta^(r-2)a`, and continue down to `a`. This shows that
every derivative through order `r-1` lies in `P_(N-1)`. Induction on `r` inside the smaller window
then gives `a in P_(N-r)`. This proves `(3)`.

## Relation to the originating conjecture

The theorem separates three notions that must not be conflated.

1. **Clock, not time.** `delta` orders observables; no state evolution or carrier is constructed.
2. **Infinite capacity.** Every inclusion `P_N < P_(N+1)` adds the independent coordinate `j_N`.
   Hence no finite observable algebra has complete clock capacity.
3. **Thin boundary.** The leakage of every rational observable is the single term
   `j_N partial_top(a)` in `(7)`. The bulk coefficient derivation remains internal.

The result therefore upgrades the negative definition of hypertranscendence into a positive
finite-resolution law: an HT element has unit algebraic clock flux through every jet cutoff and
no bulk leakage.

## Classical-parent and collision audit

The following are parents and are not claimed as new:

- Kolchin's differential dimension polynomial: for one differential indeterminate the finite-jet
  transcendence degree is `N`;
- differential kernels and their prolongations: a finite jet packet carries a partial derivation
  into the next packet;
- ordinary jet/prolongation geometry and the Cartan distribution: the top derivative is the free
  finite-order coordinate;
- Kähler and `tau`-differentials: extensions of a coefficient derivation form a torsor under an
  ordinary derivation module;
- the kernel of `d/dt` on `F(t)` in characteristic zero is `F`.

The candidate-new claim is the exact observable-field equality `(3)`, its boundary-localization
identity `(7)`, and their interpretation as a source-independent HT clock-capacity law. Exact and
adjacent primary-source searches must still test whether this package occurs in differential
kernel, prolongation, differential-dimension, or differential-rational invariant theory.

## Strong no-go and positive successor

The proper-flat complex of each free finite jet matroid is a sphere, but this is the Boolean
lattice boundary and does not by itself supply new HT topology. Likewise, “one free top
derivative” alone is classical differential-kernel theory.

The positive successor is `(3)`: topology should be attached to the nested clock-observable cores
and to coefficient systems carried by their rank-one seams. The bare cutoff poset is only a ray
and is topologically contractible. Any nontrivial unified obstruction topology must therefore be
a decorated boundary theory, not the homotopy type of the raw jet-order set.

## Formalization target

Primary Lean module:

```text
formal/GaloisForLFunctions/HTGeometry/HypertranscendentalClockBoundary.lean
```

Planned theorem surface:

1. finite prefix fields `P_N` and their monotonicity;
2. `delta(P_N) subset P_(N+1)`;
3. `j_N` transcendental over `P_N` and strict unit-capacity growth;
4. the universal rational boundary-localization identity `(7)`;
5. the one-step maximal internal-core theorem `(4)`;
6. the finite iterated erosion theorem `(3)`.

The existing `HypertranscendentalHorizonFunctionField`, `FractionRingDerivation`,
`KaehlerKernel`, and `DisjointRationalFunctionFields` modules supply the generic-point,
quotient-rule, differential, and exact-meet infrastructure. Verification must use cached exact
module dependencies, one serialized targeted build only if the leaf `.olean` is missing, and a
direct source check of the touched Lean file.

## Gates

- [x] source-pure statement isolated
- [x] physical time and generative flow excluded
- [x] classical differential-kernel and dimension-polynomial collision identified
- [x] strong positive theorem retained after the collision
- [x] paper reduction to the rational coordinate-derivation kernel completed
- [ ] exact primary-literature novelty audit completed
- [ ] rational coordinate-derivation kernel formalized over a characteristic-zero field
- [ ] one-step observable-core equality formalized
- [ ] iterated erosion law formalized
- [ ] independent specialist novelty verdict

## Log

- 2026-07-15 -- Originating conjecture stated: hypertranscendence is infinite algebraic clock
  capacity concentrated on a thin constraint boundary.
- 2026-07-15 -- Rejected the free-matroid sphere and bare differential-kernel formulations as
  classical; isolated the exact maximal clock-stable observable core and iterated erosion law.
