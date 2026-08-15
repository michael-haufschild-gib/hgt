# CCM Guinand--Weil continuous source quotient

- **Status:** LEAN-FORMALIZED
- **Lane:** CCM-FU / source-native measure layer
- **Novelty scope:** corpus-new continuous-dual realization and exact atomic specialization of
  Groskin's finite source quotient; Groskin states the finite signed-measure calculus on paper
- **External anchor:** Akiva Groskin, arXiv:2607.02828, Lemma 2.3 and Corollary 2.4
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMGuinandWeilContinuousSourceQuotient.lean`

## Source-native space

Let the physical horizon be `H=[0,1]` and let

```text
S = C(H,R)^*                                                     (1)
```

be the continuous real dual. Finite Borel measures act on `S` by integration; differences and
linear combinations represent finite signed sources. This puts finite prime atoms and continuous
pole/archimedean channels in one typed source space before finite matrix formation.

For `L in S`, Lean defines

```text
T_N(L) =
 (L(omega),
  (L(sin(2*pi*(k+1)*omega)))_(0<=k<N),
  (L(omega*cos(2*pi*(k+1)*omega)))_(0<=k<N)).                    (2)
```

The associated odd source and diagonal are

```text
psi_L(n)=L(sin(2*pi*n*omega))/pi,
d_L(n)=2L(omega*cos(2*pi*n*omega)).                              (3)
```

Their divided-difference matrix is the whole continuous-source CCM packet `Q_N(L)`.

## Exact quotient theorem

The distinguished zero edge and diagonals of `Q_N(L)` recover `(2)`. Conversely, if `(2)`
vanishes, every source value in `(3)` at modes `0,...,N` vanishes; every off-diagonal divided
difference and every diagonal therefore vanishes. Lean proves unconditionally

```text
T_N(L)=0  <=>  Q_N(L)=0.                                        (4)
```

No atomicity, positivity, density, or approximation premise occurs in `(4)`.

## Measure and atomic realizations

For every finite Borel measure `mu`, Lean constructs the bounded integration functional

```text
L_mu(f)=integral_H f dmu.                                       (5)
```

Its observer reduces definitionally to the three exact moment families in `(2)`. For a finite
weighted atomic source, Lean proves exact equality with both preceding atomic objects:

```text
T_N(L_atomic)=finite atomic observer,
Q_N(L_atomic)=finite atomic event packet.                        (6)
```

This is equality of whole matrices, not only equality of kernels or selected entries.

## CCM-FU consequence

Continuous source topology does not repair finite observer nonfaithfulness. Atom, pole, and
archimedean channels now inhabit the same pre-quotient space, while `T_N` remains only
`2N+1`-dimensional. A canonical CCM-FU producer must therefore retain the literal arithmetic channel
decomposition in `S` and transport it through a source-native connection; it cannot reconstruct
that decomposition from the finite matrix.

Next target is the literal prime/pole/archimedean functional and its normalized equality with the
published restricted-Weil matrix, followed by aperture differentiation into the continued Xi Ward
source. RH is not proved here.

## Lean declarations

- `CCMGuinandWeilHorizon`
- `CCMGuinandWeilContinuousSource`
- `ccmGuinandWeilHorizonCoordinate`
- `ccmGuinandWeilSineCoordinate`
- `ccmGuinandWeilWeightedCosineCoordinate`
- `ccmGuinandWeilContinuousSourceCoordinateObserver`
- `ccmGuinandWeilContinuousSourcePacketMatrix`
- `ccmGuinandWeilContinuousSourceCoordinateObserver_zero_iff_packet_zero`
- `ccmGuinandWeilFiniteMeasureSourceFunctional`
- `ccmGuinandWeilFiniteMeasureSourceCoordinateObserver_eq`
- `ccmGuinandWeilAtomicSourceFunctional`
- `ccmGuinandWeilAtomicSourceCoordinateObserver_eq`
- `ccmGuinandWeilAtomicSourcePacketMatrix_eq`

Targeted `lake env lean` and `lake build
GaloisForLFunctions.RHTower.CCMGuinandWeilContinuousSourceQuotient` pass. `#print axioms` reports
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no project axiom, `sorry`,
`admit`, `opaque`, or `unsafe` declaration is used.
