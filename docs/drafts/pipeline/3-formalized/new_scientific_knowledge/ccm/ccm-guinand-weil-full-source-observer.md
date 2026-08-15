# CCM Guinand--Weil full source observer

- **Status:** LEAN-FORMALIZED
- **Lane:** CCM-FU / finite Guinand--Weil source quotient
- **Novelty scope:** Lean formalization of Groskin's externally stated exact source quotient;
  corpus-new forced whole-matrix ambiguity consequence and source-selection interpretation;
  rank--nullity is classical
- **External anchor:** Akiva Groskin, arXiv:2607.02828, Lemma 2.3 and Corollary 2.4
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMGuinandWeilFullSourceObserver.lean`

## Exact finite observer

For `R` signed atomic events at horizons `omega_i`, modes `0,...,N` see the coordinates

```text
(sum_i alpha_i omega_i,
 (sum_i alpha_i sin(2*pi*(k+1)*omega_i))_(0<=k<N),
 (sum_i alpha_i omega_i cos(2*pi*(k+1)*omega_i))_(0<=k<N)).        (1)
```

Lean proves that this coordinate space has dimension exactly `2N+1`. These are precisely the
finite Guinand--Weil coordinates: the central weighted-horizon moment, positive sine moments, and
positive weighted-cosine moments.

Let `Packet(alpha)` be the whole finite sum of event matrices on modes `0,...,N`. Its distinguished
entries recover `(1)` exactly:

```text
Packet(0,0)       = 2 sum_i alpha_i omega_i,
Packet(k+1,0)     = [sum_i alpha_i sin(2*pi*(k+1)*omega_i)]/[pi*(k+1)],
Packet(k+1,k+1)   = 2 sum_i alpha_i omega_i cos(2*pi*(k+1)*omega_i). (2)
```

The divided-difference event formula supplies the other direction: if `(1)` vanishes, every source
value at modes `0,...,N` vanishes, so every off-diagonal divided difference and every diagonal in
the packet vanishes. Thus Lean proves

```text
observer(alpha)=0  <=>  Packet(alpha)=0.                            (3)
```

## Whole-matrix overcompleteness

For every horizon placement, if `R>2N+1`, rank--nullity gives

```text
exists alpha!=0, Packet(alpha)=0.                                   (4)
```

Unlike the preceding codiagonal theorem, `(4)` annihilates the entire finite CCM matrix, including
its weighted-cosine diagonal data. Full matrix formation therefore determines exactly the reported
coordinates but does not determine an overcomplete signed atomic source.

This sharpens CCM-FU's obstruction. Four-unit central energy is one reported coordinate; adding all
finite diagonal and off-diagonal entries still cannot select source provenance above reporter
dimension. A canonical arithmetic source or `Pi(lambda,k)` must be selected in a source-defined
physical horizon before quotienting and transported into the matrix afterward.

## Scope boundary

The theorem handles finite signed atomic event sources. It does not identify the literal completed
prime--pole--archimedean coordinate vector, treat its continuous measures, prove undercomplete
injectivity for the full observer, construct a canonical source lift, or establish the continued Xi
Ward incidence. No RH conclusion is claimed.

## Lean declarations

- `CCMGuinandWeilSourceCoordinates`
- `ccmGuinandWeilFiniteSourceCoordinateObserver`
- `ccmGuinandWeilSourceCoordinates_finrank`
- `ccmGuinandWeilFiniteSourceCoordinateObserver_exists_nonzero_kernel`
- `ccmGuinandWeilFiniteEventPacketMatrix`
- `ccmGuinandWeilFiniteEventPacketMatrix_zero_edge`
- `ccmGuinandWeilFiniteEventPacketMatrix_zero_diagonal`
- `ccmGuinandWeilFiniteEventPacketMatrix_positive_diagonal`
- `ccmGuinandWeilFiniteSourceCoordinateObserver_zero_implies_packet_zero`
- `ccmGuinandWeilFiniteEventPacketMatrix_zero_implies_coordinateObserver_zero`
- `ccmGuinandWeilFiniteSourceCoordinateObserver_zero_iff_packet_zero`
- `ccmGuinandWeilFiniteEventPacketMatrix_exists_nonzero_kernel`

Targeted `lake env lean` and `lake build
GaloisForLFunctions.RHTower.CCMGuinandWeilFullSourceObserver` pass. `#print axioms` reports only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no project axiom, `sorry`, `admit`,
`opaque`, or `unsafe` declaration is used.
