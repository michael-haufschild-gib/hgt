# CCM Guinand--Weil codiagonal observer dimension

- **Status:** LEAN-FORMALIZED
- **Lane:** CCM-FU / finite Guinand--Weil source quotient
- **Novelty scope:** corpus-new observer-dimension interpretation and sharp atomic phase transition;
  finite-dimensional rank--nullity is classical
- **External anchor:** Akiva Groskin, arXiv:2607.02828, Lemma 2.3 and Corollary 2.4
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMGuinandWeilCodiagonalObserverDimension.lean`

## Exact phase transition

For `R` reflection orbits with angles `theta_i` and the first `N` positive integral modes, define

```text
S_(N,R)(k,i)=sin((k+1)*theta_i),   0<=k<N, 0<=i<R.        (1)
```

Lean proves both sides of the dimension boundary.

If `R<=N`, the cosine nodes are distinct, and every sine node is nonzero, then

```text
ker S_(N,R)={0}.                                          (2)
```

The proof restricts to the first `R` modes and applies the exact
sine--Chebyshev--Vandermonde determinant.

If `N<R`, then for every horizon placement

```text
ker S_(N,R)!={0}.                                         (3)
```

This is rank--nullity for the literal rectangular sine-moment linear map. No endpoint, collision,
or limiting argument is involved.

For forward weights `a_i`, reflected weights `a_i*`, and the literal paired Guinand--Weil packet,
the zero-edge identity is

```text
Packet(k+1,0)
 = [sum_i (a_i-a_i*) sin((k+1)*theta_i)]/[pi*(k+1)].      (4)
```

Consequently `R>N` admits unequal forward/reflected weights whose complete observed codiagonal
vanishes.

## Correction to the square rigidity route

The square determinant does not rule out cancellation in the completed source. Groskin's prime
measure places atoms at

```text
omega_q = 1-log(q)/log(c),       q=p^a<=c,
```

and can have more than `N` atoms. Pole and archimedean blocks arise from continuous measures. At
Galerkin level `N`, the codiagonal reads only `N` sine moments, so source-representative ambiguity is
unavoidable above observer dimension.

The theorem does not claim the whole matrix vanishes. Groskin's exact source quotient also retains
the central moment and weighted cosine moments; a codiagonal-kernel vector can remain visible on the
diagonal. That distinction is essential: the result classifies lost codiagonal provenance, not Weil
positivity.

## Higher principle

CCM-FU's canonical-ground problem is a source-selection problem caused by finite reporting. Below
observer dimension, event weights are recoverable. Above it, multiple signed sources have the same
codiagonal data. Therefore canonical `Pi(lambda,k)` cannot be reconstructed from the finite matrix
or four-unit central mass alone. Selection must occur in the source-defined all-jet physical horizon
before the finite source quotient, and the selected lift's weighted-cosine/connection defect must be
transported to the continued Xi Ward column.

Next exact target is the full `2N+1` source-coordinate observer and its kernel phase transition,
followed by identification of the literal prime--pole--archimedean coordinate vector and a canonical
physical-horizon lift.

## Lean declarations

- `ccmGuinandWeilRectangularSineMomentMatrix`
- `ccmGuinandWeilRectangularSineMoment_rigidity_of_le`
- `ccmGuinandWeilRectangularSineMoment_exists_nonzero_kernel`
- `ccmGuinandWeilRectangularPairedEventPacketMatrix`
- `ccmGuinandWeilRectangularPairedEventPacketMatrix_zero_edge`
- `ccmGuinandWeilRectangularPairedEventPacketMatrix_exists_unbalanced_zero_codiagonal`

Targeted `lake env lean` and `lake build
GaloisForLFunctions.RHTower.CCMGuinandWeilCodiagonalObserverDimension` pass. `#print axioms` reports
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no project axiom, `sorry`,
`admit`, `opaque`, or `unsafe` declaration is used.
