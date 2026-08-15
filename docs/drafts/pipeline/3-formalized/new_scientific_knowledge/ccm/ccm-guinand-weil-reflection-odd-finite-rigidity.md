# CCM Guinand--Weil reflection-odd finite rigidity

- **Status:** LEAN-FORMALIZED
- **Lane:** CCM-FU / finite Guinand--Weil source dictionary
- **Novelty scope:** corpus-new CCM rigidity and cofinal frontier reduction; sine--Chebyshev and
  Vandermonde determinant mechanisms are classical
- **External priority:** no primary CCM source located states the event/reflection balance
  equivalence; priority of the CCM consequence remains unverified
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMGuinandWeilReflectionOddRigidity.lean`

## Result

For `N` event angles `theta_i`, define

```text
S(k,i)=sin((k+1)*theta_i),        0<=k,i<N.                (1)
```

The Chebyshev identity

```text
sin((k+1)*theta)=U_k(cos theta)*sin(theta)
```

and the facts `deg U_k=k`, `lead(U_k)=2^k` give

```text
det S
 = (prod_i sin theta_i)
   *(prod_k 2^k)
   *prod_(i<j)(cos theta_j-cos theta_i).                   (2)
```

Lean proves the matrix factorization behind (2), the triangular Chebyshev coefficient determinant,
and the full determinant equality. Hence the first `N` sine moments determine all `N` coefficients
when cosine nodes are distinct and sine nodes are nonzero.

Conversely, Lean proves exact degeneracy: `det S=0` if and only if one sine factor vanishes or two
cosine nodes collide. The factorization has no additional singular mechanism.

For literal Guinand--Weil event matrices, assign forward weight `a_i` to horizon `omega_i` and
reflected weight `a_i*` to horizon `1-omega_i`. On modes `0,...,N`, Lean proves

```text
Packet(k+1,0)
 = [sum_i (a_i-a_i*) sin((k+1)*2*pi*omega_i)]/[pi*(k+1)].  (3)
```

Combining (2) and (3) gives the exact equivalence

```text
Packet(k+1,0)=0 for every 0<=k<N
  iff
a_i=a_i* for every i.                                     (4)
```

If the horizons are distinct and lie strictly between `0` and `1/2`, Lean discharges the
nondegeneracy hypotheses: sine is positive and cosine is strictly decreasing on the corresponding
angle interval `(0,pi)`.

## CCM consequence

For a square `N`-orbit packet, distinct events cannot secretly cancel the zero-edge reflection-odd
incidence. Exact erasure of this complete square mode block is only orbitwise reflection balance.
The already-formalized source-reflection law then makes that packet diagonal, and its half-horizon
mode can still be negative.

Formula (2) shows exactly where square rigidity can lose uniformity: a horizon approaches `0` or
`1/2`, or two horizons collide in cosine coordinate. It does not govern a packet with more event
orbits than observed modes. In that overcomplete regime a nonzero codiagonal kernel exists by
dimension alone, even with separated interior horizons; the follow-on observer-dimension theorem
formalizes this correction.

Within an undercomplete subfamily, a quantitative successor could either:

- prove a source-derived uniform lower frame bound for the completed sine-moment family and use it
  in a Schur-complement positivity estimate; or
- renormalize the endpoint/collision defect and identify its noncompact limit with the continued Xi
  Ward column while retaining four-unit energy.

For the literal completed source, these alternatives are insufficient without a source-level
selection law because the prime packet may be overcomplete and the pole/archimedean sources are
continuous. This theorem does not construct canonical `Pi(lambda,k)` or prove RH.

## Lean declarations

- `ccmGuinandWeilSineMomentMatrix`
- `ccmGuinandWeilChebyshevUEvaluationMatrix_factor`
- `ccmGuinandWeilChebyshevUCoeffMatrix_det`
- `ccmGuinandWeilSineMomentMatrix_factor`
- `ccmGuinandWeilSineMomentMatrix_det`
- `ccmGuinandWeilSineMomentMatrix_det_eq_zero_iff`
- `ccmGuinandWeilSineMomentMatrix_det_ne_zero`
- `ccmGuinandWeilSineMoment_rigidity`
- `ccmGuinandWeilPairedEventPacketMatrix_zero_edge`
- `ccmGuinandWeilPairedEventPacketMatrix_offDiagonal_zero_iff_reflection_balanced`
- `ccmGuinandWeilPairedEventPacketMatrix_offDiagonal_zero_iff_reflection_balanced_of_open_half`

Targeted `lake env lean` and `lake build
GaloisForLFunctions.RHTower.CCMGuinandWeilReflectionOddRigidity` pass. `#print axioms` reports only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no project axiom, `sorry`, `admit`,
`opaque`, or `unsafe` declaration is used.
