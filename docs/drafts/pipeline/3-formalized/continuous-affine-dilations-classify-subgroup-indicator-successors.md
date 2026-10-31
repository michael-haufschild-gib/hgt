# Continuous affine dilations classify subgroup-indicator successors

- **ID:** AFFINE-CONTINUOUS-SUBGROUP-SUCCESSORS
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Cyclic Haar obstruction](cyclic-haar-averages-force-infinite-index-at-continuous-dilations.md)
- **Statement:** For an additive subgroup `H≤ℚ`, a Hermitian kernel on `Aff(ℚ)` with translation reading `1_H`, finite negative index, and positive-dilation reading continuous at one exists exactly when `H={0}` or `H=ℚ`.

## Positive boundary

For `H=ℚ`, the constant kernel `1` is positive definite. For `H={0}`, the indicator of the dilation subgroup, `k(g)=1[shift(g)=0]`, is positive definite by extension from a subgroup. Both have constant dilation reading `1` and index zero.

Every nonzero proper subgroup is excluded, including the single-prime successor `1_{ℤ_(p)}`. A finite prime height supplies the obstruction.

## Proof for nonzero proper subgroups

Conjugating the affine kernel by dilation by a nonzero element of `H` rescales the successor subgroup to contain `ℤ`, while preserving dilation readings and finite-index bounds. If `H≠ℚ`, some prime `p` has finite height `h`, meaning `1/p^h∈H` but `1/p^(h+1)∉H`. Otherwise Bézout combinations of prime-power reciprocals would generate every rational. For `q∈H`, Bézout applied to its reduced numerator and denominator first gives `1/den(q)∈H`; integer multiplication then gives each reciprocal prime-power factor. Thus membership forces `v_p(q)≥−h`.

Let `d_H(q)` be the order of `q+H` in `ℚ/H`. It is positive and divides the ordinary denominator. For nonzero `q`, membership of `d_H(q)q` in `H` gives `v_p(d_H(q))+v_p(q)≥−h`, hence `d_H(q)≥p^max(0,−v_p(q)−h)`. After the existing zero-axis polynomial correction, integer translations are invariant. The [periodic saturation argument](periodic-affine-saturation-recovers-all-successor-periods.md) then derives invariance under every member of `H`: each has the identity coefficient.

Consequently the column orbit under `T_b` has period `d_H(b/a)` and is orthonormal through that period. Its fixed projection has squared norm `1/d_H(b/a)`. If `c` is a natural multiple of `b`, the moving column of slope `c` is fixed by `T_c`. Averaging the other moving column over its `T_c` orbit leaves their pairing unchanged. The averaged moving norm is at most `1/d_H(c/a)`, because its discarded fixed-projection norm is nonnegative. Cauchy–Schwarz therefore bounds the squared moving pairing by `1/d_H(c/a)`.

For `i<n`, set `e_i=(N+1)(i+1)`, `E=(N+1)(n+1)`, and choose

`a_(N,i)=1+p^(-e_i)`, `b_N=p^(-E)`.

These positive slopes tend to one, and `a_(N,i)/b_N=p^E+p^(E−e_i)` is a positive integer. Their p-adic norms are `p^e_i`; thus `|b_N/a_(N,i)|_p≥p^(N+1)` and, for `i<j`, `|a_(N,j)/a_(N,i)|_p≥p^(N+1)`. The height bound gives `1/d_H(q)≤p^h/|q|_p`. Fixed diagonal norms and squared moving off-diagonal pairings are consequently bounded by `p^(h−N−1)`, which tends to zero. Continuity then gives the projected Gram limit `J−I`, contradicting finite index.

## Lean verification

- `BiarithmeticGeometry/Affine/SubgroupPrimeHeight.lean`, `SubgroupOrders.lean`, `SubgroupNormControl.lean`, and `PrimePowerGrids.lean` prove finite prime height, quotient-order bounds, and the separated grids.
- `AdelicKreinGeometry/Haar/SubgroupEndpoints.lean` gives both positive carriers. The [saturation theorem](periodic-affine-saturation-recovers-all-successor-periods.md) recovers every successor-subgroup period.
- `AdelicKreinGeometry/Haar/SubgroupOrbits.lean`, `SubgroupMovingBounds.lean`, and `SubgroupGramLimit.lean` prove reciprocal-order projection norms, the moving-correlation bound, and convergence to `J−I`.
- `AdelicKreinGeometry/Haar/SubgroupClassification.lean`: `negIndex_eq_top_of_nontrivial_subgroup_continuous_dilation` proves the obstruction for every nonzero proper subgroup; `exists_finite_index_continuous_subgroup_successor_iff` gives the exact classification.

All modules passed direct `lake --old env lean` audits. Printed transitive axiom closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
