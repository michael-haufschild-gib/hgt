# Route J principal-relative Julia capacity no-go

- **ID:** `route-j-principal-relative-julia-capacity-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM / ROUTE-BOUNDARY CLASSIFICATION
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE WELD] [NOVELTY UNVERIFIED]`
- **RH used:** no
- **Computation used:** no
- **Live successor:** `../../1-in-progress/route-j-principal-relative-julia-current.md`

## Result

The unrenormalized Route-J no-go left a semantic escape: insert a principal-relative counterterm
before good/bad projection and ask the resulting current to orient negative completed-source
excursions.  Four structural classes and one existing arithmetic dressing are now closed.

### 1. Positive channel-linear currents

Every scalar channel-linear quadratic current is

```text
Q(g,h)=a g^2+2bgh+c h^2.                                 (1)
```

If `Q(g,h)>=0` for all real `g,h` and `c=0`, then `b=0`.  Indeed `a=Q(1,0)>=0`, while
nonnegativity at `(g,h)=(b,-(a+1))` gives

```text
0 <= -(a+2)b^2,                                          (2)
```

so `b=0`.  Thus a positive current that cancels the pure-bad self-current also loses every mixed
good/bad orientation term.  If both diagonal weights vanish, the whole current vanishes.

### 2. Negative-excursion dominance

Suppose

```text
g-h<0 -> (g-h)^2 <= Q(g,h)                               (3)
```

for all real channel masses.  At `(g,h)=(0,1)`, `(3)` gives `1<=c`.  Hence even without assuming
positivity, universal orientation forces retention of the full pure-bad diagonal coefficient.
Moving a cancellation before projection does not change this algebraic requirement.

### 3. Canonical anchored Schur residual

For one normalized-kernel node with anchor coefficient `k` and nonzero mass `u`, the removed
anchor square and canonical Schur residual are

```text
A=u^2 k^2,
S=u^2(1-k^2),
A+S=u^2.                                                  (4)
```

Exactly

```text
A<=S <-> k^2<=1/2.                                       (5)
```

The Julia coefficient `K(x t)` tends to one as `x->0`.  Therefore throughout an eventual
source-faithful zero-scale neighbourhood, the removed anchor correlation is strictly larger than
the Schur residual.  The canonical positive relative current deletes the very rank-one component
that carries the desired source excursion.

### 4. Globally positive quadratic kernels

Let `H(i,j)` be a real kernel whose every two-node quadratic compression is nonnegative.  If
exact principal subtraction cancels one bad self-current, so `H(j,j)=0`, the two-channel theorem
forces `H(i,j)=0` for every `i`; symmetry also gives `H(j,i)=0`.  Hence the entire bad row and
column vanish.  This closes a genuine global loophole: adding all prime and archimedean nodes to a
positive-semidefinite quadratic current cannot restore a cancelled bad channel through cross-block
coupling.  Conversely, any nonzero cross term incident to a null bad diagonal certifies ambient
indefiniteness.

## Arithmetic specialization

At the sixth-power aperture `L_m=6 log m`, every prime

```text
2m^4<p<=5m^4                                             (6)
```

has prime-power length one.  Its reduced source satisfies

```text
good_p(L_m)=0,
bad_p(L_m)>0.                                             (7)
```

The good identity follows by unfolding the stable and exceptional-square branches.  Strict bad
positivity follows from the proved negative sine chamber and positive lower bound

```text
(log p)^2/(4p) <= bad_p(L_m)^2.                           (8)
```

Consequently any packet-hereditary channel-linear current with cancelled pure-bad diagonal fails
on every actual cell in `(6)`:

```text
(good_p-bad_p)^2=bad_p^2>0=Q(good_p,bad_p).               (9)
```

This is stronger than an abstract one-node counterexample because the forbidden cells occur in
the literal CCM arithmetic source on the same cofinal apertures that force the unrenormalized
energy floor.

## Existing compact dressing is not the survivor

The exact Gamma--Julia endpoint-correction multiplier satisfies

```text
chi_(p,e)^2<=1/2.                                         (10)
```

On a nonzero pure-bad Route-J cell, domination by the dressed square would require

```text
bad_p^2 <= (chi_(p,0) bad_p)^2,
```

hence `1<=chi_(p,0)^2`, contradicting `(10)`.  The Hilbert--Schmidt dressing remains a valid
phase-faithful endpoint-correction representation, but it cannot be repurposed as the missing
first-clock relative capacity.

## Exact boundary

The following are closed:

1. post-projection diagonal subtraction;
2. positive channel-linear pre-projection counterterms;
3. any packet-hereditary diagonal-null current with universal negative-excursion dominance;
4. the canonical anchored covariance/Schur complement in the source-faithful limit;
5. every globally coupled pairwise-positive quadratic kernel with cancelled bad diagonals;
6. the existing Gamma--Julia endpoint Hilbert--Schmidt diagonal dressing.

This does not close Route J.  A source-constrained current on the complete prime--archimedean
packet could still use a new exact arithmetic cross-block identity, but a quadratic version must
be indefinite on the ambient coordinate space and prove nonnegativity only on the literal source
locus.  A genuinely nonlinear current is the other unexcluded class.  No other named route owns
either construction, so this remains Route J's open core.

## Lean realization

Generic infrastructure:

```text
formal/GaloisForLFunctions/HTGeometry/TwoChannelRelativeCapacityNoGo.lean
```

Headline declarations:

```text
twoChannelLinearCurrent_mixedWeight_eq_zero_of_nonnegative_of_badWeight_eq_zero
twoChannelLinearCurrent_eq_goodDiagonal_of_nonnegative_of_badWeight_eq_zero
one_le_twoChannelLinearCurrent_badWeight_of_negativeExcursionDominance
not_negativeExcursionDominance_of_twoChannelLinearCurrent_badWeight_eq_zero
pairwiseNonnegativeKernel_entry_eq_zero_of_diagonal_eq_zero
not_pairwiseNonnegativeKernel_of_entry_ne_zero_of_diagonal_eq_zero
pairwiseNonnegativeKernel_row_eq_zero_of_symmetric_of_diagonal_eq_zero
pairwiseNonnegativeKernel_cross_eq_zero_of_symmetric_of_diagonal_eq_zero
oneNodeAnchorSquare_le_anchoredSchurResidual_iff
not_oneNodeAnchorSquare_le_anchoredSchurResidual_of_half_lt_sq
```

Arithmetic specialization:

```text
formal/GaloisForLFunctions/RHTower/CCMFirstClockJuliaPrincipalRelativeNoGo.lean
```

Headline declarations:

```text
eventually_not_juliaSchurResidual_orients_sourceFaithfulAnchor
ccmFirstClockReducedGoodPrimeTerm_eq_zero_of_length_one
ccmFirstClockJuliaSixthPower_block_goodTerm_eq_zero
ccmFirstClockJuliaSixthPower_block_badTerm_pos
ccmFirstClockJuliaSixthPower_block_not_oriented_by_badDiagonalNullLinearCurrent
ccmFirstClockJuliaSixthPower_block_not_oriented_by_endpointCorrectionDressing
```

Both modules are imported by their area umbrellas.  All declarations are unconditional and use no
project axiom, placeholder, unsafe declaration, or numerical computation.

## Novelty calibration

Positive-cone algebra and anchored Schur-complement identities are standard and receive no novelty
credit.  Candidate new content is only the exact weld to the pure-bad sixth-power CCM prime cells
and the exclusion of the existing arithmetic endpoint dressing.  Targeted corpus and arXiv
searches found no exact arithmetic-Julia/first-clock collision; external novelty remains
unverified.

## Gates

- [x] dependency-closed paper proof
- [x] generic theorem surface formalized unconditionally
- [x] source-specific pure-bad block specialization formalized
- [x] anchored source-faithful Schur failure formalized
- [x] existing endpoint dressing excluded formally
- [x] wired into `HTGeometry` and `RHTower` umbrellas
- [x] globally positive cross-block rescue excluded formally
- [ ] construct or refute ambient-indefinite/nonlinear full-source survivor
