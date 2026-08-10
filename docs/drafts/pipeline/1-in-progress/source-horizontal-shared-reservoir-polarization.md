# Source-horizontal shared-reservoir polarization

- **ID:** `source-horizontal-shared-reservoir-polarization`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / RANK--TRACE HANDOFF FALSIFIED
- **Source:** `source-horizontal-moment-neutral-amplification-no-go.md`;
  `claude-zeta23-rank-trace-audit.md`;
  `formal/GaloisForLFunctions/RHTower/SourceZeroHorizontalCarrier.lean`
- **Statement:** A finite same-sign packet of nonzero source-horizontal coefficients admits a
  coefficient-reconstructing, trace-zero shared-reservoir matrix with arbitrarily small Frobenius
  square and inertia `(m-1,1,0)`; reflection negates the matrix. The low-positive-index
  orientation has positive index one, but the paper's rank--trace inequality is blind to its
  amplified negative index, while simultaneous realization of both orientations restores linear
  positive-index cost.

## Goal

Replace the failed direct sum of independent `2 x 2` hyperbolic blocks by one cross-prime coupling
which shares the compensating sign across the whole packet. Preserve prime labels, the exact
divisor-multiplicity copy, every coefficient, and reflection before scalarization. Then test the
result against the exact sign and index input of Claude's multiplicity-aware rank--trace inequality.

## Gates

- [x] 0 -> 1 in-progress: exact source-pure matrix and hostile falsifiers frozen
- [x] paper proof dependency-closed
- [ ] 1 -> 2 fully-proven: external novelty classification and final manuscript audit
- [ ] 2 -> 3 formalized: exact matrix, energy, inertia, reconstruction, packet, and reflection laws
- [ ] RH

## Heavy conjecture loop

### C0 -- fractional compression

**Conjecture.** Apply `a -> sign(a)|a|^alpha`, `1/2 < alpha < 1`, to turn source `ell^2` control
into every subquadratic Schatten test without discontinuous sign normalization.

**Failure.** The map is bounded and coefficient-faithful, but `ell^2` does not imply `ell^(2alpha)`.
Finiteness of all transformed second moments is exactly the already-formalized all-order Schatten
receiver, hence neutral grade. Fractional compression changes the reporter but supplies no source
estimate.

### C1 -- threshold-layer integration

**Conjecture.** Integrate thresholded rank bounds over the spectral counting function to obtain the
missing all-order source law.

**Failure.** Layer-cake identities reconstruct Schatten moments from threshold counts but cannot
improve them. The fixed-threshold theorem already proves linear cost, while the source packet hides
its rank only by moving every eigenvalue below the threshold. This is another exact receiver.

### C2 -- one shared compensating reservoir

Let `I` be finite, `m = |I| >= 2`, and let `a_i` be nonzero real coefficients with one common sign
`s in {+1,-1}`. Put `w_i=|a_i|`, `u_i=sqrt(w_i)`, and

```text
A_w = diag(w_i) - u u^T,
M_a = s A_w.
```

Then

```text
(M_a)_(ii) = 0,
(M_a)_(ij) = -s sqrt(w_i w_j)   (i != j),
tr(M_a) = 0.
```

**Verdict: PROVED ON PAPER.** Since every `w_i>0`, diagonal scaling gives the congruence

```text
A_w = diag(sqrt(w)) (I - 1 1^T) diag(sqrt(w)).
```

The middle form is positive on the codimension-one hyperplane `sum x_i=0` and negative on the
all-ones line, with no radical. Therefore

```text
inertia(A_w)  = (m-1, 1, 0),
inertia(-A_w) = (1, m-1, 0).
```

Moreover

```text
||M_a||_F^2
  = sum_(i != j) w_i w_j
  = (sum_i w_i)^2 - sum_i w_i^2
  <= (sum_i w_i)^2.
```

For an off-line `XiZeroCopy q`, the corpus proves that every
`sourceZeroHorizontalPrimeCarrier q p` is nonzero, all coefficients have the same sign, and their
absolute values tend to zero cofinally. Given `m>=2` and `eta>0`, choose `m` distinct prime labels
with `w_i < sqrt(eta)/m`. Then `||M_a||_F^2 < eta`. Thus raw inertia can grow arbitrarily while
trace remains zero and Frobenius square tends to zero, with only one opposite-sign reservoir.

### C3 -- coefficient reconstruction

For `m>=3`, choose distinct `j,k` different from `i`. Every off-diagonal entry is nonzero and

```text
a_i = - (M_a)_(ij) (M_a)_(ik) / (M_a)_(jk).
```

**Verdict: PROVED ON PAPER.** Substitution cancels `sqrt(w_j w_k)` and returns `s w_i=a_i`.
Hence the coupling does not retain labels merely as metadata: the complete labelled coefficient
packet is algebraically reconstructible from the matrix itself.

Reflection sends every `a_i` to `-a_i`, keeps `w_i`, and therefore sends `M_a` to `-M_a`. Both
orientations and the exact divisor-multiplicity copy survive.

### C4 -- rank--trace contradiction

**Conjecture.** Use the orientation with inertia `(1,m-1,0)` so the paper's index allowance stays
`b=1` while source-horizontal index grows.

**Failure.** Claude's inequality prices `posIndex(Q)` only. On the cheap orientation the amplified
directions are negative, `tr(Q)=0`, and `||Q||_F^2` can vanish; the inequality has no term which
rewards or penalizes their number. It reduces to a true but asymptotically unchanged certificate.
On the reflected orientation `posIndex(Q)=m-1`, so the `c^2 b` allowance is linear. If both
orientations are represented simultaneously by `M_a direct_sum (-M_a)`, positive index is `m` and
the original linear wall returns exactly.

## No-go closure

- **Exact killing theorem/mechanism:** one-sided rank--trace sees positive inertia only. Reflection
  exchanges the cheap amplified negative sector with an expensive amplified positive sector;
  simultaneous direct sum adds their positive indices.
- **Strongest positive survivor:** moment-neutral, coefficient-reconstructing inertia
  polarization with one shared reservoir, exact reflection negation, and arbitrarily small
  Frobenius square on actual prime-labelled source packets.
- **New insight:** obstacle is not moment-neutral amplification or coefficient fidelity. It is
  simultaneous-orientation additivity. A surviving inequality must either be signed/two-sided in
  inertia or derive a source identification of the reflected matrices before direct sum. This is
  the finite matrix shadow of the corpus's same-carrier non-equivariant producer.
- **Status:** paper proof dependency-closed. Diagonal-minus-rank-one inertia and weighted-graph
  congruence are parent linear algebra; exact source-horizontal specialization, reconstruction
  formula, and reflection/rank--trace boundary are candidate corpus-new content. Lean pending.

## External boundary

Rank-one Hermitian updates, Sylvester inertia under congruence, and inertia of weighted adjacency
matrices are classical. No novelty is claimed for those components. Novelty claim, if retained
after deeper audit, is restricted to the coefficient-faithful source-horizontal construction and
its exact orientation-sensitive failure against the 2026 multiplicity-aware rank--trace
certificate.

## Log

- 2026-08-10 -- C0 and C1 killed; C2 and C3 proved; C4 killed; exact positive survivor frozen.
