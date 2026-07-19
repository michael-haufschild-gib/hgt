# Xi transverse Gamma--valuation Schur translation

- **ID:** `xi-transverse-gamma-valuation-schur-translation`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / positive resolution of the Gamma scalar-capacity no-go
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW STRUCTURAL KNOWLEDGE]`
  `[EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** `xi-transverse-valuation-szego-true-aperture-metric`;
  `gamma-conductor-schur-capacity`; `finite-fusion-infinite-hypertranscendence`
- **Lean target:** `RHTower/XiTransverseGammaValuationCoherence.lean`

## Headline theorem

Put `q_p=p^(-1)`.  The half-shifted valuation differences of the actual transverse Xi source are

```text
H_e(p)=sqrt(q_p)(1-q_p)q_p^e,             e>=0.          (1)
```

Their completed cross-prime Gram is

```text
K(p,r)=sum_(e>=0) H_e(p)H_e(r)
      =sqrt(q_p q_r)(1-q_p)(1-q_r)/(1-q_p q_r).         (2)
```

Let `u_p` be the normalized prime-to-Gamma-conductor covariance already isolated by the Gamma
Schur-capacity theorem.  Define the positive rational source gauge

```text
R_p=(p^2+1)^2/[p^2(p+1)^2]
   =(1+q_p^2)^2/(1+q_p)^2.                              (3)
```

Then the exact corrected cross-coordinate is

```text
R_p u_p=-(3 sqrt(2)/4) H_0(p).                          (4)
```

Since `(3 sqrt(2)/4)^2=9/8`, the Schur complement of the scalar Gamma conductor of capacity
`9/8` satisfies the exact self-similarity law

```text
K(p,r)-(R_pu_p)(R_ru_r)/(9/8)
  =K(p,r)-H_0(p)H_0(r)
  =q_p q_r K(p,r).                                      (5)
```

Thus Gamma Schur elimination is literally one-step valuation translation.

At the feature level the same law is

```text
H_(e+1)(p)=q_p H_e(p).                                  (5a)
```

Hence `(H_e(p))_e` is the Hardy coherent eigenvector of the backward shift at `q_p`, `H_0` is the
vacuum coordinate, and `(5)` is the reproducing-kernel defect law for the unilateral shift.  The
source-first conservative colligation requested by the earlier four-unit route is therefore
canonical on this prime--Gamma valuation sector: it is the Hardy shift colligation selected by
the actual valuation filtration, not a transfer function chosen after looking at Xi.

## Finite positive completion

For any nonempty finite valuation prefix `0<=e<N`, any finite prime packet `(p_i)`, coefficients
`x_i`, and conductor coordinate `y`, put

```text
K_N(p_i,p_j)=sum_(e<N) H_e(p_i)H_e(p_j).                (6)
```

Then

```text
sum_(i,j) K_N(p_i,p_j)x_i x_j
 +2y sum_i (R_(p_i)u_(p_i))x_i +(9/8)y^2 >=0.          (7)
```

Indeed the quadratic form is the valuation energy with its first square completed:

```text
(sum_i H_0(p_i)x_i-(3sqrt(2)/4)y)^2
 +sum_(1<=e<N)(sum_i H_e(p_i)x_i)^2.                   (8)
```

This is an explicit coherent positive prime--Gamma block.  It is not an abstract existence
argument.

## Source marking before the singular limit

For an injective `N`-prime packet `(p_j)`, the first `N` marked valuation coordinates form

```text
M_(e,j)=H_e(p_j)
       =sqrt(q_(p_j))(1-q_(p_j))q_(p_j)^e.              (8a)
```

They factor as

```text
M=V(q_(p_0),...,q_(p_(N-1)))^T
    diag(sqrt(q_(p_j))(1-q_(p_j))).                     (8b)
```

The reciprocal-prime nodes are distinct and every diagonal factor is positive, so `det M != 0`.
Thus valuation depth reconstructs every finite prime packet before a cofinal limit is taken.

This closes a specific gap exposed by the general HT graph-saturation theorem.  Raw
prime-sample/monomial graphs may become maximally multivalued at a singular carrier; the positive
survivor is to retain a source-selected divergent Cholesky/orthogonal-polynomial marking before
closure.  Here the marking is not guessed after the fact: it is the actual prime-power valuation
filtration, its finite matrix is `(8b)`, and Gamma Schur elimination advances that marked frame by
one coordinate.  The remaining Xi map must therefore act on the valuation-coordinate graph, not
on an unmarked scalar codiagonal of the prime samples.

## Why this is the positive survivor of the no-go

The diagonal prime covariance required the scalar conductor to pay the nonsummable cost
`sum_p u_p^2`; that route was correctly closed.  The strongest positive statement exposed by
the obstruction was that a successful fixed-capacity block must contain unbounded coherent
off-diagonal energy.  Equations `(1)`--`(8)` construct precisely such a covariance from the
actual prime-power valuation tower.

The correction `(3)` does not add a new transcendental source.  It is an explicit positive
rational gauge.  The `+2` Xi-shift hypertranscendence theorem shows the complementary principle:
after rational corrections are removed, the exposed prime carrier remains hypertranscendental
over the genuine coordinate field.  The finite-fusion theorem then says that advancing valuation
depth creates a genuinely new differential layer.  Equation `(5)` is the Hilbert counterpart:
after the Gamma coordinate is eliminated, the residual covariance is exactly the next valuation
tail rather than a collapsed finite-rank remainder.

This is the concrete use of the HTGeometry result in the RH architecture:

```text
finite fusion:       V_e -> V_(e+1) is a new HT layer,
Hilbert completion:  K   -> q_p q_r K is the Schur residual,
Gamma coupling:      the eliminated coordinate is exactly H_0.             (9)
```

The algebraic free-layer filtration and the positive Hilbert filtration are therefore the same
source grading viewed in two categories.

## RH impact and remaining open theorem

The previous true-aperture card left two issues mixed together: compatibility across primes and
the archimedean channel, and transport to the Xi target.  Equations `(4)`--`(8)` close the first
issue for the normalized Gamma conductor after its explicit rational source gauge.  The remaining
open theorem is narrower:

> Construct the source-defined map from this completed prime--Gamma valuation block to the finite
> Xi boundary-strip leakage vectors and prove its Pick kernel is positive for every finite packet,
> with the established four-unit normalization.

Equivalently, construct on a source-defined graph core an intertwiner from this canonical Hardy
shift colligation to the physical Xi boundary shift and prove it is nonexpansive.  The source
space, vacuum vector, shift, prime coherent states, and Gamma coupling are now fixed before the Xi
target is evaluated.

A cofinal form of that contraction would imply the existing boundary relative-trace estimate and
hence RH.  Nothing here proves that contraction or RH.

## Novelty boundary

Szego kernels, Schur complements, and completing a square are classical.  The candidate-new
content is the exact source-specific conjunction:

1. the actual normalized Gamma cross-coordinate becomes the first half-shifted transverse
   valuation coordinate under the explicit gauge `(3)`;
2. Gamma Schur elimination becomes exact valuation translation `(5)`; and
3. this is the Hilbert realization of the independently proved hypertranscendental fusion
   successor law.

No matching statement was found in the live corpus.  External novelty is not yet audited.

## Lean status

`XiTransverseGammaValuationCoherence.lean` contains the exact coordinate identity `(4)`, the
Hardy-shift eigenvector law `(5a)`, the completed Schur-translation law `(5)`, and the finite block
positivity `(7)`.  Direct compilation and the narrow object build pass.  The principal theorems
use only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`; no project axiom
or proof placeholder is present.

## Gates

- [x] 0 -> 1: coherent positive survivor extracted from the Gamma capacity obstruction
- [x] 1 -> 2: exact rational, Schur-residual, and finite quadratic-form proofs closed
- [x] 2 -> 3: direct Lean check, narrow object build, and standard axiom audit
- [ ] 3 -> 4: external novelty audit and source-to-Xi Pick contraction

## Log

- 2026-07-19 -- Transposed the valuation--Szego completion from apertures to primes.  Exact
  simplification of the normalized Gamma cross revealed the first half-shifted valuation
  coordinate.  Its Schur complement removes depth zero and advances the valuation filtration by
  one, resolving the diagonal-capacity no-go with an explicit coherent positive block.
