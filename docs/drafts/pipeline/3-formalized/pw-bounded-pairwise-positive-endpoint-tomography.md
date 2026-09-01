# PW bounded pairwise-positive endpoint tomography

- **ID:** PW-B-PPK-ENDPOINT-TOMOGRAPHY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` (read-only) · PW-B source-producer burden
- **Statement:** Every bounded symmetric pairwise-positive countable PW grade kernel whose quadratic endpoint-winding response vanishes at every prescribed physical tomography scale is the zero kernel.

## Goal

Kill bounded positive countable matrix completion as a PW-B producer. Exact chain attacked:

`countable PW matrix dynamics -> endpoint-winding darkness -> PW partner balance -> shared Ward charge extinction -> RH`.

If proved, nonzero bounded PSD/Gram histories cannot hide from the literal physical endpoint channel. Any surviving matrix producer must be indefinite, unbounded/singular, or not governed by pointwise quadratic endpoint energy.

## Gates

- [x] 0 -> 1 in-progress: statement fixed by corpus; direct attack and falsifiers identified
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: Lean theorem, target-only `lake build`, axiom audit
- [ ] 3 -> 4 publication-ready: standalone theorem/proof/Lean certificate

## Corpus basis

- `schwarzschildParikhWilczekBoundedPacketEndpointResponse_eq_zero_iff`: physical nodes recover every bounded scalar grade packet.
- `schwarzschildParikhWilczekInfiniteGradeDarkMatrix_energy_zero`: a nonzero countable PSD rank-one matrix is invisible to all three Borel moments.
- `schwarzschildParikhWilczekEndpointWinding_defeats_infiniteGradeDarkMatrix`: literal endpoint winding detects that one explicit dark kernel.
- `pairwiseNonnegativeKernel_row_eq_zero_of_symmetric_of_diagonal_eq_zero`: positivity makes a zero diagonal annihilate its full row.
- `tsum_sum_antidiagonal`: summable double series regroup by total grade.
- `natCast_succ_le_two_pow`: anti-diagonal cardinal growth is absorbed by dyadic rescaling.

## Theorem C1

Let `K : N -> N -> R` be symmetric, uniformly bounded, and `PairwiseNonnegativeKernel K`. Put

`a_K(n) = sum_{i=0}^n K(i,n-i)`

and at the corpus physical nodes `q_j = exp(-(j+1))`,

`E_K(j) = sum_n a_K(n) q_j^(n+2)`.

Then `(forall j, E_K(j)=0) iff K=0`.

## Attack

1. `|a_K(n)| <= (n+1)B`; hence `b_K(n)=a_K(n)/2^n` is bounded.
2. Since `2q_j` is a nonzero sequence in `(0,1)` tending to zero, endpoint darkness and scalar bounded power-series uniqueness force every `a_K(n)=0`.
3. Induct on `m`. In `a_K(2m)`, earlier zero diagonals annihilate their full rows by pairwise positivity and symmetry, leaving only `K(m,m)`; hence `K(m,m)=0` and row `m` vanishes.
4. All rows vanish, so `K=0`.

## Proof

**[PROVED HERE]** Choose `B >= 0` with `|K(i,j)| <= B`. For
`a(n)=sum_{i=0}^n K(i,n-i)`, the triangle inequality gives
`|a(n)| <= (n+1)B`. Since `n+1 <= 2^n`, `b(n)=a(n)/2^n` is bounded by `B`.

Let `q_j=exp(-(j+1))` and `r_j=2q_j`. Then `0<r_j<1`, `r_j -> 0`, and absolute
convergence permits

`E_K(j) = q_j^2 sum_n b(n) r_j^n`.

Thus `E_K(j)=0` for every `j` forces `sum_n b(n)r_j^n=0` for every `j`.
Bounded power-series uniqueness on a nonzero sequence tending to zero gives `b(n)=0`, hence
`a(n)=0`, for every `n`.

Induct on `m`. Assume rows `0,...,m-1` vanish. In

`0=a(2m)=sum_{i=0}^{2m} K(i,2m-i)`,

terms with `i<m` vanish by the induction hypothesis. If `i>m`, then `2m-i<m`, so symmetry and
the induction hypothesis again kill the term. Only `K(m,m)` remains; therefore `K(m,m)=0`.
Pairwise positivity plus symmetry makes a null diagonal annihilate the complete row, so row `m`
vanishes. Induction yields `K=0`. The converse is immediate. Boundedness also majorizes the literal
double endpoint series by a product of two geometric series; antidiagonal regrouping therefore
identifies it with `E_K` without conditional rearrangement.

## Falsifiers

- A bounded symmetric pairwise-positive nonzero kernel with all `E_K(j)=0`.
- Failure of the antidiagonal response to equal the literal absolutely convergent double endpoint energy.
- A physical-node rescaling outside the open unit disk.

## Novelty audit

- Internal: no matching theorem found by corpus research; existing results cover bounded scalar packets, entrywise-positive matrices, finite/sample boundary regularizations, and two explicit PSD dark matrices only.
- External: searches through 2026-08 found standard PSD-kernel factorization/diagonal uniqueness and
  standard Parikh--Wilczek tunneling/correlation papers, but no countable PW grade-kernel endpoint
  tomography or this no-go. Generic ingredients are classical; route-specific theorem is new.

## No-go closure

- **Exact killing theorem/mechanism:** all-scale physical endpoint darkness plus pairwise positivity
  recursively kills every diagonal and row.
- **Strongest positive survivor:** every nonzero bounded symmetric pairwise-positive history is
  detected at some prescribed physical endpoint scale.
- **New insight:** Borel-moment PSD darkness is not stable under literal endpoint completion; positivity plus all physical scales exposes diagonal mass recursively.
- **Status:** Lean theorem
  `schwarzschildParikhWilczekBoundedPairwisePositiveMatrixEndpointDarkRouteKilled` in
  `ThetaCuspHawkingParikhWilczekBoundedPairwisePositiveMatrixEndpointTomography`; target-only build
  passed. Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only. Wired into `RHTower`.

## Log

- 2026-09-01 — C1 fixed from corpus proof graph; Stage 1 opened.
