# Source-horizontal rigged prime fundamental symmetry

- **ID:** SC-RIGGED-PRIME-FUNDAMENTAL-SYMMETRY
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md` · SC source-derived global polarization gate
- **Statement:** The two canonical prime axes determine an explicit rank-one fundamental symmetry of the all-prime rigged form on every open-strip fibre; its polarized form is reflection-even, nonnegative, and has exactly the previously classified coefficient radical.

## Goal
Close SC's source-derived global-polarization burden without selecting a Xi zero, postulating positivity, or changing the divisor-bearing form.  This is a pre-divisor construction on the nuclear Deninger height--Köthe source.  Xi determinant/landing remains separate.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `preDivisorRiggedPrimeFundamentalSymmetry_capstone`, `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Let `r` be the sum of the first two canonical prime deltas.  Existing exact delta-kernel formulas make `B_s(r,r) < 0` on the left half-strip and `B_s(r,r) > 0` on the right.  Define the rank-one reflection

`R_s x = x - 2 B_s(x,r) / B_s(r,r) r`

and the oriented symmetry `J_s = orientation(s) R_s`.  Bilinearity gives `R_s² = 1`, `B_s(R_s x,y) = B_s(x,R_s y)`, and `B_s(R_s x,R_s y) = B_s(x,y)`.  Since reflection changes both `B_s` and `J_s` by a sign, `G_s(x,y) = B_s(x,J_s y)` is reflection-even.

For a left fibre, write `x = u + αr` with `B_s(u,r)=0`.  Existing global index-one classification forces `B_s(u,u) ≥ 0`: otherwise the orthogonal negative vectors `u,r` would span a negative plane.  Then `G_s(x,x)=B_s(u,u)-α²B_s(r,r) ≥ 0`.  The reflected positive-index argument gives the right-fibre result.  If `G_s(x,x)=0`, positivity and polarization imply `G_s(x,y)=0` for every `y`; surjectivity of the involution `J_s` then gives `B_s(x,y)=0` for every `y`.  The converse is immediate.  Existing radical classification identifies this nullspace with vanishing real coefficient on every retained prime axis.

## Novelty / literature audit
- **Internal corpus:** no theorem constructs a fundamental symmetry or reflection-even radical-exact polarization for `preDivisorRiggedPrimeWittPairing`; existing finite fundamental symmetries live on different carriers.
- **External parent theory:** fundamental decompositions and `J`-inner products are standard Krein/Pontryagin theory; rank-one perturbations in index-one Pontryagin spaces are classical.
- **Exact application:** no source located for this two-prime, prime--Gamma, nuclear Köthe realization.  `[NOVELTY UNVERIFIED]`.

## No-go closure
- **Exact killing theorem/mechanism:** A direct positive Hilbert-Gram pullback from the physical Möbius--theta source is blocked by the corpus Hilbert-Gram radical/closed-graph no-go, and no coefficient extraction into `DeningerHeightKothe` exists.
- **Strongest positive survivor:** The already-proved exact index-one form itself canonically generates the missing global polarization by a source-selected rank-one reflection.
- **New insight:** SC does not need an external Hilbert carrier for polarization.  Its negative time axis is already present in two literal prime coordinates; only Xi determinant/landing remains after this construction.
- **Status:** Paper proof dependency-closed; Lean formalization in progress.

## Log
- 2026-08-28 — Frozen after corpus searches and hostile no-go audit; paper proof completed. `[PROVED HERE] [NOVELTY UNVERIFIED]`
