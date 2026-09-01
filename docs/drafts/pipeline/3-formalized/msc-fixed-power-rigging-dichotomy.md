# MSC fixed-power rigging dichotomy

- **ID:** MSC-PWR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` MSC · `HedenmalmGammaSewnSquarefreeFisherPhysicalHilbertWall.lean`
- **Statement:** At a strict-right Xi zero, every fixed Dirichlet power rigging either fails to admit the physical squarefree-Möbius column cofinally or makes its norm tend to zero while the regular germ tends to `2`; hence no closed single-valued linear graph retains the admitted cofinal pairs.

## Goal
Kill MSC's fixed-power rigged-Hilbert continuation branch. Proof chain: strict-right zero → exact weighted source exponent → admission/collapse dichotomy → vertical defect `(0,2)` → no closed single-valued graph. Survivor must be genuinely multivalued or use non-power/distributional renormalization retaining the boundary scalar.

## Gates
- [x] 0 → 1  in-progress: corpus-derived, source-pure, exact norm-ratio attack
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted build green, axioms audited
- [ ] 3 → 4  publication-ready: standalone paper

## Proof `[PROVED HERE]`
Let `b=2 Re rho+2k-1`. Multiplication by the fixed Dirichlet power `n^{-k}` shifts the physical aperture from `(rho-sigma)/(sigma-1)` to `(rho-sigma+k)/(sigma-1)`. The exact Hilbert wall `Re u>-1/2` therefore gives admission iff `sigma<b`. Thus a cofinal admitted interval exists iff `b>1`, equivalently `k>1-Re rho`; otherwise no `sigma>1` is admitted.

Assume `b>1` and put `sigma_N=1+(b-1)/(N+2)`. Then `1<sigma_N<b` and `sigma_N→1+`. The exact squared norm is
`Z_sq(b+1-sigma_N)/Z_sq(sigma_N)`. Set `a=(b+1)/2>1`. Since `b+1-sigma_N≥a` and squarefree Dirichlet mass decreases with exponent, the numerator is at most the finite constant `Z_sq(a)`. The proved critical-mass law gives `1/Z_sq(sigma_N)→0`; squeezing gives source norm square, hence source norm, tending to zero.

For every regular term `g`, the proved MSC germ law gives
`h_{sigma_N}(u_{sigma_N})→2`. Any closed linear relation containing all admitted pairs therefore contains `(0,2)`. Its zero-source fibre is nontrivial, so it is not single-valued. At a strict-right Xi zero the existing residue-split theorem supplies the required analytic `g`, completing the stated MSC chain.

## No-go closure
- **Exact killing theorem/mechanism:** Exact admission threshold plus normalized critical-mass escape forces a nonzero vertical graph limit.
- **Strongest positive survivor:** Universal vertical value `2` (energy `4`) survives every admissible fixed power rigging.
- **New insight:** Power damping repairs membership only by collapsing the source; it cannot produce a closed operator graph carrying the MSC regular response.
- **Status:** Formalized in `HedenmalmGammaSewnSquarefreeFisherPowerRiggingNoGo.lean`; capstone `strictRightXiZero_exists_mscPowerRiggedGraphNoGo`. Targeted build green; axioms only `propext`, `Classical.choice`, `Quot.sound`. Corpus and 2026 literature collision audits negative.

## Log
- 2026-09-01 — frozen in Stage 1 after corpus and primary-literature audit.
