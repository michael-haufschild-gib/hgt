# SC skew-adjoint additive two-port no-go

- **ID:** SC-SA2P-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** `../1-in-progress/rh-current-frontier-map.md` · SC
- **Statement:** Centered entire skew-adjoint additive two-port determinants cannot converge compact-open to normalized centered Xi.

## Goal

Test chain `skew-adjoint additive SC stages → Xi determinant landing → SC divisor/orientation endpoint → RH` at its earliest non-circular landing gate.

## Gates

- [x] 0 → 1: source-pure two-port symmetry and Xi landing identified
- [x] 1 → 2: quadratic-jet sign proof dependency-closed
- [x] 2 → 3: Lean theorem `not_tendstoLocallyUniformly_skewAdjointAdditiveSCTwoPortMatrix_normalizedXiC`
- [ ] 3 → 4: publication-ready

## Approach

For Schwarz reflection `A♯(z)=conj(A(conj z))`, the skew-adjoint matrix `[[1,A],[-A♯,1]]` has determinant `1+A A♯`. If `A(0)=0`, its second central jet is `2 A′(0) conj(A′(0))`, hence has nonnegative real part. Cauchy jet convergence preserves that closed half-line, while normalized Xi has strictly negative central second jet.

## No-go closure

- **Exact killing theorem/mechanism:** compact-open Xi landing contradicts the central-curvature sign.
- **Strongest positive survivor:** opposite Hermitian matrix `[[1,A],[A♯,1]]` has exact curvature `−2|A′(0)|²`; the sign obstruction is sharp.
- **New insight:** surviving SC landing must use Hermitian sign, a nondeterminantal readout, or a singular/operator-valued limit; independent additive legs remain universal.
- **Status:** paper proof closed; Lean module `GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicSkewAdjointAdditiveTwoPortNoGo`. Literature search through 2026-08-31 found operator/Fredholm RH programs, but no matching SC two-port curvature no-go.

## Log

- 2026-09-01 — paper proof, sharp survivor, Lean formalization closed
