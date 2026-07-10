# Rectangle Residue Multi-Zero

- **ID:** rectangle-residue-multi-zero
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `RHTower/RectangleResidue.lean`
- **Statement:** The boundary integral of the logarithmic derivative of a finite product of interior zero factors times a nonvanishing analytic cofactor equals `2πi` times the sum of the multiplicities.

## Goal

Remove the placeholder from the finite multi-zero rectangle argument principle used by RHTower infrastructure.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `rectIntegral_logDeriv_multi_zero`, `lake build` green, axiom check PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Decompose the logarithmic derivative into finite Cauchy-kernel terms plus the analytic cofactor term, prove edgewise integrability, use finite additivity of the rectangle integral, apply the single-kernel rectangle integral to each zero, and sum.

## Log

- 2026-07-06 — discharged the previous placeholder in `rectIntegral_logDeriv_multi_zero`; repaired current `integral_finsetSum` API usage and pointwise finite-sum integrability conversion; verified with file build, umbrella build, `/tmp` axiom checks, generated index, and `scripts/formal_tools.py lint --check-generated`.
