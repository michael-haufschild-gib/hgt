# Boundary modulus critical line

- **ID:** boundary-modulus-critical-line
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/g5-over-fq-deligne-unitarity.md` and its `BoundaryModulus` σ-fixed-modulus floor; Lean files `formal/GaloisForLFunctions/Core.lean` and `formal/GaloisForLFunctions/BoundaryModulus.lean`
- **Statement:** For a positive real base `p>1`, the diagonal Bohr coordinate `p^{-s}` has boundary radius `p^{-1/2}` exactly when `Re(s)=1/2`; equivalently, after scaling by the inverse boundary radius, it has unit norm exactly on the critical line.

## Goal
This banks the scalar fixed-modulus floor used by the G5-over-function-field recovery: the field's σ-fixed-modulus locus is the critical-line analogue before the Deligne purity import. It does not formalize sheaves, Frobenius eigenvalues, function-field specialization, polarization, Deligne Weil II, or the full G5 unitarity theorem.

## Paper Proof
For a positive real base `p`, the Bohr coordinate attached to `s` is `x=p^{-s}`. The standard complex-power norm formula gives
`|p^{-s}| = p^{-Re(s)}`. Since `p>1`, the map `a -> p^a` is injective on real exponents, so
```
|p^{-s}| = p^{-1/2}  iff  -Re(s) = -1/2  iff  Re(s)=1/2.
```

Let `boundaryRadius(p)=p^{-1/2}` and normalize a scalar by `boundaryUnitNormalize(p,x)=boundaryRadius(p)^{-1} x`. For any positive radius `r`, multiplication by `r^{-1}` gives
`|r^{-1}x|=1` iff `|x|=r`, by multiplying both sides by `r`. Applying this with `r=p^{-1/2}` and `x=p^{-s}` yields
```
|boundaryUnitNormalize(p,p^{-s})|=1  iff  |p^{-s}|=p^{-1/2}  iff  Re(s)=1/2.
```
Thus the boundary-normalized diagonal coordinate is unitary exactly on the critical line.

## Gates
- [x] 0 -> 1  in-progress: exact scalar σ-fixed-modulus floor extracted from the G5-over-`F_q` card.
- [x] 1 -> 2  fully-proven: paper proof above, using only the norm of complex powers and positive-radius normalization.
- [x] 2 -> 3  formalized: Lean theorems `norm_cpow_eq_critical_iff`, `norm_inv_smul_eq_one_iff`, `boundaryUnitNormalize_norm_eq_one_iff`, and `diagonalBoundary_unit_norm_iff`; names checked by scratch file; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: cite as the formal certificate for the fixed-modulus/critical-line scalar floor.

## Log
- 2026-06-19 — Leaner split this exact scalar fixed-modulus lemma from `g5-over-fq-deligne-unitarity`. The parent card remains in `2-fully-proven` because the function-field specialization, Frobenius weight circle, polarization, and Deligne purity import are not fully Lean-formalized.
