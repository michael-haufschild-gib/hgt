# Suzuki shift-spectral monotone-ratio cross-Wronskian

- **ID:** `suzuki-shift-spectral-monotone-ratio-cross-wronskian`
- **Stage:** 3-formalized
- **Type:** THEOREM (LEAN)
- **Scientific status:** `[LEAN-PROVED] [UNCONDITIONAL] [NOT RH]`
- **Paper parent:**
  `../../3-formalized/new_scientific_knowledge/suzuki/suzuki-shift-spectral-monotone-likelihood-transfer.md`
- **RH used:** no
- **Computation used:** no

## Statement

For positive spectral base measure, shift below spectral nodes, and response monovarying with node,
Lean proves

```text
(integral response*K^2)(integral K)
 <=(integral response*K)(integral K^2),
K(x)=1/(node(x)-lambda).
```

Therefore exact quotient-rule expression `(N'D-ND')/D^2` is nonpositive.  Proof uses exact
two-sample identity followed by corpus theorem
`HTGeometry.integral_mul_integral_le_of_monotoneLikelihoodKernel`.

## Module

`formal/GaloisForLFunctions/RHTower/SuzukiShiftSpectralMonotoneRatio.lean`

Declarations:

```text
suzukiShiftResolventKernel_sq_cross_eq
suzukiShiftSpectralMonotoneRatio_crossWronskian_nonpos
suzukiShiftSpectralMonotoneRatio_derivativeNumerator_nonpos
```

## Honest boundary

Formal theorem consumes common positive spectral measure and monotone response law.  It does not
assert actual restricted-Weil cross measures satisfy those hypotheses.  Paper parent proves full
finite anti-Pick/negative-Stieltjes consequence and identifies concrete eigen-coefficient tests.

## Gates

- [x] unconditional Lean proof
- [x] imported by RHTower and SOTA umbrellas
- [ ] concrete Suzuki spectral factorization
- [ ] source chord-mass gap
- [ ] RH
