# Gamma factorial jet-connection tensor law

- **ID:** gamma-factorial-jet-connection-tensor-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), literature audit pending
- **Source:** Bottom-up Lean dependency closure of `GammaFactorialAsymptoticConnection` and `GammaPoleWeightedCovariantAsymptotic`
- **Statement:** Intrinsic Gamma jet grade `j` carries the `j`th tensor power of the inverse factorial pole connection; adjacent residue norms scale by `(m+1)^j`.

## Goal

Close the explicit open bridge between pole-index clock and intrinsic differential-jet grading.
Neither the scalar factorial connection nor the fixed-branch covariant residue law alone identifies
how changing pole index acts on jet grade.

## Gates

- [x] 0 → 1 in-progress: theorem-first closure, exact source quantities, no conjectural input
- [x] Complete paper proof with no open dependency
- [x] Lean source passes direct `lake env lean <file>`
- [ ] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs

1. `norm_reciprocalGammaFactorialScale_eq_connectionTransport` identifies scalar connection
   transport with norm of actual reciprocal-Gamma pole scale.
2. `gammaFactorialConnectionTransport_succ` gives adjacent scalar transport recursion.
3. `gammaPoleCovariantTopResidueValue` gives exact intrinsic grade-`j` top residue in the
   factorially normalized chart.

## Paper proof

The grade-`j` residue equals

`(-s_m⁻¹)^j · (-1)^j · j!`,

where `s_m` is reciprocal-Gamma factorial scale. Taking norms and using
`‖s_m‖=T_m`, factorial connection transport, gives

`‖R_{m,j}‖ = T_m^{-j} j! = (m!)^j j!`.

Since `T_{m+1}=L_m T_m` and `L_m=1/(m+1)`, inversion and the `j`th power give

`‖R_{m+1,j}‖ = L_m^{-j} ‖R_{m,j}‖ = (m+1)^j ‖R_{m,j}‖`.

Thus intrinsic jet grade is precisely tensor-power exponent for pole-index transport.
`[PROVED HERE]`

## Formalization

- Module: `formal/GaloisForLFunctions/HTGeometry/GammaFactorialJetConnectionTensorLaw.lean`
- Theorems:
  - `norm_gammaPoleCovariantTopResidueValue_eq_factorialConnectionTensorPower`
  - `norm_gammaPoleCovariantTopResidueValue_succ_eq_connectionLinkTensorPower`
  - `norm_gammaPoleCovariantTopResidueValue_eq_factorial_pow_mul_factorial`
  - `norm_gammaPoleCovariantTopResidueValue_succ_eq_indexPow_mul`

## Log

- 2026-07-21 — Discovered by closing factorial-clock marker against covariant top-residue dependency.
- 2026-07-21 — Complete proof formalized; direct Lean check passed.
