# Möbius--Gamma/Xi singular conormal residue split

- **Stage:** 3-formalized
- **Route:** MSC
- **Lean:** `RHTower/HedenmalmGammaSewnSquarefreeFisherConormalResidueSplit.lean`
- **Result:** If a strict-right Xi zero has multiplicity `m`, then the coefficient-faithful
  singular correction has the unique analytic-germ decomposition
  `F(v)/B(v) = 2m/(v-u) + h(v)` with `h` analytic at `u`.
- **Proof chain discharged:** forced-residue/regular-remainder split in the MSC
  `ORD + ORIENT + COF + LAND` chain.
- **Remaining core:** source-framed nonexpansive estimate and horizontal annihilation for `h`;
  the residue line cannot be removed by holomorphic divisibility.
