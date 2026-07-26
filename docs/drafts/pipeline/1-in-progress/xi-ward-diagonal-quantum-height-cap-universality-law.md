# Xi Ward diagonal quantum height-cap universality law

Status: **Stage 3 — formalized in Lean**

## Discovery

Whole-corpus theorem-posting closure joined two independent Xi/Ward mechanisms:

- `XiWardCriticalBudgetProbe`: every strict-right Xi zero pair has centered height squared
  strictly greater than `65`; and
- `XiWardEdgeGramSharpLaws`: the diagonal edge Gram term has its exact two-channel Cauchy form and
  lies strictly above the universal `8π` packet floor.

No theorem in either module or in the corpus index bounds the same local diagonal packet from
above by using the independently certified height floor.

## Universal law

For every `q : XiRightUpperZeroCopy`, put

`x_q = Re(xiRightCenteredZero q) + 1/2`

and let `G(q,q) = xiPairGramTerm q q`. Then

`8π < G(q,q) < 8π · 131/65`.

Thus every strict-right Xi Schwarz pair contributes a local Ward diagonal quantum in one
universal open band. The lower edge comes from critical-strip geometry; the upper edge comes from
the global strip-edge spectral budget through its forced height floor.

## Dependency-closed paper proof

1. Critical-strip confinement gives `0 < Re(xiRightCenteredZero q) < 1/2`, hence
   `1/2 < x_q < 1`.
2. Expanding `xiPairGramTerm q q` gives the exact identity

   `G(q,q) = 8π · (1/x_q + x_q/(x_q² + b_q²))`,

   where `b_q = Im(xiRightCenteredZero q)`.
3. `eightPi_div_le_xiPairGramTerm_diag`, together with `x_q < 1`, gives
   `8π < G(q,q)`.
4. `x_q > 1/2` gives `1/x_q < 2`.
5. `xiWard_offlinePair_height_sq_gt_sixtyfive` gives `65 < b_q²`; since `0 < x_q < 1`,
   `x_q/(x_q²+b_q²) < 1/65`.
6. Adding the two strict estimates in the identity yields

   `G(q,q) < 8π · (2 + 1/65) = 8π · 131/65`.

No RH premise, computation, numerical zero table, or new analytic assumption enters.

## Formal targets

- `xiPairGramTerm_diag_eq`
- `xiPairGramTerm_diag_lt_heightCap`
- `xiWard_diagonalQuantum_heightCapUniversality`

## Novelty audit

Post-proof searches covered `Riemann xi + Ward/Gram/Cauchy energy + off-critical zeros`,
`logarithmic derivative spectral sums + height bounds`, and `local diagonal zero energy`. Adjacent
literature studies Xi away from the critical line and bounds or signs of logarithmic derivatives,
but does not state the exact Ward diagonal packet or the height-floor-induced open band
`(8π, 8π·131/65)`. Representative adjacent sources:

- [The argument of the Riemann Xi-function off the critical line](https://arxiv.org/abs/0904.1051)
- [On a positivity property of the real part of logarithmic derivative of the Riemann xi-function](https://arxiv.org/abs/2201.08599)
- [Extension of the Riemann xi-function's logarithmic derivative positivity region to near the critical strip](https://doi.org/10.4153/CMB-2009-021-3)
- [Bounding the log-derivative of the zeta-function](https://doi.org/10.1007/s00209-021-02820-9)

No exact collision found in this scoped audit. **[NOVELTY UNVERIFIED]**

## Lean formalization

Formal source:
`formal/GaloisForLFunctions/RHTower/XiWardDiagonalQuantumHeightCapUniversalityLaw.lean`.

Verified with:

`lake env lean GaloisForLFunctions/RHTower/XiWardDiagonalQuantumHeightCapUniversalityLaw.lean`

Umbrella:
`formal/GaloisForLFunctions/RHTower.lean`.
