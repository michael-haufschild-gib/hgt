# Library ticket: BV prime-window decimation boundary contraction

- **Date:** 2026-07-15
- **Requested index surfaces:** `docs/drafts/door/00-index.md`, `docs/drafts/door/00-status.md`
- **Do not apply here:** a separate library-maintenance agent owns those files.

## Add proved paper theorem

- `bv-prime-window-polar-coefficient-decimation-law`
- Stage: `2-fully-proven/not_new_scientific_knowledge`
- Type: paper theorem / exact value relation / top-down interface discharge
- Summary: integer dilation of a compact-BV prime window becomes exact square-index decimation of
  its polar coefficient sequence; on every uncensored zeta pole the same map has Laurent character
  `r^(2rho-1)`, while the off-multiple layer retains the universal residue fraction `1-r^(-2)`.
  Ordinary Dirichlet--Hardy space is excluded for every uncensored meromorphic source.

## Add live RH construction card

- `bv-prime-window-decimation-boundary-contraction-rh`
- Stage: `1-in-progress`
- Type: conjectural source Gram construction with proved conditional RH endpoint
- Summary: construct a source-defined singular scale-zero Gram completion of the fixed sharp
  window dilation orbit.  Square-index decimation must be contractive and Laurent pole
  functionals continuous.  The resulting adjoint eigenvalue bound forces
  `|r^(2rho-1)|<=1` for every right zero and proves RH.

## Cross-links

- Parent paper card: `bv-prime-window-laurent-orientation-polarization`.
- Analytic providers:
  `formal/GaloisForLFunctions/RHTower/BVPrimeWindowContinuation.lean` and
  `formal/GaloisForLFunctions/RHTower/BVPrimeWindowDivisorTomography.lean`.
- Closest boundary comparison: `burnol-hedenmalm-boundary-null-graph-completion-rh`.
- Explicitly separate from the active dyadic sharp-source subpower coefficient route.
