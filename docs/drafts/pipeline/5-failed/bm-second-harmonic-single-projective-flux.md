# BM second-harmonic single-projective flux

- **Route:** identify one pole-cancelled BM `++` projective response and its Schwarz-conjugate `--`
  response directly with nonzero polarized Peierls boundary flux
- **Status:** `FAILED / RETIRED`
- **Date:** 2026-08-27
- **Parent:** `bm-third-order-peierls-polarized-causal-cut.md`

## Frozen claim

The single ingoing BM projective response and its Schwarz-conjugate second-harmonic fibre produce
the nonzero outer-boundary carrier in the cubic Peierls polarization law.

## Killing mechanism

For outer coefficient vectors `(S_++,V_++)` and `(S_--,V_--)`, polarized Green concomitant is

\[
\mathfrak B=\frac12(\bar V_{--}S_{++}-\bar S_{--}V_{++}).
\]

Exact Gamma conjugation and second-harmonic Schwarz parameter exchange give

\[
S_{--}(\bar\chi)=\bar S_{++}(\chi),\qquad
V_{--}(\bar\chi)=\bar V_{++}(\chi).
\]

Substitution makes determinant zero by commutativity. Equivalently, for branch responses
`V_++=R_ret S_++` and `V_--=bar(R_adv)S_--`,

\[
\mathfrak B=\frac12\bar S_{--}S_{++}(R_{adv}-R_{ret}).
\]

One response used for both branches has no causal jump and no boundary flux.

## Strongest positive survivor

Nonzero outer Peierls carrier is response-difference datum, not one projective value:

\[
\mathfrak B=\frac12\bar S_{--}S_{++}(R_{adv}-R_{ret}).
\]

This preserves exact source normalization and identifies missing object: distinct augmented
retarded and advanced response maps, including horizon affine coordinate and AdS counterterms.

## Audits

- **Paper proof:** dependency-closed algebra above
- **Lean:** `[LEAN-PROVED]` `ThetaCuspHawkingBMSecondHarmonicProjectiveCausalNoGo.lean` proves
  exact connection-coefficient conjugacy, response-jump factorization, and same-branch vanishing
- **Literature:** generic Green/Peierls reciprocity supports response difference; audited BM and
  Kodama--Ishibashi papers do not supply augmented causal branches or this nonlinear weld

## No-go closure

- **Exact new insight:** Schwarz conjugacy identifies fibres but not causal branches. Pairing same
  branch with its Schwarz partner is a zero symplectic determinant.
- **Survivor paper status:** fully proved
- **Survivor Lean status:** dependency-closed theorem proved; physical branch construction open
- **Next hard problem:** construct genuine augmented `R_ret` and `R_adv`, prove their boundary
  difference equals horizon-plus-AdS flux, then identify it with Peierls `++/--` block.
