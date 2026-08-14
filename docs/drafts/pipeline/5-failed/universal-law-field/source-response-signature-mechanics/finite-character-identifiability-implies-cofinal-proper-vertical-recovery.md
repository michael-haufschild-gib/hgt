# Finite character identifiability implies cofinal proper vertical recovery

- **ID:** ULF-SRSM-FAIL-3
- **Stage:** 5 — failed
- **Type:** FALSIFIED STABILITY CONJECTURE
- **Source:** ULF-SRSM-10 character-twisted response geometry
- **Statement:** Once a source-character family identifies every finite-dimensional formation
  velocity, its complete response operator should have closed range and a uniformly bounded
  inverse.
- **Status:** `[FALSIFIED] [EXACT ORIGIN-ATOM SURVIVOR PROMOTED] [NOT RH]`

## Conjecture

The all-subset hypoexponential source has distinct poles.  Its integer Laplace responses recover
every finite rate velocity.  The conjecture promoted this finite algebraic identifiability to a
cofinal topological statement: the full character-response action of adding another positive
formation should be uniformly invertible.

## Exact killing theorem

For a probability law `nu` on `[0,infinity)`, convolution multiplies the `n`th Laplace response by

\[
 a_n=\int e^{-nx}\,d\nu(x).
\]

On the `c_0` response completion the action is the diagonal operator

\[
 M_\nu(b_n)=(a_nb_n).
\]

Dominated convergence gives

\[
 a_n\longrightarrow\nu(\{0\}).
\]

Every exponential and hypoexponential source law has `nu({0})=0`.  Hence `a_n>0` for every finite
`n`, so every coordinate survives, but `a_n->0`.  The operator is injective compact with dense
nonclosed range.  Unit vectors give

\[
 \|M_\nu e_n\|=a_n\longrightarrow0,
\]

so no uniform inverse exists.

This is an explicit countermodel with complete finite identifiability and maximally unstable
cofinal inversion.

## No-go closure

- **Exact killing mechanism:** nonzero finite character multipliers need not have a positive
  cofinal lower bound.
- **Strongest positive survivor:** convolutional response recovery on `c_0` is bounded below
  exactly when `nu({0})>0`.  In that case `a_n>=nu({0})`; otherwise the action is injective compact
  with dense nonclosed range.
- **New insight:** informational completeness and global properness are independent axes.  The
  source's instantaneous formation face, not pole distinctness, controls stable cofinal recovery.
- **Executed survivor:** dependency-closed proof in
  `../../../2-fully-proven/universal-law-field/source-response-signature-mechanics/character-twisted-coinvariant-laplace-fisher-reconstruction-and-origin-atom-properness-law.md`.
- **Lean:** corpus audited read-only; no Lean write/build in this research pass.

## Log

- 2026-08-14 — conjecture killed by every atomless exponential formation; exact origin-atom
  properness classification extracted and promoted.
