# Scalar grade weighting completes the all-grade formation tower

- **ID:** ULF-SRSM-FAIL-1
- **Stage:** 5 — failed/retired
- **Type:** FALSIFIED COMPLETION CONJECTURE
- **Source:** ULF-SRSM-7 all-grade subset-phase formation
- **Statement:** A scalar Fock-like weight depending only on response arity can make the complete
  all-prime formation tower bounded and uniformly reconstructible.
- **Status:** `[FALSIFIED] [POSITIVE SURVIVOR EXECUTED IN ULF-SRSM-8] [NOT RH]`

## Conjecture

Let `H_I` be the all-subset exponential CDF attached to a finite prime tuple `I`, and let

\[
 e_I\longmapsto w_{|I|}H_Ie_I
\]

be the weighted complete formation operator.  The conjecture asked for positive scalar weights
`w_r` making this operator bounded with closed range.

The proposal was attractive because every fixed grade already has a uniform frame, and ordinary
Fock, tensor, and word completions are commonly controlled by one scalar weight per arity.

## Exact killing theorem

ULF-SRSM-7 proves two incompatible asymptotics at each growing grade.

1. On the tuple of the first `r` primes,

   \[
   \|H_{I_r}\|_{L^2(0,T)}\longrightarrow0
   \]

   superexponentially in `2^r`.
2. For every fixed `r`, sending all `r` primes jointly to infinity gives

   \[
   \sup_{|I|=r}\|H_I\|_{L^2(0,T)}=\sqrt T.
   \]

Boundedness of the weighted tower therefore forces `sup_r w_r<infinity`.  The first-prime sequence
then gives `w_r||H_(I_r)||→0`, so the operator is not bounded below and its range is not closed.
No scalar grade-only sequence can satisfy both requirements.

## No-go closure

- **Exact killing theorem/mechanism:** low-prime and high-prime channels at the same arity require
  incompatible scalar normalization.  This is an exact diagonal closed-range obstruction, not a
  failure to guess the correct growth rate.
- **Strongest positive survivor:** a source-dependent diagonal weighting `w_I` gives a bounded
  closed-range tower exactly when

  \[
  0<\inf_Iw_I\|H_I\|\le\sup_Iw_I\|H_I\|<\infty.
  \]

  Thus a complete topology can exist, but it must depend on the source configuration rather than
  arity alone, or leave the scalar Hilbert/Fock category.
- **New insight:** fixed-grade properness and complete-tower properness are different laws.  The
  next field mechanism must generate tuple-adaptive renormalization before observation; choosing
  `w_I=1/||H_I||` afterwards is fitted and supplies no selector.
- **Executed survivor:** ULF-SRSM-8 avoids diagonal renormalization entirely.  It retains each
  generated probability formation as an `ell^1`-valued measure, where total variation makes the
  full tower isometric and total mass is one common recovery.  Finite-horizon Hilbert observation,
  not formation itself, is the nonproper map.
- **Status:** dependency-closed paper proof in
  `pipeline/2-fully-proven/universal-law-field/source-response-signature-mechanics/all-grade-flag-determinant-subset-phase-conservation-and-arity-properness-fracture-law.md`.
  Lean corpus audited read-only; no Lean write/build in this pass.

## Log

- 2026-08-14 — conjecture falsified by the low-prime/high-prime incompatibility theorem; retired
  only after extracting the exact source-adaptive diagonal criterion.
- 2026-08-14 — positive survivor executed more strongly by the base-norm formation-measure
  isometry; no tuple-dependent scalar weights are needed.
