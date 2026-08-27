# BM mixed-horizon one-channel Peierls landing

- **ID:** HB-BM3-MIX-PEIERLS
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `HB-BM3-PNCC` · `ThetaCuspHawkingBMMixedHorizonCausalOpticalProducer.lean`
- **Statement:** `[FALSIFIED]` Off critical, mixed `+-` response incidence, vanishing sourced `++` jump, and positive mixed reciprocity cannot jointly arise from one cyclic augmented action with skew Peierls propagator.

## Goal

Test whether corpus conditional mixed-horizon optical producer can be welded directly to physical
retarded/advanced Green theory while retaining its zero-`++` hypothesis.

## Gates

- [x] 0 → 1 in-progress: exact assumptions and off-critical falsifier fixed
- [x] 1 → 2 fully-proven: dependency-closed algebraic contradiction
- [x] 2 → 3 formalized: Lean no-go theorem, targeted build and axiom audit pass
- [ ] 3 → 4 publication-ready: retired theorem can be included with successor route

## Frozen claim

Assume one augmented field--residual pairing `P`, symmetric quadratic residual `B`, cyclic third
action variation, and causal propagator `Delta=Rret-Radv` skew under source pairing
`Omega(f,g)=P(Delta f,g)`. Assume corpus mixed block equals `Delta` on `f_+-`, its response jump is
the nonzero BM Frobenius monodromy mode, sourced `++` response jump vanishes, and

\[
P(m,B(p,u))=\|\Pi_{hor}\|^2.
\]

Frozen claim asserted these hypotheses can hold at an off-critical Xi fibre and make complete
cubic cut equal nonzero mixed optical section.

## Hostile proof of impossibility

Hessian symmetry identifies `f_+-=B(p,m)`. Action cyclicity sends mixed projected term to

\[
P(m,B(p,\Delta f_{+-}))=P(\Delta f_{+-},f_{+-}).
\]

Peierls skewness makes this self-pairing zero. Zero sourced `++` jump kills remaining response term,
so complete retarded-minus-advanced cubic cut is zero. Corpus conditional optical theorem makes
same cut equal BM mixed optical section, whose proved zero locus is exactly critical line for
nonzero amplitude. Off critical gives contradiction.

## No-go closure

- **Exact killing theorem/mechanism:** Peierls self-pairing cancellation plus assumed zero sourced `++` jump forces total cut zero.
- **Strongest positive survivor:** complete phase-normalized cut is twice polarized `++/--` source pairing when both graded jumps are blocks of one causal propagator.
- **New insight:** nonzero mixed Frobenius field monodromy need not contribute to cubic action coefficient; physical optical carrier must include second-harmonic conjugate polarization.
- **Status:** `[FALSIFIED] [LEAN-PROVED]` in `ThetaCuspHawkingBMMixedOpticalPeierlsNoGo.lean`; survivor `[LEAN-PROVED]` in `ThetaCuspHawkingCubicPeierlsPolarization.lean`.

## Log

- 2026-08-27 — exact contradiction paper-proved and Lean-formalized. Direct Lean and targeted
  module build pass; axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`.
