# TG C9.11o — raw linear-prime nuclear admission fails

- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Route:** TG, principal source admission
- **Rejected claim:** the original linear-prime correction response family is summable in genuine Schatten-one before joint completion.
- **Scope:** raw admission only; no falsification of joint prime–Gamma admission, TG, or RH.

## Exact killing theorem

For every a>0, `soninLinearPrimeNuclearSource a ha p` is exactly
`p^(-1/2) C_a(soninPrimeDilationSignal p)`, with both actual dilation directions
and the complete correction response. The theorem
`not_summable_soninLinearPrimeNuclearSource` proves this family is not
summable in `SchattenOneOperator SoninL2` with its genuine trace norm.

The proof first establishes the exact harmonic law of its ordinary trace,
then uses reciprocal-prime divergence and continuity of trace in Schatten-one.
It does not replace the operator with its coefficient energy or a Gram source.

## Strongest positive survivor

`tendsto_soninLinearPrime_trace_harmonic` and
`soninLinearPrimeTraceCoefficient_pos` give the canonical positive coefficient

`p Re Tr S_p → 2(Phi_a(1)+1)>0`,

where Phi is the literal double Fourier window of the actual physical/Fourier
cutoffs. Both dilation legs contribute; neither contribution is discarded.
The exact identity before the limit is

`p Re Tr S_p = 2(Phi_a(1-p⁻¹)+p Phi_a(p-1))`.

This coefficient is a necessary scalar cancellation datum for an actual
joint source construction. It does not certify a chosen counterterm or any
operator-level continuation. The full dependency-closed paper proof and
previous window/dilation trace audits are in
`../3-formalized/tg-principal-source-trace-current.md`.

## New insight and surviving route

The proper-prime-power family is already admitted; the obstruction is now
proved on the complete original linear-prime response. Admission must pair
this source with its actual polar/Gamma contribution before taking the
cofinal limit. The literal polar source fixes a candidate density
`2 cosh(u/2)/u`; its operator cancellation is the next hard target in
`../1-in-progress/tg-principal-polar-operator-cancellation.md`.

## Audit

2026-10-02: `SoninLinearPrimeTraceObstruction.lean` passes foreground
`lake --old env lean <leaf> -o <olean>` with no diagnostics. All six public
declarations pass separate `/tmp/tg-c911o-axioms.lean` queries and depend only
on `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired; no full build.
No computations, proof holes, added axioms or heartbeat increases. Positive
survivor is formalized, not merely proposed. Final logs are
`/tmp/tg-c911o-leaf-final.log` and `/tmp/tg-c911o-axioms.log`.
