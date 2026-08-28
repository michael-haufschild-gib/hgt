# FZZ-P covariant reporter conservation rigidity

- **ID:** FZZ-P-HC8
- **Stage:** 3-formalized
- **Type:** THEOREM / unique moving-reporter classification and selection no-go
- **Source:** HC6 exact flow + HC7 full coefficient-space action
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityCovariantReporterConservationRigidity`
- **Statement:** A unique source-covariant moving Hermitian reporter exactly conserves unit diagonal
  energy, but it conserves the complete reflected mismatch and therefore cannot produce matching.

## Main theorem

For the HC6 stabilized flow, write

`e=exp(Pt)`, `k=(Q/R)(e-1)`

and

`q=k/e=(Q/R)(1-exp(-Pt))`.

The moving Hermitian reporter

`C_t=(q^2,q,0,1)`

satisfies, for every real time and state,

`H_(C_t)(Phi_t u)=H_(0,0,0,1)(u)`.

At coefficient level this reporter is unique: the pullback equations

`A'=0`, `B'=0`, `C'=0`, `d'=1`

hold exactly when `(a,b,c,d)=(q^2,q,0,1)`.

For every centered Mellin carrier and every time,

`H_(C_t)(Phi_t M(rho))=H_(C_t)(Phi_t M(reflect rho)) <-> Re rho=1/2`.

More strongly, the whole reflected reading difference is independent of time and equals the
initial unit-diagonal reflected defect.  Thus every off-wall carrier remains unmatched at every
time.  Universal covariant matching on all open-strip parity-Mellin modes at any chosen scale and
time is equivalent to RH.

## Paper proof

HC7 gives the pulled coefficients

`(e^2 a-2 e k b+k^2 d, e b-k d, e c, d)`.

Substitution of `(q^2,q,0,1)` with `q=k/e` reduces these to `(0,0,0,1)`, proving conservation.
Conversely, `d=1`; since `e>0`, `ec=0` forces `c=0`; then `eb-kd=0` forces `b=k/e=q`; finally the
first equation forces `a=q^2`.  This proves uniqueness without any zero or target input.

Apply conservation first to `M(rho)` and then to `M(reflect rho)`.  HC5's unit-diagonal detector
theorem yields the critical-line equivalence.  Subtracting the two identities proves exact defect
conservation.  Quantifying matching over source-defined parity-Mellin modes converts the moving
predicate to HC3's unit-diagonal matching predicate, already proved equivalent to RH.

## New route knowledge

- fixed all-time reporters fail, but a unique contragredient moving reporter exists;
- its coefficients are source-only and explicit at every real time;
- moving compensation removes HC6/HC7 cone escape at pullback level;
- conservation retains the detector but preserves every off-wall mismatch exactly;
- covariant transport is therefore kinematic, not dissipative or selective;
- universal divisor matching has unchanged RH proof burden;
- surviving FZZ-P dynamics must contain nonconservative interaction, nonlinear feedback,
  singularity, or cross-mode incidence rather than pure inverse-flow transport.

This formalizes the strongest moving-reporter survivor exposed by HC7 and proves why it cannot
close the FZZ-P orientation gate alone.

## Corpus audit

Mandatory searches on 2026-08-28:

- `scripts/formal_tools.py research "FZZ stabilized flow covariant moving Hermitian reporter invariant pullback unique compensation"`
- `scripts/formal_tools.py research "time dependent Hermitian observable triangular semigroup conserved quadratic reporter inverse flow"`
- `scripts/formal_tools.py research "FZZ co-moving reflection detector conserved energy Mellin matching nonselective"`
- `scripts/formal_tools.py research "rank one source flow Lyapunov equation time dependent quadratic invariant unique"`

Corpus returned HC6/HC7 coefficient infrastructure and unrelated conservation/Lyapunov results,
but no FZZ moving reporter, uniqueness theorem, or reflected-mismatch conservation no-go.

## Literature boundary

Primary and close neighbors checked:

- Hikida--Schomerus, FZZ duality and correlation matching, arXiv:0805.3931:
  https://arxiv.org/abs/0805.3931
- Mostafazadeh, time-dependent pseudo-Hermitian Hamiltonians and metric uniqueness,
  arXiv:0706.1872:
  https://arxiv.org/abs/0706.1872
- Mostafazadeh, geometric framework for time-dependent pseudo-Hermitian systems,
  arXiv:2004.05254:
  https://arxiv.org/abs/2004.05254
- Fring--Moussa, time-dependent quasi-Hermitian evolution, arXiv:1511.08092:
  https://arxiv.org/abs/1511.08092
- Khantoul--Bounames--Maamache, invariant method for time-dependent non-Hermitian Hamiltonians,
  arXiv:1610.09273:
  https://arxiv.org/abs/1610.09273

These works discuss time-dependent metrics and invariant operators in general settings.  Exact-
object searches found no FZZ source-specific coefficient classification, conserved Mellin
reflection defect, or proof-burden rigidity theorem.  Status is “no collision located,” not an
absolute priority claim.

## Lean closure

Main declarations:

- `fzzCigarParityDilatedCovariantReporterRatio_eq`
- `fzzCigarParityDilatedCovariantReporter_conservation`
- `fzzCigarParityDilatedReporter_pullback_eq_unitSecondDiagonal_iff`
- `fzzCigarParityDilatedCovariantReporter_mellinReading_eq_reflection_iff`
- `fzzCigarParityDilatedCovariantReporter_reflectionDefect_conserved`
- `fzzCigarParityDilatedCovariantReporter_mellinReading_ne_reflection_of_re_ne_half`
- `fzzCigarParityDilatedCovariantReporterReflectionMatchedAt_iff_unitSecondDiagonal`
- `fzzCigarParityDilatedCovariantReporterReflectionMatchedAt_iff_riemannHypothesis`

Verification on 2026-08-28:

- direct `lake env lean` passed;
- targeted module build passed;
- axiom audit reported only `propext`, `Classical.choice`, and `Quot.sound`;
- scoped forbidden-token and `git diff --check` audits passed;
- module wired into `GaloisForLFunctions.RHTower` umbrella;
- frontier map untouched.

## Gates

- [x] 0 -> 1 in-progress: source-pure conjecture frozen after corpus search
- [x] 1 -> 2 fully-proven: conservation, uniqueness, and rigidity proof complete
- [x] 2 -> 3 formalized: unconditional Lean theorem package and audit
- [ ] 3 -> 4 publication-ready: independent specialist priority/physics audit

## Log

- 2026-08-28 — Conjectured from HC7's surviving moving-reporter possibility.
- 2026-08-28 — Unique conservation law and unchanged-RH-burden theorem formalized.
