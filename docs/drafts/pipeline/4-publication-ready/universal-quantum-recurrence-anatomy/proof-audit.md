# Proof audit

Date: 2026-08-23

Scope: internal verification ledger. Not part of submitted manuscript.

## Admission rule

Every mathematical result stated in `main.tex` and `body.tex` must be an exact
specialization or direct composition of closed declarations listed in
`claim-trace-localization.md`. Definitions, interpretation, literature
summaries, and explicit nonclaims are not mathematical theorem claims.

## Headline closure

The load-bearing local theorem is
`qubitPath_everyChart_sameDraw_recurrenceCollisionLaw` in
`formal/GaloisForLFunctions/HTGeometry/QubitPathRecurrenceCollisionCapstone.lean`.
It quantifies over every nonempty preconnected open simple-spectrum chart and
proves that almost every coefficient draw in that chart simultaneously has:

- maximal projective rank;
- stroboscopic first-hit exponent `D - 1`;
- first-gap-clock-normalized winding exponent `D - 2`;
- every positive-weight, every-order collision floor;
- every corresponding long-time survival-moment floor.

The theorem uses
`SpectrumEscapesRealRelations.linearFamily_toAffine` from
`formal/GaloisForLFunctions/HTGeometry/LinearSpectrumAffineEscape.lean` to
upgrade homogeneous real spectral escape to every nonempty open affine chart.

## Universal-law closure

Exact source mappings appear in `claim-trace-localization.md`. Load-bearing
declarations cover:

- projective rank conservation;
- Dirichlet upper bound and exact non-VWA first-hit exponent;
- survival-fidelity replica expansion and long-time collision limit;
- all-order collision-floor equivalence with maximal projective rank;
- exact full traceless onsite-plus-edge Pauli path family;
- escape of every nonzero balanced real spectral relation;
- generic qudit-path maximality;
- exact anchored chord-return density and absence of nonzero exact returns;
- thermodynamic density extinction and both exact asymptotic rates.

## Quantifier and limit-order audit

- Qubit path size is `n = k + 3`, hence `n >= 3` and `D = 2^n`.
- One coefficient draw satisfies all clauses; clauses are not assembled from
  unrelated generic draws.
- Stroboscopic exponent is anchored and discrete-time.
- `D - 2` exponent is for first-gap-clock-normalized winding, not unrestricted
  continuous-time first return.
- Collision statements require positive spectral weights.
- Thermodynamic theorem completes the long-time limit at each finite size
  before sending system size to infinity.
- No infinite-volume orbit recurrence is asserted.

## Kernel and source checks

- `lake env lean GaloisForLFunctions/HTGeometry/QubitPathRecurrenceCollisionCapstone.lean`:
  passed.
- `lake build GaloisForLFunctions.HTGeometry.QubitPathRecurrenceCollisionCapstone`:
  passed; targeted module only.
- `#print axioms` for every-chart capstone, existence capstone, and affine
  bridge reports only `propext`, `Classical.choice`, and `Quot.sound`.
- New modules contain no `sorry`, `admit`, custom `axiom`, `opaque`, or
  `unsafe` declaration.
- Full umbrella build was not run.
- Project-wide lint still reports unrelated pre-existing RHTower umbrella
  reachability failures; no paper claim treats global lint as clean.

## Manuscript independence

Compiled manuscript contains no mention of Lean, HGT, Riemann-hypothesis
research, internal corpus, black holes, loss, channels, circuit complexity, or
finite-record inference. Internal proof machinery appears only in supporting
audit files.
