# Xi CCM multi-observable divisor universality law

- **ID:** xi-ccm-multi-observable-divisor-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper-proved and Lean-formalized)
- **Source:** Post-Law-31 theorem-first scan of all `CCM*.lean` modules
- **Statement:** At every right-half Xi divisor copy, translated critical Mellin, inverse-tilted,
  shifted-log-derivative, dyadic sharp-prime, arbitrary noncensoring compact-BV, raw rectangular,
  admissible rectangular-tail, and cutoff-free rectangular charts recover one pole coordinate.
  All nine source poles are simple. Eight normalized residues equal the analytic Xi multiplicity;
  the elementary prime source residue is its exact negative.

## Gates

- [x] 0 → 1 in-progress: exact Lean declarations and downstream consumers read
- [x] Complete paper proof with no open dependency
- [x] Lean direct check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Internal noncollision audit

Three exact `scripts/formal_tools.py research` searches returned individual divisor-tomography
components, the generic compact-BV censorship theorem, the identity between the inverse-tilted
source and a corrected critical-Mellin defect, and individual manuscript capstones. No existing
consumer identifies all nine source charts at one divisor copy, derives the compact-BV normalized
trailing coefficient, derives the elementary source trailing coefficient from its punctured
limit, or proves the eight-equal/one-opposite residue law. Existing rectangular intrinsicity
varies width/copy only within rectangular charts.

## Paper proof

Let `rho` be the support point underlying a right divisor copy `q`. Definitions give the
critical-Mellin coordinate `rho - 1`, the inverse-tilted/BV coordinate `rho + 1/2`, and the shifted
right-copy coordinate `1 + (rho - 1/2) = rho + 1/2`. Thus translating the critical-Mellin
coordinate by `3/2` produces the common pole used by all shifted and rectangular sources.

The source-specific divisor-tomography theorems state that each observable has meromorphic order
`-1` at its coordinate. For arbitrary compact-BV window, nonzero Mellin value is exactly the
noncensorship condition; uniqueness of punctured limits identifies its normalized trailing
coefficient with the Xi order. The same uniqueness argument turns the elementary source limit
into trailing coefficient `-m`. Remaining residue theorems yield `m` after their explicit
nonzero aperture/Mellin normalizations. Transitivity gives seven positive cross-chart equalities
and the elementary-source opposition. No RH assumption is used.

## Lean formalization

`RHTower/XiCCMMultiObservableDivisorUniversalityLaw.lean` proves two missing trailing-coefficient
connectors, defines a twenty-eight-field pointwise certificate, and constructs it from the nine
component tomography mechanisms.
Exact direct check:

```text
lake env lean GaloisForLFunctions/RHTower/XiCCMMultiObservableDivisorUniversalityLaw.lean
```

passed first run.

## Hostile literature noncollision audit

Searches covered Xi divisor multiplicity, logarithmic-derivative residues, Mellin explicit
formulae, compact-BV/dyadic prime windows, rectangular Weil observables, and current
screw-function/Weil operator work. Classical explicit-formula literature uses Mellin weights and
residues of logarithmic derivatives at zeta zeros, but does not contain these nine internally
defined source charts or their eight-equal/one-opposite normalized-residue identity. Suzuki's screw-function papers organize Weil/RH
criteria through continuous kernels and finite-interval operators
([arXiv:2206.03682](https://arxiv.org/abs/2206.03682),
[arXiv:2606.09096](https://arxiv.org/abs/2606.09096)); Connes--Consani treat compressed scaling
actions and Weil positivity ([arXiv:2006.13771](https://arxiv.org/abs/2006.13771)). None states the
critical-Mellin `+3/2` common-pole law or this normalized nine-source residue law. This is a
noncollision audit, not a priority claim.

## Log

- 2026-07-21 — Found bottom-up in the complete `CCM*.lean` scan after excluding growth bounds and
  single-chart capstones already consumed by prior laws. Exact internal duplicate search passed;
  dependency-closed paper proof recorded before Lean checking.
- 2026-07-21 — Thirteen-field certificate passed exact direct Lean check first run. Hostile search
  across explicit-formula, screw-function, and Weil-operator literature found no four-chart
  statement. Exhaustion resumed from the augmented corpus.
- 2026-07-21 — Continued source scan found five omitted chart mechanisms. Strengthened Law 32 to
  nine sources and twenty-eight fields, adding generic compact-BV and elementary-source trailing
  coefficient connectors. Exact direct Lean check passed after one coordinate-normalization fix;
  exhaustion resumed from the stronger law.
