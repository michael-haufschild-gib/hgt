# Prime--arch polar all-order incidence-completion universality law

- **ID:** prime-arch-polar-all-order-incidence-completion-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus closure of polar-seam removal and completed-flux incidence powers
- **Statement:** At every positive incidence order, the translated prime--arch source germ has the
  completed Xi incidence-power germ as its unique analytic completion, with filled polar-center
  value zero.

## Goal

Connect unique removal of the prime--arch polar seam at `s = 1` to the corpus's all-order completed
incidence hierarchy.  Do not stop at the visible quadratic case: close every positive natural
power at once.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, exact `lake env lean` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus inputs

- `primeArchPolarFlux_eventuallyEq_seamFluxCochain_one`
- `completedFluxIncidencePowerGermAt_analyticAt_zero`
- `completedFluxIncidencePowerGermAt_zero`
- `xi_ne_zero_of_one_le_re`

## Proof

`[PROVED HERE]` Translate the punctured source identity from `s → 1` to `x → 0`.  Away from
`x = 0`, the completed local flux is
`x * seamFluxCochain (1 + x)`.  Raising this identity to arbitrary order `m` gives exactly

```text
x^m * (infinitePrimeFlux (1+x) - logDeriv archFactor (1+x))^m.
```

The existing all-order incidence germ is analytic at `x = 0`.  Since `xi 1 ≠ 0`, its local order
at `1` is zero, so every positive power has filled center value zero.  Any other analytic
completion agrees on a punctured neighbourhood; the analytic identity theorem forces local
agreement with the completed incidence germ.

No numerical computation is used.

## Novelty protocol

No literature search before exact Lean proof.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.PrimeArchPolarAllOrderIncidenceCompletionUniversalityLaw`
- Main theorem:
  `RHTower.primeArchPolar_allOrderIncidenceCompletionUniversality`
- Exact source check:
  `lake env lean GaloisForLFunctions/RHTower/PrimeArchPolarAllOrderIncidenceCompletionUniversalityLaw.lean`
  (exit 0, no output).
- Imported by `GaloisForLFunctions/RHTower.lean`.
- Axiom audit and module build deferred to required final audit; no intermediate `lake build`.

## Post-proof literature audit

- **Status:** `[LEAN PROVED — LITERATURE AUDITED]`
- [DLMF §25.4](https://dlmf.nist.gov/25.4) records the classical Gamma-completed Xi definition and
  reflection formula.
- Coffey studies Xi logarithmic derivatives at `s = 1` and Laurent coefficients of the zeta
  logarithmic derivative there
  ([Math. Phys. Anal. Geom. 8 (2005)](https://doi.org/10.1007/s11040-005-7584-9)).
- Goldštein--Grigutis study positivity and zero expansions for `xi'/xi`
  ([J. Math. Inequalities 18 (2024)](https://doi.org/10.7153/jmi-2024-18-45)).
- Targeted searches found no statement classifying, simultaneously for every positive natural
  order, `x^m` times the `m`th power of the prime-minus-archimedean polar source as the unique
  analytic completed-Xi incidence germ with forced center value zero.  The no-match conclusion is
  an inference from the audited classical completion/log-derivative sources and targeted exact-
  phrase/concept searches, not a claim that every publication has been enumerated.

## Log

- 2026-07-23 — theorem-first scan exposed quadratic seam connector; generalized it to all positive
  incidence powers before formalization.
- 2026-07-23 — exact Lean source check passed; post-proof literature audit found no exact prior law.
