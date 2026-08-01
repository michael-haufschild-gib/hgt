# Route G2 relative-Volterra source-germ weld

- **ID:** `route-g2-relative-volterra-source-germ-weld`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / RH-BEARING SOURCE REALIZATION
- **Scientific status:** `[CONJECTURE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:** `../3-formalized/new_scientific_knowledge/suzuki-volterra-cartesian-phase-defect.md`,
  `suzuki-carleman-jump-euler-defect-weld.md`
- **Statement:** The literal Suzuki screw/Volterra source constructs, without Xi-zero data,
  positivity assumptions, or RH, analytic boundary responses and an analytic upper-half-plane
  Euler-defect source `D_src` whose pointed germ is the Euler defect of the actual two-shift
  affine-sewn exterior Weyl quotient, thereby discharging every premise of
  `riemannHypothesis_of_suzukiVolterraPhaseEulerDefect_source_germ_weld`.

## Goal

Decide Route G2 at source level. Either prove the exact statement by a dependency-closed paper
argument and unconditional Lean theorem, or kill its representation by an exact obstruction and
formalize the strongest non-trivial positive survivor.

## Exact inherited frontier

- `[CORPUS]` `SuzukiVolterraCartesianPhaseDefect.lean` proves the Cartesian split, relative phase
  homogenization, two-resolvent projective/marked-secant identities, and the conditional RH
  connector.
- `[OPEN CORE]` Construct the actual continuous Suzuki operators and prove the source Green/CD
  germ identity `hseed`, plus the analytic and real-zero packages, from literal source.
- No Lean infrastructure may be added until the exact source theorem has a complete paper proof.

## Falsifiers

1. the proposed source object depends on Xi zeros, RH, a hidden zero-free hypothesis, or the
   exterior quotient itself rather than literal prime--Gamma/Volterra data;
2. the source Euler defect has a residual not killed by the common-gauge Euler operator;
3. the Green/CD boundary image loses the marked affine or homogeneous Neumann channel;
4. any required upper-half-plane analyticity is equivalent to absence of the same nonreal Xi poles
   the route is meant to exclude;
5. actual source operators fail boundedness, adjoint/parity, Fubini, or germ compatibility.

## Gates

- [x] 0 -> 1: exact inherited claim, source-purity conditions, and falsifiers recorded
- [ ] 1 -> 2: full internal and external audit; hostile conjecture loop; dependency-closed paper proof
- [ ] 2 -> 3: exact unconditional Lean theorem, umbrellas, lint, axiom audit, final module build
- [ ] 3 -> 4: independent priority and expert review

## No-go closure

- **Exact killing theorem/mechanism:** pending hostile audit
- **Strongest positive survivor:** pending mandatory second pass
- **New insight:** pending
- **Status:** Stage 1; no paper proof; no route-closing Lean theorem

## Log

- 2026-08-01 — opened from `rh-current-frontier-map.md` Route G2. Existing Stage-3 artifact is
  correctly classified as source algebra plus conditional connector, not closure of source core.
