# Hedenmalm prime translation / completed radial-work equivalence

- **Label:** `P-G128`
- **Route:** P
- **Parents:** `P-G97`, `P-G126`, `P-G127`, `FrankensteinThetaPrimeTranslationPluckerLanding`
- **Status:** theorem and no-go proved in Lean; umbrella integration complete

## Conjecture tested

For one Xi divisor copy `q`, ordinary prime `p`, centered rate

```text
t(q) = 2 Re(q) - 1,
```

define fixed-prime reflected translation excess

```text
D_p(q) = E_p(q) + E_p(q#) - 2.
```

Test whether Route P's remaining fixed-prime detector and P-G126's completed radial source work
are quantitatively the same obstruction before any RH equivalence is invoked.

Conjectured exact and quantitative laws are

```text
D_p(q) = 2(cosh(t(q) log p) - 1),
4(log p)^2 W(q) <= D_p(q) ||f_q||^2,
```

and, whenever `|t(q) log p| <= 1`,

```text
D_p(q) ||f_q||^2 <= 8(log p)^2 W(q).
```

Every actual Xi copy satisfies the window at `p=2`, so prime two should give an unconditional
two-sided comparison with universal constants `4(log 2)^2` and `8(log 2)^2`.

## Scientific decision gate

- **Success:** fixed-prime translation excess and completed radial work are uniformly equivalent
  source energies on every actual Xi fibre. This removes translation imbalance as an independent
  pressure and identifies one universal horizontal dissipation class behind P-G97, P-G126, and
  P-G127.
- **Failure:** isolate mismatch between Xi centered rate, spectral width, or completed divided-mode
  normalization.
- No RH premise, zero-selected coefficient, computation, axiom, or abstract positivity hypothesis.

## Prior-research audit

- 2026-08-13 — Searched `formal/`, paper-proven/formalized stages, and failed routes for a theorem
  joining fixed-prime reflected translation excess to completed radial source work. Existing corpus
  separately proves translation reciprocity/imbalance, hyperbolic gap bounds, completed work, and
  Ward/work amplification. No coefficient-exact cross-construction comparison was found.
- P-G109/P-G110 already exclude diagonal critical-rigging contractivity and symmetric pinned
  rank-two repair. P-G55--P-G59 show information, Bockstein action, Wold/Gauss virial, and Burnol
  holonomy are successive presentations of one positive horizontal mode. P-G128 tests whether the
  remaining fixed-prime open core is the same mode at finite scale.

## Conjecturing log

- 2026-08-13 — C1 opened: exact hyperbolic translation-excess formula.
- 2026-08-13 — C2 opened: global quadratic lower comparison to completed work.
- 2026-08-13 — C3 opened: submicroscopic upper comparison, unconditional at prime two on Xi strip.

## Verification log

- 2026-08-13 — Direct foreground check passed:
  `lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmPrimeTranslationCompletedRadialWorkEquivalence.lean`.
- 2026-08-13 — Exact module build passed:
  `lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPrimeTranslationCompletedRadialWorkEquivalence`
  (`12953/12953`).
- 2026-08-13 — Axiom audit passed for all capstones; dependencies are exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-08-13 — Imported by `GaloisForLFunctions/RHTower.lean`. Global lint/umbrella snapshot is
  currently unstable under concurrent unrelated writers; exact target verification is green.

## Result and no-go closure

- C1 proved exactly:
  `D_p(q)=2(cosh((2 Re(q)-1)log p)-1)`.
- C2 proved for every ordinary prime:
  `4(log p)^2 W(q) <= D_p(q)||f_q||^2`.
- C3 proved on `|(2 Re(q)-1)log p|<=1`; every actual Xi divisor copy satisfies this at prime two.
  Therefore

  ```text
  4(log 2)^2 W(q) <= D_2(q)||f_q||^2 <= 8(log 2)^2 W(q).
  ```

- Prime-two translation excess energy vanishes exactly when completed radial source work vanishes.
  This is a uniform quantitative equivalence, not only two separately RH-equivalent zero tests.
- No-go closure: fixed-prime translation imbalance, P-G126 completed Dirac work, and P-G127
  Ward/Krein energy belong to one universal positive horizontal-dissipation class. None can
  neutralize another. A live producer must act on the signed Bockstein/Green current before radial
  action and positive scalarization, and must be source-nonlocal or reflection-breaking because
  diagonal critical rigging and symmetric pinned rank-two repair are already formally excluded.
