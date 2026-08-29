# Theta C5 likelihood-homotopy curvature

- **ID:** CLG-TTF-C5-likelihood-homotopy-curvature
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** fixed-action C5 likelihood lift and amplitude-stable curvature-topology audit

## Exact claim

Fix the physical structural tail

```text
0 < t <= u,
6 <= thetaCuspSingleAtomReflectionScale 1 u,
0 <= lambda <= 1.
```

Let every completed action/displacement/centre jet be the affine interpolation between its exact
first-atom value and its exact full-theta value, and let `M(lambda)` be the literal C5 completed
compensation formula evaluated on those seven interpolated jets.

```text
[CONJECTURE]  M'''(lambda) > 0  and  M''(0) >= 0.
```

Together these imply `M''(lambda)>=0`. The separate atom-tangent conjecture
`M'(0)>=-M(0)/5`, combined with formal `M(0)>0`, would then prove `M(1)>0` and discharge the
literal full-theta structural-tail compensation gate.

## Internal frontier

- `[CORPUS]` Exact first-atom compensation is positive.
- `[CORPUS]` Likelihood action and first three displacement jets are negative; all three centre-flow
  jets are positive.
- `[CORPUS]` Action--jet hierarchy and mixed trapezoid coupling constrain the adverse channels.
- `[CORPUS]` Pointwise signs and current pairwise cone are insufficient: saturated second-channel
  direction is strictly adverse.
- `[CORPUS]` Full compensation equals false adaptive-reserved endpoint plus an exact positive
  third-channel residual.
- `[CORPUS]` Higher-tail likelihood is an exact Laplace transform of a positive atomic spectral
  measure; dominant second-atom `exp(-3A)` identities already exist.

## External frontier

Chouikha proves complete monotonicity for classical theta quotients and their logarithmic
derivatives (arXiv:1409.1498). Yang--Tian prove variation-diminishing monotonicity rules for ratios
of Laplace transforms (arXiv:1803.02513). Standard theta log-convexity controls isolated source
derivatives. None supplies the nonlinear seven-jet C5/Bose compensation curvature above.

## Hostile status

- Monotone improvement `M'(lambda)>=0` is `[FALSIFIED]`.
- Coarse sign/pairwise-cone proof of atom-tangent reserve is `[FALSIFIED]`.
- Adaptive-reserved positivity is `[FALSIFIED]` by its negative fifth seam germ.
- Raw far-tail subtraction is numerically invalid; amplitude-factored dominant coefficient is
  positive but is diagnostic only and cannot enter a proof.
- Exact seam algebra isolates the new source invariant
  `F2 * F5 - 2 * F3 * F4`, equivalently `(F4 / F2^2)' > 0`.
- Pointwise fourth/sixth Cauchy is `[FALSIFIED]`: the physical score defect
  `p4*p6-p5^2` is negative in the tail. Pointwise `p5 <= 3*A*p4` also fails away from the
  minimal spectral edge.
- The sufficient split `3*A*F2 < -F3` and `-F5 < 6*A*F4` survived a 4,096-point,
  80-digit scan on `6<=A<=1000`; this is diagnostic only.
- The complete `n=2` atom-plus-ray ordinary reserve for `F5+6*A*F4` has an exact rational
  numerator whose expansion in `A-6` has only positive coefficients. At `A=6`, computed
  `n>=3` ordinary opposition is `2.01e-10` of that reserve.
- **Verdict:** `SURVIVES PRELIMINARY ATTACK`.

## Open core

Prove or kill the fourth-cooling law

```text
-F5 < 6 * A * F4,
```

equivalently `(exp (3*A) * F4)' > 0`, on `A>=6`. Exact dominant-sector positivity is closed.
Remaining paper obligations are: absorb all `n>=3` ordinary loss using the spectral gap, and prove
the Bell correction cannot consume the dominant reserve. The lower cooling lemma
`3*A*F2 < -F3` is now formal and axiom-audited. Once fourth cooling closes, the exact source seam invariant and the
leading seam sign close without numeric input. Full `M'''(lambda)` and `M''(0)` remain beyond that
seam gate.

## Log

- 2026-08-29 — Claim frozen after internal corpus and primary-literature audit; algebraic hostile
  attack opened.
- 2026-08-29 — Exact seam factorization found. Generic pointwise proof killed. Dominant-atom/ray
  cooling route opened and computation archived in
  `2-fully-proven/computations/2026-08-29-c5-homotopy-seam-cooling/`.
- 2026-08-29 — Closed lower cooling theorem `3*A*F2 < -F3` formalized in
  `ThetaCuspFixedActionC5LikelihoodLiftReduction`; targeted module build and axiom audit pass.
