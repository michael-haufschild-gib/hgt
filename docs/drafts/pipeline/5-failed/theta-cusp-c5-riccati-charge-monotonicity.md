# Theta C5 Riccati-charge monotonicity no-go

- **ID:** `C5-RB1-CHARGE-MONO-NOGO`
- **Stage:** 5-failed
- **Type:** FALSIFIED; POSITIVE SURVIVOR FORMALIZED
- **Source:** `theta-c5-cofinal-functional-absorption.md`, conjecture `C5-RB1`
- **Statement:** Positivity or strict forward increase of the conjugated Riccati charge, even when
  combined with global Riccati margin, seam C5 positivity, and the corpus six-jet
  atom/likelihood sign architecture, does not force global fifth-root curvature.

## Goal

Test the strongest lower-drift shortcut for `C5-RB1`. If charge monotonicity forced the stationary
charge envelope, it would give modular-center C5, then feed off-center direct-J/rank-four
transport, higher-packet/no-escape, CLG/TTF or Weil positivity, and RH. Later joins remain separate.

## Gates

- [x] 0 → 1  corpus-derived target and explicit RH chain
- [x] 1 → 2  dependency-closed analytic counterexample and survivor
- [x] 2 → 3  Lean theorem, targeted build, axiom audit
- [ ] 3 → 4  publication-ready standalone no-go note

## Approach

For the corpus sextic-Gaussian action `q`, define the same integrating-factor charge exposed by
the completed theta calculation:

```text
Q(t) = exp(2*q(t)) * (2*q'(t)*q''(t) - q'''(t)).
```

Exact differentiation cancels the mixed third-jet channel:

```text
Q'(t) = exp(2*q(t)) *
  (2*q''(t)^2 + 4*q'(t)^2*q''(t) - q''''(t)).
```

Writing `x=t^2`, the bracket is strictly positive on the whole real line by one completed-square
estimate and positivity of the remaining polynomial terms. Hence `Q(0)=0` and `Q` is strictly
increasing on `[0,∞)`. The same profile already has global nonnegative Riccati margin, C5 positive
on a right seam interval, and the full six-jet atom/likelihood sign architecture, yet its C5 is
strictly negative at a later positive radius.

## No-go closure

- **Exact killing theorem/mechanism:**
  `sexticGaussianRiccatiChargeMonotonicity_does_not_force_globalC5`; paired with
  `atomLikelihoodRiccatiSignArchitecture_with_localC5_does_not_force_globalC5`, it proves all
  lower-drift data coexist with strict C5 failure for one smooth positive even profile.
- **Strongest positive survivor:** the exact completed-theta charge-envelope coordinate already
  formalized as
  `thetaCuspReflectedActionRiccatiChargeEnvelopeGapAtZero`; global modular-center C5 is equivalent
  to its nonnegativity only at negative intrinsic minima. The charge is the literal raw
  source-flux Wronskian, so a viable proof must upper-control it through nonlocal chord,
  likelihood-history, or modular-ODE structure.
- **New insight:** strict charge growth is not incomplete evidence for the desired sign; it has
  provably insufficient orientation. No further theorem whose only new conclusion is a lower
  bound, positivity, or monotonicity of this charge can close `C5-RB1`.
- **Status:** countermodel, exact derivative law, strict monotonicity, and no-go capstone are closed
  in Lean in
  `GaloisForLFunctions.HilbertMetric.RiccatiChargeFifthRootNoGo`. No computation enters any proof.

## Novelty audit

Corpus search used `scripts/formal_tools.py research`. It contained the completed-theta increasing
charge and the earlier sextic C5 countermodel separately, but no theorem connecting them. August
2026 literature audit found no completed-theta ninth-order quotient or this Riccati-charge/C5
counterexample. Novelty claim is limited to this exact strengthened no-go and its envelope-only
survivor.

## Log

- 2026-08-29 — Route killed on paper and in Lean; positive survivor retained and already
  dependency-closed/formalized.
