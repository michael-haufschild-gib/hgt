# Xi local analytic-order phase universality law

- **ID:** xi-local-analytic-order-phase-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper-proved and Lean-formalized)
- **Source:** Post-Law-25 terminal inventory of algebraic, circle, K-theory, Böttcher, and SEM phase files
- **Statement:** At every complex point, vanishing of the finite local Xi analytic
  order is equivalent simultaneously to algebraicity of the reflected quadratic prime phase,
  vanishing of its quadratic circle charge, existence of irrational-rotation `K₀` and algebraic
  Weyl determinant data, triviality of the complete Böttcher Prüfer character, vanishing of the
  prime order-circle charge, and closure of every actual completed-SEM phase/charge realization.
  Nonzero local order synchronizes six explicit algebraic/topological failure channels.

## Gates

- [x] 0 → 1 in-progress: exact Lean declarations and every downstream use read
- [x] Complete paper proof with no open dependency
- [x] Lean direct check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs read

1. Reflected quadratic algebraic phase and quadratic circle charge are each exact detectors of
   `(analyticOrderAt xi ρ).toNat = 0`.
2. Prime-rotation `K₀` index data and algebraic prime--Weyl determinant descent exist exactly at
   rank/order zero for every nonzero rational-imaginary step.
3. The full Böttcher Prüfer character tower is trivial exactly at order zero.
4. One irrational prime-log circle charge is faithful on integral order.
5. Every actual `SEMSplitData` identifies hole count, completed prime-circle charge, dyadic phase,
   and integral Fitting charge with the same local analytic order.

## Internal noncollision audit

`scripts/formal_tools.py research "analytic order algebraic phase circle charge K zero Weyl
determinant Bottcher Pruefer SEM"` returned the component detectors but no pointwise common
consumer. Direct symbol-use search found only separate right-half RH criteria. Those global
criteria are partly vacuous and are rejected as the mathematical delta; the surviving theorem is
the unconditional local classifier before any zero/right-half assumption.

## Paper proof

For fixed prime `p`, nonzero step `q`, and arbitrary `ρ`, each of the first six charts already has
an exact local biconditional with `(analyticOrderAt xi ρ).toNat = 0`: reflected quadratic
algebraic phase, reflected quadratic circle charge, prime-rotation `K₀` datum, algebraic prime--Weyl
determinant descent, complete Böttcher Prüfer character, and prime order-circle charge. Thus local
order zero discharges all six, while any one chart recovers order zero.

For an actual `SEMSplitData` at `ρ`, the hole-count theorem identifies `zs.length` with that same
local order. Order zero therefore closes every dyadic root phase. The completed prime-circle
transport identifies its charge with the already-vanishing local order-circle charge, and the
integral Fitting-charge identity reduces every modulus to the zero cast. This proves the seventh
chart without a right-half or zero assumption.

If local order is nonzero, negating the six biconditionals gives nonalgebraicity, two nonzero circle
charges, absence of both `K₀` and Weyl data, and failure of the complete Prüfer tower; classical
negation extracts a concrete nontrivial Prüfer depth. Conversely, zero order makes the quadratic
phase algebraic, contradicting the first failure field. Finally, at a hypothetical right-half Xi
zero, the pointwise universal certificate forces zero order while the analytic zero theorem forces
nonzero order, yielding the RH corollary.

## Lean formalization

`RHTower/XiLocalAnalyticOrderPhaseUniversalityLaw.lean` defines the completed-SEM and seven-chart
local certificates plus the six-channel failure certificate. It proves
`xiLocalAnalyticOrder_eq_zero_iff_phaseUniversalCertificate`,
`xiLocalAnalyticOrder_ne_zero_iff_phaseFailureUniversalCertificate`, and
`riemannHypothesis_iff_all_rightZeros_localPhaseUniversalCertificate`. Exact direct check:

```text
lake env lean GaloisForLFunctions/RHTower/XiLocalAnalyticOrderPhaseUniversalityLaw.lean
```

passed on the first run.

## Hostile literature noncollision audit

Exact searches combined analytic order/multiplicity with Gelfond--Schneider phase, irrational
circle and rotation-algebra `K₀`, Weyl determinant descent, Prüfer character, Euler--Maclaurin
Fitting charge, and RH. No source located the seven-way pointwise classifier. Nearest rigorous Xi
work studies multiplicity and derivative-zero statistics (Farmer--Gonek,
[arXiv:0803.0425](https://arxiv.org/abs/0803.0425)), operator/Hilbert-space positivity
(Connes--Consani, [arXiv:1910.14368](https://arxiv.org/abs/1910.14368)), and screw-function Weil
criteria (Suzuki, [arXiv:2206.03682](https://arxiv.org/abs/2206.03682)). None identifies local Xi
analytic order simultaneously through these algebraic, `K`-theoretic, Prüfer, circle, and SEM
detectors. This is a noncollision audit, not a priority claim.

## Log

- 2026-07-22 — Found after Law25 restart. Rejected arbitrary conjunction of vacuous RH-indexed
  criteria; retained the stronger non-vacuous pointwise analytic-order classifier shared by six
  independent mechanisms plus actual SEM realizations.
- 2026-07-22 — Pointwise positive/failure laws and RH corollary paper-proved and formalized; exact
  direct check passed first run. Hostile literature audit found no collision. Final audit remains.
