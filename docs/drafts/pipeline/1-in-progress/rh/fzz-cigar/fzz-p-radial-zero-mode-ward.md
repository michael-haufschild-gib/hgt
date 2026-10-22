# FZZ-P: radial zero-mode boundary contribution to the Ward identity

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** FZZ-P frontier; Halder–Jafferis, arXiv:2402.00932v3, (3.14), (3.26), and (3.28)–(3.33).

## Proof chain and obstacle

Fixed theta/FZZ occurrence → source-derived integrated replica–momentum Ward identity → balanced external-Gamma vacuum-delay saturation → passivity → RH.

The previous two-marked calculation retained a direct mixed source term. Its worldsheet-position scale must not be confused with the target-radial cutoff considered here. The present attack asks whether zero-mode neutrality permits dropping the radial boundary term from the source Ward identity.

## Conjecture and direct test

**Rejected conjecture:** at zero background radial charge, the logarithmic coupling Ward response disappears after geometric subtraction of the infinite radial volume.

In the positive effective-coupling chamber, the neutral radial constant-mode kernel from an exponential winding potential is

`K(u,b,x)=exp(-exp(u+b*x))`, with `b>0` and effective coupling `exp(u)>0`.

At physical radial cutoff `x=-R`, set `I_R=integral_(-R)^infinity K dx`. The substitution `t=exp(u+b*x)` predicts

`I_R=E1(exp(u-b*R))/b`.

The corpus theorem `DaiYoshikawa.expIntegralE1_add_log_eq` gives the exact small-endpoint remainder. Hence

`I_R-R -> -(u+gamma)/b`.

Its logarithmic coupling derivative is `-1/b`, not zero. Direct differentiation of the integrand gives a convergent insertion integral with value `exp(-exp(u-b*R))/b`, tending to `1/b`. This is the radial boundary contribution that a neutral-source Ward argument must retain.

**Sharp positive survivor.** For every real effective coupling `A`, positive slope `b`, and finite cutoff, `exp(-A*exp(b*x))` is integrable on `(-R,infinity)` exactly when `A>0`. If `A<=0`, the kernel is at least one throughout that infinite tail, so ordinary integrability fails. In the positive chamber, the exact cutoff integral, finite part, integrated coupling insertion, and differentiation-under-integration identity are all closed in Lean. Thus the failed cancellation leaves a complete radial normalization law, rather than just a negative statement.

## Scope

The positive effective-coupling chamber is parametrized, not assumed as a positivity theorem for the complete sine–Liouville field integral. The angular winding sum can leave this chamber; its contour/continuation has not been supplied. This calculation does not evaluate the nonzero modes, the full torus source, external-momentum coupling, or RH. It tests the specific proposed cancellation of the neutral radial boundary.

## Plan

- [x] Inspect current source prescription, corpus methods, and broad recent arXiv results.
- [x] Prove the original radial integral equals its transformed exponential integral.
- [x] Prove its convergence chamber, finite part, and complete coupling-insertion boundary law in Lean, without source hypotheses.
- [ ] Check whether the retained boundary can participate in the actual mixed momentum Ward identity; do not replace that identity with neutrality.

## Search evidence

2026-09-10: deep `source replica momentum counterterm Ward identity`; hybrid `marked source coupling integration by parts boundary momentum zero mode`; deep `radial constant mode integral exponential exponential gamma Mellin substitution finite part`. Results are partial, with pending coverage. Method records for integration by parts retain explicit boundary terms; retrieved replica covariance results require their own positive Hilbert realization. Neither gives a source cancellation.

Broad arXiv searches used `screening`, `isomonodromic`, `anomaly`, and `boundary`, preferring June–September 2026. [Ma, 2 September 2026](https://arxiv.org/html/2609.02952v1), constructs connection-preserving transformations for degree-one q-difference systems. Attempted transfer would require a source-derived coefficient matrix and its nonresonant canonical normalization; neither has been identified for the torus replica correlator. This does not provide the missing Ward law.

## Status

Closed module: `formal/GaloisForLFunctions/RHTower/FZZCigarNeutralRadialZeroModeWard.lean`, namespace `GaloisForLFunctions.RHTower`. Positive slopes and couplings are parametrized by exponentials; there are no hypothesis binders in the public theorem statements.

Main results:

- `fzzNeutralRadialSignedKernel_integrable_iff`: exact convergence chamber for every real effective coupling.
- `fzzNeutralRadialCutoffIntegral_eq` and `fzzNeutralRadialCutoffIntegral_finitePart`: original radial integral and volume-subtracted limit.
- `fzzNeutralRadialCouplingInsertion_integral`, `fzzNeutralRadialCutoffIntegral_couplingWard`, and `fzzNeutralRadialCutoffIntegral_deriv_eq_integral_deriv`: complete integrated source derivative, retaining the cutoff boundary.
- `fzzNeutralRadialCutoffIntegral_couplingWard_limit` and `fzzNeutralRadialFinitePart_couplingWard_ne_zero`: nonzero surviving Ward contribution and agreement with the finite-part derivative.

Verification on 2026-09-11: scratch `lake env lean /tmp/fzzp_zero_mode.lean` passed; the installed proof body matches it exactly. Final `lake build GaloisForLFunctions.RHTower.FZZCigarNeutralRadialZeroModeWard` passed, compiling only the new leaf and replaying cached dependency messages. `lake env lean /tmp/fzzp_zero_mode_axioms.lean` audited all 13 public theorems and their dependency closures: only `propext`, `Classical.choice`, and `Quot.sound`, with no added axioms. `python3 scripts/formal_tools.py lint` passed with existing large-file warnings. The module is wired into `RHTower.lean`; no umbrella/full build or numerical experiment was run.

**Next source attack.** Derive the charged radial factor from the original regulated integral and compare its meromorphic neutral limit with the retained cutoff boundary. The anticipated factor is `Gamma(s)*exp(-s*u)/b`, whose coupling Ward product contains `s*Gamma(s)`, not an isolated factor `s`. The inspected Mathlib theorem `Complex.tendsto_self_mul_Gamma_nhds_zero` supplies the residue limit, but the full source continuation and its external-momentum identification are not yet proved here. Even matching these radial prescriptions would not force vacuum-delay saturation without the complete nonzero-mode Ward balance.

The direct coupling-insertion test is now [closed in Lean](../../fzz-p-coupling-insertion-gamma.md). The original density `b*exp(u+b*x)*exp(-exp(u+b*x))` is positive and integrable with mass one. Its full-line characteristic, using `exp(i*p*x)`, is `exp(-i*p*u/b)*Gamma(1+i*p/b)`. Its exact coupling derivative divided by the characteristic is `-i*p/b` at every momentum; this derivative vanishes exactly at `p=0`. Identifying `p` with the actual external BRST label, deriving the shifted external-leg Gamma arguments and assembling the remaining fields are still required. No complete-source stationarity or vacuum-saturation law is proved.

FZZ-P remains active. RH remains unproved.
