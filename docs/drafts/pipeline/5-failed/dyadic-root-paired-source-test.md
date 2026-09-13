# Dyadic roots: paired-source obstruction and exact cancellation

- Stage: 5-failed, only for taking separate global analytic roots of the paired
  eta series and its elementary factor. The actual dyadic-root route remains open.
- No RH proof and no new global root of completed xi.
- Lean module: `RHTower.PairedEtaRootContinuationBoundary`.

## Frozen producer and killing result

The actual absolutely convergent paired series `etaPair` is analytic on `Re(s)>0`.
Could it replace the failed heat producer, with its elementary multiplier removed
after taking a global square root? No: at `rho = 1+2*pi*i/log(2)`,

`etaPair(rho)=0`, `etaPair'(rho)=log(2)*zeta(rho) != 0`.

The multiplier, not zeta, supplies this simple zero: `Re(rho)=1`, `rho!=1`, and
zeta is nonzero on that line. Any analytic square vanishing there has derivative
zero. `not_exists_analytic_etaPair_squareRoot_rightHalf` is a closed no-existence
theorem; `analyticOrderAt_etaPair_auxiliary` records the exact order one.

## Positive survivor [PROVED HERE]

Let `U=zetaPoleUnit`, the entire continuation of `(s-1)*zeta(s)`, and let

`C(s)=dslope (fun z => 1-2^(1-z)) 1 s`.

Then `C` is entire, `C(1)=log(2)`, and the complete source identity is
`etaPair(s)=C(s)*U(s)` for every `Re(s)>0`, including `s=1`.
Thus `etaPair(1)=log(2)`. Cancellation before fractional powers preserves the
original function without requiring either factor to have a global root.

A second exact comparison uses

`J_h(s)=dslope exp 0 (-h*(s-1))`, `H_h(s)=J_h(s)*U(s)`.

Both are entire in `s`; `J_h(1)=H_h(1)=1` for every real `h`. As `h->0`,
`J_h->1` and `H_h->U` locally uniformly on the whole complex plane. Moreover,
`H_log(2)(s)=etaPair(s)/log(2)` throughout the positive half-plane.

This family is an analytic comparison **defined using the already continued
pole unit**. It is not an independent arithmetic producer for roots of that unit.
The limit theorem supplies no square-root estimate or monodromy cancellation.

## Dependency-closed paper proof

1. The paired-series identity gives `(1-2^(1-s))*zeta(s)` away from one.
   At `rho`, its exponential multiplier is zero and has derivative `log(2)`.
   Zeta's established nonvanishing on `Re(s)=1` proves the derivative is nonzero.
2. Analyticity of `C` follows from the shifted power series at one and the ordinary
   quotient elsewhere. The identity `(s-1)*C(s)=1-2^(1-s)` is exact at every point.
   The identity theorem extends `etaPair=C*U` across one on `Re(s)>0`.
3. The entire divided difference of `exp` has value one at zero. Composition gives
   all stated analyticity and normalization facts for `J_h`.
4. Joint continuity in `(h,s)` at every `(0,s)` proves local uniform convergence
   of `J_h` to one, and of `H_h` to `U`. Substitution of `h=log(2)` and the exact
   divided-difference identity identify the paired source, including at one.

## Conjecture outcomes and remaining obstacle

- Separate global roots after eta pairing: disproved by an actual simple zero.
- Combine the cancelling factors first: exact entire source recovery proved.
- Recover roots by shrinking the dilation: no root construction obtained. The
  proved limit returns the original `U`, whose global roots remain the hard step.
- This is not a no-go for signed sources, all compensated constructions, or RH.

## Verification

- `/tmp/dyadic-paired-source.1NxN2O/Names.lean` passed `lake env lean`.
- `Paired.lean` and the complete `Combined.lean` passed direct Lean checks.
- New module is umbrella-wired. Targeted `lake build
  GaloisForLFunctions.RHTower.PairedEtaRootContinuationBoundary` passed (37 seconds).
  `Axioms.lean` audits all 27 public theorems: only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Global lint fails on two unrelated missing umbrella imports:
  `RHTower.Sieve.KloostermanGlobalCollisionCoprime` and
  `RHTower.ThetaCuspHawkingBMLaurentHorizonValue`. This module's import is present;
  the unrelated modules were not changed.
- No numerical experiments, added axioms, placeholders, or heartbeat increases.
- Imports narrowed to the paired-series derivative, pole split, and analytic
  divided-difference modules; coercions handled explicitly.

## Search audit

- Deep/method corpus searches returned partial coverage; the inspected eta query
  had empty generated proof ideas and ingredient sets. Relevant candidates
  were checked in source and Lean; no complete-corpus verification is claimed.
- Broad `renormalization` search found Hasenfratz et al.,
  [August 2026](https://arxiv.org/abs/2608.28580). Its abstract describes approximate
  inverse blocking with conditional reconstruction and rethermalization. This is
  not a theorem constructing analytic roots of an identified complex function.
- Broad `desingularization` search found Enciso--Fernandez--Meyer,
  [July 2026, Theorem 1.1](https://arxiv.org/html/2607.19233v1).
  It constructs exact Euler vorticities tending distributionally to an analytic
  vortex sheet. Its limiting topology and conclusion do not provide complex
  square-root descent or local uniform root convergence.
- Broad `resurgence` search led to Kervyn--Stieberger,
  [April 2026 fallback, section 3.2.3](https://arxiv.org/html/2604.07444v1).
  The authors leave the higher-dimensional connection problem incomplete and
  distinguish changing reduced directions from continuation of a fixed problem.
  No source-specific root continuation theorem was imported from that paper.
