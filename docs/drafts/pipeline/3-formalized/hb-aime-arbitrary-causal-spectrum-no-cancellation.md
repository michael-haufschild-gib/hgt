# HB AIME arbitrary causal-spectrum no-cancellation

- **ID:** HB-AIME-ACS-NC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` HB returned-determinant open core; local corpus modules `ThetaCuspHawkingNonlinearChiralTeukolskyReturnProducer`, `ThetaCuspHawkingAIMECrossBranchTeukolskyResidue`, and `ThetaCuspHawkingTeukolskyDelayedPumpProbe`
- **Statement:** Every finite-variation superposition of strictly damped causal Teukolsky modes decays at late advanced time even when damping accumulates at zero; consequently it cannot supply the unique nonzero counterterm cancelling the fundamental BM AIME pole, and adding any passive stationary mass response still leaves that pole eventually nonzero.

## Goal

Discharge a significant part of HB's full third-order `++-` noncancellation burden. Existing Lean
proves the AIME pole numerator is nonzero on every Xi fibre and classifies its unique cancelling
counterterm, but excludes only finite local packets plus one uniformly damped continuum. This card
attacks the hardest surviving spectral escape: an arbitrary infinite threshold spectrum with no
uniform damping gap. The theorem is source-pure and does not assume RH, source FE covariance, or
the desired pole survival.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: premise-free Lean theorem `d4BMPassiveArbitraryCausalSpectralCancellationRouteKilled`, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus audit

- `d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff`: normalized AIME numerator is nonzero
  on every Xi fibre.
- `d4FullCrossBranchPolePrincipalPart_order_qnmMinus_xi_iff`: pole survival is exactly failure of
  the forced same-pole counterterm.
- `d4BMPassiveStationaryFullNumerator_xi_ne_zero`: nonnegative absorbed stationary mass cannot
  cancel AIME.
- `d4BMFiniteLocalContinuumDelayedSourceRemainder_tendsto_zero`: existing result covers finite
  local Jordan packets plus one `L2` continuum with uniform damping `3/2`.
- `tendsto_tsum_zero_of_pointwise_damping_of_summable_majorant`: corpus precedent removes a
  uniform damping gap for countable sums, but has not been applied to the full measurable
  Teukolsky spectral completion.

## External novelty audit (through 2026-08-30)

- Spiers--Pound--Moxon, arXiv:2305.19332, derive the reduced second-order Teukolsky source and its
  gauge dependence; they do not prove a third-order BM/AIME noncancellation theorem.
- Green--Hollands--Sberna--Toomani--Zimmerman, arXiv:2210.15935, construct QNM projections but
  explicitly retain direct and late-time tail contributions and do not assume QNM completeness.
- Sberna--Bosch--East--Green--Lehner, arXiv:2112.11168, identify AIME as a third-order effect but
  do not classify arbitrary causal spectral counterterms.
- Spiers, arXiv:2402.00604, separates extended Teukolsky sources; no all-spectrum late-time
  counterterm exclusion is proved.
- No primary source found through the audit date proving the exact BM/Xi finite-variation
  no-cancellation result below.

## Frozen conjecture and proof chain

Let `(Omega, mu)` be an arbitrary measure space, `c : Omega -> C` integrable, and
`omega : Omega -> C` measurable. Assume `im (omega x) < 0` for almost every `x`. Define

`R(t) = integral c(x) exp(-i omega(x) t) dmu(x)`.

Then:

1. `R(t) -> 0` as `t -> +infinity`, with no uniform lower bound on `-im omega`.
2. `R` cannot eventually equal any fixed nonzero complex number.
3. For every Xi fibre `q` and passive stationary mass `m >= 0`,
   `AIME(q) + m AIME(q) + R(t)` is eventually nonzero.
4. The corresponding full cross-branch principal part eventually has exact simple-pole order
   `-1` at the negative fundamental BM QNM.

Proof idea: for `t >= 0`, character norm is `exp(im(omega x) t) <= 1`, so `norm c` is an
integrable dominator. Strict pointwise damping makes each character tend to zero. Dominated
convergence gives (1); (2) follows by uniqueness of limits; exact AIME nonvanishing and
`1 + m > 0` give the nonzero stationary limit in (3); the existing pole-order equivalence gives
(4).

## Hostile tests and boundary

- **No damping gap:** allowed; rates may accumulate at zero.
- **Infinite/continuous spectrum:** allowed; arbitrary measure space and integrable complex
  density.
- **Complex cancellation:** allowed inside the integral; proof uses norm domination only.
- **Peripheral spectrum:** excluded exactly where `im omega = 0`; such mass need not decay.
- **Singular/non-finite-variation completion:** excluded because no integrable dominator exists.
- **Gauge issue:** theorem applies only after projection to the coordinate-invariant full
  same-pole residue; it does not claim invariance of a raw second-order source coefficient.

## Approach

Prove the arbitrary-measure dominated-convergence theorem first, then instantiate the exact BM
AIME numerator and existing passive stationary source. Promote only after the full paper chain is
dependency-closed, then formalize in one new RHTower module and wire it into `RHTower.lean`.

## Paper proof

**[PROVED HERE]** Fix an arbitrary measure space `(Omega, mu)`. Let `c` be integrable and let
`omega` be measurable with `im (omega x) < 0` almost everywhere.

For every `t >= 0`,

`norm (c(x) exp(-i omega(x) t)) = norm(c(x)) exp(im(omega(x)) t) <= norm(c(x))`

almost everywhere. The right side is integrable. For almost every fixed `x`, write
`omega(x)=a+ib` with `b<0`. Then

`exp(-i omega(x)t)=exp(bt) exp(-iat)`,

whose norm is `exp(bt) -> 0`; hence the complex character itself tends to zero. Measurability of
the integrands follows from measurability of `omega` and strong measurability of the integrable
density `c`. Dominated convergence therefore gives `R(t) -> 0`. Notice that the argument is
pointwise in `b`; no uniform spectral gap is used.

Now fix an Xi fibre `q`. Existing exact BM algebra gives a nonzero AIME numerator `N(q)`. A passive
stationary mass `m >= 0` contributes `m N(q)`, so the stationary total is
`S(q)=(1+m)N(q) != 0`. Thus

`N(q)+mN(q)+R(t) -> S(q) != 0`.

The complement of `{0}` is a neighbourhood of `S(q)`, so the full numerator is eventually
nonzero. In particular `R` cannot eventually equal the forced counterterm `-S(q)`. Applying the
already-proved equivalence between nonzero full numerator and meromorphic order `-1` gives exact
eventual survival of the negative-branch fundamental BM pole. Every step is unconditional and
uses neither RH nor QNM completeness. This proves all four frozen claims.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:**
  `d4BMCausalSpectralSourceRemainder_tendsto_zero` kills every finite-variation completion carried
  almost everywhere by strictly damped frequencies, without a uniform damping gap.
  `eventually_d4BMPassiveArbitraryCausalSpectralPole_order_qnmMinus_xi` then proves the exact
  negative-branch fundamental BM pole eventually has meromorphic order `-1` after adding arbitrary
  such spectrum and any passive stationary mass response. The premise-free wrapper
  `d4BMPassiveArbitraryCausalSpectralCancellationRouteKilled` universally quantifies the whole
  route class and is the closed Lean certificate.
- **Strongest positive survivor:**
  `d4BMPassiveArbitraryCausalSpectral_forcedCounterterm` proves a persistent cancelling
  counterterm forces spectral mass outside the strictly damped sector. Thus the only spectral
  survivors are peripheral/growing modes or non-finite-variation source densities.
- **New insight:** Accumulation of decay rates at zero is not an HB escape. Uniform damping used in
  the earlier physical-continuum proof was unnecessary; finite variation plus pointwise strict
  damping already forces total extinction. Remaining full-source PDE burden is now a peripheral
  or singular spectral-incidence problem, not an infinite damped-threshold summation problem.
- **Status:** Internal/external audit complete; paper proof and Lean proof dependency-closed in
  `GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEArbitraryCausalSpectrumNoCancellation`.
  Direct `lake env lean` and targeted `lake build` pass. Axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`, including for the premise-free wrapper. Module is wired into `RHTower.lean`. Global lint reports
  unrelated pre-existing shared-tree reachability errors and does not report the new module.

## Log

- 2026-08-30 — created directly in stage 1 after corpus and current-literature audit; conjecture
  frozen before Lean work.
- 2026-08-30 — dominated-convergence proof closed arbitrary infinite threshold spectra; promoted
  to stage 2.
- 2026-08-30 — formalized exact all-spectrum decay, peripheral-spectrum survivor, eventual
  noncancellation, and meromorphic pole-order capstone; promoted to stage 3.
