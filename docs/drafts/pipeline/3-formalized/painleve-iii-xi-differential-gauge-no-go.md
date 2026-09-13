# Painlevé III–Xi Differential-Gauge No-Go

- **ID:** painleve-iii-xi-differential-gauge-no-go
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Sources:** Michel Planat, *Painlevé III-\(D_6\), Wild Character Varieties, and the Isomonodromic Cosine: Toward a de Branges Positivity Construction*, *Gauge Freedom Journal* **1** (2026), no. 1, Article 003, doi:10.65323/gfj.2026.003; and the longer preprint *Wild Character Varieties, Painlevé III\(_{D_6}\), the Isomonodromic Cosine, and a Complete Positivity Framework toward the Riemann Hypothesis* (April 2026), Eq. (5), Eq. (18), Conjecture 3, and §7
- **Statement:** No fixed-monodromy Painlevé III\(_{D_6}\) isomonodromic tau-function, pulled back by `t = s(1-s)` and multiplied by any polynomial exponential gauge, can equal the completed Riemann `xi` function.

## Goal

Decide the paper's open Monodromy Selection Conjecture for its stated finite-dimensional wild
Riemann--Hilbert family.  The argument must be independent of zero computations, asymptotic phase
tests, RH, and choice of Stokes/monodromy point.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: explicit cleared tau relation, regular local PIII carrier, quadratic-pullback closure, unrestricted gauge no-go, and exact degree-two corollary; targeted `lake env lean` and module build green; new declarations pass `#print axioms`
- [x] 3 → 4  publication-ready: standalone paper (theorem + complete proof + Door-2)

## Literature audit

- Journal-version metadata and DOI were checked against the journal record.  Exact equation
  numbering and wording of Conjecture 3 were checked against the longer source preprint.
- Planat defines `E_D6(s) = exp(-2s) * tau_D6(s(1-s))`, conjectures
  `xi(s) = exp(Q(s)) * E_D6(s)` for a polynomial `Q` of degree at most two, and leaves selection of
  a distinguished monodromy pair open.  The paper states that a negative answer would prove the
  isomonodromic and arithmetic Hermite--Biehler subfamilies disjoint.
- Jimbo--Miwa--Ueno/Okamoto theory gives `sigma(t) = t * tau'(t) / tau(t)` and the
  Painlevé III\(_{D_6}\) sigma equation.  Modern PIII tau literature uses the same
  logarithmic-derivative/sigma characterization.
- Miwa's analyticity theorem supplies regular local isomonodromic tau charts.  On a simply
  connected regular chart, the JMU definition integrates to a holomorphic nowhere-zero tau
  function, so the manuscript's local carrier hypothesis is the exact restriction of Planat's
  object rather than an added global premise.
- Ostrowski (1920), Reich (1982, 1984), Nagoshi (2016), Markus (2007), Han--Liu (2021),
  Wang--Yao (2024), Lü (2025), Lü--Jiang--Lü (2025), and Lü--Ma--Cao (2026) cover classical
  Dirichlet-series hypertranscendence and current zeta--gamma differential-independence results.
  The paper states explicitly that completed-xi hypertranscendence is not claimed as novel in
  isolation.
- Targeted searches found no use of differential hypertranscendence to decide this bridge.
- Novelty verdict: **[BRIDGE] [PROVED HERE]**.  Differential-algebra closure is standard; applying
  it through the exact `+2` xi defect and explicit denominator-free PIII tau elimination to close
  the stated 2026 bridge is the new delta.

## Corpus audit

- `RHTower.xi_hypertranscendental` proves unconditionally that completed `xi` satisfies no nonzero
  algebraic differential equation over `C(s)`.
- `differentiallyAlgebraic_exp_polynomial` and `differentiallyAlgebraic_mul` provide the exact
  polynomial-exponential gauge closure needed for Lean.
- No earlier corpus theorem stated the Painlevé/isomonodromic exclusion itself.  The completed
  formalization is an applied RHTower leaf, not new irregular-RH foundations.

## Lean scope

- `painleveIIID6TauRelation` is the explicit order-three, denominator-cleared polynomial relation in
  `(t, tau, tau', tau'', tau''')`; `painleveIIID6TauRelation_ne_zero` proves it is nonzero for every
  parameter pair.
- `PainleveIIID6TauCarrier` asks only for one regular local tau--sigma chart satisfying the
  cross-multiplied identity `tau * sigma = t * tau'`, the PIII sigma equation, and the exact
  carrier identity `E(s) = exp(-2s) * tau(s(1-s))`.  It does **not** assume tau is entire or assume
  the cleared third-order relation.
- `PainleveIIID6TauCarrier.tau_equation` differentiates the cross-multiplied identity twice,
  eliminates `sigma'` and `sigma''`, and derives the explicit third-order tau equation without
  division by tau.  The result therefore includes tau zeros whenever the tau--sigma chart is
  regular there.
- `PainleveIIID6TauCarrier.differentiallyAlgebraic` proves such a carrier is differentially
  algebraic once the carrier is entire.  In the no-go theorem, entireness follows from the alleged
  global bridge `xi = exp(Q) * E`, so it is not an extra conjectural hypothesis.
- `no_painleveIIID6_expPolynomialBridge_to_xi` excludes every polynomial gauge;
  `planat_polynomialGauge_painleveIIID6_bridge_false` records Planat's exact `natDegree ≤ 2` form.
- `painleveIIID6PulledTauNormalizationPolynomial_eval` and
  `painleveIIID6PulledTauNormalizationPolynomial_natDegree_le_four` prove that Planat's quoted
  quadratic tau normalization becomes a degree-at-most-four polynomial gauge after pullback.

## Conjecture and hostile attack

### Candidate killing theorem

Let `tau` be a nonzero local Painlevé III\(_{D_6}\) tau-function with fixed parameters and fixed
monodromy data.  If

`sigma(t) = t * tau'(t) / tau(t)`

satisfies

`(t sigma'')^2 = (2 sigma' - theta0 - thetaInf)^2 (sigma - t sigma')
  + 4 sigma' (sigma' - theta0) (sigma' - thetaInf)`,

then, for every polynomial `Q`, the function

`F(s) = exp(Q(s)) * tau(s(1-s))`

is differentially algebraic wherever defined.  Consequently no entire continuation of `F` equals
`xi`.

### Attacks

1. **Tau logarithm/movable zeros.**  `tau'/tau` is only meromorphic.  Clear denominators in the
   sigma equation.  Result is a polynomial differential equation for `tau`, valid off its zeros and
   then everywhere by analytic continuation.
2. **Could cleared relation vanish identically as a differential polynomial?**  No.  Its squared
   highest-jet term has coefficient `t^4 * tau^4` and no right-hand term contains `tau'''`.
3. **Quadratic pullback critical point.**  Away from `s = 1/2`, chain rule is triangular with
   nonzero diagonal powers of `1-2s`; clearing them gives a nonzero relation.  Analytic continuation
   crosses the isolated critical point.
4. **Exceptional monodromy.**  Monodromy selects a solution, not the sigma equation.  Every fixed
   monodromy choice remains differentially algebraic.
5. **Gauge escape.**  `exp(Q)` is differentially algebraic for every polynomial `Q`, with no degree
   bound.  Multiplication cannot leave the differential-algebraic field.
6. **Canonical-system escape.**  A de Branges function not represented by a finite-dimensional
   isomonodromic tau-function is not excluded.  This is the positive survivor, not a loophole in the
   killing theorem.

## Paper proof

Write `u = tau`, `u_j = d^j u/dt^j`, and

`A = u*u_1 + t*u*u_2 - t*u_1^2`,

`B = 2*u*(u*u_2-u_1^2) + t*(u^2*u_3-3*u*u_1*u_2+2*u_1^3)`.

Differentiate the cross-multiplied defining identity `u*sigma = t*u_1`.  Without dividing by `u`,
one obtains

`u^2*sigma' = A`,

`u^2*(sigma - t*sigma') = t^2*(u_1^2-u*u_2)`,

`u^3*sigma'' = B`.

Multiplying the sigma equation by `u^6` and using these three polynomial identities gives

`t^2*B^2 = t^2*(2*A-(theta0+thetaInf)*u^2)^2*(u_1^2-u*u_2)
  + 4*A*(A-theta0*u^2)*(A-thetaInf*u^2)`.

This is an algebraic differential equation with polynomial coefficients.  It is nonzero: evaluation
at `(t,u,u_1,u_2,u_3)=(1,1,0,0,1)` is `1`, independently of the monodromy parameters.  Because the
derivation never divides by `u`, the equation is proved directly at every point of the regular
tau--sigma chart; no continuation across tau zeros is assumed.  Hence every fixed-monodromy PIII
tau-function is locally differentially algebraic over `C(t)`.

Let `g(s)=s(1-s)` and `y(s)=u(g(s))`.  On `s != 1/2`, chain rule expresses each
`u^(k)(g(s))` triangularly as a rational expression in `s,y,...,y^(k)`, with top coefficient
`(g'(s))^(-k)=(1-2s)^(-k)`.  Substitute these expressions into a nonzero differential equation for
`u` and clear powers of `1-2s`.  Nonconstancy of `g` and the explicit inverse triangular recursion
preserve nonzeroness.  This yields a local differential equation on any chart avoiding `s=1/2`.
If a global bridge exists, its identity with `exp(-Q) * xi` makes the carrier entire; the identity
theorem then propagates the cleared local equation globally.  No continuation of `u` or `y` across
the critical point is assumed.

For every `Q in C[s]`, `exp(Q(s))` satisfies the first-order algebraic differential equation
`v' - Q'v = 0`.  Differentially algebraic meromorphic functions form a differential field, so
`F(s)=exp(Q(s))*y(s)` is differentially algebraic.  If an entire continuation of `F` equalled
completed `xi`, then `xi` would be differentially algebraic.  This contradicts the unconditional,
dependency-closed theorem `RHTower.xi_hypertranscendental`.  Thus no polynomial gauge and no fixed
monodromy pair realizes the proposed bridge.  QED.

## No-go closure

- **Exact killing theorem/mechanism:** finite-dimensional PIII\(_{D_6}\) tau-functions are
  differentially algebraic; `xi` is hypertranscendental; algebraic pullback and polynomial
  exponential gauge preserve differential algebraicity.
- **Strongest positive survivor:** polynomial-exponential gauge class of `xi` is entirely
  hypertranscendental.  Any successful irregular microlocal RH realization must therefore escape
  finite-dimensional isomonodromy--for example through a genuinely arithmetic ind/pro-holonomic
  object or a non-differentially-algebraic canonical system.
- **New insight:** missing arithmetic input cannot be encoded by choosing one point of the finite
  PIII wild character variety.  It must enlarge representation class, not merely select monodromy.
- **Status:** **[PROVED HERE] [FORMALIZED]** in
  `GaloisForLFunctions.RHTower.XiPainleveTauGaugeNoGo`; targeted direct Lean and module build pass.
  Explicit relation, local-to-global carrier theorem, unrestricted no-go, and exact degree-two
  corollary use only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-24 — created in `1-in-progress`; internal corpus and primary-literature audits complete.
- 2026-08-24 — hostile audit closed; paper proof promoted to `2-fully-proven`.
- 2026-08-24 — exact survivor and closed bridge exclusion formalized; promoted to `3-formalized`.
- 2026-09-13 — closed remaining formal gap: derived the nonzero cleared PIII tau equation directly
  from the defining tau--sigma identity and sigma equation, proved local quadratic-pullback
  differential algebraicity, derived carrier entireness from the alleged bridge, and added the exact
  degree-two falsification theorem.  No heartbeat limit changes.
- 2026-09-13 — publication manuscript completed at
  `docs/drafts/pipeline/4-publication-ready/painleve-iii-xi-polynomial-gauge-no-go/main.tex` with a
  clean 17-page PDF render and a full proof of completed-xi hypertranscendence, tau elimination,
  pullback closure, and degree-unrestricted bridge exclusion.
- 2026-09-13 — hostile editorial revision closed literature, formal-series-domain, weighted
  convergence, pullback-injectivity, local tau-chart, motivation, interpretation, and normalization
  gaps.  Added degree-at-most-four normalization lemmas to the formal module.  Targeted Lean
  verification and full PDF layout inspection passed; no project build run.
- 2026-09-13 — added explicit manuscript declaration that all research and writing were performed
  by AI agents based on OpenAI GPT-6 and Anthropic Fable 5, Fable 5.1, and Opus 5; human
  contribution was project management only.
- 2026-09-13 — second hostile pass updated literature coverage through 2026, supplied the omitted
  noncollapse argument for the gamma Weierstrass product, and made human scholarly accountability
  explicit without changing the disclosed contributor roles.
- 2026-09-13 — third hostile pass found no remaining literature, proof-closure, motivation,
  interpretation, scope, disclosure, or layout defect.  Publisher records verify cited 2025--2026
  metadata; all 17 PDF pages were inspected; terminal theorem axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
