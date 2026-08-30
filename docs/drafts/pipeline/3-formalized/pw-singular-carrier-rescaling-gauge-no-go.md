# PW singular-carrier rescaling-gauge no-go

- **ID:** pw-singular-carrier-rescaling-gauge-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · PW-B surviving singular/transseries branch
- **Statement:** The exact positive-ray singular PW multiplier is a globally trivial positive reciprocal cocycle, so its weighted reflection is gauge-conjugate to bare reflection; hence no channel-rescaling-invariant criterion can select the critical wall, while neutral-channel energy conservation selects it exactly.

## Goal

Kill the conservative/unitary sewing class after the now-proved singular-carrier step in

`PW endpoint winding -> singular FE partner -> source-forced partner balance -> Deninger Ward -> RH`.

The intended theorem does not assume Xi-zero data. It asks whether the exact forced singular carrier, plus any criterion insensitive to independent positive normalization of the two reflected channels, can force the missing partner balance. A universal negative answer removes that whole producer class. The positive survivor identifies the extra premise precisely: source-independent neutral channel calibration.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `RHTower.pwSingularCarrier_rescalingGauge_noGo`, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Frozen conjecture SCG-2

For `x > 0`, put

`a(x) = A(x^2) = x^{-1} exp(x - x^{-1})`,

where `A` is the unique positive-ray singular PW reflection multiplier, and define

`B_x(u,v) = (a(x)v, a(x)^{-1}u)`, `S_c(u,v) = (cu,v)`.

Prove simultaneously:

1. `a(x)>0`, `a(x)a(x^{-1})=1`, `B_x^2=I`, and `B_x = S_{a(x)} B_1 S_{a(x)}^{-1}` for every `x>0`.
2. With `g(x)=sqrt(a(x))`, the entire positive-ray cocycle is a coboundary,
   `a(x)=g(x)/g(x^{-1})`; consequently the weighted reflection
   `(R_a f)(x)=a(x)f(x^{-1})` is globally conjugate to bare reciprocal reflection by multiplication with `g`.
3. There is no predicate `P` on real two-channel endomorphisms such that
   - `P(S_c T S_c^{-1}) <-> P(T)` for every `c>0` and every `T`, and
   - `P(B_x) <-> x=1` for every `x>0`.
4. `E_x(u,v)=a(x)^{-1}u^2+a(x)v^2` is positive definite and `B_x`-invariant for every `x>0`.
5. The neutral energy `E_0(u,v)=u^2+v^2` is `B_x`-invariant iff `x=1`.
6. The trivializing gauge tends to zero at the singular Borel boundary, so its inverse is unbounded there. Thus algebraic gauge triviality does not erase the singular domain/topology question.

Items 2–3 are the exact killing theorem. Items 4–6 are the strongest positive survivor: calibrated neutral geometry detects the wall, and the only carrier information not erased algebraically is its singular boundary class.

## Approach

Use the proved carrier formula and reciprocal law. Positivity makes every reciprocal cocycle an explicit square-root coboundary, giving global multiplication conjugacy as well as its two-channel diagonal form. The universal no-selector theorem follows already from the pair `x=1,2`: similarity invariance makes `P(B_1)` and `P(B_2)` equal, while wall selection makes them opposite. For neutrality, direct coefficient comparison reduces Euclidean invariance to `a(x)=1`; prove strict monotonicity of `x - x^{-1} - log x` on the positive ray.

## Paper proof `[PROVED HERE]`

Let `x>0`. The proved singular-carrier formula gives

`a(x)=x^{-1} exp(x-x^{-1})>0`.

Direct substitution gives

`a(x^{-1})=x exp(x^{-1}-x)`,

hence `a(x)a(x^{-1})=1`; in particular `a(1)=1`.

For `B_x(u,v)=(a(x)v,a(x)^{-1}u)`, a second application cancels the two reciprocal coefficients, so `B_x^2=I`. If `S_c(u,v)=(cu,v)`, then

`S_{a(x)} B_1 S_{a(x)}^{-1}(u,v)=(a(x)v,a(x)^{-1}u)=B_x`.

This proves item 1.

Put `g(x)=sqrt(a(x))`. Positivity gives `g(x)>0`. The reciprocal law and uniqueness of the positive square root give

`g(x^{-1})=sqrt(a(x)^{-1})=g(x)^{-1}`,

so `g(x)/g(x^{-1})=g(x)^2=a(x)`. For multiplication `(M_g f)(x)=g(x)f(x)` and bare reflection `(R_1 f)(x)=f(x^{-1})`, pointwise calculation gives

`(M_g R_1 M_g^{-1}f)(x)=g(x)g(x^{-1})^{-1}f(x^{-1})=a(x)f(x^{-1})=(R_a f)(x)`.

Thus the full positive-ray weighted reflection, not only each orbit matrix, is an explicit coboundary conjugate of bare reflection. This proves item 2.

For item 3, suppose a predicate `P` had both frozen properties. Wall selection at `x=1` yields `P(B_1)`. Since `a(2)>0`, rescaling invariance and the displayed conjugacy yield `P(B_2)`. Wall selection at `x=2` then yields `2=1`, contradiction. Therefore no such `P` exists.

For item 4, define

`E_x(u,v)=a(x)^{-1}u^2+a(x)v^2`.

Both coefficients are positive, so `E_x>=0`, with equality exactly at `(u,v)=(0,0)`. Moreover

`E_x(B_x(u,v))=a(x)^{-1}a(x)^2v^2+a(x)a(x)^{-2}u^2=E_x(u,v)`.

For item 5, neutral energy invariance implies, on `(u,v)=(0,1)`, that `a(x)^2=1`; positivity gives `a(x)=1`. Conversely `a(x)=1` makes `B_x` channel exchange and preserves neutral energy.

It remains to show `a(x)=1` iff `x=1`. Taking logarithms reduces this to

`F(x)=x-x^{-1}-log x=0`.

Certainly `F(1)=0`. If `x>1`, the strict logarithm inequality `log x < x-1` and `x-1 < x-x^{-1}` give `F(x)>0`. If `0<x<1`, then `x^{-1}>1` and direct substitution gives `F(x^{-1})=-F(x)`; the preceding case makes `F(x)<0`. Hence `F(x)=0` exactly at `x=1`, completing item 5.

Finally, the prior carrier theorem gives `A(y)->0` as `y->0+`; since `a(x)=A(x^2)` and square root is continuous, `g(x)->0` as `x->0+`. Therefore `g^{-1}` is unbounded on every punctured positive neighborhood of zero: for any `M>0`, choose `x` with `0<g(x)<M^{-1}`. This proves item 6 and shows precisely why the result is an algebraic/local sewing no-go, not a dismissal of singular operator domains.

All dependencies are the already Lean-proved singular-carrier formula/flat boundary limit plus elementary real algebra and logarithm monotonicity. No Xi divisor or RH-equivalent premise enters.

## Hostile audit

- **Internal corpus:** `OperationalHistorySimilarityGauge` proves generic finite-history similarity gauge; `CompleteHistoryInvariantMetricCone` classifies invariant metrics abstractly; `ThetaCuspHawkingBMRadiativeSourceFEPositiveHermitianMetricNoGo` proves an HB-specific positive-metric no-go. None proves that the exact singular PW multiplier is a global positive coboundary, applies that fact to the weighted reciprocal reflection, or gives the universal no wall-selector plus exact neutral survivor.
- **External parent theory:** Mostafazadeh's pseudo-Hermitian framework and Kleefeld's two-dimensional metric classification cover general positive metrics for non-Hermitian operators. They make a bare 2x2 metric classification non-novel, so SCG-1 is frozen at the stronger route-level universal gauge obstruction. Parikh--Wilczek and later tunnelling-correlation work do not contain this singular Gamma carrier. Akpinar--Aoki--Cristofoli--Jeong--Yoshimura (2026) obtain local detailed balance only after an additional spin-universality input, consistent with the survivor here.
- **Novelty label sought:** `[PROVED HERE] [PW-B ROUTE-CLASS NO-GO] [EXACT POSITIVE SURVIVOR]`; generic conjugacy algebra is prior art, exact carrier obstruction is the new bridge.

## No-go closure (mandatory)

- **Exact killing theorem/mechanism:** SCG-2(2–3): the exact singular reflection is a positive coboundary, and no positive channel-rescaling-invariant predicate can select the wall.
- **Strongest positive survivor:** SCG-2(4–6): positive conserved geometry exists at every scale; neutral calibration selects exactly `x=1`; trivializing gauge has an unbounded inverse at the singular boundary.
- **New insight:** singular FE reflection has no algebraic gauge-invariant balance content. A surviving PW-B dynamics must fix channel calibration or exploit a domain/connection sensitive to the Borel boundary; conservation, involutivity, spectrum, and existence of some positive metric are insufficient.
- **Status:** dependency-closed paper proof and Lean theorem `RHTower.pwSingularCarrier_rescalingGauge_noGo` in `ThetaCuspHawkingParikhWilczekSingularCarrierRescalingGaugeNoGo.lean`. Direct `lake env lean` and targeted module build pass. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Module is wired and reachable from `RHTower.lean`. Global lint reports unrelated pre-existing unreachable modules in the shared dirty worktree; it reports no forbidden proof token or reachability failure for this module.

## Log

- 2026-08-30 — created directly in Stage 1 after corpus-led conjecture loop rejected a routine 2x2 metric-classification claim and froze the universal similarity-gauge obstruction.
- 2026-08-30 — strengthened before proof to SCG-2 after the corpus similarity theorem exposed the global cocycle question; literature search found weighted-composition and cocycle parent theories but no exact PW singular-carrier coboundary/no-selector result.
- 2026-08-30 — SCG-2 proved on paper and promoted to Stage 2; Lean formalization begins only after this promotion.
- 2026-08-30 — formalized as `RHTower.pwSingularCarrier_rescalingGauge_noGo`; direct check and targeted build pass, closed axiom audit clean, umbrella wired. Promoted to Stage 3.
