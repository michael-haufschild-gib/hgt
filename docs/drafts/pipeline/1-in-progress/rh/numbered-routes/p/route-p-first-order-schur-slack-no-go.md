# Route-P first-order Schur slack no-go

- **ID:** P-G162
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean); producer no-go with positive survivor
- **Source:** Route P, P-G160 curvature toll + P-G161 graph-normal tangent + Xi Julia defect law
- **Lean:** `RHTower/RoutePFirstOrderSlackNoGo.lean`
- **Statement:** if RH fails, then at all sufficiently small positive apertures the unconditional
  Julia defect strictly exceeds the exact quadratic graph-normal mass toll.

## Goal

Test whether ordinary finite-aperture Schur contractivity can supply P-G160's missing tangent-block
positivity.  Compare actual contractivity slack with exact curvature demanded by P-G161 mass mode,
without assuming boundary saturation or RH.

## Gates

- [x] 0 → 1 in-progress: precise source/target quantities and hostile falsifier identified
- [x] 1 → 2 fully-proven: derivative comparison and explicit small-aperture proof complete
- [ ] 2 → 3 formalized: scratch Lean check passed; umbrella wired; axiom/lint audit pending
- [ ] 3 → 4 publication-ready: external novelty and exposition audit

## Conjecture loop

### P-G162a — finite-aperture contractivity pays the tangent toll

Let

```text
r = continuedXiAntiCausalWardResponse(1/2),
D(a) = 1-|Phi_(1/2)(a)|^2,
T(a) = |a r|^2.
```

P-G160.5 says `T(a)` is exactly the extra bottom curvature required by mass coefficient `a r`.
The existing infinitesimal Julia law says

```text
D(0)=0,             D'(0)=2 Re r.                       (P-G162.1)
```

The conjecture was that unconditional `D(a)>=0` might be the missing source of this curvature.

### Proof/failure

Under `¬RH`, P-G161 proves `Re r>0`.  The right derivative in `(P-G162.1)` gives

```text
D(a)/a -> 2 Re r                                    as a -> 0+.
```

Choose

```text
delta = Re r/(|r|^2+1)>0.
```

For all sufficiently small `0<a<delta`, derivative convergence gives

```text
D(a)>a Re r,
```

while the explicit choice of `delta` gives

```text
a^2 |r|^2 < a Re r.
```

Therefore

```text
T(a)=a^2|r|^2 < D(a).                                  (P-G162.2)
```

The conjecture is **FALSIFIED**: Schur contractivity has more than enough slack to hide the
off-line mass mode when RH fails.  It cannot force `r=0`.

## No-go closure

- **Exact killing theorem/mechanism:** Julia defect opens linearly with coefficient `2 Re r`,
  whereas P-G160 mass-curvature toll is quadratic in aperture.
- **Strongest positive survivor:** unconditional closed implication `(P-G162.2)`, formalized as
  `eventually_xiWardCriticalMassCurvatureToll_lt_boundaryPhaseDefect_of_not_rh`.
- **New insight:** missing producer is not generic contractivity or positive curvature.  It must
  cancel the complete first-order Julia loss, leaving a genuinely saturated second variation on
  which P-G160 rigidity can act.
- **Status:** paper proof dependency-closed; Lean scratch check passes; module umbrella-wired.

## Higher principle

P-G160--P-G162 expose an order mismatch.  Graph-normal arithmetic information lives in a
second-order curvature toll, while ordinary Schur positivity records first-order dissipation.
Every earlier attempt to pass directly from contractivity to the four-unit tangent block stalled
because it compared different jets.  A successful Route-P construction must be conservative to
first order on the source-selected causal channel and place the anti-causal Ward response in the
orthogonal second derivative.  This is exactly the structural role of block-unitary Ward
decomposition, but the required arithmetic unitary incidence and graph domain remain open.

## Novelty audit

- First variation of Julia defect and positivity of `Re r` are prior corpus theorems.
- Exact quadratic mass toll is P-G160.
- Corpus search found no prior theorem comparing these quantities or proving eventual strict
  domination `(P-G162.2)`.
- Novel content is their sharp jet-order synthesis and resulting exclusion of generic
  finite-aperture contractivity as Route-P producer.

## Exact next producer

Construct a source-derived, pre-divisor Gamma/Sonin incidence whose causal block is first-order
isometric at aperture zero and whose anti-causal derivative is the P-G161 rank-one tangent.  Then
apply the exact block-unitary second-variation identity.  Hostile test: any candidate with positive
first derivative of its norm defect falls under `(P-G162.2)` and cannot prove RH.

## Log

- 2026-08-14 — conjecture posed from P-G160.5/P-G161 order comparison.
- 2026-08-14 — conjecture falsified; exact eventual strict inequality proved in Lean scratch.
- 2026-08-14 — module wired into `RHTower` umbrella; RH remains open.
