# HB Isolated Unit-Amplitude Covariance Interpolation No-Go

- **ID:** HB-IUACI
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` HB `ORIENT DYN` survivor; `ThetaCuspHawkingBMVacuumDifferentiableNonlinearEvolutionNoGo.lean`
- **Statement:** Every centered BM clock admits a coordinatewise degree-three nonlinear correction with the same vacuum first variation that is source-FE covariant on every unit Xi basis packet; isolated unit-amplitude covariance is therefore unconditional and cannot be an RH producer.

## Goal

Kill the exact finite-amplitude survivor of the vacuum-differentiation no-go. HB's RH chain needs full packet/amplitude-neighborhood source-FE covariance, which differentiates to the centered-clock law and hence RH. This claim proves that replacing it by covariance only on the universal unit basis is nonselective even when evolution is finite-support preserving and polynomial on every source axis.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `d4HBIsolatedUnitAmplitudeNonlinearEvolutionRouteKilled`, targeted `lake build` green, axiom audit passes
- [ ] 3 → 4  publication-ready: standalone paper

## Exact conjecture and RH proof chain

Let `R` be Xi FE reflection, `c_q` the nowhere-zero source cocycle, `m_q` the centered-QNM finite-clock multiplier, and `T` the anti-linear packet transport, so `T(e_q)=c_q e_{Rq}`. Define

`K_q = 0` if `c_{Rq}=1`, and otherwise

`K_q = (conj(m_{Rq})-m_q)/(c_{Rq}(c_{Rq}-1))`.

For a finite packet `x`, define coordinatewise

`E(x)_q = m_q x_q + x_q^2 (x_q-1) K_q`.

Conjecture: `E` is finite-support preserving, its real-amplitude vacuum first variation is the centered BM clock, and

`T(E(e_q)) = E(T(e_q))`

for every Xi copy `q`, unconditionally. Yet full covariance of any evolution with this first variation forces RH by the existing vacuum-differentiation and finite-clock classifications. Thus unit-basis-only covariance cannot close HB; a producer must control an accumulating amplitude family/full packet law or leave vacuum differentiability/literal source transport.

## Paper proof candidate

`x_q^2(x_q-1)` vanishes at both vacuum to second order and at the unit input. Hence `E(e_q)=m_q e_q`, and dividing `E(a x)` by nonzero real `a` leaves the clock plus a correction proportional to `a x_q^2(a x_q-1)`, which tends to zero.

At the transported input, `T(e_q)=c_q e_{Rq}`. If `c_q != 1`, reflection of the definition gives

`K_{Rq}=(conj(m_q)-m_{Rq})/(c_q(c_q-1))`,

so the correction at amplitude `c_q` is exactly

`c_q^2(c_q-1)K_{Rq}=c_q(conj(m_q)-m_{Rq})`.

Therefore `E(T(e_q))=c_q conj(m_q)e_{Rq}=T(E(e_q))`. If `c_q=1`, its norm square is one, the corpus cocycle orientation theorem puts `q` on the critical line, and the existing finite-clock single-packet theorem gives the same equality with zero correction. No open mathematical dependency remains if these identities elaborate exactly.

## Hostile audit

- `[CORPUS]` Full nonlinear covariance plus this vacuum first variation forces the linear BM clock covariance and RH; no corpus theorem treats only universal unit-basis inputs.
- `[LITERATURE]` Whitney/Borel jet interpolation supplies broad parent theory, while nonlinear Teukolsky literature constructs perturbative sources and quadratic QNMs; no located result couples finite-value interpolation to the Birmingham–Mokhtari Xi source cocycle or this RH route.
- **Verdict:** `SURVIVES PRELIMINARY ATTACK` as a route-kill. The interpolation mechanism alone is a bridge; significance is the sharp HB boundary it proves.

## No-go closure

- **Exact killing theorem/mechanism:** `[LEAN-PROVED]` `d4HBIsolatedUnitAmplitudeNonlinearEvolutionRouteKilled`; explicit polynomial interpolant exists for every clock and time.
- **Strongest positive survivor:** amplitude-neighborhood/full-packet covariance remains RH-strength; isolated unit-basis covariance is freely interpolable without changing the vacuum jet.
- **New insight:** regularity at vacuum is insufficient unless covariance itself persists to vacuum; polynomial dynamics can retain the correct jet while fitting every isolated unit source.
- **Status:** exact theorem in `ThetaCuspHawkingBMIsolatedUnitAmplitudeCovarianceInterpolationNoGo.lean`; direct check and targeted build pass; axioms only `propext`, `Classical.choice`, `Quot.sound`.

## Log

- 2026-08-31 — frozen after internal corpus and current primary-literature audit.
- 2026-08-31 — `[PAPER-PROVED]`; promoted after hostile proof review.
- 2026-08-31 — `[LEAN-PROVED]`; targeted module build and axiom audit passed.
