# Retuning the seven-eighths detector without stronger arithmetic estimates

- **ID:** quasi-rh-detector-scale-retuning
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** [Active fixed-strip research](../1-in-progress/quasi-rh-fixed-strip-improvement.md)
- **Statement:** Lower the detector boundary solely by redistributing its two low scales or increasing total prime-slot length, while retaining the displayed Gram and reflected-energy exponent estimates.

## Goal

Determine whether the numerical slack in the upstream parameter choices already permits a strict improvement below `7/8`. This card retires only the stated exponent-budget retuning; the actual arithmetic estimates and the larger quasi-RH task remain open.

## Gates

- [x] Exact source formulas and parameter changes identified.
- [x] Dependency-closed paper proof of the obstruction and positive survivor.
- [x] Positive survivor formalized; targeted foreground leaf and axiom audits passed.
- [ ] External novelty and publication audit. No external search is authorized.

## Approach and paper proof

The Gram exponent is `(5x+y)/12`; the principal shift is `x/3−5/6+L/6`. Their difference is `(x+y)/12+5/6−L/6`, so redistributing x and y with sum `5/6` and `L=1/6` preserves `7/8` exactly.

For total scales `p=1−L`, the nominal boundary is `11/12−L/4`. At `L=1/6+h`, `0<h≤5/6`, choose

`d=1/6−h/5`, `H=1/2−3h/5`, `z=ell0=6h/5`,

and set every other cost variable to zero. Then `d≥0`, `d≤1/6`, `H≥0`, `z=L−d`, and `H=p−2d`. The retained length `T=2H+z−1` is zero. Both the hybrid saving and the retained-kernel saving vanish, so the reflected exponent is `H+z`, exceeding the target `p−2d` by `6h/5`.

Thus the proposed extension of those exponent inequalities is false. Paying this face adds at least `max(0,(6L−1)/5)` to the energy exponent, hence half that amount after taking the square root. The resulting budget is

`B(L)=11/12−L/4+max(0,(6L−1)/5)/2`.

It equals `7/8+(1/6−L)/4` for `L≤1/6`, and `7/8+7(L−1/6)/20` for `L≥1/6`. Therefore its unique minimum is `7/8` at `L=1/6`.

## No-go closure

- **Exact killing mechanism:** scale redistribution leaves the signal-adjusted exponent invariant; slot extension exposes a zero-retained-length reflected configuration with a positive missing cost.
- **Strongest positive survivor:** the exact piecewise cost law and unique minimum of B(L), plus the sensitivity law `Gram power 1/6−u → nominal boundary 7/8−u/16` at the original scales.
- **New insight:** the low exceptional-frequency term, rather than slack in the high-row parameter budget, needs a stronger arithmetic estimate. A sharper intermediate retained-kernel inequality cannot fix a witness whose retained length is zero.
- **Scope:** the witness satisfies the listed exponent constraints; it is not asserted to be an actual arithmetic configuration. The result does not prove optimality of the true Gram energy, rule out additional source identities, or disprove a narrower strip.
- **Status:** paper proof above is closed. Formal module: [QuasiRHDetectorScaleBudget.lean](../../../../formal/GaloisForLFunctions/RHTower/QuasiRHDetectorScaleBudget.lean). Capstones: `zero_retained_length_witness`, `retunedBoundary_exact`, `retunedBoundary_sharp_minimum`, and `gram_power_saving_boundary`. Targeted `lake --old env lean` passed without warnings; all six theorem axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. This is an internal exponent audit; external novelty is uncertified.
