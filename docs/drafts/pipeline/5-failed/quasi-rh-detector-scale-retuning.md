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

## Joint Gram profile: sharp remaining requirements

Write `X=Z^x`, `Y=Z^(1−L−x)` and `P=Y/X`, ignoring arbitrarily small positive exponent losses. For a proposed Gram profile `1+P^ν+P^κ/Y`, put

`e = max(0, max(ν(1−L−2x), (κ−1)(1−L)−(2κ−1)x))`,

`B = 5/6+(x−L)/6+e/2+max(0,(6L−1)/5)/2`.

This retains the unit contribution, both other Gram contributions, the principal normalization, and the previously identified reflected allowance. It is a model of the displayed upper estimates, not a lower bound on actual energy.

Three dependency-closed algebraic conclusions follow:

1. **Unchanged nonexceptional term:** for `κ=2`, even after deleting the exceptional term, `B≥23/27`. Equality in the reduced profile occurs exactly at `L=1/6`, `x=5/18`, `y=5/9`. Indeed, set `a=x−(1−L)/3`. The reduced budget is
   `23/27+max(2(1/6−L)/9,17(L−1/6)/45)+max(a/6,−4a/3)`.
2. **Five-sixths feasibility:** for `ν≥0`, some `x≥0,L∈ℝ` gives `B≤5/6` exactly when `ν≤1/15` and `κ+4ν≤4/3`. To prove necessity, write `r=max(0,(6L−1)/5)` and `t=1−L`. The budget gives `x+3e+3r≤L`, hence `x+3e≤t/5` by combining `r≥0` and `5r≥6L−1`. It also gives `t>0`, `x≤t/5`, and `δ=t−2x>0`. Since `e≥νδ` and `e≥κδ−(t−x)`, one gets `15νδ≤δ` and `(κ+4ν)δ≤4δ/3`. Conversely choose `L=1/6` and `x=(1−15ν)/(6−36ν)`. The denominator is positive, `0≤x≤1/6`, and direct substitution gives the required budget from the two stated inequalities. The interior point `ν=1/30,κ=6/5,x=5/48,y=35/48` attains `5/6`.
3. **Three-quarters restriction:** for every `x≥0`, even replacing all nonunit Gram contributions by zero leaves `B≥29/36>3/4`. The unit budget equals
   `29/36+x/6+max((1/6−L)/6,13(L−1/6)/30)`.
   Its relaxed minimum is at `x=0,L=1/6`. Reaching `3/4` requires changing the reflected allowance, principal normalization, or unit contribution itself.

The five-sixths parameter region is an exact arithmetic-estimate target, not a provider of those estimates. Source inspection also shows that `sourceMobiusWeight` implements the coprimality restriction in `originalCommonBlock`; its signs alone do not justify a power saving in the exceptional-frequency sum.

Formal status: all three classifications, their exact decompositions, and the explicit interior witness are proved in [QuasiRHDetectorGramTradeoff.lean](../../../../formal/GaloisForLFunctions/RHTower/QuasiRHDetectorGramTradeoff.lean). Its focused `lake --old env lean` check passes without warnings; all 14 exported theorems use only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into `RHTower`. External novelty unclaimed.

## No-go closure

- **Exact killing mechanism:** scale redistribution leaves the signal-adjusted exponent invariant; slot extension exposes a zero-retained-length reflected configuration with a positive missing cost.
- **Strongest positive survivor:** exact five-sixths feasibility region for the three-term Gram profile; sharp reduced minima `23/27` with the nonexceptional term retained and `29/36` with only the unit term retained. The latter includes `x≥0`; its minimum at `x=0` is a relaxed scale boundary.
- **New insight:** five sixths requires simultaneous improvement of exceptional and nonexceptional contributions within this profile. Three quarters additionally requires changing the reflected allowance, principal normalization, or unit contribution. A sharper retained-kernel inequality cannot fix a witness whose retained length is zero. Möbius inversion encoding coprimality does not itself provide cancellation.
- **Scope:** the witness satisfies the listed exponent constraints; it is not asserted to be an actual arithmetic configuration. The result does not prove optimality of the true Gram energy, rule out additional source identities, or disprove a narrower strip.
- **Status:** paper proof above is closed. Formal module: [QuasiRHDetectorScaleBudget.lean](../../../../formal/GaloisForLFunctions/RHTower/QuasiRHDetectorScaleBudget.lean). Capstones: `zero_retained_length_witness`, `retunedBoundary_exact`, `retunedBoundary_sharp_minimum`, and `gram_power_saving_boundary`. Targeted `lake --old env lean` passed without warnings; all six theorem axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. This is an internal exponent audit; external novelty is uncertified.
