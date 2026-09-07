# EDQ complete reflected logarithmic response

- **ID:** EDQ-FRR
- **Stage:** 3-formalized
- **Type:** THEOREM; paper proof and Lean audited
- **Source:** [frontier](../1-in-progress/rh-current-frontier-map.md), [incoming response](edq-incoming-reflection-response.md)

## Full chain

Euler deletion → complete reflected arithmetic remainder balance → signed comparison of the full logarithmic source → off-line-zero exclusion → RH. The incoming response alone leaves the complementary Fourier sectors; this component assembles their exact first response before making a signed comparison.

## Complete source and response

At unit anchor define the literal centered Fourier source

`F(s)=integral_(1,infinity) (bernoulliPeriodic(x)+1/12)*x^(-conj(s)-2) dx`.

Its actual critical logarithmic response is

`L_full(t)=integral_(1,infinity) (bernoulliPeriodic(x)+1/12)*x^(-5/2)*log(x)*exp(i*t*log(x)) dx`.

Absolute coefficient mass `1/12` and the exact first logarithmic moment `4/9` give absolute summability of all response modes and `norm(L_full)<=1/27`. The full sum–integral interchange is proved with the logarithmic factor retained. The literal Fourier source equals `g(s,1)+1/(12*(conj(s)+1))` in the strip.

For `delta=Re(s)-1/2`, `0<=Re(s)<=1`, all heights:

`norm(F(s)-F(1-conj(s))+2*delta*L_full(t))<=abs(delta)^3/6`.

The bound follows by summing the previously proved pointwise cubic residual over every integer mode and integrating its exact third logarithmic moment. For nonzero displacement the divided difference differs from `-L_full` by at most `delta^2/12`.

For any finite incoming cutoff, subtracting the exact incoming response retains the actual complementary source `F-H`, whose response is `L_full-L_in`. Triangle inequality gives cubic error at most `abs(delta)^3/4`. This is a complete retained comparison, without claiming an advantageous sign for either component.

## Zero constraint

At a strip zero away from the line, the previous exact reflected balance forces

`abs(Im(L_full(t))+t*(1/C-1/(4*A*B)))<=delta^2/12`,

where `C=normSq(conj(s)*(1-conj(s)))`, `A=normSq(s+1)`, `B=normSq(2-s)`. The rational term has known positive sign at positive height, but the signed logarithmic source remains uncontrolled. This necessary constraint is not an unconditional zero exclusion or an RH proof. Any claimed exclusion must prove a strict opposing source estimate.

The complete complex condition retains the real zero equation as well. With

`V(s)=i*t/C-1/[12*(conj(s)+1)*(2-s)]`,

the exact zero balance is `F(s)-F(1-conj(s))=2*delta*V(s)` and hence

`norm(L_full(t)+V(s))<=delta^2/12`.

The second mean factor is `2-s`, so both mean denominators have imaginary part `-t`. This condition keeps the simultaneous real and imaginary constraints. The norm estimate retains both components together; no strict source comparison contradicting it has been proved.

## Lean inventory and audit

Leaf: `GaloisForLFunctions.RHTower.ArithmeticFullReflectionResponse`, namespace `RHTower.DeletionMixedRefinement`. 276 lines, 15 theorems and three definitions.

- `unitFullFourierSource`, `criticalFullLogAtom`, `criticalFullLogResponse`: literal full source and logarithmic response.
- `hasSum_unitFullFourierSource`, `unitFullFourierSource_eq_remainder`: all-mode reconstruction with the exact mean.
- `criticalIncomingLogMode_eq_fourier`, `integral_norm_criticalIncomingLogMode`, `hasSum_criticalFullLogResponse`, `norm_criticalFullLogAtom_le`, `norm_criticalFullLogResponse_le`: retained Fourier characters, absolute logarithmic mass, legitimate interchange, and the complete norm bound.
- `norm_fullFourierAtom_reflection_response_le`, `norm_unitFullFourierSource_reflection_response_le`, `norm_unitFullFourierSource_divided_reflection_response_le`: complete half-line mode, all-mode cubic estimate, and divided quadratic estimate.
- `norm_complementaryFourierSource_reflection_response_le`: full retained complement after any finite incoming head.
- `unitFullFourierSource_reflection_im_at_zero`, `abs_criticalFullLogResponse_zero_constraint`: exact projected balance and necessary inequality.
- `unitFullFourierSource_reflection_at_zero`, `norm_criticalFullLogResponse_zero_constraint`: full complex balance and simultaneous zero-constraint disk.

Foreground scratch passed; its sole stylistic warning was removed before final audit. `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticFullReflectionResponse` built only the new leaf in 3.9 seconds with cached dependencies. The umbrella import is wired; no umbrella or full build ran. Formal lint found ten unrelated unwired `HTGeometry.PolynomialODEOddCompact*` modules (`Cubic`, `Model`, `Remainder0` through `Remainder6`, and `SourceJets`), and no issue in this leaf. Those concurrent files were left untouched; global lint is not clean.

All 18 new declarations were audited once, with only `propext`, `Classical.choice`, and `Quot.sound`. No existing declaration was re-audited. The corpus index was refreshed. All owned Lean processes exited, and the three temporary Lean sources were removed. No numerical experiment or computational certificate was used. Logs: `/tmp/edq_full_response.check.log`, `/tmp/edq_full_response_{build,axioms,lint,index}.log`.

## Gates

- [x] Corpus research and exact source inspection.
- [x] Full logarithmic source reconstruction and mass bound.
- [x] Full and complementary cubic response, divided response, complete imaginary and complex zero constraints.
- [x] Foreground scratch, leaf wiring, targeted build, new-only axioms, lint run, both ledgers, index, cleanup.
- [ ] Global lint clean: ten unrelated concurrent modules remain unwired.
- [ ] Signed arithmetic exclusion for all off-line zeros; RH.
