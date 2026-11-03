# Small aperture does not give iterated compact Hecke admission

- **Stage:** 5-failed
- **Rejected claim:** Some positive window length admits every smooth test to compact support under repeated actual Hecke action.
- **Obstruction [K]:** Every `A>0` contains a single smooth test whose first Hecke image has a finite upper cutoff and whose second image has none, simultaneously at every complex parameter.
- **Mechanism:** The first cusp samples the germ at `2`; the halving branch of that germ samples the original lift near `1`. Under logarithmic inversion this is the window's left germ at endpoint `0`. Smooth endpoint vanishing does not imply vanishing of the germ.
- **Positive survivor [K]:** For `A<log(4/3)`, finite upper support after two steps is equivalent to vanishing of `H` on some `(−ε,0)`. For an arbitrary input vanishing above `1≤R<4/3`, the corresponding exact condition is its left germ at `1`.
- **Paper proof and Lean:** [Second-step admission law](../3-formalized/f2-second-hecke-endpoint-admission.md); `MayerScattering/TheSecondHeckeStepSeesTheWindowEndpoint.lean`. Final individual check and standard-only transitive-axiom audits passed. Finite-energy cusp completions remain outside this compact-support obstruction.

**Additional positive survivor [K].** [Every finite word in the actual prime-two and prime-three Hecke operators preserves decaying finite-energy cusp admission](../3-formalized/f2-hecke-cusp-decay-carrier.md) for window lifts at every aperture when `Re s>0`. The paper proof and final Lean audit are complete. Compact-support failure therefore does not imply cusp-energy divergence.
