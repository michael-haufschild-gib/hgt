# Route L energy-graph saturation

- **ID:** L-ENERGY-GRAPH-SATURATION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **RH proved:** no
- **Source:** [source-selected completion attack](../1-in-progress/route-l-source-selected-completion-attack.md)

## Exact theorem

Let `D` be the actual finite Big-Witt edge-packet space, `i : D → X` its admission into the completed one-leg source, and `E_A` the linear reporter with coefficient `A/p` at each left-prime label. In the Hilbert product `X × ℂ`,

`closure { (i(d), E_A(d)) : d ∈ D } = X × ℂ ↔ A ≠ 0`.

At a Xi copy, substitute the existing Gamma-six Wold–Jordan weight. Full saturation then holds exactly off the critical line. This is an unconditional classification; it asserts neither existence nor absence of an off-line Xi copy.

## Proof

A joint annihilator `(x,y)` with `y≠0` expresses `E_A` as a bounded linear functional of `i(d)`. On the actual normalized fixed-prime rows this supplies the descent already proved equivalent to `A=0`. Thus for `A≠0`, `y=0`; density of the admitted finite packets forces `x=0`. The corpus Hilbert graph-saturation theorem gives the full product. At `A=0`, the graph and its closure lie in the closed kernel of the energy projection, excluding `(0,1)`.

## Meaning and limits

The enlarged graph admits every scalar output above every source vector when its coefficient is nonzero. It makes the energy projection continuous by adding an independent completed coordinate; it supplies no selection of the fixed physical value. Minimizing squared output norm in these fibres chooses zero for every source input and does not preserve the original finite reporter.

This closes the proposed unrestricted linear energy-graph completion as a source of physical annihilation. It does not exclude a source-derived restriction before completion, another topology, or a new arithmetic identity. Full-product saturation is not asserted for the positive cone.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/XiGammaSixWoldJordanEnergyGraphSaturation.lean`.
- Exact source classifier: `RHTower.HedenmalmThetaSource.deningerBigWittPrimeEnergyGraph_closure_eq_top_iff`.
- Xi classifier: `RHTower.HedenmalmThetaSource.xiGammaSixWoldJordanEnergyGraph_closure_eq_top_iff`.
- `lake env lean /tmp/route_l_graph_attack.lean`: passed, no warnings.
- Both classifier axiom audits: `propext`, `Classical.choice`, `Quot.sound` only.
- Scoped `lake build GaloisForLFunctions.RHTower.XiGammaSixWoldJordanEnergyGraphSaturation`: passed; dependency warnings were replayed. Only the new module compiled.
- `scripts/formal_tools.py lint`: passed, with existing large-file warnings.
- RHTower umbrella import added; no umbrella or full build run.
- No numerical experiments, `native_decide`, added axioms, or unproved declarations.
