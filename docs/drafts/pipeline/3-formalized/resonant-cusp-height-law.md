# Exact height law and cusp escape of normalized resonant states

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [arithmetic measure rigidity](../1-in-progress/resonant-state-arithmetic-measure-rigidity.md).

## Statement

Let `u` be an actual resonance: `u∈eisensteinLineDomain`, `Re u<0`, and `msA u=0`.
Put `κ=-2 Re u∈(0,1)`, `B=msB u`, and `τ_Y=Λ^Y E_u`. The Maass–Selberg norm is
`N_Y=|B|²Y^κ/κ`. For `Y≥1`, let `ν_Y` be the height pushforward of
`|τ_Y|² dμ/N_Y` on the modular fundamental domain.

The exact equality of probability measures is

`ν_Y = Y^(-κ) ν_1 + κ Y^(-κ) 1_(1,Y](y) y^(κ-1) dy`.

The measure `P_κ(dt)=κ 1_(0,1](t)t^(κ-1)dt` is a probability for every `κ>0`.
For every bounded measurable real `f` with `|f|≤M`,

`|∫ f(y/Y) dν_Y − ∫ f(t) dP_κ| ≤ 2 M Y^(-κ)`.

For `1≤C≤Y`,

`ν_Y((0,C]) ≤ (C/Y)^κ`.

More generally, if `κ≥ε>0` and `C,Y≥1`, then
`ν_Y((0,C]) ≤ (C/Y)^ε`. Consequently, for any sequence of actual resonances
with `κ_n≥ε>0` and any `Y_n→∞`, the normalized mass at each fixed height
`(0,C]` tends to zero. Every estimate is independent of spectral ordinate.

## Proof

The cutoff difference `τ_Y−τ_1` is the constant Fourier mode
`B y^(1/2-u)` on `(1,Y]`, and zero elsewhere. The cutoff-one state has zero
constant mode there. Complete horocycles therefore cancel the cross term
against every bounded continuous height test. Integration in the horizontal
variable gives the added height density `|B|²y^(κ-1)dy`.

Both height-energy measures and the power-band measure are finite. Equality
of their integrals against bounded Lipschitz tests gives equality of Borel
measures, hence the identity applies to all bounded measurable tests.
Nonvanishing of `B` and the exact Maass–Selberg norm justify normalization
and prove that `ν_Y` has total mass one.

After the substitution `t=y/Y`, the explicit band becomes `P_κ` restricted
to `(1/Y,1]`. The omitted power-law tail and the remaining cutoff-one
component each have mass `Y^(-κ)`. Bounding both test integrals by their
mass times `M` gives the error bound.

For `1≤C≤Y`, the mixture puts at most `Y^(-κ)` from its cutoff-one component
below `C`; its explicit band contributes `Y^(-κ)(C^κ−1)`. Their sum is
`(C/Y)^κ`. If `κ≥ε`, monotonicity of powers on `(0,1]` gives the uniform
bound. When `Y<C`, probability mass is at most one, which is at most
`(C/Y)^ε`. Since `(C/Y_n)^ε→0`, the escape assertion follows.

## Lean certificates

Modules: `RenormalizedIntersectionTheory/ResonantStates/`.

| Module | Main declarations |
|---|---|
| `HeightCutoffEnergy` | `height_weighted_energy_increment`, `resonant_height_weighted_energy` |
| `HeightProbabilityLaw` | `resonant_heightEnergyMeasure`, `heightProbabilityMeasure_probability`, `resonant_heightProbabilityMeasure` |
| `HeightScalingLimit` | `powerHeightProbabilityMeasure_probability`, `resonant_rescaled_height_error`, `resonant_height_local_mass`, `resonant_height_escape_bound`, `resonant_height_mass_tendsto_zero` |

All three source modules pass direct `lake --old env lean` checks. Main
certificates depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Mathematical boundary

The rescaled height law is positive for every negative resonant rate and
retains that rate explicitly. Increasing truncation height produces escape,
not a tight finite measure on the original surface. Neither the power-law
classification nor this escape estimate selects the critical rate or proves
Hecke recurrence, positive entropy, or microlocal rigidity.
