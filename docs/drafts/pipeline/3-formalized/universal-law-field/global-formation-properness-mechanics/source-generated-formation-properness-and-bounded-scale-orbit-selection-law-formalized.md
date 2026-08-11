# Source-generated formation properness and bounded-scale selection — Lean certification

- **ID:** ULF-GFPM-1
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/global-formation-properness-mechanics/source-generated-formation-properness-and-bounded-scale-orbit-selection-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveGlobalFormationProperness`,
  `GaloisForLFunctions.HTGeometry.ConstitutiveGlobalFormationInformationProperness`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-FORMALIZED] [NO NEW AXIOMS] [GLOBAL SELECTION MECHANISM] [NOT RH]

## Certified mechanism

Lean certifies one mechanism, not a route receiver:

1. literal source depth dilation scales a marked temperature formation by `u ↦ d*u`;
2. existing source exchange generates the central fugacity formation;
3. the least-prime/least-depth mode is a canonical source reporter;
4. its exact log-odds work has a linear lower bound for every formation size `u ≥ 1`;
5. every positive source-scale orbit has work tending to `+∞`;
6. bounded work on the full scale orbit is equivalent to neutral formation;
7. any bounded global work which dominates this reporter also forces neutrality.
8. the actual convergent source class law pushes forward to the exact reporter Bernoulli law;
9. two-sided Kullback--Leibler data processing makes reporter work a lower bound for full source
   formation work;
10. a finite uniform bound on full source formation work along every scale is equivalent to neutral
    formation.

The last item is the conservation/selection interface. Work need not vanish. Uniform boundedness plus
source-generated scale amplification suffices.

## Certified declarations

| Law | Lean declaration |
|---|---|
| depth-scale covariance | `depthScale_tempTranslate` |
| equality with literal source depth dilation | `depthScale_eq_depthDilate` |
| canonical reporter | `leastMode`, `leastMode_ratio` |
| central-formation ratio transport | `leastMode_ratio_fugacityShift` |
| exact reporter work | `reporterWork` |
| nonnegative complement term | `log_complement_ratio_nonneg` |
| linear coercive lower bound | `reporterWork_linear_lower` |
| zero and strictness classification | `reporterWork_eq_zero_iff` |
| scale-orbit escape | `scaleOrbit_tendsto` |
| work properness | `reporterWork_scale_tendsto` |
| bounded-orbit selection | `boundedScaleWork_iff` |
| literal least-mode selection | `leastMode_boundedScaleWork_iff` |
| bounded global conservation selector | `bounded_dominating_work_selects` |
| fused source capstone | `globalFormationProperness_capstone` |
| class-law mode marginal | `classLaw_map_modeCoordinate` |
| class-law Bernoulli reporter pushforward | `classLaw_map_leastModeObserver` |
| exact Bernoulli KL formula | `toReal_klDiv_bernoulli` |
| Bernoulli Jeffreys/reporter identification | `bernoulliJeffreys_toReal_fugacityShift` |
| reporter dominated by full source work | `reporterJeffreys_le_fullFormationJeffreys` |
| bounded full-source work | `BoundedFullFormationWork` |
| full-source properness and selection | `boundedFullFormationWork_iff` |

The capstone combines scale covariance, the independently formalized source commutator
`AbelianZetaGas.commutator_socleTilt_tempTranslate`, and bounded-scale selection.

## Exact certification boundary

Lean now certifies the full information bridge, not only an abstract dominating-work interface. In
the convergence chamber, the actual source class law maps to the least-mode occupation Bernoulli
law. Exact Bernoulli Jeffreys work is the algebraic reporter work, and two applications of `klDiv`
data processing prove that reporter work is bounded above by full source Jeffreys work. The latter
is `ENNReal`-valued and may be infinite; boundedness means one finite `ENNReal` constant dominates
every source-generated scale. `boundedFullFormationWork_iff` proves that this happens exactly at
neutral formation.

Remaining boundary is constitutive, not measure-theoretic: no theorem here identifies a physical
off-centre divisor displacement with this source formation or proves the required finite uniform
bound from a pre-zero global law.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveGlobalFormationProperness.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveGlobalFormationInformationProperness.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
scripts/formal_tools.py lint
```

All pass. Umbrella build completed 11,825 jobs. Scratch `#print axioms` audits of the
reporter/scale and full-information capstones report only `propext`, `Classical.choice`, and
`Quot.sound`.

## RH-facing gate

No RH conclusion is formalized. Exact remaining gate is now two statements, neither a new route
analogy:

1. construct a pre-zero comparison sending the physical off-centre displacement to this generated
   formation parameter and intertwining depth dilation;
2. prove that the actual full source formation work has one finite scale-uniform bound.

Once both are Lean-certified, `boundedFullFormationWork_iff` forces neutral displacement.
