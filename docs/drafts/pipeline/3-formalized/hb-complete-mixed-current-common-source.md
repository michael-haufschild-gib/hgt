# HB: complete mixed Einstein current and common physical source operator

Status: four unconditional pointwise identities formalized. Complete physical pairing, fixed Hawking-clock extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Positive results

The original mixed Einstein action supplies all four current components, including the temporal curvature term and both angular curl terms. Their exact stream reconstruction retains the full original master and its angular action. Both literal theta source branches are produced by one radial differential operator with the common scalar eigenvalue `lambda=rho(rho-1)`. The original smooth onset and the actual half-square Laplacian remain in the identity.

These results address the SV–SV cancellation coefficient by putting every boundary direction and both original source branches into explicit formulas. They do not supply the SS/VV response fields or the integrated cancellation.

## Exact Lean scope

`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedRadialActionCurrent`:

- `RHTower.D4BMMixedActionCurrent.mixed_complete_action_current`: actual volume-weighted Einstein action variation at every original exterior point equals `completeCurrentDensity` in all four coordinate directions. The mixed metric entries and first jets are free; no field equation or boundary condition is assumed.
- `RHTower.D4BMMixedActionCurrent.stream_complete_action_current`: substituting `streamMetricJet` gives the full `streamCurrentDensity`, with `streamAngularAction` and `streamMasterValue` retained. This evaluates reconstructed metric jets; it does not assert that arbitrary covector jets satisfy the coexact field equation.

`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCommonRadialSource`:

- `RHTower.D4BMCommonRadialSource.timeOriginalForcing_common_source`: for every actual Xi copy, either branch, original angular point and exterior tortoise coordinate, `timeOriginalForcing` equals `-2(1-u²)u commonSource`. Its two seed inputs contain the actual theta half-square and its actual Laplacian. All source and radial differentiation facts are discharged internally.
- `RHTower.D4BMCommonRadialSource.commonSource_differential_form`: the same operator in ordinary radial derivative form, with no differentiation or division of the fixed onset.

In compact radius `u=-tanh x`, the common source operator is

```
P_lambda=(5lambda-6)/4
 +u²/8[(lambda-2)(4lambda-4-Delta)
       -(1+u)(7lambda-2-2Delta)partial_u].
```

Its actual ingoing seeds are `a² chi(v)exp(2sv)(1+u)^(2s)Q`, where the two rates are `s` and `-s-3`. The proof uses the actual radial derivative and the already established full-square Laplacian identity. It does not replace `Delta Q` by an eigenvalue multiple of `Q`.

## Cancellation work exposed by these identities

The [complete-current derivation](../1-in-progress/hb-mixed-complete-current.md) gives a paper proof of the source-contact transgression

```
div(omega+C)=[S_Psi dot A Phi-S_Phi dot A Psi]/r⁴,
A=roughLaplacian-1, S=M Psi.
```

It also derives the common producer's formal transpose in the original master's radial measure, its radial boundary density, and the precise conversion from the scalar wave source to `S=2 coexact(P_lambda F)`. These differentiated, integrated and inverse-transport statements are analytical. The four Lean theorems above do not formalize those statements.

The remaining direct target is the actual source pairing through the retarded-minus-advanced master inverse, retaining the temporal, horizon, AdS and cusp boundary terms. The common producer alone supplies no vanishing theorem. All independent polarization coefficients remain required.

## Validation

Both sources passed foreground `lake env lean` scratch checks without Lean warnings. Final audits used only `lake build` on the two exact modules, sequentially, with 3988 existing own-corpus import artifacts frozen. The mixed-current leaf completed in 23 seconds and the common-source leaf in 17 seconds; each build reported two jobs. No old dependency, full or umbrella build ran.

The installed sources and olean/ilean files are byte-identical to the audited artifacts. The original current import remains wired; the new common-source module is wired into RHTower without building the umbrella. Only the four newly created public theorems were axiom-audited; each reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

Index refresh and scoped whitespace checks passed. Whole-corpus static lint reported two unwired modules from concurrent work, `SelbergMaassDilationStress` and `SelbergModularCurrentGreen`; it reported no error in these HB leaves. Those unrelated files and imports were left to their active work. No mathematical computation was used. All owned Lean/Lake processes exited; the owned scratch and frozen-cache audit directory were removed.
