# Pre-divisor Wold-orbit completed-source conservation

- **ID:** P-G211
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Cross-corpus CCM/Gamma source polarization + Route-P Burnol colligation + Wold/Julia orbit
- **Statement:** The literal two-variable completed-source orbit current is a positive output
  channel of an independently defined primitive Euler colligation: before either Xi residue is
  taken, primitive Euler budget operator equals orbit-current operator plus Gram of explicit
  Gamma/polar/Wold defect channels. Hence every finite orbit current is Loewner-dominated by
  primitive Euler budget, and iterated residue plus prime-clock limit gives the existing literal
  `16/3 * ||c||^2` orbit bound.

## Goal

Prove requested source producer without assuming a Xi-side inequality. Conservation equality must
be source-derived and coefficient-faithful; Loewner order must follow because remainder is Gram of
actual independently defined defect channels. Combined with
`tendsto_frankensteinCCMGammaWoldRegularizedJuliaOrbitFirstLanding` and
`sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_lt_quantum`, theorem closes RH.

## Gates

- [x] 0 → 1 in-progress: exact source current, target operator order, residue landing, and hostile
  falsifiers fixed
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: unconditional Lean theorem, direct check, exact leaf build, axiom audit
- [ ] 3 → 4 publication-ready: standalone proof and external novelty audit

## Frozen objects and claim

Let `A_q(u)` and `B_q(v)` be the two independently holomorphic centered CCM/Gamma pole gauges in
`frankensteinCCMGammaSchwarzCenteredCubicSource`. Define the bilateral Julia orbit lift

```text
J(a,b) = B(a,b) + B(b,a) + B(-b,-a) + B(-a,-b),
B(a,b) = [[a*b,a],[b,1]].
```

Then `J(a,b)=diag(4ab,4)` identically, while successive selected source residues give
`a -> rho-1/2`, `b -> star(rho-1/2)`. Multiplication by finite Wold coefficient and Route-P
conormal normalization gives the already formalized finite literal orbit response and then
`16/3 * ||c||^2`.

Required new theorem is not a definition of remainder as `budget-current`. It must construct
source channels `D_k` independently from literal primitive Euler/Gamma/polar/Wold data and prove

```text
PrimitiveEulerBudgetOperator = WoldOrbitSourceOperator + sum_k Gram(D_k),
```

on the genuine source chamber, with analytic continuation compatible with both selected residue
maps. Consequently

```text
WoldOrbitSourceOperator <=_Loewner PrimitiveEulerBudgetOperator.
```

All prime/depth coefficients, analytic multiplicity normalization, Schwarz mate, two independent
pole variables, and four Julia orientations remain explicit.

## Hostile audit / pivot log

1. **Use four-shift Wold orbit-residue exactness as positive compensation.** Failed. Existing
   theorem says discarded shifts carry negative *signed orbit residue*. It gives no positive Gram
   energy and cannot pay a positive Julia corner.
2. **Use ordinary Burnol Hilbert colligation.** Insufficient by itself. It proves source Gram equals
   three positive channel Grams, but no existing channel has the completed Wold-orbit residue.
   Mixed primitive/Xi conormal Gram has a strict positive Schur residual, so target column is not
   one finite source atom or its Hilbert projection.
3. **Use post-Gamma coherent shorting.** Falsified by
   `routePPrimitiveGammaResolvedWoldPacket_not_trace_le_coherentNormSq`: coherent report is zero
   while hidden Gram trace is positive.
4. **Current live attack.** Build a pre-residue bilateral Julia dilation in an indefinite completed
   Gamma/polar carrier, then prove its positive physical corner is paid by an independently
   positive discarded-shift/defect Gram before Hilbert compression. If source construction merely
   names `budget-current`, imports a Xi-side order premise, or loses residue landing, reject it.

## Exact falsifiers

- Taking the two residues and prime-clock limit must recover
  `16/3 * ||c||^2`, not a damped or differently normalized current.
- Source budget trace must remain
  `sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c`.
- Since that budget is strictly smaller for `c != 0`, successful conservation eliminates every
  `XiRightZeroCopy`; any proof retaining such a copy is algebraically inconsistent.
- Global/equivariant completed-source positivity is blocked by corpus no-gos; valid theorem must be
  source-selected and non-equivariant while still preceding divisor residues.

## External status

Pending exact primary-literature audit. Generic conservative Julia colligations and Wold
decompositions are expected parents; coefficient-faithful completed prime--Gamma residue
compatibility and this four-orientation source identity are the novelty-bearing seam.

## Log

- 2026-08-18 — Stage-1 exact conservation conjecture frozen; first signed-orbit compensation
  attempt failed and pivoted to positive source-channel dilation.
