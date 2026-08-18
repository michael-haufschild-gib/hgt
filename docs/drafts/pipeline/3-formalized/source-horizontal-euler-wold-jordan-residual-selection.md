# Source-horizontal Euler--Wold Jordan residual selection

- **ID:** `source-horizontal-euler-wold-jordan-residual-selection`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Status:** `[FORMALIZED] [AXIOM-AUDITED] [LITERATURE-ALIGNED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Source:** `source-horizontal-euler-wold-independent-krein-xi-residue-transport`
- **Statement:** Apply the canonical Jordan negative/positive-part operation to the intrinsic
  Euler/Wold source-jet grades before physical grade-forgetting; the negative part retains the full
  order-one Euler action, the positive part retains the Wold regulator, and their subsequent linear
  compression is exactly the already-proved vanishing defect.

## Goal

Close the nonlinear/non-spectral physical-selection wall without an operator spectral projection,
an arbitrary scalar, or deletion of the Wold leg. The selector must be canonical on signed source
data, reconstruct the complete current from its two selected parts, preserve prime labels, Euler
depth multiplicity `k^2`, four orientations, actual Xi multiplicity, and the BV endpoint component,
and transport the pre-Xi primitive-budget theorem to the selected Gamma/polar landing.

## Literature frontier

- `[LITERATURE]` Hahn--Jordan decomposition is the unique minimal mutually-singular positive/negative
  decomposition of a finite signed measure. The corpus already formalizes the exact measure theorem
  as `HTGeometry.totalVariation_toSignedMeasure_sub` in
  `HTGeometry/MutuallySingularTotalVariation.lean`.
- `[LITERATURE]` Ali--Silvey's Radon--Nikodym divergence class and Csiszar's indirect-observation
  theory place total variation inside the convex divergences contracted by observation/compression:
  [Ali--Silvey 1966](https://doi.org/10.1111/j.2517-6161.1966.tb00626.x),
  [Csiszar 1967](https://real.mtak.hu/196543/).
- `[LITERATURE]` Current BV work makes the residual-data point categorical: BV pushforward is a
  quasi-isomorphism only together with a strong deformation retract and a quasi-inverse retaining
  effective/residual observables
  ([Cattaneo--Mnev 2026](https://arxiv.org/abs/2605.30558)). BV--BFV similarly retains boundary
  fields rather than quotienting them before physical reduction
  ([Cattaneo--Mnev--Reshetikhin 2014](https://arxiv.org/abs/1201.0290)). Neither paper supplies an
  arithmetic Xi selector or the Euler/Wold source grading.
- Bounded searches found no primary source applying source-grade Jordan selection to the completed
  Euler/Wold Xi residue. Priority remains `[NOVELTY UNVERIFIED]`.

## Internal frontier

- `[CORPUS]` `iteratedDeriv_sourceHorizontalEulerWoldBigradedCompletedSource_euler` and `_wold`
  identify the two pure source jets before Gamma selection.
- `[CORPUS]` `_mixed_zero` proves their intrinsic `(3,0)` and `(0,3)` independence, so the grade is
  not an external tag.
- `[CORPUS]` `sourceHorizontalEulerWoldIndependentKreinXiResidueTransport` carries both grades,
  four orientations, actual Xi multiplicity, and the unchanged BV endpoint through the same two
  completed residues.
- `[CORPUS]` linear grade-forgetting is exactly `-2 D_N/H_N^3 O(c) -> 0`.
- `[CORPUS]` `eventually_sourceHorizontalWoldBVKreinEulerGammaCubicCompensatedEnergy_lt_sourceBudget`
  proves the untransported negative Euler action enters the literal primitive budget cofinally.

## Heavy-conjecture loop

### C0 -- Jordan selection after physical compression

Take the positive and negative parts of the scalar `W_N-G_N` after the grades are added.

**Verdict:** `[FALSIFIED]`. The compressed current is `-D_N`; its total variation is `D_N`, hence
vanishes after cubic normalization. Nonlinearity after information loss cannot recover Euler mass.

### C1 -- operator positive/negative part after matrix transport

Apply Loewner/spectral positive and negative parts to the landed matrix.

**Verdict:** `[FALSIFIED]` for the requested mechanism. It is spectral, occurs after the common
orientation block has merged the source grades, and falls under the corpus's ordinary
Loewner-continuous descent firewalls.

### C2 -- intrinsic source-grade Jordan selection before compression

For `0 <= n <= N`, use the source atom space
`Euler(n) | Wold(n)` and signed density

```text
j_N(Euler n) = -2 G_(p_n)/H_N^3,
j_N(Wold n)  =  2 W_(p_n)/H_N^3.
```

Take pointwise Jordan parts `j+ = max(j,0)` and `j- = max(-j,0)` before multiplying by the common
four-orientation block or forgetting the source grade.

**Verdict:** `[PAPER-PROVED]`. Positivity fixes the parts uniquely;
`j-` is exactly Euler and `j+` exactly Wold. The pair reconstructs `j`, so regulator data is not
discarded. The operation is nonlinear on general signed densities and uses only scalar source
order, not an operator spectrum.

## Frozen conjecture

Let `E_N=G_N/H_N^3`, `W_N=Wold_N/H_N^3` and `O(c)` be the literal four-orientation block. Then:

1. Jordan masses are `J_N^- = 2 E_N` and `J_N^+ = 2 W_N`.
2. Selected physical action is `P_N(c)=-J_N^- O(c)`, exactly the completed Euler landing.
3. Retained regulator is `R_N(c)=J_N^+ O(c)`, exactly the completed Wold landing.
4. `P_N+R_N=-2D_N/H_N^3 O(c) -> 0`, but separately
   `P_N -> -(2/3)O(c)` and `R_N -> (2/3)O(c)`.
5. Before compression total variation tends to `4/3`; after grade-forgetting it is
   `2D_N/H_N^3 -> 0`, strictly smaller at every finite clock.
6. The pair `(P_N,R_N)` is actual-fibre multiplicity-faithful; adjoining the existing BV component
   leaves its endpoint defect unchanged.
7. The physical `(0,0)` corner of `P_N` is
   `-8 normSq(c) E_N`; adding it to the signed BV split is definitionally the existing compensated
   energy, hence tends to zero and lies below the literal source budget cofinally for `c != 0`.

## Dependency-closed proof

Write `x+ = max x 0` and `x- = max (-x) 0`. For every real `x`, case splitting at zero gives

```text
x = x+ - x-,        |x| = x+ + x-,        x+ * x- = 0.
```

Thus pointwise positive and negative parts are mutually singular, reconstruct the signed atomic
measure, and realize its total variation. This is the finite-atomic Hahn--Jordan theorem. The
operation is genuinely nonlinear: `(-)⁻(1 + (-1)) = 0`, while `(-)⁻(1) + (-)⁻(-1) = 1`.

Fix `N` and abbreviate `H = xiMassNthPrimeLogHeight N`. The source theorem
`xiMassNthPrimeLogHeight_pos` gives `H > 0`. For every retained prime label `n <= N`,
`sourceHorizontalEulerGammaCubicAtom_pos` gives `g_n > 0`, and `woldCoeff_pos` together with
`xiMassNthPrimeLogHeight_pos` gives `w_n > 0`. Therefore the Jordan parts of the exact signed
source density are forced pointwise:

```text
j-(Euler n) = 2 g_n/H^3,   j+(Euler n) = 0,
j-(Wold n)  = 0,           j+(Wold n)  = 2 w_n/H^3.
```

Summing over `Finset.range (N+1)` proves

```text
J_N^- = 2 G_N/H^3,         J_N^+ = 2 W_N/H^3.
```

No source coefficient has been deleted: `j = j+ - j-` pointwise. Prime labels remain the atom
indices. The existing third-derivative theorem expands each `g_n` over every prime-power depth with
literal factor `k^2`; Jordan selection changes only the sign of the source coefficient and hence
preserves that depth multiplicity.

Before grade forgetting, total variation is

```text
TVpre_N = J_N^- + J_N^+ = 2(G_N+W_N)/H^3.
```

The additive physical compression has scalar output `J_N^+ - J_N^-`. Since the proved source split
is `G_N = W_N + D_N` with `D_N > 0`,

```text
TVpost_N = |J_N^+ - J_N^-| = 2D_N/H^3,
TVpre_N - TVpost_N = 4W_N/H^3 > 0.
```

Hence compression is strictly information-losing at every clock; the selected Jordan pair is a
faithful residual lift, not a function of the compressed observable. The proved limits
`G_N/H^3 -> 1/3`, `D_N/H^3 -> 0`, and `G_N/H^3 = W_N/H^3 + D_N/H^3` imply

```text
J_N^- -> 2/3,   J_N^+ -> 2/3,   TVpre_N -> 4/3,   TVpost_N -> 0.
```

Now multiply only after selection by the common completed four-orientation block `O(c)`. Define

```text
P_N(c) = -J_N^- O(c),       R_N(c) = J_N^+ O(c).
```

The exact completed-residue identities already proved in the source card identify `P_N` with
`sourceHorizontalEulerGammaPolarPureSelectedLanding` and `R_N` with
`sourceHorizontalWoldGammaPolarPureSelectedLanding`. Thus both legs pass through the same two
Gamma/polar residues and preserve all four orientations. Their sum is the already-classified
linear defect landing `-2D_N/H^3 O(c)`, while the two limits are separately
`-(2/3)O(c)` and `(2/3)O(c)`.

The selected matrices do not depend on the representative in `XiRightSupportFiber q`. Finite
summation therefore multiplies the complete selected pair by the fibre cardinality, and the proved
cardinality theorem identifies this number with the analytic `xiSupportMultiplicity`. Adjoining
the unchanged first component of `sourceHorizontalEulerWoldKreinSelectedLandingBundle` preserves
the literal BV endpoint defect.

Finally `routePJuliaSharedOrientationOrbitBlock_eq_diagonal` gives `O(c) 0 0 = 4 normSq(c)`. Hence

```text
re (P_N(c) 0 0) = -8 normSq(c) G_N/H^3.
```

Adding this corner to `sourceHorizontalWoldBVKreinSignedSplitEnergy` is exactly
`sourceHorizontalWoldBVKreinEulerGammaCubicCompensatedEnergy`, already proved to tend to zero and,
for `c != 0`, to lie eventually below the positive literal primitive source budget. This transports
the independent pre-Xi order law to the nonlinear Xi-selected landing without a spectral
projection or a new analytic assumption.

## Hostile audit

- **Not post-compression recovery.** Strict `TVpost_N < TVpre_N` proves the pair contains source
  information absent from the scalar compressed current.
- **Not a spectral selector.** `max` is applied to real source coefficients before multiplication by
  any operator or matrix; no eigenvalue, Loewner order, or functional calculus occurs.
- **Not an arbitrary grading.** Pure `(3,0)` and `(0,3)` jets and vanishing mixed jet identify the
  two summands intrinsically in the completed source.
- **Not regulator deletion.** Both Jordan legs are returned and reconstruct the original current.
- **Not RH-equivalent.** Proof uses finite real order, existing unconditional asymptotics, residue
  transport, and source budget only; it asserts no Xi-zero location or positivity equivalent to RH.
- **Novelty boundary.** Hahn--Jordan minimality and total-variation contraction are literature.
  Their coefficient-faithful application to this intrinsic Euler/Wold completed-source grading was
  not found in the bounded primary-source audit, so priority remains `[NOVELTY UNVERIFIED]`.

## Falsifiers

1. Any selector applied after grade-forgetting fails by C0.
2. Any matrix spectral/Loewner positive part fails the non-spectral requirement.
3. Any source grade not linked to the two partial-jet theorems and mixed-zero theorem is an external
   tag.
4. Any output that keeps only `P_N`, rather than the reconstructing pair `(P_N,R_N)`, discards the
   regulator and is not faithful.
5. If pre-compression variation tends to zero or selected Euler action does not tend to
   `-(2/3)O(c)`, the construction has silently recompressed the grades.

## Gates

- [x] 0 -> 1 in-progress: exact source-pure statement, literature boundary, hostile falsifiers
- [x] 1 -> 2 fully-proven: dependency-closed proof and hostile audit
- [x] 2 -> 3 formalized: exact Lean theorem, leaf build, axiom audit
- [ ] 3 -> 4 publication-ready

## Approach

Prove the generic finite-atomic Jordan and compression theorem first. Specialize to the exact
Euler/Wold source atoms, use existing positivity and moment identities for the Jordan parts, then
transport the selected parts through the already-proved Gamma/polar landing. Finish with limits,
strict compression loss, actual Xi-fibre summation, BV projection, and the literal budget identity.

## Lean formalization

- `HTGeometry/SourceGradeJordanDataProcessing.lean` formalizes scalar Hahn--Jordan parts,
  reconstruction, mutual exclusion, explicit nonadditivity, total-variation contraction under
  grade forgetting, exact contraction loss, and strictness when both source grades are occupied.
- `RHTower/SourceHorizontalEulerWoldJordanResidualSelection.lean` specializes the construction to
  the literal prime-labelled Euler/Wold atom space. It proves exact pointwise Jordan parts, moment
  masses, positivity, `k²` depth preservation, strict compression loss, limits `2/3`, `2/3`, `4/3`,
  and `0`, exact identification with both completed residue landings, reconstruction of the linear
  defect, four-orientation retention, actual Xi multiplicity, unchanged BV component, and the
  selected physical-corner primitive-budget identity.
- Capstone: `sourceHorizontalEulerWoldJordanResidualSelection`.
- Targeted checks passed:
  `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalEulerWoldJordanResidualSelection.lean`,
  `lake build GaloisForLFunctions.RHTower.SourceHorizontalEulerWoldJordanResidualSelection`.
  No umbrella build was run.
- Axiom audit for generic frontier, selected budget identity, and capstone reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Formal lint has no forbidden proof debt. Global reachability check remains blocked by six
  unrelated pre-existing HTGeometry modules not imported by its umbrella.

## Log

- 2026-08-18 -- C0 and C1 killed; C2 frozen after internal and primary-literature audit.
- 2026-08-18 -- C2 dependency closed: exact Jordan parts, strict compression loss, residue
  transport, multiplicity, BV preservation, and selected primitive-budget identity proved.
- 2026-08-18 -- Generic literature frontier and arithmetic specialization formalized; exact leaf
  build and standard-axiom audit passed; wired into HTGeometry and RHTower umbrellas without
  building either umbrella.
