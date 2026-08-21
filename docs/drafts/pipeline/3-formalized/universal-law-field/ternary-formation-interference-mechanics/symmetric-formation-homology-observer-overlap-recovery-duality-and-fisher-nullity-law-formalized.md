# Symmetric formation homology and its four organs — Lean certification

- **ID:** ULF-TFIM-1
- **Paper card:** `symmetric-formation-homology-observer-overlap-recovery-duality-and-fisher-nullity-law.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ConstitutiveSymmetricFormationHomology`
  (algebraic core), `GaloisForLFunctions.HTGeometry.TernaryFormationComplex` (§2–§4),
  `GaloisForLFunctions.HTGeometry.TernaryFormationDualityHodge` (§5–§9)
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

## §2 The symmetric three-formation complex (Theorem 2.1)

`TriChainOne`, `TriChainTwo`, `triD1`, `triD2` are `(TFIM.1)`–`(TFIM.2)`.

* `triD1_comp_triD2` and `range_triD1` — item 1;
* `triTripleIncl`, `range_triTripleIncl`, `triKerTwoEquiv` — item 2, `(TFIM.3)`:
  `ker d₂ ≅ U ⊓ W ⊓ Z` via `x ↦ (x, −x, x)`;
* `triCycle`, `triBoundary`, `triBoundary_le_triCycle`, `TriHomology` — `(TFIM.4)`;
* `triProjU`/`triProjW`/`triProjZ`, `triChargeU`/`triChargeW`/`triChargeZ`, their surjectivity and
  the three kernel computations `ker_triChargeU`/`ker_triChargeW`/`ker_triChargeZ`, assembled by
  `triHomologyEquivOfProj` into `triHomologyEquivU`, `triHomologyEquivW`, `triHomologyEquivZ` —
  item 4, `(TFIM.5)`.  All three charts are surjections from the *same* cycle space with the
  *same* kernel, which gives item 3 (permutation invariance) as `formationChargeEquivW` and
  `formationChargeEquivZ` without any separate chain-permutation argument.
* item 5, `(TFIM.6)`, is the pre-existing `formationCharge_finrank_balance`.

## §3 Observer-created overlap

* `observerPairs`, `pairToCore`, `pairToOverlap`, `pairCharge`, `pairOverlap`, their surjectivity
  and `ker_pairCharge_eq_ker_pairOverlap`, giving
  **`formationChargeEquivObserverOverlap`** — **Theorem 3.1 `(TFIM.9)`–`(TFIM.10)`** as a
  *canonical isomorphism*, not just an equality of ranks.  The construction is choice-free: both
  sides are quotients of the space of unobserved pairs by the same subspace.
* `formationBoundary_ker_eq_bot`, `formationChargeEquivExcessKernel` — **Corollary 3.2
  `(TFIM.11)`**; `disjoint_sup_iff_overlap_le` — **`(TFIM.12)`**.
* `subQuotCongr`, `formationChargeCongr`, `mkQSubQuotMap`, `mkQSubQuotEquiv` and
  **`formationChargeEquivQuotientOverlap`** — **Corollary 3.3 `(TFIM.13)`**: quotienting creates an
  intersection.
* `finrank_formationCharge_eq_rank_slack` and `finrank_formationCharge_eq_nullity_slack` —
  **Corollary 3.4 `(TFIM.13b)`**, both the submodularity-slack and supermodularity-slack forms.
* `mvDiag`, `mvAdd`, `mvDiag_injective`, `mvAdd_surjective`, `range_mvDiag_le_ker_mvAdd`,
  `mvMiddle`, `ker_mvMiddle` and **`mvMiddleHomologyEquiv`** — **Theorem 3.5 `(TFIM.13c)`–
  `(TFIM.13e)`**: degreewise observation of the two-subspace Mayer–Vietoris sequence creates
  exactly this homology in the middle.

## §4 Reduced fusion complex (Theorem 4.1)

`RedTwo`, `RedOne`, `RedZero`, `redLegW`, `redLegZ`, `redD1`, `redD2` are `(TFIM.15)`–`(TFIM.16)`;
`redD2_injective` and `redD1_surjective` are the endpoint claims; `redPairs`, `redPairToCore`,
`redPairToCycle`, `redPairCharge`, `redPairHomology`, their surjectivity and
`ker_redPairCharge_eq_ker_redPairHomology` give **`redHomologyEquiv`** — `(TFIM.17)`, hence
`(TFIM.18)`–`(TFIM.19)`.  `finrank_formationCore_eq` is **`(TFIM.20)`**.

## §5 Reporter duality (Theorem 5.1)

`dualSubmoduleHasQuotient` registers the submodule-quotient instance for subspaces of the dual
(mathlib's general instance is not found through `Module.Dual`).  `annihilatorToDual`,
`ker_annihilatorToDual`, `annihilatorToDual_surjective` (extension of functionals) give
`subQuotDualEquiv`; with `dualAnnihilator_formationBoundary` and
`dualAnnihilator_formationCore` this yields **`formationChargeDualEquiv`** — **`(TFIM.23)`–
`(TFIM.24)`**.

## §6 Positive Hodge carrier (Theorem 6.1)

`relCompEquivSubQuot` is the unique-harmonic-representative theorem for nested closed subspaces.
`hodgeLaplacian` is `(TFIM.25)`; `re_inner_hodgeLaplacian_self` is the sum-of-two-squares identity;
`ker_hodgeLaplacian` is **`(TFIM.26)`**; `harmonicEquivHomology` realizes the homology;
`finrank_relComp_eq_finrank_subQuot` and `range_starProjection_relComp` are `(TFIM.27)`–
`(TFIM.28)`.

## §7 Equivariance and the functional-equation countermodel

`map_formationCore`, `map_formationBoundary` and **`formationChargeEquivOfAut`** are
`(TFIM.29)`–`(TFIM.30)`.  The countermodel `(TFIM.31)`–`(TFIM.35)` is built over an arbitrary
field: `firstAxis`, `diagLine`, `axisLine`, with `firstAxis_inf_diagLine`,
`firstAxis_inf_axisLine`, `diagLine_sup_axisLine`, `countermodelChargeEquiv`,
`counterInvolutionMap`, `counterInvolution`, `counterInvolutionMap_involutive`,
`snd_comp_counterInvolution`, the three transport identities, and the capstone
**`countermodel_functional_equation_neutral`**: the involution fixes the observer exactly,
exchanges the two legs, fixes the recovery kernel, and the charge still has dimension one.

## §8 Fused Fisher nullity (Theorem 8.1)

`gramOp` is `(TFIM.36)`; `ker_gramOp` and `finrank_ker_domRestrict` are `(TFIM.37)`;
**`finrank_ker_gramOp_sup`** is `(TFIM.38)` and **`finrank_ker_gramOp_sup_of_disjoint`** is
`(TFIM.39)`: two separately identifiable Gaussian legs fuse into a nonidentifiable model whose
exact nonidentifiability rank is the formation charge.

## §9 Cofinal properness selection (Theorem 9.1)

**`bddAbove_cofinalAction_iff`** — `(TFIM.41)`–`(TFIM.43)`: for a coherent noncontracting history
with divergent weight tails, bounded truncated action is equivalent to identical vanishing.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/TernaryFormationComplex.lean
lake env lean GaloisForLFunctions/HTGeometry/TernaryFormationDualityHodge.lean
```

Both elaborate with no errors and no warnings.  `#print axioms` on all 97 + 39 public
declarations reports only `propext`, `Classical.choice`, `Quot.sound`.  Both modules are imported
by `GaloisForLFunctions.HTGeometry.UniversalLawField` and by `GaloisForLFunctions.HTGeometry`.

## Still open (not a proved theorem)

Gate 3 → 4 of the card: a literal arithmetic three-formation realization and the publication
paper.  The card states these as construction burdens, not theorems.
