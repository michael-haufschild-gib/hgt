# Actual coarse-source Gamma accounting

- **ID:** acs-coarse-gamma-accounting
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** ACS: full-source sections → Riemann–Roch/ampleness → Hodge index → RH.
- **Parent:** [coarse Gamma recovery](../1-in-progress/acs-coarse-gamma-recovery.md)
- **Statement:** The original Gamma energy of every finite signed complete-pair average is bounded by its retained mean graph, exterior charge, and explicit integrated endpoint-error rows.

## Exact theorem

Let `g=averageSectionProfile q X`, with arbitrary real `q` and arbitrary finite horizon `X`. For each pair interval `Iᵢ`, let `Rᵢⱼ` be the actual integrated farthest-endpoint replacement loss, set `Rᵢᵢ=0`, and let `Dᵢ` be its integrated averaging loss against the complement of the whole interval family. The actual row is

`completePairGammaErrorRow X i = Σⱼ Rᵢⱼ + Dᵢ`.

Lean proves

`2*ofReal(levyEnergy g) ≤ ofReal(completePairMeanGraph q X) + 2*completePairExteriorCharge q X + 4*Σᵢ ofReal(qᵢ²)*completePairGammaErrorRow X i`.

The theorem does not assume any bound on these rows. Every error is defined from the original Gamma density and actual interval integrals.

## Matched proof

The two adjacent half-open cells form exactly their complete pair interval. Thus `g=qᵢ` on its open interior, and `g=0` almost everywhere on the family exterior; the omitted boundary points form a null set. Existing complete-pair regularity gives compact support and bounded variation for arbitrary signed coefficients.

Partition the actual double Gamma-difference integral into all interval pairs and the two orientations of the exterior blocks. The exterior–exterior block vanishes almost everywhere. On each pair, its coefficient difference factors out of the original kernel integral. The checked replacement inequality gives its mean edge plus `(qᵢ-qⱼ)² Rᵢⱼ`. Symmetry and `(u-v)²≤2(u²+v²)` bound the sum by `4*Σᵢ qᵢ²*Σⱼ Rᵢⱼ`. The exact exterior kernel decomposition gives the retained boundary charge plus `qᵢ² Dᵢ`; its factor two is at most the common factor four. This proves the displayed inequality without discarding any coarse coefficient.

## Lean evidence

[CompleteCellGammaAccounting.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteCellGammaAccounting.lean):

- `averageSectionProfile_gamma_le_graph_exterior_rows`
- `coarseProfile_eq_indicator`, `averageSectionProfile_eq_on_pair`
- `averageSectionProfile_bv`, `averageSectionProfile_compact`
- `averageSectionProfile_zero_ae_exterior`.

Exact project command passed without warnings:

`lake --old env lean GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteCellGammaAccounting.lean`

All six transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. Log: `/tmp/acs-complete-cell-gamma-accounting-final.log`. Umbrella import wired; umbrella not compiled. The supporting finite-error estimates are [formalized](acs-gamma-interval-averaging-loss.md).

## Remaining parent obligation

[CompleteCellGammaUniformRows.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteCellGammaUniformRows.lean) now proves `completePairGammaErrorRow_le`: every actual row is at most `ofReal(completePairGammaRowConstant*logCellWidth a)`, with `completePairGammaRowConstant=13*exp(1/2)+2*gammaTailMass(log(3/2))`. `completePairGammaRowConstant_nonneg` proves nonnegativity; `completePairExteriorCharge_ne_top` proves every retained exterior charge finite for arbitrary signed coefficients and horizon.

The complete pairs are exactly the `log 2` translate of the logarithmic partition. Removing the zero diagonal identifies their finite pair row with the checked uniform row. The family exterior is contained in each pair complement, so the checked exterior averaging-loss bound adds `exp(1/2)` per source width. Each weighted far charge is bounded by a finite actual exterior-kernel integral; a finite sum remains finite before conversion to real numbers.

The exact project check and all three transitive axiom audits passed without warnings, with only `propext`, `Classical.choice`, `Quot.sound`. Log: `/tmp/acs-complete-cell-gamma-uniform-rows-final.log`. Final real coarse-energy recovery remains on the parent card. Full signed Gamma–prime–pole payment remains open.
