# Recover coarse Gamma energy from the retained mean graph

- **ID:** acs-coarse-gamma-recovery
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** ACS: actual complete-cell sources → effectivity → Riemann–Roch and ampleness → Hodge index → RH.
- **Parent:** [complete-cell mixed payment](acs-complete-cell-mixed-payment.md)
- **Statement:** The original Gamma energy of arbitrary complete-pair averages is at most their retained mean-graph and exterior charges plus one universal constant times their actual square mass, independently of the upper horizon.

## Precise target

For `g=averageSectionProfile q X`, seek one `C≥0`, independent of `q,X`, with

`levyEnergy g ≤ (1/2)*completePairMeanGraph q X + (completePairExteriorCharge q X).toReal + C*Σ_(a=1..X) logCellWidth(a)*q(a)²`.

The graph and boundary charges are defined by actual interval means and the original Gamma kernel. Their simultaneous lower bound inside arbitrary average-plus-detail sources and its complete-cell specialization are [formalized](../3-formalized/acs-gamma-detail-mean-boundary-payment.md).

## Mathematical issue

Each pair uses the Gamma kernel at its farthest endpoint distance. Recovering the actual coarse energy requires controlling the difference between integrated and endpoint weights. Near touching cells, use the integrable boundary kernel. For nonadjacent nearby cells, compare endpoint weights through finitely shifted monotone rows. For distant cells, retain the integrable Gamma tail. The logarithmic partition has comparable neighboring widths; no uniform-mesh premise may be added.

## Status

The full coarse recovery statement remains conjectural. No full mixed Weil sign is claimed; checked component theorems are recorded below. The signed prime and pole interactions remain separate parent obligations. No stage-2 parking.

## Log

- 2026-10-28 — Opened after the general simultaneous Gamma variance, mean-graph, and exterior bound passed exact Lean audits.

[Nearby endpoint losses](../3-formalized/acs-gamma-near-row-remainders.md), in `LogCellGammaRemainderRows.lean`, passed the exact final check and both transitive audits: `gammaCellNearUpperRemainder_le` bounds the complete upper near row by `6*exp(1/2)`; `gammaCellNearLowerRemainder_le` bounds the lower near row by `2*exp(1/2)`, independently of source index. Four forward and two backward monotone shifts telescope; inverse-width and Gamma bounds control the endpoint readings. Audit log: `/tmp/acs-logcell-gamma-remainder-rows-final.log`. Only standard axioms; no warnings.

The [complete interval averaging loss, separated tail rows, pair-kernel decomposition, finite symmetric error estimate, and arbitrary exterior-subset bounds](../3-formalized/acs-gamma-interval-averaging-loss.md) passed twenty-nine exact-file/transitive audits. The exterior-subset estimates give finite weighted far charges before real conversion and retain the touching-cell row loss. [Logarithmic-cell geometry and finite nearby, distant, and touching rows](../3-formalized/acs-gamma-near-row-remainders.md) passed fourteen further audits. Both nearby integrated replacement-loss rows have fixed width bounds; the entire distant interaction row costs two fixed Gamma tails per source width, independently of the finite horizon. Both touching cells together cost at most `4*exp(1/2)*wₐ`. Complete error-row assembly and final coarse-energy comparison remain open.

`gamma_interval_row_defect_eq` proves the exact complete exterior loss `2*∫_(0,w) t*k(t) dt`; `gamma_interval_row_defect_le` bounds it by `exp(1/2)*w` for `w≤1`. The actual kernel decomposition and its finite bound are also checked. This pays touching/exterior averaging loss in one row.

[Actual coarse-source accounting](../3-formalized/acs-coarse-gamma-accounting.md) passed its exact project check and all six transitive audits. `averageSectionProfile_gamma_le_graph_exterior_rows` bounds twice the original coarse Gamma energy by the retained graph, twice the exterior charge, and four times the coefficient-square-weighted actual error rows. Compact BV regularity, exact pair values, and zero exterior almost everywhere are proved for every signed coefficient vector. The remaining step is a universal width bound on those rows, followed by finite real conversion. Full signed prime and pole payment remains open.

## Verification handoff

The user explicitly resumed the three remaining tasks: uniform row assembly, actual-pair transfer and exterior finiteness, and simultaneous coarse/detail recovery. All touching bounds passed the exact `LogCellGammaBoundaryRows.lean` audit. The `LogCellGammaNearFiniteRows.olean` dependency was built successfully. The cancelled `LogCellGammaDistantRows.olean` build produced no olean; its earlier exact source audit remains valid. Its missing dependency build is now resumed.

Unverified assembly candidates remain at `/tmp/acs-logcell-gamma-uniform-rows.lean`, `/tmp/acs-complete-cell-gamma-uniform-rows.lean`, and `/tmp/acs-complete-cell-gamma-recovery.lean`. They are not project modules or proved results. Resume with missing dependency oleans, one at a time, then check the candidates and exact installed files. The last candidate includes actual coarse square-mass identification and both original cell coefficients. No recovery theorem is certified until these checks pass.
