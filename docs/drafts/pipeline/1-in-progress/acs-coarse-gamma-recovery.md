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

Conjecture only. No completed paper proof, Lean theorem, or full mixed Weil sign is claimed. The signed prime and pole interactions remain separate parent obligations. No stage-2 parking.

## Log

- 2026-10-28 — Opened after the general simultaneous Gamma variance, mean-graph, and exterior bound passed exact Lean audits.

[Nearby endpoint losses](../3-formalized/acs-gamma-near-row-remainders.md), in `LogCellGammaRemainderRows.lean`, passed the exact final check and both transitive audits: `gammaCellNearUpperRemainder_le` bounds the complete upper near row by `6*exp(1/2)`; `gammaCellNearLowerRemainder_le` bounds the lower near row by `2*exp(1/2)`, independently of source index. Four forward and two backward monotone shifts telescope; inverse-width and Gamma bounds control the endpoint readings. Audit log: `/tmp/acs-logcell-gamma-remainder-rows-final.log`. Only standard axioms; no warnings.

Adjacent, distant, exterior, and integrated-kernel recovery remain open. `/tmp/acs-gamma-interval-remainder.lean` contains unverified exact tail rows, a triangular first-moment formula, and the complete exterior averaging-loss identity; verification is underway.

A sharper decomposition is under investigation: first replace the actual kernel along each source interval by `gammaFarCharge` on its entire complement. The resulting nonnegative row loss should equal `2*∫_(0,w) t*k(t) dt`, hence be at most `exp(1/2)*w` for `w≤1`. This would handle touching interactions and the exterior in one row estimate. Only the further passage from the pointwise far charge to the pairwise farthest endpoint would require discrete rows; adjacent far-charge readings are nonsingular. This identity and its application are conjectural until checked in Lean.
