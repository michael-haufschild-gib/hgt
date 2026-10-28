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

A first candidate `/tmp/acs-logcell-gamma-remainder-rows.lean` bounds the complete upper near row of nonadjacent endpoint losses by `6*exp(1/2)`, independently of source index. Four monotone kernel shifts telescope; the checked inverse-width lower bound controls the first reading. This candidate is unverified, and does not yet bound adjacent, lower, or distant interactions.
