# EM reflected-budget offline-domination universality law

Status: exact `lake env lean` audit passed; final module/lint/axiom audit pending.

## Lean sources

- `emCarrier_gN_close_on_of_reflected_budget`
- `raw_domination_of_emCarrier_close_pointwise_domination`
- `completed_domination_of_emCarrier_close_pointwise_domination`

## Survivor

On any strip set, explicit Euler--Maclaurin pole and tail budgets together with one reflected
Dirichlet-block budget directly imply both raw finite-carrier domination and completed Xi-carrier
domination.  No abstract approximate-functional-equation or carrier-closeness premise remains.

This closes the missing connector between the terminal remainder reduction and the terminal
offline comparison: the reflected block is now the only non-elementary budget reaching both
consumer inequalities.

## Proof skeleton

Use the pole, tail, reflected-block, and depth-`M` Euler--Maclaurin bounds to construct carrier
closeness at radius `epsilon1 + (deltaP + deltaT + Rchi)`.  Feed that exact bound and the displayed
Dirichlet domination inequality into the raw and completed offline discharge theorems.

## Novelty audit

Pending post-formalization literature search.
