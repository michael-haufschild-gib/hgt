# HB universal copywise-unit-phase darkness no-go

Status: formalized; direct scratch check passed 2026-09-14.

## Route burden discharged

Shared proposed chain: phase-sensitive source polarization -> BM darkness -> Ward charge zero ->
HB / FZZ-P / RBH / PW-B -> RH.

Every function `phase : XiZeroCopy -> ℂ` with pointwise `normSq (phase q) = 1`, including
discontinuous and sheet-changing choices, leaves the universal HB BM Peierls cubic cut unchanged.
For nonzero amplitude in the physical parameter range, the rephased cut vanishes iff the copy lies
on `Re(s) = 1/2`. Thus phase-only source repair cannot darken an off-line copy.

Lean capstone:
`hbUniversalCopywiseUnitPhaseOffLineDarknessRepairRouteKilled`.

## Positive survivor

The exact covariance law scales the cut by `(normSq A)^2`. Any surviving source repair must change
magnitude, carrier, propagator, or source incidence; phase/sheet selection alone is excluded.

## Novelty audit

Corpus deep search found the general conjugate-branch scaling law and universal HB realization, but
no arbitrary-copywise unit-phase off-line darkness no-go. Primary-literature search through August
2026 found general Peierls/gauge frameworks, not this Xi-copy classification.

## Verification

- Identical scratch theorem: `lake env lean /tmp/HBUnitPhaseNoGoScratch.lean` passed.
- Tree-file direct check was stopped after 30 seconds during shared cache churn; no long retry.
- No computation enters any statement or proof.
