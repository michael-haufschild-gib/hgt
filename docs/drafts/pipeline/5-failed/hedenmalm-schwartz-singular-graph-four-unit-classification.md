# REDISCOVERED: Hedenmalm--Schwartz singular-graph four-unit classification

- **ID:** `hedenmalm-schwartz-singular-graph-four-unit-classification`
- **Stage:** 5-failed (retired as exact duplicate)
- **Type:** REDISCOVERY RECORD
- **Verdict:** `[REDISCOVERED] [BRIDGE] [POSITIVE SURVIVOR ALREADY FORMALIZED]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Read this before re-attempting:** changing ordinary `L2`/Schwartz topology to the canonical
  Mobius--Gamma singular graph topology, or asking when its packet Gram remains positive at the
  original four-unit Hardy--Fisher budget.

## Attempted topology pivot

Ordinary-`L2` Hilbert--Gram agreement is excluded by
`not_hedenmalmThetaOrdinaryL2PreQuasiRealization`. The proposed replacement was the existing
source-selected singular graph coordinate and its positive completion. The intended closed
classification was

```text
(for every finite inward packet u,
  mobiusGammaXiCoupledErrorWallWithBudget(u, 4) is positive semidefinite)
  <-> RiemannHypothesis.
```

The paper argument specializes
`all_mobiusGammaXiCoupledErrorWallWithBudget_posSemidef_iff` to budget `4`. Its right side is
`4 + D <= 4`, where `D = mobiusGammaXiCoupledErrorSingularGraphDebt` is a squared norm and hence
nonnegative. This is equivalent to `D = 0`, which
`mobiusGammaXiCoupledErrorSingularGraphDebt_eq_zero_iff_rh` identifies with RH.

## Exact prior formalization

Whole-corpus declaration search found the intended proposition already formalized verbatim as

```text
mobiusGammaXiPreScalarAffineBoundaryRenormalization_fourUnit_iff_rh
```

in
`formal/GaloisForLFunctions/RHTower/MobiusGammaXiPreScalarAffineBoundaryRenormalization.lean`.
Its Stage-3 source card is
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm/g-ce-coefficient-faithful-affine-boundary-renormalization.md`.
That card already records the sharper positive survivor: exact finite-depth Ward landing, source
response fidelity, cofinal transport, unconditional positive budget `4 + D`, and the fact that
removing graph debt is RH-equivalent.

The briefly created wrapper module `MobiusGammaXiFourUnitGraphPositivity.lean` merely introduced a
name for the same quantified proposition and reproved the same equivalence. It was deleted and
unwired before final audit. No new Lean declaration remains.

## Consequence for topology choice

- **Use:** canonical source-selected singular graph completion with budget `4 + D`; positivity is
  unconditional and Hilbertian.
- **Do not claim:** positivity at budget `4`; that condition is exactly RH.
- **Abandon:** literal ordinary-`L2`/full-Schwartz Hilbert--Gram agreement.
- **Do not use as escape hatch:** a Krein metric alone; indefinite self-adjointness does not supply
  positive Gram agreement.

This topology pivot is mathematically meaningful, but already complete in the corpus. No positive
salvage remains beyond the existing coefficient-faithful boundary-renormalization theorem.

## External parent mechanisms

- Hedenmalm's spectral setup uses the operator pair `(LD,L)`, not an ordinary bounded Hilbert
  operator: arXiv:2606.17494.
- Burnol's Sonine/de Branges constructions provide source-selected Hilbert quotient and
  distributional Fourier parent mechanisms: arXiv:math/0203120 and arXiv:math/0105120.
- Kapustin's Krein-space construction illustrates why indefinite self-adjointness alone does not
  force RH: DOI 10.1134/S0037446624010087.

These are parent-theory comparisons only. None is a novelty source for the repository-specific
Mobius--Gamma graph debt.

## Log

- 2026-08-19 — ordinary Hilbert topology rejected; singular graph completion selected.
- 2026-08-19 — paper proof of fixed-four classification closed from existing budget and debt
  theorems.
- 2026-08-19 — hostile exact-declaration audit found proposition already formalized verbatim;
  duplicate wrapper deleted and card retired.
- 2026-08-19 — authoritative module passed `lake env lean` and targeted `lake build`; axiom audit
  reports only `propext`, `Classical.choice`, and `Quot.sound`. Global formal lint remains blocked
  by seven unrelated pre-existing unreachable modules (one `RHTower`, six `HTGeometry`).
