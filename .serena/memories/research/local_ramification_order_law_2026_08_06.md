# Local ramification order law closed in Lean (2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
(still stage 2).

## New module

`GaloisForLFunctions/HTGeometry/LocalRamificationOrderLaw.lean`

| statement | declaration |
|---|---|
| units have valuation zero | `addVal_of_isUnit` |
| powers scale by `e` | `addVal_map_pow_of_addVal_eq` |
| **ramification index scales every valuation** | `addVal_map_eq_mul_ramification` |
| **`ord(pullback) = e·ord(form) + (e−1)`** | `addVal_pullback_form` |
| `(8)` iff `(9)` (the Jacobian shift) | `orderLaw_iff_shiftLaw` |

All axiom-clean.

## The mathlib gap that was filled

mathlib defines `Ideal.ramificationIdx` **combinatorially** (multiplicity of `q` in `p.map`) and
has **no theorem computing its effect on adic valuations**.  Searched:
`RingTheory/DedekindDomain/{AdicValuation,Factorization}.lean`,
`RingTheory/RamificationInertia/*`, `RingTheory/Localization/AtPrime/Extension.lean` — no
`v_q(algebraMap x) = e · v_p(x)` in any form.

Proof used here needs **no** finiteness, separability or Dedekind hypothesis: for a ring hom
`φ : A →+* B` of DVRs with `addVal B (φ π) = e` for some uniformizer `π`, decompose
`a = u * π^n` (`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`), note ring homs preserve
units (`IsUnit.map`), and induct on the power.

## State of the card's Theorem A

Formal now:
- (7) eigenvolume identity — `TopExteriorPowerDeterminant.lean` (top exterior power = det);
- (8) local order law — this module (the `e`) + `TameEisensteinDifferentExponent.lean` (the `e−1`);
- (9) shifted form — `orderLaw_iff_shiftLaw`;
- steps 3, 4, 5 and conclusions (2)–(6) — `EigenvolumeRamificationSystem.lean`.

Remaining, all irreducibly geometric: identifying a rational top form on a variety with the top
wedge of a coframe space, globalising the local law over all prime divisors of a smooth projective
variety, and `e_E > 1` from int-amplification on `N^1`.  Corollary B needs MMP.  mathlib has no
Weil divisors, no canonical divisor of a morphism, no `N^1`.

## Repo hazard (recurring)

The shared lint gate keeps failing on *other* agents' untracked unwired modules — on 2026-08-06
alone: `HTGeometry.SquarefreeClockLaw`, `RHTower.Sieve.DirichletHeadTailSplit`,
`HTGeometry.SubsystemComponentDecomposition`, `RHTower.Sieve.DirichletBlockTrivialBound`.
Always `git status` the reported module before assuming the failure is yours.
