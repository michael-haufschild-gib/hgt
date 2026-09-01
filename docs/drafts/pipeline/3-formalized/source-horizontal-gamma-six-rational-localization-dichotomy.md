# Source Γ₆ rational-localization dichotomy

- **ID:** RH-SOURCE-G6-RATLOCAL-DICHOTOMY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Finite-denominator source localizations cannot support every additive holonomy gauge, while the total rational function field supports a unique untwisting for every holonomy and is therefore nonselective.

## Goal

Kill `source-pure localization untwisting → fixed Γ₆ Stokes descent → shared HB/FZZ-P/PW-B/RBH Ward → RH` at both natural localization extremes.

## Gates

- [x] 0 → 1 in-progress: corpus-derived after algebraic-unit obstruction; exact chain fixed
- [x] 1 → 2 fully-proven: dependency-closed proof above; `[PAPER-PROVED]`
- [x] 2 → 3 formalized: exact Lean theorem, targeted build, axiom audit, umbrella
- [ ] 3 → 4 publication-ready

## Hostile loop

- `[CONJECTURE]` Localization still forces trivial holonomy.
- `[FALSIFIED]` In `K(X)`, translation `τ_{u-1}:X↦X+(u-1)` intertwines `X-u` with `X-1` for every `u`.
- Stronger replacement: finite-denominator localization cannot be grade-universally translation-stable, whereas total fraction-field localization has exactly one untwisting for every grade.
- Verdict: `SURVIVES PRELIMINARY ATTACK`; parent translation/PGL₂ theory is classical, but corpus and targeted literature searches found no Γ₆/RH localization-dichotomy application.

## Proof

For a field `K`, put `B_u(f)=(X-u)f` on `K(X)`. If `φ` intertwines `B_u` and `B_1`, evaluation at `f=1` forces `φ(X)=X+(u-1)`. Algebra maps out of `K(X)` are determined by `X`, so `φ=τ_{u-1}`. Conversely this translation intertwines the boundaries multiplicatively. Thus every `u` has a unique rational untwisting.

For `D∈ℝ[X]`, the principal localization at powers of `D` admits translation by `q` on the Laurent generator inverse exactly when `X+q` divides `D^n` for some `n>0`. This holds exactly when `D(-q)=0`: divisibility gives a root of `D^n`, hence of `D`; conversely the factor theorem gives `X+q∣D`. A nonzero polynomial has finitely many roots, so no nonzero finite denominator admits every real translation.

Hence finite source-pure localization cannot implement the grade-universal gauge, while total fraction-field localization implements it unconditionally and uniquely for all physical holonomies. Neither supplies RH selection.

## No-go closure

- **Exact killing mechanism:** finite pole support cannot follow every additive translate; the generic field deletes all closed fibres and makes every holonomy gauge-equivalent.
- **Strongest positive survivor:** unique rational gauge `τ_{u-1}` and exact admission law `q admitted ↔ D(-q)=0`.
- **New insight:** holonomy detection lives precisely in retained closed fibres; finite localization cannot move them universally, total localization erases them completely.
- **Status:** `[LEAN-PROVED]` as `sourceHorizontalGammaSixRationalLocalizationRouteKilled`; direct Lean and targeted build pass; standard axioms only; umbrella wired.
