# Source Γ₆ algebraic untwisting no-go

- **ID:** RH-SOURCE-G6-ALG-UNTWIST-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** An ℝ-algebra automorphism of the infinite-cyclic source algebra intertwines `t-u` with fixed `t-1` only when `u=1`.

## Goal

Kill `source-algebra automorphic untwisting → fixed Γ₆ Stokes descent → shared HB/FZZ-P/PW-B/RBH Ward → RH` without assuming RH.

## Gates

- [x] 0 → 1 in-progress: corpus-derived, source-pure, exact proof chain and obstruction
- [x] 1 → 2 fully-proven: dependency-closed proof below
- [x] 2 → 3 formalized: Lean certificate, targeted build, axiom audit, umbrella
- [ ] 3 → 4 publication-ready

## Proof

Let `R=ℝ[ℤ]`, `t` its cyclic generator, and suppose `φ : R ≃ₐ[ℝ] R` satisfies
`φ((t-u)f)=(t-1)φ(f)` for every `f`. At `f=1`, `φ(t)=t+(u-1)`. Since `t` is a unit and automorphisms preserve units, the translate is a unit. If `u≠1`, evaluate at the cyclic character `t↦1-u∈ℝˣ`; the translate maps to zero, impossible for a unit. Hence `u=1`. The identity gives the converse.

For physical holonomy `u=exp(a(q))`, this exists exactly at `Re(q)=1/2`; universal existence is therefore equivalent to RH and the shared four-route Ward endpoint.

## No-go closure

- **Exact killing mechanism:** nonzero translates of the cyclic generator have a character zero and are not units.
- **Strongest positive survivor:** source holonomy is an algebraic unit-translate invariant under all ℝ-algebra source reparametrizations.
- **New insight:** viable untwisting must change category/localize or supply non-algebraic source dynamics; reparametrizing the existing source algebra cannot close any route.
- **Novelty audit:** targeted internal search found no such classification; targeted arXiv search found no direct antecedent.
- **Status:** formalized as `sourceHorizontalGammaSixAlgebraicUntwistingRouteKilled` in `SourceHorizontalGammaSixAlgebraicUntwistingNoGo`; direct Lean and targeted build pass; standard axioms only; umbrella wired.
