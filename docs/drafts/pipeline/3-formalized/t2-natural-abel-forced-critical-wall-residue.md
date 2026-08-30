# T2 natural Abel continuations have forced critical-wall residue

- **ID:** T2-NATURAL-ABEL-FORCED-WALL-RESIDUE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md`, Route T2
- **Statement:** Every holomorphic continuation on the upper translated critical sector of the literal natural Wold Abel germ has a nonzero, negative-integer radial residue at one unconditional Hardy critical-line zero.

## Goal

Kill the entire regular-continuation branch of T2, not merely one square-energy producer.  Route T2
needs a continuation of the natural Wold residual/Abel representation across `Re s = -1/2` that is
regular enough to supply a finite boundary value or norm identity.  This theorem will prove that any
holomorphic continuation agreeing with the unconditional safe Abel germ necessarily has a pole on
that wall.  Surviving T2 mechanisms must therefore retain the singular divisor explicitly; no
regular Abel continuation, regardless of how produced, can close T2.

## Gates

- [x] 0 → 1 in-progress: exact germ, sector, forced residue, and T2 proof chain specified
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted build green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper + Lean certificate + external priority audit

## Exact conjecture

Let

`A(s) = abelDirichlet woldNatDifferenceCoeff s`,

`M(s) = integerLogMeshContinuation s`, and

`U = {s : ℂ | -1/2 < Re s ∧ 0 < Im s}`.

There exist `s₀ : ℂ` and `m : ℕ` with

`Re s₀ = -1/2`, `Im s₀ > 0`, and `m ≥ 1`,

such that for every `F : ℂ → ℂ`, if `F` is holomorphic on `U` and

`F(s) = A(s)` for every `s ∈ U` with `Re s > 0`, then

`lim_{x→0+} x F(s₀+x) = -m`.

Consequently `F(s₀+x)` has no finite right-radial limit.  Quantifiers place `s₀,m` outside the
choice of `F`: one unconditional Hardy zero obstructs every regular continuation of this germ.

## RH proof chain closed or killed

`T2 natural residual control / identity`
→ `regular holomorphic continuation of literal natural Abel germ to U`
→ **forced nonzero critical-wall residue**
→ contradiction with finite boundary value, continuity, Hardy/Smirnov regularity, or any norm
identity whose output is a regular representative.

This does not prove RH.  It kills this whole T2 producer class and sharpens T2's survivor: only an
explicitly singular unsplit divisor mechanism can remain.

## Corpus audit

Required searches used `scripts/formal_tools.py research`, including:

- `abelDirichlet_woldNatDifferenceCoeff_eq_wold_sub_mesh`
- `xiHeatCassiniWoldCriticalLaplaceContinuation_zero_residue`
- `xiHeatCassiniWoldZetaClearedContinuation_eq_mul_critical`
- `exists_riemannZeta_line_zero_dyadic`
- `eventually_riemannZeta_ne_zero_nhdsNE`
- exact searches for natural-Abel continuation, critical-wall residue, and no-extension variants.

Corpus already proves the unconditional safe identity

`A = WoldLaplaceCurrent - integerLogMeshCurrent` on `Re s > 0`,

the zeta-cleared analytic continuation on `U`, isolatedness of nontrivial zeta zeros, unconditional
existence of a positive-height critical-line zero, and exact Wold residue `-m`.  Corpus only kills a
specific square-energy producer (`not_woldNatResidualSquareEnergy_of_half_lt`) or studies the
canonical Wold continuation.  It contains no theorem quantifying over every analytic continuation
of the literal natural Abel germ.

## Literature audit through 2026-08-30

Exact-phrase and concept searches found no Wold/natural-Abel theorem of this form.  Adjacent
literature covers prime-zeta/log-zeta singularities, logarithmic-derivative residues, and weighted
prime-counting error correlations, but not this natural-cutoff Wold finite-difference germ or the
universal continuation classification.  Closest recent adjacent source:

- Bhattacharya–Martin–Simpson, *Correlations of error terms for weighted prime counting functions*,
  arXiv:2507.13504 (2025), https://arxiv.org/abs/2507.13504.

Novelty claim is therefore exact-object and exact-quantifier novelty, not novelty of the classical
fact that a logarithmic derivative detects zeros by residues.

## Attack

1. For arbitrary admissible `F`, set `G = F + M` and `H = ζ(s+1) G(s)`.
2. `G` and `H` are holomorphic on `U`; `M` is holomorphic there because `Re s > -1` and `Im s > 0`.
3. On the nonempty open safe germ `Re s > 0`, unconditional Abel summation gives
   `G = WoldLaplaceCurrent = WoldCriticalContinuation`; zeta-clearing gives `H = Wclear`.
4. Connected-sector identity theorem gives `H = Wclear` on all `U`.
5. Choose `rho = 1/2+i tau`, `tau>0`, with `ζ(rho)=0` by unconditional Hardy; put `s₀=rho-1`.
6. Existing residue theorem supplies `m≥1` and
   `x WoldCriticalContinuation(s₀+x) → -m`.
7. Zeta zeros are isolated.  For small `x>0`, cancel `ζ(rho+x)` in the two cleared identities and
   obtain `F(s₀+x)+M(s₀+x)=WoldCriticalContinuation(s₀+x)`.
8. `M` is continuous at `s₀`, hence `x M(s₀+x)→0`; subtraction yields `xF(s₀+x)→-m`.
9. Any finite radial limit for `F` would instead give `xF(s₀+x)→0`, contradicting `m≥1`.

## Hostile audit

- No RH or zero-location hypothesis: Hardy supplies an unconditional on-line zero.
- No square energy, asymptotic computation, or boundary-value assumption enters forced residue.
- Safe germ identity is unconditional and uses literal natural coefficients.
- Identity theorem applies on one convex upper sector containing safe points and every positive
  radial translate of chosen wall point.
- Zeta cancellation is only off the isolated zero and only eventually along `x→0+`.
- Mesh term is regular at wall because `Re s₀=-1/2>-1` and `Im s₀>0`, so `s₀≠0`.

## No-go closure

- **Exact killing theorem/mechanism:** `exists_woldNatAbelContinuation_no_finite_criticalWall_limit`; every holomorphic continuation of the literal natural Abel germ is forced to diverge radially at one universal Hardy wall point.
- **Strongest positive survivor:** exact residue classification `-m(rho)` shared by every analytic continuation of natural Abel germ.
- **New insight:** obstruction belongs to representation itself, not square-energy estimate; regularizing producer can be discarded before analytic-estimate work.
- **Status:** dependency-closed paper proof and Lean formalization complete; external exact-object priority search negative through 2026-08-30.

## Log

- 2026-08-30 — created directly in Stage 1 after corpus-first conjecture and hostile route audit.

## Proof

**[PROVED HERE]** Fix arbitrary `F` satisfying the two continuation hypotheses.  On `U`, both
`F + M` and `ζ(s+1)(F+M)` are holomorphic: mesh regularity follows from `Re s > -1/2 > -1` and
`Im s > 0`, which excludes its translated zeta pole.  On the nonempty safe subdomain `Re s > 0`,
the unconditional natural Abel identity and mesh continuation identity give

`F + M = WoldLaplaceCurrent = WoldCriticalContinuation`.

Multiplication by shifted zeta and the canonical cleared identity show equality with `Wclear` on
that open germ.  Convexity of `U` and the identity theorem extend the cleared equality to all of
`U`.

Hardy's theorem gives `rho=1/2+i tau`, `tau>0`, with `ζ(rho)=0`; put `s₀=rho-1`.  The existing
critical-Wold residue theorem supplies `m≥1` and

`x WoldCriticalContinuation(s₀+x) → -m` as `x→0+`.

Zeta zeros are isolated in the open critical strip, so `ζ(rho+x)≠0` for all sufficiently small
positive `x`.  Canceling that factor in the canonical and arbitrary cleared identities yields

`WoldCriticalContinuation(s₀+x)=F(s₀+x)+M(s₀+x)`.

Mesh continuation is differentiable at `s₀`, hence `xM(s₀+x)→0`.  Subtraction proves
`xF(s₀+x)→-m`.  If `F(s₀+x)` had finite limit `L`, multiplication by `x→0` would instead give
`xF(s₀+x)→0`.  Uniqueness of limits forces `m=0`, contradicting `m≥1`.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAbelForcedCriticalWallResidue`
- Main classification: `exists_woldNatAbelContinuation_forced_criticalWall_residue`
- Branch kill: `exists_woldNatAbelContinuation_no_finite_criticalWall_limit`
- Direct check: `lake env lean ...XiHeatCassiniWoldNaturalAbelForcedCriticalWallResidue.lean` passed.
- Final targeted build: `lake build GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAbelForcedCriticalWallResidue` passed.
- Axiom audit: only Lean foundations `propext`, `Classical.choice`, `Quot.sound`; no added axioms.
- Umbrella: imported by `GaloisForLFunctions/RHTower.lean`.
- Global lint reports only pre-existing/unrelated unreachable modules; this module is reachable and has no forbidden declarations.
- 2026-08-30 — universal residue theorem formalized; regular-continuation branch of T2 retired.
