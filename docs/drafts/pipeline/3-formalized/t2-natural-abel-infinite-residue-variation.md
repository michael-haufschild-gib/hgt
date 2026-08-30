# T2 natural Abel infinite residue variation

- **ID:** T2-NAT-ABEL-INFINITE-RESIDUE-VARIATION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · Route T2 natural Abel continuation branch
- **Statement:** No radial residue profile of an admissible natural Wold Abel continuation tends to zero along the cofinite filter; consequently no such profile is summable.

## Goal

Kill the remaining infinite-but-finite-variation polar-repair branch of Route T2.  Exact RH-chain
position:

`T2 natural Wold Abel representation`
→ `analytic continuation agreeing with the literal Abel germ`
→ `assign a right-radial residue at every positive wall height`
→ `finite-variation/summable repair requires a summable residue profile`
→ `summability forces cofinite decay to zero`
→ `Hardy's arbitrarily high critical-line zeros force negative-integer residues of norm at least one`
→ contradiction.

This does not prove RH.  It eliminates a whole infinite-pole continuation class that survives the
finite-singular-support no-go.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `not_woldNatAbelSummableRadialResidueProfile`, targeted `lake build` green, axiom audit clean
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Definitions

Let `F` be analytic on `xiHeatCassiniWoldResidualODESector 1` and agree there, in positive real
part, with `abelDirichlet woldNatDifferenceCoeff`.  A function `r : ℝ → ℂ` is a right-radial
residue profile for `F` when, for every `tau > 0`,

`x * F((linePt tau - 1) + x) → r(tau)` as real `x → 0+`.

The stronger target is that no such `r` tends to zero along `Filter.cofinite`.  Summability is then
an immediate corollary, since every summable family tends cofinally to zero.

## Approach

Assume a residue profile `r` tends cofinally to zero.  Then all but finitely many ordinates satisfy
`‖r tau‖ < 1`; call the exceptional finite set `B`.  Choose a Hardy dyadic interval whose lower
endpoint exceeds every member of `B` in absolute value.  It contains a positive critical-line zero
`linePt tau`, with `tau ∉ B`.

The already formalized full critical-divisor theorem gives an integer `m ≥ 1` and the same radial
limit `-(m : ℂ)` at `tau`.  Uniqueness of limits identifies `r tau = -(m : ℂ)`, so
`‖r tau‖ = m ≥ 1`, contradicting `‖r tau‖ < 1`.

## Hostile novelty and route audit

- The result is not the finite-support theorem restated: it permits infinitely many nonzero
  residues and rules out the strictly larger `c₀(Filter.cofinite)` class.
- Classical prime-zeta/logarithmic-derivative literature supplies adjacent facts about singularities
  and multiplicity residues, but corpus and literature searches found no theorem for this exact
  natural Wold Abel germ with a universal quantifier over admissible continuations and a global
  cofinite-decay obstruction.
- The mathematical input is exact divisor inheritance plus Hardy's unbounded critical divisor;
  neither RH nor a zero-density hypothesis is assumed.
- The claim does not kill arbitrary finite-rank or trace-class operator modifications.  It kills
  exactly those repairs whose induced scalar radial residue profile is summable (indeed, merely
  cofinally null).
- Strongest positive survivor: every admissible radial residue profile has norm at least one on an
  unbounded set of ordinates, expressed intrinsically as failure of cofinite convergence to zero.

## Paper proof

**Theorem.** Let `F` be an admissible continuation and `r` its right-radial residue profile.  Then
`r` does not tend to zero along the cofinite filter.

**Proof.** Suppose `r → 0` cofinally.  The open unit ball about zero is a neighbourhood of zero, so
`‖r tau‖ < 1` for all `tau` outside a finite set `B`.  By the dyadic Hardy theorem there is `T₀ > 0`
such that every interval `[T, 2T]`, `T ≥ T₀`, contains `tau` with
`riemannZeta(linePt tau) = 0`.  Put

`T = T₀ + ∑_{u∈B} |u| + 1`.

Choose such `tau ∈ [T, 2T]`.  Then `tau > 0`.  If `tau ∈ B`, the elementary finite-sum bound gives
`tau ≤ |tau| ≤ ∑_{u∈B}|u|`, while `tau ≥ T = T₀ + ∑_{u∈B}|u| + 1`, contradiction.  Hence
`tau ∉ B` and `‖r tau‖ < 1`.

The full critical-divisor inheritance theorem, applied to `rho = linePt tau`, supplies `m ∈ ℕ`,
`m ≥ 1`, such that

`x * F((linePt tau - 1) + x) → -(m : ℂ)` as `x → 0+`.

The residue-profile hypothesis gives the same function tending to `r tau`.  Uniqueness of limits
yields `r tau = -(m : ℂ)`, so `‖r tau‖ = m ≥ 1`, contradiction.  Therefore `r` is not cofinally
null.  If `r` were summable, `Summable.tendsto_cofinite_zero` would make it cofinally null, so no
summable radial residue profile exists. ∎ `[PROVED HERE]`

All dependencies are already unconditional Lean theorems: dyadic Hardy zeros, full critical-divisor
inheritance, finite-set sum domination, uniqueness of limits, and summability implying cofinite
decay.

## No-go closure

- **Exact killing theorem/mechanism:** Hardy zeros occur beyond every finite exceptional set and force negative-integer residues, preventing cofinite decay and summability.
- **Strongest positive survivor:** Every admissible radial residue profile fails `Tendsto r Filter.cofinite (𝓝 0)`; the proof witnesses this through norm-at-least-one residues at arbitrarily high Hardy-zero ordinates.
- **New insight:** Infinite singular support is insufficient for T2; any viable polar continuation must carry non-decaying, infinite-total-variation critical divisor mass.
- **Status:** Formalized in `XiHeatCassiniWoldNaturalAbelInfiniteResidueVariation.lean` as `woldNatAbelRadialResidueProfile_not_tendsto_cofinite_zero` and `not_woldNatAbelSummableRadialResidueProfile`. Direct Lean and targeted module build pass. Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.

## Log

- 2026-08-30 — created in 1-in-progress after corpus search and exact-route hostile audit.
- 2026-08-30 — `[PROVED HERE]`; dependency-closed paper proof completed.
- 2026-08-30 — formalized stronger cofinite non-decay theorem and summability no-go; direct Lean, targeted build, and axiom audit passed.
