# CCM all-frequency cofinal scalar-wall no-go

- **ID:** CCM-AF-COFINAL-SCALAR-WALL
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` (read-only) · shared HB/FZZ-P/PW-B/RBH Ward chain
- **Statement:** Every continuous real scalar faithful to one literal prime-power all-frequency reporter has zeros above every bound; hence no eventually nondegenerate scalar carrier exists.

## Goal
Kill bounded/finite singular-gluing repairs at the producer step
`source sign/gluing -> Ward orientation -> shared four-route endpoint -> RH`.

## Gates
- [x] 0 → 1  in-progress: exact source reporter, attack, and proof-chain passport fixed
- [x] 1 → 2  fully-proven: dependency-closed paper proof below; `[PROVED HERE]`
- [x] 2 → 3  formalized: Lean theorem, target build, axiom audit
- [ ] 3 → 4  publication-ready

## Approach
For `n = p^(e+1)`, put `L = log n > 0`. Corpus gives
`R_n(xi)=exp(2 A_n(xi))`, where
`A_n(xi)=cos(2*pi*L*xi) C_n(xi)+sin(2*pi*L*xi) S_n(xi)` and
`C_n(xi)>0` for `xi != 0`. For every `k : Nat`, set
`a_k=(k+1/2)/L`, `b_k=(k+1)/L`. Then
`A_n(a_k)<0<A_n(b_k)`, so the exact Boolean reporter is false at `a_k` and true at
`b_k`. Also `a_k<b_k` and `a_k -> +infinity`.

If continuous `c : Real -> Real` has the same Boolean orientation, then
`c(a_k)<=0<c(b_k)`. Given any bound, choose `k` with `a_k` above it. The intermediate
value theorem gives `x in [a_k,b_k]` with `c(x)=0`, still above the bound. Therefore
the zero set is cofinal. In particular, a carrier continuous and nonzero on some tail
cannot be reporter-faithful.

Novelty audit (31 August 2026): the internal corpus has only the two-frequency sign straddle and
connected metric-line obstruction; no cofinal alternation or tail-regular scalar theorem. Suzuki
2023/2026 and Connes--Consani--Moscovici 2025 contain screw/Weil positivity and spectral-limit
programs, but no reporter-orientation, connected-component, or reduced-`H0` transport theorem.

## No-go closure
- **Exact killing theorem/mechanism:** cofinal half-period alternation plus IVT forces unbounded singular walls.
- **Strongest positive survivor:** faithful continuous scalar realization has a cofinal zero set.
- **New insight:** finite, compactly supported, or eventually regular scalar repairs cannot supply the source Ward sign. A survivor needs cofinal singular/discontinuous walls or phase-sensitive non-scalar data.
- **Status:** formalized in `CCMActualHeadMatchedAllFrequencyCofinalScalarWallNoGo.lean`; direct check, target build, and axiom audit passed. Axioms: `propext`, `Classical.choice`, `Quot.sound` only. Global lint is non-green only for unrelated unwired modules.

## Log
- 2026-08-31 — `[PROVED HERE]` on paper after corpus-first and parent-literature audits.
- 2026-08-31 — formalized; target build and axiom audit passed.
