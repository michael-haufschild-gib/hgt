# MSC physical-zero half-density wall

- **ID:** MSC-HDW
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · MSC
- **Statement:** For `σ > 1`, squarefree-Möbius source coefficients are in `ℓ²` exactly when `Re u > -1/2`; every physical coordinate `uσ=(ρ-σ)/(σ-1)` with `Re ρ < 1` lies strictly outside this domain.

## Goal

Kill standard-`ℓ²` singular-graph MSC continuation to a fixed strict-right Xi zero. Chain: strict-right zero `ρ` → `Re ρ < 1` → `Re uσ < -1/2` for every `σ > 1` → physical source column is not square-summable → no ordinary Hilbert graph can evaluate, converge to, or annihilate that divisor fibre. No RH premise enters.

## Gates

- [x] 0 → 1  in-progress: corpus-derived, source-pure, exact prime-subseries proof
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module built, axiom audit standard-only
- [ ] 3 → 4  publication-ready: standalone theorem + Lean certificate + literature audit

## Approach

The coefficient norm-square equals squarefree mass at shifted exponent `a=σ+2u(σ-1)`, divided by positive total mass. If `u≤-1/2`, then `a≤1`; prime terms dominate `1/p`, hence diverge. Existing corpus proves summability for `u>-1/2`, giving an exact iff. For physical `uσ`, `Re uσ<-1/2` follows from `σ>1>Re ρ`.

**[PROVED HERE]** If `a≤1`, squarefree mass dominates the divergent squarefree transverse weight at exponent one. Multiplication by the positive finite normalization transfers this divergence to the damped source norm-square. Conversely the corpus Euler-half-plane theorem gives summability for `u>-1/2`; imaginary phase preserves every coefficient norm. Finally
`Re uσ=(Re ρ-σ)/(σ-1)<-1/2` because `σ>1>Re ρ`. Thus no `lp(ℕ,ℂ,2)` vector can have the physical source coefficients.

## No-go closure

- **Exact killing theorem/mechanism:** physical fixed-divisor coordinate crosses the sharp squarefree-Möbius `ℓ²` abscissa at every finite `σ>1`, not merely in the cofinal limit.
- **Strongest positive survivor:** maximal source domain is exactly the open half-plane `Re u>-1/2`; algebraic regular-germ/residue laws survive only in a rigged or distributional completion.
- **New insight:** singular graph normalization fixes gain but cannot repair source-domain loss; standard Hilbert graph convergence and divisor landing are incompatible objects.
- **Status:** formalized in `RHTower/HedenmalmGammaSewnSquarefreeFisherPhysicalHilbertWall.lean`; targeted build passed; `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired. Corpus audit found no prior converse/application, and targeted arXiv audit through 2026-08 found no physical-zero/domain incompatibility theorem. Global lint remains blocked only by pre-existing unreachable modules, none from this result.

## Log

- 2026-09-01 — formalized exact source domain and ordinary-Hilbert MSC no-go.
