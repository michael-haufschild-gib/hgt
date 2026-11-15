# Order-six metaplectic theory over ℚ(ω) (OSM)

- **ID:** osm
- **Stage:** 1-in-progress
- **Type:** programme card (goal loop)
- **Source:** docs/reports/review-1511/obstacles-summary.md §2.9 ("unbuilt programme: order-six metaplectic theory over ℚ(ω)"); J6, O2, O3
- **Statement:** develop the order-six Kubota series of the row root numbers `Φ = Gγ₂²` (continuation, functional equation, residue, remainder uniformly in the column), the sextic large sieve, the tower; decide success (curve reaches 2/3) or kill (irremovable main term `U^{2/3}`).

## Goal
README: `formal/GaloisForLFunctions/OrderSixMetaplecticTheory/README.md` (questions Q1–Q8). Lean in
`formal/GaloisForLFunctions/OrderSixMetaplecticTheory/`, umbrella `OrderSixMetaplecticTheory.lean`.

## Gates
- [x] 0 → 1 in-progress: README draft, questions, thesis "order six is the square of order three"
- [ ] 1 → 2 fully-proven: per conjecture below
- [ ] 2 → 3 formalized: per module

## Approach
Thesis: Hasse–Davenport makes every first moment of order six a twisted Rankin–Selberg convolution of
the cubic theta function on the cubic cover (STCC engine). Order of attack:
1. Bridge `γ₂ = normalizedCubicUnitGauss`; row-root series = conjugate twisted squarefree theta-square
   series (column 1). Transfer of STCC's simple pole: a coherent main term at `2/3`.
2. Columns: `Φ_n(c) = (n/c)₃(n/c)₂Φ(c)`; cubic part = shift `T(nc)T(1) = (n/c)₃T(n)T(c)`.
3. Isolation of the untwisted squarefree series: `O/3O` translates of θ_s normalize `Γ(3)` and keep κ;
   `(1/9)Σ_τ C_τ` projects onto `ν ∈ 3O` (layers `m ≥ 2`, constant term included); `D − (1/9)Σ_τ C_τ`
   is the unit layer `2Σ_I T(gen I)²…` = `S_1` times `Z₀(3w−1)`. Double poles of `C_τ` from the cusps fixed by
   the translation.
4. Smoothed first moments: incomplete Eisenstein series with entire rapidly decaying Mellin transform,
   polynomial growth of the resolvent pairing (`‖R(λ)‖ ≤ 1/|Im λ|`), contour shift to `Re s = 1 + ε`;
   squarefree part through `1/Z₀(3w − 1)` and the seed.
5. Sextic large sieve (Heath-Brown recursion at order six).

## Paper notes

**N1 [D] Bridge.** `residueAdditive 3 c d = tracePhase(d/(traceLambda·c))` and `principalTraceChar c d =
exp(2πi Tr(d/(traceLambda c)))`: the two additive normalizations agree, so `γ₂(c) = normalizedCubicUnitGauss c`.
With `σ(A) = ((9/a)₃ \overline{γ₂(a)})²` (STCC `thetaSquareWeight`): `Φ(a) = G(a)(9/a)₃²\overline{σ(A)}`, i.e.
`σ(A) = G(a)(9/a)₃²\overline{Φ(a)}` on odd squarefree `A`.

**N2 [D] Budget readings at `n = 6`.** Broken branch `θ(R) = (96R − 34)/(5(12R + 1))`, half-plane
`½ + (5/12)θ`. `R = 2/3 ↦ 7/9`, `R = 5/8 ↦ 77/102`, `R = ½ ↦ 2/3`. If the squarefree first moment has
remainder `(1 + Θ)/3` (cube convolution, zeros of `ζ_K` at `3w − 1`) uniformly in the columns and the main
term is harmless, the map `Θ ↦ ½ + (16Θ − 1)/(6(5 + 4Θ))` has the fixed point `(√337 − 1)/24 ≈ 0.7232`
(model only: both premises open).

## Conjecture ledger
- C1 (open, Lean target): bridge + row-root series = conjugate twisted `S_{h₀}`; main term at `2/3` for the combination.
- C2 (open): column `n` = shifted Rankin–Selberg `Σ T(nc)T(c)` twisted by `(n/·)₂`.
- C3 (open): isolation of `S_1` by the `O/3O` translation correlations; residue in closed form.
- C4 (open): smoothed asymptotic for `Σ T(ν)² W(N(ν)/X)` with remainder `X^{½+ε}`.
- C5 (open): smoothed squarefree first moment with remainder `X^{(1+Θ)/3+ε}`.
- C6 (open): sextic large sieve `(M + N + (MN)^{2/3})(MN)^ε`; below `(MN)^{2/3}`?

## Lean modules
| Module | Content | State |
|---|---|---|

## Log
- 2026-11-16 — created; README first draft.
