# Borel–Weil (and Borel–Weil–Bott) in Lean 4

- **ID:** borel-weil-bott
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** user goal, 2026-08-21
- **Statement:** For `G = SL(N,k)` with `k` an infinite field, `B` the standard Borel, and a weight
  `λ`, the space `H⁰(λ) = { f ∈ k[G] : f(gb) = χ_λ(b) f(g) }` of global sections of the associated
  line bundle on `G/B` is nonzero exactly for dominant `λ`, is finite dimensional, and (in
  characteristic zero) is the irreducible `G`-module of highest weight `λ`.

## Goal
Mathlib has no Borel–Weil, no flag varieties, no algebraic groups, no highest weight theory and no
sheaf cohomology of line bundles.  The corpus has none either (checked 2026-08-21 by
`scripts/formal_tools.py research` and greps over `formal/`, `docs/`).  So the whole development is
built here from scratch.

Formulation: the *associated-bundle* description of the sections of `L_λ = G ×^B k_λ` on `G/B`,
i.e. `ind_B^G λ`.  This is the standard algebraic definition (Jantzen, *Representations of
Algebraic Groups*, II.2) and avoids scheme-theoretic sheaf cohomology entirely.  Regular functions
on `SL(N,k)` are realized concretely as polynomial functions of the matrix entries, which is
faithful because `k` is infinite.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven on paper
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Layers (Lean modules under `formal/GaloisForLFunctions/HTGeometry/BorelWeil/`)

| Module | Content | Status |
|---|---|---|
| `RegularFunctions` | `regularFun n k`, translation stability | DONE |
| `BorelSubgroup` | `borel n k`, `borelChar` | DONE |
| `Sections` | `bwSections lam`, `bwRep` (left translation representation) | DONE |
| `PrincipalMinors` | `truncate`, `leadingMinor`, Borel semi-invariance | DONE |
| `Realization` | `bwVector`, `weightOfMult`, non-vanishing for dominant `λ` | DONE |
| `BlockAlgebra` | `blk` `2×2`-block calculus inside `Matrix n n k` | DONE |
| `RootSL2` | root `SL₂` elements + Bruhat identity | DONE |
| `PolynomialCurve` | regular functions along affine curves are polynomials | DONE |
| `PolynomialInversion` | degree bookkeeping for `x^d q(x) = r(-x⁻¹)` | DONE |
| `Vanishing` | `bwSections lam = ⊥` for non-dominant `λ` | DONE |
| `Dominance` | `bwSections lam ≠ ⊥ ↔ Antitone lam` | DONE |
| `BigCell` | injectivity of restriction to the opposite big cell | TODO |
| `FiniteDimensional` | `dim H⁰(λ) < ∞` | TODO |
| `HighestWeight` | weight vectors, `dim H⁰(λ)^{U⁻} = 1` | TODO |
| `Irreducible` | irreducibility of `bwRep λ` in characteristic zero | TODO |
| `Bott` | higher cohomology, dot action, rank-one case | TODO |

## Approach
1. Non-vanishing: `Δ_λ = ∏_j (leading j×j minor)^{m_j}` is a section, `Δ_λ(1) = 1`.  DONE.
2. Vanishing: rank-one Bruhat + polynomial degree bookkeeping.  DONE.
3. Finite dimensionality: a section is determined by its restriction to the opposite unipotent
   `U⁻` (density of the big cell `U⁻ B`), and that restriction has bounded degree.
4. Irreducibility: `dim H⁰(λ)^{U⁻} = 1` plus complete reducibility in characteristic zero.
5. Bott: rank-one higher cohomology with the `ρ`-shifted dot action.

## Log
- 2026-08-21 — created; layers 1–11 formalized and green under `lake env lean`.
