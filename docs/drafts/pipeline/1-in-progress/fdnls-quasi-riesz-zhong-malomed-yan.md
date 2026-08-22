# FDNLS with the quasi-Riesz derivative (Zhong–Malomed–Yan, arXiv:2407.12441)

- **ID:** fdnls-quasi-riesz
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** arXiv:2407.12441v1, "Dynamics of discrete solitons in the fractional discrete nonlinear
  Schrödinger equation with the quasi-Riesz derivative", M. Zhong, B. A. Malomed, Z. Yan.
- **Statement:** Formalize, unconditionally and closed, every analytical (non-numerical) statement of
  the paper in Lean 4 inside `GaloisForLFunctions.HTGeometry.FDNLS`.

## Goal
The paper is a physics paper whose analytic core is a small, sharp, fully rigorous package:
an exact Fourier-multiplier definition of a discrete fractional Laplacian on `ℤ`, its coupling
coefficients, their closed forms at `α = 1, 2`, their large-distance asymptotics, an exact
dispersion relation, the conserved quantities, the anti-continuum limit and its Bogoliubov spectrum,
a staggering symmetry, a scaling reduction, and a dipolar-chain realization integral.  None of it is
in the corpus.  Formalizing it adds a reusable discrete-Fourier-multiplier layer (lattice Fourier
transform, cosine coefficients of `|k|^α`, absolute summability of those coefficients) that the
corpus does not own.

## Inventory of formalization targets (paper equation numbers)

| # | Paper | Content | Status |
|---|---|---|---|
| T1 | (10) | `D_ℓ^{(α)} = (1/π)∫_0^π cos(ℓk) k^α dk`; evenness in `ℓ`; `D_0 = π^α/(α+1)`; vanishing at `α = 0` for `ℓ ≠ 0` | |
| T2 | (10') | integration-by-parts form `D_ℓ^{(α)} = -(α/(πℓ))∫_0^π sin(ℓk)k^{α-1}dk`, `ℓ ≠ 0` | |
| T3 | (11) | `α = 2`: `D_0 = π²/3`, `D_ℓ = 2(-1)^ℓ/ℓ²` | |
| T4 | (14) | `α = 1`: `D_0 = π/2`, `D_ℓ = ((-1)^ℓ - 1)/(πℓ²)` (0 at even `ℓ ≠ 0`) | |
| T5 | — | uniform bound `|∫_0^π sin(ℓk)k^{α-1}dk| ≤ (2π+3)ℓ^{-min(α,1)}` and absolute summability of `D_·^{(α)}` | |
| T6 | (9) | operator identity: the Fourier multiplier `|k|^α` acts on finitely supported lattice data as `∑_ℓ D_ℓ u_{n+ℓ}` | |
| T7 | (32)(33) | **the dispersion relation** `∑_{ℓ∈ℤ} D_ℓ^{(α)} cos(ℓk) = |k|^α` on `[-π,π]` | |
| T8 | (34)(35)(38) | `ω(0) = 0`, `ω(π) = Cπ^α`, band `0 ≤ ω ≤ Cπ^α` | |
| T9 | (36)(37) | `∑_{ℓ≥1} sin(ℓk)/ℓ = (π-k)/2` (corpus already owns it) and `∑_{ℓ≥1}(-1)^ℓ sin(ℓk)/ℓ = -k/2` | |
| T10 | (39) | group velocity `dω/dk = Cα|k|^{α-1}sgn k`, and its blow-up at `k → 0` when `α < 1` | |
| T11 | (17)(18) | conservation of power and Hamiltonian along the FDNLS flow | |
| T12 | (21) | the staggering transform at `α = 1` exchanges `σ = +1` and `σ = -1` | |
| T13 | (27) | the scaling reduction to `ω = -1` | |
| T14 | (40) | anti-continuum limit: `(|v|²-1)v = 0 ⟺ v = 0 ∨ |v| = 1` | |
| T15 | (41) | anti-continuum Bogoliubov spectrum: nilpotent double zero at every excited site, `λ = ±i` at every empty site | |
| T16 | (28)–(30) | the Bogoliubov–de Gennes linearization is the exact first-order term | |
| T17 | (23)(24) | non-commutativity: `ω(k) = Ck²` differs from the nearest-neighbour `2C(1-cos k)` | |
| T18 | (12) | `α ∈ (0,1)`: `ℓ^{α+1}D_ℓ → -(αΓ(α)/π)sin(πα/2)` (needs the Mellin sine transform) | |
| T19 | (13) | `α ∈ (1,2]`: `(-1)^ℓ ℓ² D_ℓ → απ^{α-2}` | |
| T20 | (31) | dipolar chain energy `E = -m₁m₂ sinθ₁ sinθ₂/(2πL²)` | |
| T21 | (42)(43) | the Peierls–Nabarro free-energy barrier `ΔG = ΔH - ω ΔP` | |

Cited-but-not-proved external inputs (MacKay–Aubry continuation [64], discrete Sturm–Liouville [71],
Krein-signature collision theory [78–80]) are not results of this paper; a self-contained
implicit-function continuation from the anti-continuum limit is a stretch target.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven on paper
- [ ] 2 → 3  formalized in Lean
- [ ] 3 → 4  publication-ready

## Approach
`HTGeometry/FDNLS/` subtree.  Bottom-up: coupling coefficients → closed forms → decay bound →
summability → `AddCircle (2π)` Fourier inversion for `|k|^α` → dispersion relation → band, group
velocity → dynamics (conservation, staggering, scaling) → anti-continuum spectrum → asymptotics
(needs `∫_0^∞ s^{α-1} sin s ds = Γ(α) sin(πα/2)`, a mathlib gap) → dipolar realization.

## Log
- 2026-08-22 — created; paper read in full; corpus searched (no overlap; the sawtooth series (36) is
  already owned by `RHTower.SawtoothFourierSeries`).
