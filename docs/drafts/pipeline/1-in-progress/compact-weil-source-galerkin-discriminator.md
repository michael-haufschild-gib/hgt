# Compact-Weil source-Galerkin discriminator

- **ID:** route-o-source-galerkin-discriminator
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md`, Route O
- **Statement:** Exact published Laurent-Galerkin ground states have enough lag-space order to force the literal prime-polar-Gamma form nonnegative.

## Goal

Attack Route O's source-selected finite-head inequality using the literal geometric-side matrix,
not a zeros-side surrogate. The corpus already proves convergence of abstract Laurent-Galerkin
floors and separately formalizes the published finite source matrix. This card tests structural
inequalities that could make the finite source matrix positive for every aperture and rank.

## Frozen conjectures

Let `L = 2a`, let `M_(a,N)` be the published centered Laurent matrix, and let `v` be a normalized
lowest even eigenvector. Let `C_v(h)` be the zero-extended autocorrelation of its Laurent packet,
normalized by `C_v(0)=1`.

1. **C1 (ordered ground autocorrelation).** `C_v(h) >= 0` and `C_v` is nonincreasing on `[0,L]`.
2. **C2 (cumulative polar domination).** For `F_v = 2 C_v` and every `H in [0,L]`,
   `integral_0^H 2 cosh(h/2) F_v(h) dh >= sum_(log k <= H) Lambda(k) F_v(log k)/sqrt(k)`.

C1 would supply an arithmetic-compatible cone absent from generic autocorrelations. C2 would turn
the dangerous prime atoms into a cumulative Stieltjes comparison against the polar carrier. Their
combination would materially sharpen the remaining Gamma/source-head inequality. Failure of either
conjecture must be localized and replaced by the strongest surviving integrated or parity law.

## Hostile attack

- Construct source, diagonal, and full matrix directly from the published polar, von Mangoldt, and
  archimedean formulas at high precision.
- Verify closed special-function formulas against independent quadrature on selected modes.
- Diagonalize increasing centered packets for several apertures; check inter-rank stability.
- Search dense lag grids for negative autocorrelation, upward excursions, cumulative polar-prime
  deficits, parity leakage, and component cancellation.
- Compare no numerical result with Lean premises. Computation only kills, opens, or sharpens routes.

## Exact analytic opportunities

- The endpoint value of the Gamma quotient is already an unconditional first-jet theorem in Lean.
- A missing corpus connector remains: identify the published source matrix with the convergent
  abstract Laurent-Galerkin operator. This is useful independently of any numerical sign.
- Any counterexample to C1 or C2 should yield an unconditional finite-dimensional decomposition or
  boundary law suitable for Lean formalization without importing its numerical witness.

## Gates

- [x] 0 -> 1: source-pure, exact matrix, falsifiable claims, hostile scan
- [ ] 1 -> 2: dependency-closed survivor/no-go with paper proof
- [ ] 2 -> 3: unconditional Lean theorem, targeted build and axiom audit
- [ ] 3 -> 4: publication-ready note

## No-go closure

- **Exact killing theorem/mechanism:** pending computation and analytic extraction
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** active

## Log

- 2026-08-29 — Card frozen before computation. C1 and C2 will be attacked on RunPod using only the
  literal source-side published matrix.
