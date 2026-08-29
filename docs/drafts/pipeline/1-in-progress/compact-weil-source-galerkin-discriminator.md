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
- [x] 2 -> 3: exact principal-tower survivor formalized; main C1/C2 sign burden remains open
- [ ] 3 -> 4: publication-ready note

## No-go closure

- **Exact killing theorem/mechanism:** The proposed universal carrier `E(x) >= 0` is impossible.
  Suzuki's cited Littlewood oscillation for `psi_(1/2)(x) - 2 sqrt(x)`, together with the decaying
  endpoint/half-jump correction, forces the completed error `E` to take both signs eventually.
  Computation through `10^11` found no negative value, exposing a deceptive finite-range bias.
- **Strongest positive survivor:** C1 survived all 66 source-matrix cases. C2 survived as a
  ground-specific statement, but cannot be obtained from global pointwise positivity of `E`.
  The exact centered principal-submatrix tower is unconditionally formalized in
  `CCMPublishedRestrictedWeilPrincipalTower.lean`.
- **New insight:** Route O must control an autocorrelation-weighted average of the oscillatory
  completed error against the source-selected positive lag density `-dC`, not the raw completed
  error pointwise. Exact published-matrix-to-abstract-Galerkin identification remains the missing
  Lean connector.
- **Status:** active; universal raw-carrier subroute retired, ordered-ground subroute survives

## Log

- 2026-08-29 — Card frozen before computation. C1 and C2 will be attacked on RunPod using only the
  literal source-side published matrix.
- 2026-08-29 — Completed 66 high-precision matrices and completed-error event scan through `10^11`.
  C1/C2 survived numerically. Literature kills universal `E >= 0`; retained ground-weighted escape
  and formalized exact principal nesting. Full report and raw artifacts are in
  `2-fully-proven/computations/2026-08-29-compact-weil-source-galerkin/`.
