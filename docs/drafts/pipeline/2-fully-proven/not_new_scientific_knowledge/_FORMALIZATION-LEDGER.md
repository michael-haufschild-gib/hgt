# Stage-2 → stage-3 formalization ledger — `not_new_scientific_knowledge`

Scope: every card in this folder must have its proven theorems formalized unconditionally in Lean 4
and then move to `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/`.

Folder size at sweep start (2026-08-16): **496** top-level cards, no subfolders.

## Working rules

- No added hypotheses standing for analytic inputs; no axioms; no `sorry`.
- Search the corpus first (`scripts/formal_tools.py research`, `rg`) before writing any new module —
  ~29 700 Lean files already exist.
- Check with `lake env lean <file>`; build only the oleans needed; wire new modules into the area
  umbrella but never build the umbrella.
- Audit axioms in a scratch file (`#print axioms`), expect only
  `propext`, `Classical.choice`, `Quot.sound`.
- One Lean process at a time; clean up stale processes.

## Promoted

| Date | Card | Lean module(s) |
|---|---|---|
| 2026-08-16 | `co6-involution-host-caveat` | `HTGeometry/InvolutionIdempotentHost.lean` |
| 2026-08-16 | `unbounded-one-coordinate-monodromy-obstruction` | `HTGeometry/ScalarMonodromyAlgebraicIndependence.lean` |
| 2026-08-16 | `suzuki-one-prime-fractional-carrier` | `RHTower/SuzukiOnePrimeFractionalCarrier.lean` (pre-existing) |
| 2026-08-16 | `endpoint-sheared-gram-ridge-parity` | `RHTower/EndpointShearedGramRidgeParity.lean` (+ `Z/2Z` sharpness witness) |
| 2026-08-16 | `finite-wick-contracted-interaction-matroid` | `HTGeometry/WickInteractionMatroidLabels.lean` (+ contraction rank law) |
| 2026-08-16 | `one-sided-compression-bound-not-bounded-operator` | `RHTower/OneSidedCompressionUnbounded.lean` |
| 2026-08-16 | `shifted-towers-do-not-fix-t0-tail-class` | `RHTower/ShiftedTowerTailClasses.lean` |

## Already carrying a stage-3 certificate (verify, then move the paper card)

- `square-aperture-von-mangoldt-correlation-energy` — forward implication and exact identity are
  formalized (`RHTower/CCMSharpPrimeWindowSquareCorrelationEnergy.lean`, axiom-clean). **Open gate:**
  the reverse implication `RH ⇒ C_M = O_δ(M^{1+δ})` needs a formal von Koch–Schoenfeld bound
  `|ψ(x) − x| ≪ √x log²x` under RH. Nothing weaker than `ψ(x) − x = O_ε(x^{1/2+ε})` is required.
- `universal-typed-event-network-fixed-carrier-no-go` — `HTGeometry/EventNetworkFixedCarrier.lean`
  covers the algebraic no-go; `HTGeometry/TraceClassQuantumCorner.lean` covers certified corners.
  **Open gate:** the literal Hilbert direct-sum corner must be proved completely positive, normal
  and trace-nonincreasing (i.e. construct a `TraceClassQuantumCorner` instance for
  `⊕^{ℓ²} H_i` with its inclusion isometries). The last card gate (monoidal-locality obstruction)
  is an open research target, not debt.

## Known blocking infrastructure (shared across several cards)

1. **von Koch–Schoenfeld**: `RH → |ψ(x) − x| ≤ √x log(x)²/(8π)` for `x > 73.2`, or any
   `O_ε(x^{1/2+ε})` form. Blocks the reverse half of several RH-equivalence cards.
2. **Riemann–von Mangoldt zero counting** `N(T) = O(T log T)`: needed by
   `reciprocal-seam-t0-infinite-mass-obstruction` (convergence of `Σ|ρ−1/2|^{-2k}` for `k ≥ 1`).
3. **Hadamard factorization for finite-order entire functions** (zero-free ⇒ `exp(polynomial)`):
   needed by `involutive-reflection-quadratic-rigidity`.
4. **von Neumann algebra generation** (`W*(S)` for a set of operators, and
   `W*(D, H_x) = B(ℓ²)`): needed by `additive-heat-diagonal-generates-full-operator-algebra`.
   mathlib has `VonNeumannAlgebra` but no generated-algebra API.
5. **Derived inverse limits** (`R lim` of a diagram of zero objects): needed by
   `acyclic-finite-fibers-derived-limit-zero`.
6. **Complex-dynamics layer** (Böttcher coordinate, equilibrium measure of a Cantor Julia set,
   winding-number integration): needed by the three `bottcher-*` monodromy cards.

## New reusable infrastructure added by this sweep

- `HTGeometry/InvolutionIdempotentHost.lean` — self-inverse elements ↔ idempotents over a
  commutative ring with `2` invertible.
- `HTGeometry/ScalarMonodromyAlgebraicIndependence.lean` — unbounded scalar monodromy forces
  transcendence over a fixed subalgebra.
- `HTGeometry/WickInteractionMatroidLabels.lean` — **`contract_eRk_add_eRk_eq`, the relative-rank
  law for matroid contraction (a mathlib gap)**, plus the labeled algebraic matroid layer.
- `RHTower/OneSidedCompressionUnbounded.lean` — diagonal inner products of a bounded operator are
  bounded by the operator norm; `ℓ²(ℕ)` basis layer.
- `RHTower/ShiftedTowerTailClasses.lean` — exponential-scale summability comparison and three
  separated weight classes.

## Triage snapshot

- 83 cards carry no open gate box at all (status must be read from the prose).
- 165 cards mention at least one Lean module that already exists in `formal/`.
- 330 cards mention no Lean module at all.
