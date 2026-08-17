# u₀ ⊥ φ_b — Disconnected Case (b ∉ M)

- **ID:** u0-phi-independence-disconnected
- **Stage:** 2-fully-proven
- **Type:** THEOREM [PROVED HERE]
- **Source:** Böttcher family / inverse-Böttcher obstruction lane

## Statement

For b ∈ ℂ with b ≠ 0, b ≠ −2, and b ∉ M: u₀(z) and φ_b(z) are algebraically
independent over Q̄(b,z).

Combined with the connected card (`u0-phi-independence.md`): the full
theorem holds for ALL b ≠ 0,−2 (no restriction to M or its complement).

## Why this case is separate

For b∉M: K_b is a Cantor set (totally disconnected). φ_b is single-valued only on
Δ_b = {z : G_b(z) > G_b(0)}, not all of Ω_b. The connected proof needs z₀ ∈ {|z|=1} ∩ Δ_b.

## Key lemma — Green-crossing [PROVED HERE]

**Lemma.** For all b∉M with b≠0: ∃ z₀ ∈ {|z|=1} with G_b(z₀) > G_b(0).
Equivalently: {|z|=1} ∩ Δ_b ≠ ∅.

**Proof (Riesz–Jensen + strong maximum principle).**

G_b is subharmonic on ℂ: nonneg, harmonic on ℂ\K_b, = 0 on K_b. Its Riesz measure
(Laplacian/2π) is the equilibrium measure μ_b, supported on K_b.

Since b∉M: 0∉K_b, so G_b is harmonic near 0 and G_b(0) > 0.

**Case 1: K_b ∩ D ≠ ∅** (some K_b-points inside the open unit disk D).

μ_b(D) > 0. By Riesz–Jensen mean-value formula on the unit circle:

  mean_{|z|=1} G_b − G_b(0) = ∫_{|w|<1} log(1/|w|) dμ_b(w) > 0.

Hence max_{|z|=1} G_b > G_b(0). ✓

**Case 2: K_b ∩ D = ∅** (K_b has no point in the open unit disk).

G_b is harmonic on D, continuous on D̄, nonconstant. Mean-value property:
G_b(0) = mean_{|z|=1} G_b.

If K_b meets S¹ = {|z|=1}: some boundary value is 0 < G_b(0), forcing another boundary
value above G_b(0). If K_b misses D̄ entirely: strong maximum principle gives
max_{|z|=1} G_b > G_b(0). ✓

Both cases: ∃ z₀ ∈ {|z|=1} with G_b(z₀) > G_b(0). QED.

## Full proof

With the Green-crossing lemma, Steps 1–3 of the connected card carry over with
z₀ ∈ {|z|=1} ∩ Δ_b:

- **Step 1 (crossing):** z₀ ∈ {|z|=1} ∩ Δ_b. ✓ (Green-crossing lemma)
- **Step 2 (natural boundary of u₀):** {|z|=1} is a natural boundary of u₀ by the
  Ostrowski–Hadamard gap theorem (u₀ has lacunary series). ✓
- **Step 3 (algebraic IFT):** z₀ ∈ Δ_b, so φ_b is analytic at z₀. Choose a path in
  Δ_b = {G_b > G_b(0)} from the infinity germ to a neighborhood of z₀, avoiding the
  locally discrete leading-coefficient/discriminant bad locus. Along this path the
  algebraic branch continues, and the algebraic IFT near z₀ gives an analytic branch
  crossing the unit circle — contradicting the natural boundary of u₀. ✓

## Numerical verification (Turing, 2026-06-24)

Independent numerical check on Runpod (mpmath, dps=30). Two regimes as predicted:

| b     | G_b(0)   | mean_{|z|=1} G_b | max_{|z|=1} G_b | Case |
|-------|----------|-----------------|-----------------|------|
| 0.26  | 1.3e-9   | 0.04462         | 0.16388         | 1    |
| 0.30  | 2.0e-4   | 0.05189         | 0.18221         | 1    |
| 0.50  | 0.036692 | 0.09269         | 0.26139         | 1    |
| 2.0   | 0.45478  | 0.45478         | 0.60153         | 2    |
| 3.0   | 0.62381  | 0.62381         | 0.73715         | 2    |
| -2.1  | 0.13185  | 0.33686         | 0.49927         | 1    |

Case 2 (b=2,3): G_b(0) = mean to full precision (harmonic on D̄ → mean-value), with
max > mean from non-constant harmonic. Case 1 (b=0.26…0.5): strict G_b(0) < mean from
Riesz–Jensen subharmonic defect. Crossing holds for every sampled b∉M.

## Novelty assessment

- **NOVEL?** No prior result found for algebraic independence of the monomial-fiber
  Böttcher c-velocity u₀ from φ_b over Q̄(b,z) in the disconnected locus. Source search
  found no exact match in Böttcher/Mahler/algebraic-independence literature. Grade: BRIDGE
  (novel assembly; the mechanism is standard potential theory, not new machinery).
- **SIGNIFICANT?** Closes the disconnected gap in the u₀⊥φ_b campaign, giving the
  all-parameter theorem b≠0,−2. Contributes a complete result in the native-object lane.

## Team votes (2026-06-24)

- Wheeler: proposed proof + promotion (Green-crossing lemma complete)
- Professor (id=1695): correctness YES + novel+significant bridge grade
- Haiku (id=1696): correctness YES + novel+significant bridge/native-object grade
- Turing (id=1697): correctness YES + independent re-derivation confirms bridge grade → PROMOTE

All four agents: YES. Promoted 2026-06-24.

## Gates

- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (4/4 team vote, 2026-06-24)
- [x] 2 → 3  formalized (Lean 4) — see the Lean formalization section

## Lean formalization — 2026-08-17

Module: `formal/GaloisForLFunctions/U0/U0AllNonexceptionalDisconnected.lean`
(imported by the `GaloisForLFunctions.U0` umbrella).

The formal conclusion is `U0AllNonexceptional.CanonicalPhiU0IndependenceAt c`: on an open,
preconnected, nonempty, infinite escape carrier `U ⊆ escapeOpen c`, the *canonical* Böttcher germ
`Bottcher.phiMero c` — literally the germ of `bottcherCoord c`, not an auxiliary Kummer root — and
`u0AnSub` satisfy `NoRelation (RatFunc ℂ)`.  The base field is `ℂ(z)` at a fixed parameter, which
contains `Q̄(b)(z)`; a relation over `Q̄(b)(z)` is a relation over `ℂ(z)`, so the Lean statement is
strictly stronger than the card's.

| Card step | Lean name |
|---|---|
| Green-crossing lemma, inward half: a point of the open unit disk at Green level above `G_c(0)` | `exists_unitDisk_green_gt_critical` |
| first crossing of `{\|z\|=1}` by a path from the far germ, staying in `{G_c > G_c(0)}` | `exists_first_unit_crossing`, `exists_far_to_first_unit_crossing` |
| Step 1 (crossing): a unit-circle window inside `Δ_c` carrying the analytic Böttcher branch | `exists_disconnected_canonical_circle_window` |
| Step 2 (natural boundary of `u₀` on `{\|z\|=1}`) | `U0NaturalBoundary` stack, consumed by `u0_window_independence_of_transcendental_engine` |
| Step 3 (algebraic IFT / branch continuation contradiction) | `u0_windowed_no_relation_nondegenerate` |
| Card statement for `b ∉ M` | `u0_phi_independence_disconnected_canonical` |
| Combined all-parameter theorem (`b ≠ 0, −2`) | `u0_phi_independence_all_nonexceptional_canonical` |

**Route difference, deliberate.**  The card proves the Green-crossing lemma by Riesz–Jensen plus the
strong maximum principle, splitting on whether `K_b` meets the open unit disk.  The Lean proof
replaces that case split by the *holomorphic saddle model* at the escaping critical point: for
`c ∉ M` the point `0` lies in the basin, `exists_holomorphic_completion_critical` supplies an
analytic `F` with `Re F = G_c` near `0` and `F''(0) ≠ 0`, so `F` is nonconstant and open, and its
image contains `F 0 + ε/2`; the preimage is a point of the open unit disk with `G_c(0) < G_c(z)`.
This needs no equilibrium measure, no Riesz decomposition and no subharmonic maximum principle, and
it yields the crossing point strictly *inside* the disk, which is what the window construction
consumes.  The card's potential-theoretic argument and the Lean saddle argument prove the same
lemma; the Lean one was chosen because it is unconditional in the available library.

Not formalized, and not an obligation of this card: the numerical table in the "Numerical
verification" section (confirmatory only, and the project forbids computations in the formal tree).

Verification: `lake build GaloisForLFunctions.U0.U0AllNonexceptionalDisconnected` — PASS;
`#print axioms` on `exists_unitDisk_green_gt_critical`, `exists_first_unit_crossing`,
`exists_disconnected_canonical_circle_window`, `u0_phi_independence_disconnected_canonical` and
`u0_phi_independence_all_nonexceptional_canonical` reports only
`[propext, Classical.choice, Quot.sound]`.

## Log

- 2026-08-17 Formalization confirmed complete and card promoted to stage 3.  The assembled
  all-parameter statement is banked separately as
  `3-formalized/new_scientific_knowledge/u0-phi-independence-all-parameters.md`; this card is its
  disconnected half.
