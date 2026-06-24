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
- [ ] 2 → 3  formalized (Lean 4, future)
