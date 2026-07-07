# 104 — The weight the multiplicative truncation cannot carry

Formal home: `formal/GaloisForLFunctions/RHTower/EulerTruncationRigidity.lean`
(all endpoints axiom-clean: `[propext, Classical.choice, Quot.sound]`).

Builds the σ_p-side input the base rung was missing: the arithmetic of the finite
truncations, in the one form that is neither steerable nor a re-expression of the
functional equation. It is the answer to doc 126 §5's demand.

## 1. Two truncation families of the same ζ

Both converge to ζ, and they carry opposite monodromy:

- **additive** `emCarrier N s = Σ_{n≤N} n^{−s} + N^{1−s}/(s−1)` — the completed member
  `completedEM N` dominates ξ on an isolating annulus and there carries exactly
  `ord_ρ ξ` hole-zeros (doc 111, 126). Its deck weight around a hole is `exp(2πi·m/N)`,
  of order `m`. This is the order-linked side.
- **multiplicative** `eulerPartial P s = ∏_{p∈P} (1 − p^{−s})⁻¹` — the reciprocal of the
  finite Euler head `eulerHeadAnchor`. This module is its arithmetic.

## 2. The multiplicative truncation is rigid [PROVED HERE]

- `eulerPartial_ne_zero`: **zero-free on the entire right half-plane `Re s > 0`** — not
  just the convergence region `Re s > 1`, but through the wall `Re s = 1` and across the
  whole critical strip. The proof is one line of arithmetic: `|p^{−s}| = p^{−σ} < 1` for
  `σ > 0`, so `1 − p^{−s}` sits in the disc `|w−1|<1 ⊂ {Re w > 0}` (`re_one_sub_natCast_cpow_pos`)
  and never vanishes; a finite product of nonzero factors is nonzero.
- Consequence — **the strip zeros of ζ are emergent**: present at no finite multiplicative
  level, they can appear only in the limit, and exactly where the finite family stops
  converging locally uniformly. The zeros live where the σ_p construction breaks; this is
  the "constraint, not flow" picture of §4.1 of `00-approach.md`, now a machine-checked
  finite fact rather than a slogan.

## 3. The free Kummer tower on the σ_p side [PROVED HERE]

- `exists_global_pow_root_eulerPartial`: for **every** `k`, `eulerPartial P` has a
  single-valued analytic `2^k`-th root on all of `Re s > 0`, unconditionally. Built
  explicitly, factor by factor: `eulerRootFactor k p s = exp(−log(1−p^{−s})·2^{−k})`, whose
  base `1 − p^{−s}` avoids the branch cut (`one_sub_natCast_cpow_mem_slitPlane`), so the log
  is analytic; `eulerRootFactor_pow` checks it raises to the factor. The Kummer tower is
  **free** on the multiplicative side: trivial monodromy at every point, no divisibility
  condition on anything.

Contrast with ξ (approach doc §3.3, root form): `ξ` has a global `2^k`-th root on the
*smaller* half-plane `Re s > 1/2` **iff** every strip zero's multiplicity is divisible by
`2^k` (RH_{2^k}). The multiplicative truncation has one on the *larger* `Re s > 0` with no
condition at all. `euler_tower_free_but_xi_tower_costs` states this dichotomy: the
unconditional σ_p side, and the ξ side pinned to `2^k ∣ zs.length`, i.e. `RHLadder k`.

## 4. Landau positivity: the arithmetic source [PROVED HERE]

Why is the σ_p tower free while ξ's costs RH? Because the exponent generating it is
**positive**, not merely even:

- `neg_log_euler_base_hasSum`: `−log(1 − p^{−s}) = Σ_{n≥1} (p^{−s})^n/n` (Mercator). Each
  `(p^{−s})^n = p^{−ns}` is a Dirichlet monomial at the prime power `p^n` with coefficient
  `1/n ≥ 0`. The tower's log-exponent is a **nonnegative-coefficient Dirichlet series** —
  Landau positivity in finite form.
- `neg_log_euler_base_re_nonneg`, `eulerRootFactor_real_ge_one`: on the real axis the
  exponent is a nonnegative real and the tower factor is real and `≥ 1`. The tower inherits
  the truncation's dominance from the *coefficient positivity*, not from any symmetry.

This is the crux distinction from the dead parity route. Parity is symmetry-blind: off-line
zeros come in mirror pairs, contribute even counts, and a mod-2 count can never see them
(doc 121, Gate 4). **Positivity is oriented** — a strictly stronger invariant than a mod-2
count — and it is exactly the invariant the σ_p side supplies for free.

## 5. The weight mismatch, pinned [PROVED HERE]

`euler_additive_weight_mismatch`: at any strip point `ρ`,

- the multiplicative truncation `eulerPartial P` does **not** vanish (trivial local weight,
  tower single-valued);
- if `ξ(ρ) = 0`, the additive completed member of **every** dominating split vanishes to
  order `zs.length = ord_ρ ξ ≥ 1` (`emSplit_length_pos_at_xi_zero`), deck weight
  `exp(2πi·zs.length/N)`, of positive order.

Two finite families of the same ζ, structurally incompatible weights at the same pinned
point: one trivial, one of order `m`. The base-rung parity `2 ∣ m` is therefore **not** a
re-expression of `ξ = ξ(1−·)` — it is a compatibility condition between two truncation
weights, exactly the object the Gate-4 fork demanded (one invariant, an order-linked reading
and a structurally-pinned reading). Everything is at one pinned point; no `N` or `P` flows.

## 6. Where the obstruction now sits

The map is sharp. Right of the wall `Re s > 1`, the σ_p side is freely and positively
towered at every finite level. Right of the line `Re s > 1/2`, ξ is towered iff RH_{2^k}.
The gap between the two — the strip `1/2 < Re s < 1` — is where the whole obstruction lives,
and its content is now named exactly: **does the finite Landau positivity of §4 have a
`mod 2^k` shadow that survives pole subtraction across the wall `Re s = 1`?** (approach doc
§4.1, Arc B2). The positive exponent is manifest at finite level; the question the lane now
opens is whether that positivity — not the FE, not the count parity — is what forbids the
order-`m` additive weight from reconciling with the trivial multiplicative weight inside the
strip. That is a constraint at a pinned annulus (the incompatibility of two weights at one
`ρ`), read through the positivity rather than through any flow in the truncation length —
the next object to construct on this ground.
