# Asymptotic prime support of the bounded nonnegative Weil cone

- **ID:** MC-182
- **Stage:** 3-formalized (STATUS MUST-616)
- **Type:** THEOREM (Lean)
- **Source:** MC conjecture loop cycle 182; builds on MC-181 (MUST-614)
- **Statement:** If `lam ≥ 0` is full-cone Weil-positive and `lam(n) ≤ K(1 + Λ(n))` for non-prime `n ≥ 2`, then `(Σ_{n≤N, n not prime} lam(n)/n)/log N → 0`.

## Goal
MUST-614 gives finite mass on each `pℕ`. Summing over `p ≤ z` and adding a sieve bound for `z`-rough integers removes all composite mass at the harmonic scale. With pinning, the bounded nonnegative cone is asymptotically prime-supported. The uniqueness question for such producers reduces to prime deviations, i.e. the `α ≥ 1` regime of the MC loop and HF.

## Paper proof
1. **Rough sums:** `R_z(N) = Σ_{n≤N, P⁻(n)>z} 1/n ≤ (1 + 2 log N)/log(z+1)` for `1 ≤ z ≤ N`. The map `(n, s) ↦ ns` on (`z`-rough `n ≤ N`) × (`1 ≤ s ≤ z`) is injective, since `s` is coprime to every `z`-rough integer. Its image lies in `[1, Nz]`, so `R_z(N) · H_z ≤ 1 + log(Nz) ≤ 1 + 2 log N`, and `H_z ≥ log(z+1)`.
2. **Splitting.** A non-prime `n ≥ 2` with a prime factor `p ≤ z` lies in `pℕ` with `n > p`. Its mass is at most `Σ_{p≤z} Σ_{p∣n, n>p} lam(n)/n =: B_z < ∞` (MUST-614). Otherwise `n` is `z`-rough and `lam(n)/n ≤ K/n + KΛ(n)/n`, with `Σ_{non-prime} Λ(n)/n < ∞`.
3. So `mass(N) ≤ B_z + K T_Λ + K/log(z+1) + (2K/log(z+1)) log N` for `N ≥ z`. Choose `z` with `2K/log(z+1) ≤ b/3`, then `N` large.

## Lean
- Module `WeilConeAsymptoticPrimeSupport`: `IsRoughAbove`, `sum_rough_inv_le`, `tendsto_nonprimeMass_div_log`.
- Compiles cleanly with `lake env lean` (olean written with `-o`).
- `#print axioms` gives the standard three.
- Wired into `RHTower.lean` after `WeilConeMultiplesOfPrimeLaw`.
- `lake build` deferred: the upstream chain was invalidated by other agents.

## Open
- **Unbounded composite weights.** Signed or unbounded composite weights are not covered. L148 producers have polylog weights, and only their averages are controlled.
- **Prime deviations.** With composites removed, a bounded nonnegative producer is `Λ + d_ℙ + (o(log)-harmonic composites)`. The prime deviation `d_ℙ` of size `Λ` is the open core.

## Log
- 2026-10-01: created and formalized (cycle 182).
