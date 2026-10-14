# Constant-vector JAS tests detect a maximal off-line zero at every scale

## Statement

Setting: the level-one JAS test with a constant vector `z ∈ ℂ` on a finite prime set `P`,

`T_P(z) = Re Σ_ρ ∏_{p∈P} (1 + z A_p(ρ) + z̄ B_p(ρ) + |z|²)/(ρ(1−ρ))`,

where `A_p(ρ) = p^{−σ} p^{−(ρ−½)}` and `B_p(ρ) = p^{−σ} p^{ρ−½}`. The positivity predicate is
`JasConstProductPositiveOn P σ`.

**Theorem** (`eventually_not_jasConstProductPositiveOn_of_maximal_offLine`). Suppose an off-line zero
has the largest distance `δ` from the critical line, and `δ < σ < 1 + δ`. Then for every `X` and every
sufficiently large `N`, `T_{(X,N]}(z) < 0` for some `z`.

**Capstones.**

- `RH ⟺ ZAL ∧ ∃ X, ∃ᶠ N, JasConstProductPositiveOn (primes in (X, N]) 1`.
- The same holds with "no off-line chain" in place of ZAL.

## Proof

1. **Normalization.** `(1 + |z|²)^{−|P|} T_P(z) = Re Σ_ρ K_u(ρ)/(ρ(1−ρ))` with
   `K_u(ρ) = ∏_p (1 + u A_p + ū B_p)` and `u = z/(1 + |z|²)`. The phase of `u` is free.
2. **Symmetrization.** Add the tests at `z` and `z̄`. In the term `(K_u + K_ū)/(ρ(1−ρ))`, the four
   points `ρ, ρ̄, 1−ρ, 1−ρ̄` have equal real parts, because `K_u(1−s) = K_ū(s)` and
   `K_u(s̄) = conj K_ū(s)`.
3. **Dominant zero.** `ρ* = ½ + δ + iγ` has the largest distance and then the smallest `|γ|`. Let `S`
   be its large prime sum `Σ_{X<p≤N} p^{−(σ−δ−iγ)}`, set `ω = S/S̄`, and take `z = conj(Y/S)`. Then
   `K_u(ρ*) = e^{Y+e₁}` and `K_ū(ρ*) = e^{Ȳω+e₂}` with small `e_i`.
4. **Anti-alignment** (`exists_pair_antiAligned`). Let `c = Re w/‖w‖`, where `w = 1/(ρ*(1−ρ*))`.
   - Case `‖ω − 1‖ ≤ c/(8(R₀+4))`: take `Y = R₀ + iπ`. Both kernels are near `−e^{R₀}`, and
     `Re w(...) ≤ −(Re w)e^{R₀}`.
   - Otherwise take `Y = R₁ + i(π − arg w)` with `R₁` large. The conjugate kernel is smaller by
     `e^{−R₁‖ω−1‖²/2}`.
5. **Competitors.**
   - Zeros at the same distance have prime sums `≤ ρ₂‖S‖` with `ρ₂ < 1`, using the main term
     `N^{1−s}/((1−s) log N)` and `|1−s₀| < |1−s₁|`.
   - Zeros closer to the line have prime sums `o(‖S‖)`.
   - The tail is light.

## Reading

Under ZAL, the asymptotic-abscissa-law part of RH needs only constant-vector positivity on an
arbitrary infinite sequence of initial prime windows. This is the sparsest AAL receiver in the JAS
family. CANNOT-518 (`5-failed/jas-sparse-dyadic-scale-detector.md`) shows that the ZAL/no-chain input
cannot be removed for sparse families: super-high off-line clusters can dominate any single-scale
test.

The dyadic-window version `(N, 2N]` is formalized (MUST-1411, card `jas-constant-vector-dyadic-shells.md`) via a multi-tie argument. Zeros at the
same distance can have equal `|2^{1−s} − 1|/|1 − s|`.

## Lean

Module `RHTower/JointAncestryConstantVectorEveryScale`, 1336 lines, standard axioms. It is wired
after `WeilLagLatticeExcursionBudget`.

Reusable pieces:

- `exists_pair_antiAligned`;
- `re_tsum_jasConstPairTerm_nonneg`;
- `re_jasConstPairTerm_dominant_le`;
- `norm_jasConstKernel_competitor_le`;
- `exists_large_exponent_forall`.
