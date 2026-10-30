# The shells and the pole cancel on the top band

- **ID:** ssh-joint-witness-cancellation
- **Stage:** 3-formalized
- **Type:** THEOREM (positive survivor of `ssh-separate-payment-floor`)
- **Statement:** Let `φ ∈ C²` be supported in `[0,1]`, `∫φ² > 0`, `c > 0`, `g = φ(·/w)`, `w = c/N`,
  `a_∓ = ∫ g e^{∓u/2}`, `T` the top band, `R` the pole row. Along `x_η = b + ηb1_T` the joint block
  `2(∫f e^{−u/2})(∫f e^{u/2}) − NR` equals its value at `b` plus `2η·κ_N + 2η²a₋a₊S_T|T|`, with
  `κ_N = a₋a₊(H_N|T| + N S_T) − Σ_T b_nR(n)`. There is `K` with `|κ_N| ≤ K G (1 + log N)` for all
  large `N`.

## Paper proof

Pole: `∫ g(u − log n)e^{∓u/2} = n^{∓1/2}a_∓`, so the pole moments of `x_η` are
`a₋a₊(H_N + ηS_T)(N + η|T|)`; with the base collapse `NR(x_η) = NR(b) + 2ηΣ_T b_nR(n)` this gives the
quadratic.

Row: below overlap `N log 2`, `R(n) = Σ_{ℓ≠n} F_n(ℓ)`, `F_n(t) = (log t/√t)β(log t − log n)`,
`β(s) = wA(s/w)`, `A` the profile autocorrelation (`C²`, derivative bounded by `A₁`). `F_n` vanishes
outside `[ne^{−w}, ne^w]`, and for `n ∈ T`, `w ≤ 1/4`, `N ≥ 8`, the cells `[A, ⌊ne^w⌋ + 1]`,
`A = ⌊ne^{−w}⌋`, lie in `[n/2, 2n]`. There
`F_n' = (t√t)⁻¹((1 − log t/2)β + log t·A'(u/w))` is at most
`K_n = ((n/2)√(n/2))⁻¹(1 + log 2n)(G + A₁)`. Comparing each cell value with its integral, the lattice
sum differs from `∫F_n` by at most `(n(e^w − e^{−w}) + 2)K_n`. The substitution `t = ne^u` gives
`∫F_n = √n(log n ∫e^{u/2}β + ∫u e^{u/2}β)`, and `∫e^{u/2}β = a₋a₊` (Laplace transform of an
autocorrelation at `½`). Subtracting `F_n(n) = G log n/√n`:
`b_nR(n) = a₋a₊ log n + I₁ − G log n/n + e_n`, `|e_n| ≤ b_n(3nw + 2)K_n ≤ (18w/N + 24/N²)(2 + log N)(G + A₁)`.

Sum: `κ_N = a₋a₊Σ_T(H_N − log n) + a₋a₊NS_T − |T|I₁ + GΣ_T log n/n − Σ_T e_n`. With
`|a₋a₊| ≤ 4wG`, `|I₁| ≤ 4w²G`, `0 ≤ H_N − log n ≤ 2`, `S_T ≤ 2`, `|T| ≤ N`, `wN = c`, `GN = cM`:
`|κ_N| ≤ 17cG + 2G log N + (18c + 24)(1 + A₁/(cM))(2 + log N)G ≤ K G(1 + log N)`.

## Scope

Each of `a₋a₊(H_N|T| + NS_T)` and `Σ_T b_nR(n)` is `≍ Gcq log N` (`sum_topBand_shellPoleRow_ge`);
their difference is `O(G(1 + log N))`. The `c²/ε` floor of the separate payment therefore does not
survive on this witness when the shells are paid together with the pole.

## Lean proof

`SuccessorShellArithmetic/TheShellsAndThePoleCancelOnTheTopBand.lean`:

- `abs_sum_sub_integral_le_of_deriv` (cell comparison)
- `bumpCorr_atomDilate_eq`, `hasDerivAt_bumpCorr_atomDilate`, `exists_abs_deriv_shellAutocorr_le`,
  `bumpCorr_atomDilate_eq_zero_of_le`, `integral_exp_half_mul_bumpCorr`
- `poleMoments_atomicTest`, `poleMoments_topWitnessVector`
- `hasDerivAt_rowIntegrand`, `abs_deriv_rowIntegrand_le`, `integral_rowIntegrand`, `abs_poleRow_sub_le`
- `jointBlock_topWitnessVector`, `exists_abs_jointWitnessCoefficient_le`

`lake --old env lean` passes; axioms `propext`, `Classical.choice`, `Quot.sound`. Wired into
`SuccessorShellArithmetic.lean`.
