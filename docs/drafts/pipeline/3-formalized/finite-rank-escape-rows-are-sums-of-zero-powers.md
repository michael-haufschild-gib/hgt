# Finite-rank escape rows are sums of translated-zero powers

- **ID:** adr-finite-rank-escape-rows
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Let `0 < ε < 1/2`, `1/2 < σ < 1 − ε`, and `F` a finite set of complex exponents with
  `Re s = σ` for `s ∈ F`, such that `s ↦ 2^{−s}` and `s ↦ 3^{−s}` are injective on `F`. Let `w` be a
  complex row with `w(0) = 0` such that `∏_{s∈F}(I − 2^s D₂) w` and `∏_{s∈F}(I − 3^s D₃) w` have finite
  pronic energy (`D_p v(n) = v(⌊n/p⌋)`), and `S_ε w − c' n^{1−ε}` has finite pronic energy for some
  `c'`. Then there are `c_{st}, z_{st}` (`(s,t) ∈ F × F`) with `Re z_{st} = σ`,
  `w − Σ c_{st} n^{z_{st}}` of finite energy, and for `c_{st} ≠ 0`: `2^{z_{st}} = 2^s`,
  `3^{z_{st}} = 3^t`, `ζ(z_{st} + ε) = 0`. If `ζ` has no zero on `Re = σ + ε`, `w` has finite energy.

## Paper proof
1. **Operators.** `D_p` is linear on rows; `Q(D_p)v(n) = Σ_i q_i v(⌊n/p^i⌋)`; polynomials in `D_2` and
   `D_3` commute (`⌊⌊n/a⌋/b⌋ = ⌊n/ab⌋`). Finite-energy rows vanishing at `0` are stable under sums,
   scalars, and `D_p` (`pronicNorm_rowDilate_le`), hence under every `Q(D_p)`.
2. **Lagrange projectors.** `1 − aX = (−a)(X − a⁻¹)`, so `∏_s(1 − p^sX) = κ_p·N_p` with
   `N_p = ∏_s(X − p^{−s})`, `κ_p ≠ 0`; thus `N_p(D_p)w` is admitted. With `ℓ_s` the Lagrange basis of the
   nodes `p^{−s}`: `Σ_s ℓ_s = 1` and `(X − p^{−s})ℓ_s = λ_s N_p`, so `(1 − p^sX)ℓ_s ∈ ℂ·N_p`.
3. **Components.** `w_{st} = ℓ'_t(D₃)ℓ_s(D₂)w` sum to `w`. By step 2 and commutation,
   `(I − 2^sD₂)w_{st} = ℓ'_t(D₃)(const·N_2(D₂)w)` and `(I − 3^tD₃)w_{st}` are admitted.
4. **Inversion law of a component.** `S_ε D_p v = D_p S_ε v` for `v(0) = 0` (terms with `j > n/p` vanish),
   hence `S_ε Q(D_p) = Q(D_p) S_ε`. On powers, `Q(D_p) n^a = Q(p^{−a}) n^a + O(1)` from
   `|⌊n/q⌋^a − q^{−a}n^a| ≤ ‖a‖ + 1` (mean value on `[⌊n/q⌋, n/q]`). So
   `S_ε w_{st} − c'·ℓ_s(2^{−α})ℓ'_t(3^{−α}) n^α` is admitted (`α = 1 − ε`).
5. **Conclusion.** Two-dilation tiedness gives `w_{st} = c_{st} n^{z_{st}} + admitted` with
   `Re z = σ`, `z` tied to `(s,t)` when `c_{st} ≠ 0`; the Mellin residue theorem on the component gives
   `ζ(z_{st} + ε) = 0`. Summing over `F × F` gives the decomposition.

## Lean
`ArithmeticDefectRigidity/FiniteRankEscapeRowsAreSumsOfZeroPowers.lean`:
`dilOp`, `aeval_dilOp_apply`, `aeval_dilOp_comm`, `Adm.polyDil`, `norm_floor_cpow_sub_le`,
`exists_bound_aeval_cpow`, `cTotalCofactorSum_dilOp`, `cTotalCofactorSum_aeval`,
`adm_cofactor_aeval`, `prod_euler_eq_C_mul_nodal`, `euler_mul_basis`, `adm_euler_component`,
`exists_finiteRank_zeroPower_decomposition`, `cPronicEnergy_ne_top_of_finiteRank_of_zeroFree`.
Standard axioms only.

## Insight
The source-level escape dictionary is closed under finite rank: the dilation algebra `ℂ[D₂, D₃]`
acts on the inversion law (it commutes with `S_ε` and multiplies the pole trace by a scalar), so
Lagrange projection splits any finite-rank escape row into rank-one escape rows, each pinned to a
translated zero. A finite-dimensional escape module whose dilation errors are absolutely admitted
therefore carries exactly zeros of `ζ` on the translated line; on a zero-free line it cannot exist.
Real rows are the case `F = {s, s̄}`. Repeated nodes (power-log rows) remain open.
