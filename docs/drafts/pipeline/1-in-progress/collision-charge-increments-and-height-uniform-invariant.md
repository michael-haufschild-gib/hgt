# Collision-charge increments and the correct height-uniform invariant

- **ID:** collision-charge-increments-and-height-uniform-invariant
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-3110/obstacles-summary.md`, §2.3 Q3 and §2.5.3.
- **Statement:** Write `O(T)` for `xiHorizontalCollisionCharge T`, `W(T)` for the ξ-zeros with
  `0 < Re < 1`, `T ≤ Im < T + 1`, `n(T) = Σ_{W(T)} m_ρ`, `n_off(T)` its off-line part and
  `ΔO(T) = O(T + 1) − O(T)`.
  1. `ΔO(T) = Σ_{ρ ∈ W(T)} m_ρ (H(Im ρ) − m_ρ)` and
     `Σ_{ρ ∈ W(T), Re ρ ≠ ½} m_ρ² ≤ ΔO(T) ≤ 2 n(T) n_off(T)`.
  2. Unconditionally `ΔO(T) ≤ C log² T` for large `T`, and `O(n) ≤ A + C n log² n`.
  3. `sup_T ΔO(T) < ∞` implies `N₀(T, 2T) / N(T, 2T) → 1`.
  4. `sup_T O(T) < ∞` implies a zero-free half-plane `Re s > σ₀`, `σ₀ < 1`.

## Goal
Decide which height-uniform statement about `O` sits below RH. `O` is cumulative, so
`sup O < ∞` is equivalent to "RH above some height" (corpus: `index_exit_first_rung_tfae`); by 4.
it is at least quasi-RH, and by Littlewood's local argument it implies Lindelöf. The unit-window
increment `ΔO` is the invariant that bounds off-line zeros per window: its boundedness is strictly
weaker, implies critical density one (3.), and is still open; the unconditional size is `log² T` (2.).

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems in `ConjugateDiagonalGeometry`, `lake --old env lean` green, `#print axioms` PASS

## Approach
1. `O(T) = Σ_{S_T} c(ρ)` with `c(ρ) = m_ρ (H(Im ρ) − m_ρ)` independent of `T`; `S_{T+1}` splits
   into `S_T` and `W(T)`. For `ρ ∈ W(T)` the fibre of `Im ρ` lies in `W(T)`. A critical `ρ` meets
   only off-line points in its fibre, so `c(ρ) ≤ m_ρ n_off(T)`; an off-line `ρ` has
   `c(ρ) ≤ m_ρ n(T)`. Lower bound: `m_ρ² ≤ c(ρ)` at off-line `ρ`
   (`xi_order_sq_le_horizontalCollisionTerm_of_offLine`).
2. `n(T)` is the cardinality of the zero-copies over `W(T)`, all within height `1` of `T`;
   `exists_card_near_xi_zeros_le` gives `n(T) ≤ C log T`.
3. `ΔO ≤ M` bounds the off-line mass of every unit window by `M`, hence every window `(T−1, T+1]`
   of `zetaZeroConfig` by `2M` (conjugation for negative heights); then
   `tendsto_N0_div_N_of_offLineLocallyBounded` with `Zeta23.riemannVonMangoldt_zeta`.
4. `sup O < ∞` gives finitely many off-line zeros; each has `Re < 1`.

## Falsification record
- Counting inputs: the SRT falsifier `exists_zeroConfig_rvm_not_localCountBound` has RVM and the
  critical count of ζ but violates every off-line window bound, so by 1. its increments are
  unbounded: RVM-type counting cannot bound `ΔO`.
- Soft theta-source data: for `τ > 0` the kernel `e^{−τx²}Φ` is positive, even, super-exponentially
  decaying and splits into positive integer shells, yet `H_{−τ}` has infinitely many nonreal zeros
  (`riemannHeat_neg_nonreal_zeros_infinite`); for `t > 0` the nonreal zeros are finite and lie below
  `Re = 2π e^{40/t}` (`riemannHeat_zeros_real_of_le_re`). Q3 is the `t = 0` endpoint of Ki–Kim–Lee
  and is not decided by any property shared by the kernels `e^{tx²}Φ`, `t` near `0`.
- Sharpness of 2.: a horizontal fibre holding `k` off-line pairs and one critical zero contributes
  `(2k + 1) 2k`; such a fibre with `k ≍ log T` is compatible with the local count, Selberg-type depth
  bounds and `Λ < 1/8` when the offsets are small, so `log² T` is the limit of continuous inputs.
