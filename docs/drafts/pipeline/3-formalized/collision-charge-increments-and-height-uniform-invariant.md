# Collision-charge increments and the height-uniform invariant below RH

- **ID:** collision-charge-increments-and-height-uniform-invariant
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-3110/obstacles-summary.md`, §2.3 Q3 and §2.5.3.
- **Statement:** Write `O(T)` for `xiHorizontalCollisionCharge T`, `W(T)` for the ξ-zeros with
  `0 < Re < 1`, `T ≤ Im < T + 1`, `n(T) = Σ_{W(T)} m_ρ`, `n_off(T)` its off-line part and
  `ΔO(T) = O(T + 1) − O(T)`.
  1. `ΔO(T) = Σ_{ρ ∈ W(T)} m_ρ (H(Im ρ) − m_ρ)` and `n_off(T) ≤ ΔO(T) ≤ 2 n(T) n_off(T)`.
  2. Unconditionally `ΔO(T) ≤ C log² T` for large `T`, and `O(n) ≤ A + C n log²(n + 1)`.
  3. If `ΔO(T) ≤ M` for all `T`, then `N₀(T)/N(T) → 1` for the strip windows.

## Classification of the height-uniform statements
- `O(T) < 2` for all `T` ⟺ RH (`riemannHypothesis_iff_forall_horizontalCollisionCharge_lt_two`).
- `sup_T O(T) < ∞` ⟺ finitely many off-line zeros ⟺ RH above some height ⟺ `sup_{t>0} N(t) < ∞`
  for the de Bruijn–Newman nonreal count (`index_exit_first_rung_tfae`); it gives `Θ < 1`
  (`zetaZeroAbscissa_lt_one_of_finite_rightZeros`) and, by Littlewood's local argument, Lindelöf.
  It is the `t = 0` endpoint of Ki–Kim–Lee (`riemannHeat_nonreal_zeros_finite` for `t > 0`).
  §2.5.3's label "below RH / quasi-RH" is wrong for this statement.
- `sup_T ΔO(T) < ∞` is the per-window statement: it implies critical density one (3.), implies
  neither quasi-RH nor Lindelöf, and is open. Unconditionally `ΔO ≪ log² T` (2.).

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems in `ConjugateDiagonalGeometry`, `lake --old env lean` green, `#print axioms` PASS

## Proof `[PROVED HERE]`
1. `O(T) = Σ_{S_T} c(ρ)` with `c(ρ) = m_ρ (H(Im ρ) − m_ρ)` independent of `T`, and
   `S_{T+1} = S_T ⊔ W(T)`. For `ρ ∈ W(T)` the fibre of `Im ρ` lies in `W(T)`. If `Re ρ = ½`, every
   other point of the fibre is off-line, so `H − m_ρ ≤ n_off(T)`; if `Re ρ ≠ ½`, `H ≤ n(T)`. Summing
   `c(ρ) ≤ m_ρ n_off + [Re ρ ≠ ½] m_ρ n` gives `ΔO ≤ 2 n n_off`. At an off-line `ρ`, `m_ρ ≤ c(ρ)`
   because the reflection `1 − ρ̄` lies in the fibre with the same order.
2. The divisor copies over `W(T)` lie within height `1` of `T`, so `n(T) ≤ C log T`
   (`exists_card_near_xi_zeros_le`); then `ΔO ≤ 2 n² ≤ 2C² log² T`. Summing over unit steps above
   the threshold gives the cumulative bound.
3. `n_off ≤ ΔO ≤ M` and `S_0 = ∅` give `Off(n) ≤ M n`, hence `Off(T) ≤ M(T + 1)`. The zero count
   satisfies `N(T − 1) ≤ Tot(T)` and `N(T) ≥ T log T / 4π` for large `T` (`exists_xiZeroCount_close`),
   so `Off/Tot ≤ 8πM / log(T − 1) → 0`, and `Line = Tot − Off`.

## Falsification record (corpus objects)
- Counting inputs do not bound `ΔO`: the falsifier of
  `SquareRootThreshold.exists_zeroConfig_rvm_not_localCountBound` has RVM and the critical count of ζ
  but violates every off-line window bound, and `n_off ≤ ΔO`.
- Soft theta-source data do not decide Q3: for `τ > 0` the kernel `e^{−τx²}Φ` is positive, even,
  super-exponentially decaying and splits into positive integer shells, yet `H_{−τ}` has infinitely
  many nonreal zeros (`riemannHeat_neg_nonreal_zeros_infinite`); for `t ∈ (0, 1/8]` all nonreal zeros
  of `H_t` lie in `|Re z| < 2π e^{40/t}` (`riemannHeat_zeros_real_of_le_re`). The charge is bounded on
  one side of `t = 0` and unbounded on the other.
- Functional equation, order one and `Λ ≥ 0` do not force critical zeros:
  `lambdaPositive_entire_functionalEquation_not_criticalLine`.
- Sharpness of 2. against continuous inputs: a fibre with `k` off-line pairs and one critical zero
  contributes `(2k + 1) 2k`; with `k ≍ log T` and small offsets it is compatible with the local count,
  the depth bounds and `Λ < 1/8`. Only arithmetic can exclude it.

## Lean verification
Module `GaloisForLFunctions/ConjugateDiagonalGeometry/CollisionChargeIncrements.lean` (wired into
`GaloisForLFunctions/ConjugateDiagonalGeometry.lean`): `xiUnitWindowZeros`, `xiCollisionTerm`,
`xiCollisionIncrement`, `xiUnitWindowOrder`, `xiUnitWindowOffLineOrder`, `sum_stripZeros_add_one`,
`xiHorizontalCollisionCharge_add_one`, `xiCollisionIncrement_eq`,
`xiUnitWindowOffLineOrder_le_increment`, `xiCollisionTerm_le`, `xiCollisionIncrement_le_two_mul`,
`exists_xiUnitWindowOrder_le_log`, `exists_xiCollisionIncrement_le_log_sq`,
`exists_xiHorizontalCollisionCharge_nat_le`, `xiStripWindowOffLineOrder_nat_le`,
`xiZeroCount_le_xiStripWindowTotalOrder`, `tendsto_lineOrder_div_totalOrder_of_bounded_increment`.
`lake --old env lean` passes with default limits and no warnings; all six `#print axioms` checks
report only `propext`, `Classical.choice`, `Quot.sound`.
