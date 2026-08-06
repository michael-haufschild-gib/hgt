# Toric model: every divisor-level quantity computed (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Extension of module 27,
`CoordinateDivisorOrder.lean`.  See [[research/coordinate_divisor_order_2026_08_06]].

## Added

- `orderAt_one` — general.
- **`orderAt_coordDivisor_monomialMap_X`** — the ramification index of the monomial map along the
  `i`-th coordinate divisor is exactly `e i`.
- **`formOrder_coordDivisor_log`** — the logarithmic volume form has `formOrder = −1` there,
  stated in the **same `formOrder` vocabulary as the abstract capstone**.

So in one concrete model every divisor-level quantity of the horizon theorem is now computed from
definitions: `c = −1`, `e = e i`, `ord J = e i − 1`.

## Known blocker for a *full* toric instantiation of the abstract system

Instantiating `EigenvolumeRamificationSystem` needs the divisor map `F`, i.e.
`Ideal.comap (monomialMap k σ e) (span {X i}) = span {X i}`.

- `⊇` is easy (`X i ↦ X i ^ e i ∈ span {X i}` when `e i ≥ 1`).
- `⊆` reduces to **injectivity of the monomial map**.  True — `α ↦ e·α` is injective on `σ →₀ ℕ`
  when all `e i ≥ 1` — but there is **no direct mathlib route**: `aeval (X i ↦ X i ^ e i)` is not
  syntactically `AddMonoidAlgebra.mapDomain`, so the `mapDomain_injective` lemmas do not apply
  without first proving that identification.

Useful observation found while attacking it: with `θ` the coordinate-killing map
(`X i ↦ 0`, `X j ↦ X j`), one has **`θ ∘ φ = φ ∘ θ`** as algebra maps (check on generators).
That reduces the comap identity to injectivity of `φ`, so injectivity is the single missing lemma.
