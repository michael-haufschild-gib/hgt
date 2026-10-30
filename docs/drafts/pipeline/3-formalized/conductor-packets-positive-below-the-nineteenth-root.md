# Conductor packets are positive below the nineteenth root

- **ID:** ssh-packets-one-nineteenth
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For `0 < α < 1/19` and every injective family `m : Fin d → ℕ+`, eventually in `N`,
  the complete Weil form of the tilted spline at `c_N = (log N)^α` is positive on every nonzero
  combination of the normalized conductor modes `u_{m_i}`. Some unbounded `Q(N) → ∞` keeps
  `span{u_1, …, u_{Q(N)}}` positive for every `N`.

## Paper proof

Scale the packet matrix by `c⁷`. The diagonal is `≥ κ` by the conductor floor `E_m(c) ≥ κc⁻⁷`. The
entry errors are `c⁷⟨(W − E_i)u_i, u_j⟩ + c⁷E_i(⟨u_i,u_j⟩ − δ_ij)`. The horizon-decay residual
`‖(W − E_m)u_m‖² ≤ K_m(c⁵/log N + c¹⁰(log N/N)²)` (valid once `4(e+3)²c² ≤ N`) bounds the first by
`(K_m(c¹⁹/log N + c²⁴(log N/N)²))^{1/2} → 0` since `19α < 1`; with `E_i ≤ C c²` and the Gram error
`(2ml + 1)/log N` the second is `O(c⁹/log N) → 0`. A diagonal matrix with entries `≥ κ` plus a `d × d`
perturbation with entries `≤ κ/(2(d+1))` is positive definite. For growing packets let `N₀(Q)` be the
horizon of the packet `{1, …, Q}` and `Q(N)` the largest `Q ≤ N` with `N₀(q) ≤ N` for all `q ≤ Q`.

## Scope

Improves the corpus range `α < 1/40` (`eventually_tiltedWeil_growing_packet_pos`). The exponent
`19 = 2·7 + 5` is twice the floor exponent plus the residual exponent. The growing range is not
effective: seven of the eight residual components have constants not explicit in `m`.

## Lean proof

`SuccessorShellArithmetic/FixedConductorPacketsArePositiveBelowTheNineteenthRoot.lean`:

- `tendsto_scaled_residual_norm_of_lt_one_nineteenth`
- `tendsto_scaled_packet_entry_error_of_lt_one_nineteenth`
- `eventually_tiltedWeil_packet_pos_of_lt_one_nineteenth`
- `firstConductors`, `exists_growing_packet_pos_of_lt_one_nineteenth`

`lake --old env lean` passes; axioms `propext`, `Classical.choice`, `Quot.sound`.
