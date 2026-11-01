# Collective Packet Coercivity Below 1/4 and Power-of-Logarithm Defect Confinement Below 1/9

- **ID:** collective-packet-coercivity-and-logarithmic-confinement
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-3110/obstacles-summary.md · Q1 / Q2a / Confinement Exponent Bottleneck
- **Statement:**
  1. **Collective Packet Coercivity (`0 < α < 1/4`):** For every `0 < α < 1/4`, every `q > 3α`, and every `0 < θ ≤ 1/4096`, eventually in `N` and uniformly across `1 ≤ c ≤ (log N)^α`, every vector `u ∈ V_{⌊N^θ⌋₊} ∩ V_{⌊(log N)^q⌋₊}^⊥` satisfies
     `1/64 · poleDefect_N(u) + (κ₀ + 2)‖u‖² ≤ W(tiltedUnitSpline, c, N, u)`.
  2. **Power-of-Logarithm Defect Reserve & `O(log c)` Sublevel Confinement (`0 < α < 1/9`):** There exist absolute constants `a₀, C, b₂ > 0` such that for every `0 < α < 1/9`, eventually in `N` and uniformly across `1 ≤ c ≤ (log N)^α`, every horizon vector `x` satisfies
     `(a₀ / c⁷)(poleDefect_N(x) − C log(2c)‖x‖²) + (κ₀ / 2c⁷)‖x‖² ≤ W(tiltedUnitSpline, c, N, x)`
     and `(b₂ / c⁸) poleDefect_N(x) ≤ W(tiltedUnitSpline, c, N, x)`; on the `(κ₀ / 2c⁷)‖x‖²` sublevel set, `poleDefect_N(x) ≤ C log(2c)‖x‖² ≤ C c²‖x‖²`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `lake --old env lean` green, `#print axioms` = `[propext, Classical.choice, Quot.sound]`

## Mathematics

1. **Defect–Jump Sandwich on Ramanujan Packets:** Using `poleDefect_ramanujanPacket_eq`, `primeConductorDilationJump_packet`, and the two-sided Riesz frame on `[1, Q]` (`18(1 + log Q) ≤ log N`), the finite-horizon prime-power dilation defect of `y = Σ_{m≤Q} a_m v_{m,N}` satisfies
   `½ E(Q, a) ≤ poleDefect_N(y) ≤ (3/2) E(Q, a)`.
2. **Collective Packet Coercivity up to `α < 1/4`:** Orthogonal splitting along `Q₁ = ⌊(log N)^q⌋₊ ≤ R₀ = ⌊exp((log N)^{1/2})⌋₊ ≤ R₁ = ⌊N^θ⌋₊` combines:
   - `u₀ ∈ V_{R₀} ∩ V_{Q₁}^⊥`: `W(u₀) ≥ ⅛ E(R₀, a₀) + (¾ log Q₁ − log c − C₀)‖u₀‖²` (from the `c^{3/2}(1+log c)/√Q₁` mid-band overlap decay);
   - `u₁ ∈ V_{R₁} ∩ V_{R₀}^⊥`: `W(u₁) ≥ ⅛ E(R₁, a₁) + (¼ log R₀ − C₁ c²(1+log c))‖u₁‖²` (where `log R₀ ≍ (log N)^{1/2} ≫ c²(1+log c)` for all `α < 1/4`);
   - Cross term `2|⟨W u₀, u₁⟩| ≤ (1/32) E(R₀, a₀) + ¼‖u₀‖² + (1/16)(log N)^{1/2}‖u₁‖²`.
   Converting the retained `3/32 · E(R₀, a₀) + ⅛ E(R₁, a₁)` via the `(3/2)` upper Riesz sandwich and quadratic subadditivity `poleDefect(u₀ + u₁) ≤ 2 poleDefect(u₀) + 2 poleDefect(u₁)` yields `1/64 · poleDefect_N(u) + (κ₀ + 2)‖u‖² ≤ W(u)` on `V_{R₁} ∩ V_{Q₁}^⊥` for all `0 < α < 1/4`.
3. **Logarithmic Confinement & `c⁻⁸` All-Vector Defect Reserve (`0 < α < 1/9`):** Splitting the terminal `(a/c⁷) poleDefect_N(w)` reserve on `V_{R₁}^⊥` into `(a/2c⁷) poleDefect_N(w)` plus `(a/2c⁷) k₁ S_w` propagates `(b₀/c⁷) poleDefect_N(z) + (κ₀ + 2)‖z‖² ≤ W(z)` across `z ∈ V_{Q₁}^⊥`. Combining with `completedConductorEnergy_ge_logarithmic_reserve` (`δ = c⁻⁷`) on `y ∈ V_{Q₁}` and the `O((c⁹ + c² Q₁²(1+log Q₁)²)(log N)^{1/k−1})` inverse-energy Schur budget yields the joint logarithmic-defect and spectral-floor inequality on all vectors, replacing `c^{16}` sublevel confinement by `C log(2c) ≤ C c²` and sharpening the all-vector positive defect reserve from `c⁻²³` to `c⁻⁸`.

## Lean
- `CACT/CollectivePacketCoercivityAndLogarithmicConfinement`:
  `poleDefect_normalizedRamanujanPacket_sandwich_primeAdjunctionMass`,
  `eventually_tiltedUnitSpline_collective_packet_coercive_with_defect_below_one_quarter`,
  `eventually_tiltedUnitSpline_collective_packet_coercive_below_one_quarter`,
  `exists_completeWeilEnergy_asymmetric_two_region_with_defect_reserve`,
  `exists_complement_coercive_with_defect_reserve_below_one_ninth`,
  `exists_completeWeil_logarithmic_defect_and_spectral_floor_below_one_ninth`,
  `exists_completeWeil_logarithmic_defect_reserve_below_one_ninth`,
  `exists_sublevel_completeWeil_poleDefect_logarithmic_bound_below_one_ninth`,
  `exists_tiltedUnitSpline_completeWeilEnergy_ge_c8_poleDefect_reserve_below_one_ninth`.
