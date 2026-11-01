# Conductor packets below the eighth-root overlap

- **ID:** one-eighth-conductor-packet-positivity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0111/obstacles-summary.md`, §2.1 A2
- **Statement:** For `0 < α < 1/8`, tilted-spline complete Weil matrices are
  eventually positive on every fixed conductor packet, uniformly for
  `1 ≤ c ≤ (log N)^α`. Polylogarithmic conductor subspaces are coercive when
  `q > 0` and `α + 2q < 1`.

## Exact bounds

Write `L = log N`, `v_m = normalizedRamanujanHorizonVector m N`,
`E_m(c) = completedConductorEnergy tiltedUnitSpline c m`, and
`r_m = W v_m - E_m(c) v_m`.
There is `K > 0` such that, for every `A ≥ 0` and integer `k ≥ 1`, eventually
in `N`, uniformly for positive `m,l ≤ L^A`, `c ≥ 1`, and
`4(e+3)^2 c^2 ≤ N`,

`|⟨r_m,v_l⟩| ≤ K √(ml)(1+log m) [c(1+log c)^2 L^(1/k-1) + c^5 L/N]`.

The symmetric relative residual sum satisfies

`Σ_{m,l≤Q} |⟨r_m,v_l⟩|²/(E_m E_l) ≤ K [c^7+Q²(1+log Q)²]² [c(1+log c)²L^(1/k-1)+c^5L/N]²`.

For `Q = ⌊L^q⌋`, `0 < α < 1/8`, `q > 0`, and `α + 2q < 1`, eventually
uniformly for `1 ≤ c ≤ L^α` and `y = Σ_{m≤Q} a_m v_m`,

`⟨(W - κ₀/(2c^7) I)y,y⟩ ≥ (1/4) Σ_{m≤Q} E_m(c) a_m²`.

Every fixed conductor subspace consequently has floor
`completeWeilEnergy(y) ≥ κ₀/(2c^7) ‖y‖²`, with `κ₀ > 0`, and strict positivity
on nonzero vectors.

## Proof

Pair each of the eight exact residual terms against a second Ramanujan mode.
Harmonic quotient summation, the prime Mertens remainder, and direct boundary
estimates give the linear overlap rate above. No correlation or zero-location
hypothesis enters the tilted-spline specialization.

The conductor-scale floor `E_m(c) ≥ κ₀ min(1,(m/c)^7)` bounds inverse-energy
weights by summable low-conductor tails plus `Q²(1+log Q)²`. Rescale coefficients
by `√E_m` and apply Cauchy–Schwarz to the bilinear residual matrix. Its leading
relative error is governed by `c^8/L` and `cQ²/L`, up to arbitrarily small
logarithmic losses. The strict inequalities `8α < 1` and `α + 2q < 1` absorb
these losses. The quantitative Gram estimate supplies the remaining diagonal
control. Every fixed packet lies in the growing subspace eventually.

## Lean and audit

Module:
`formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/BilinearConductorResidualsAndOneEighthPackets.lean`.

- `exists_completeWeil_bilinear_conductor_residual_variable_rate`
- `exists_tiltedUnitSpline_bilinear_conductor_residual_variable_rate`
- `exists_tiltedUnitSpline_quadratic_inv_energy_residual_sum_le`
- `exists_tiltedUnitSpline_bilinear_relative_residual_sum_le`
- `eventually_tiltedUnitSpline_polylog_conductorSubspace_energy_ge`
- `eventually_tiltedUnitSpline_fixed_conductorSubspace_energy_ge_below_one_eighth`
- `eventually_tiltedUnitSpline_fixed_conductorSubspace_pos_below_one_eighth`

Direct `lake --old env lean <file>` check passed. All seven transitive axiom
lists contain only `[propext, Classical.choice, Quot.sound]`.
The module is imported by `CriticalArithmeticCorrelationTheory.lean`.

The broader four-band all-vector argument below `1/9` is separate; see
`../2-fully-proven/bilinear-conductor-residuals-and-one-ninth-weil-positivity.md`.
