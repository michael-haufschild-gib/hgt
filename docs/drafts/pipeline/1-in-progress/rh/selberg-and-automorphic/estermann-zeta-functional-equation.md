# Estermann's zeta function and its functional equation

- **ID:** EST-001
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** CANNOT-320 / CANNOT-321 — the mollified second moment needs the product functional equation (twisted second moment), not a split of the approximate functional equation into halves.
- **Statement:** `D(1-s, a/q) = 2 q^{2s-1} (2π)^{-2s} Γ(s)² ( D(s, a⁻¹/q) + cos(πs) D(s, -a⁻¹/q) )` for every unit `a` mod `q`.

## Goal

`RHTower.not_sharpEnergyInput` (CANNOT-321) and the earlier CANNOT-320 close the route that bounds
the mollified second moment by splitting the approximate functional equation into halves and
estimating each in absolute value: that loses a factor `log N` and cannot be repaired by any choice
of head cutoff. The surviving route is the twisted second moment
`∫_T^{2T} |ζ(1/2+it)|² (h/k)^{-it} dt` of Balasubramanian–Conrey–Heath-Brown. The corpus already owns
its **diagonal**: `twistedDiagonalAdapted_sum_eq` and `abs_twistedDiagonalAdapted_sub_main_le`
evaluate the adapted diagonal exactly, `BchbDensityIntegral` supplies the `2γ − 1`, and
`TwistedMainTermMerge` proves the removable singularity of the shifted pair. What it does not own is
the **off-diagonal**: `TwistedOffDiagonalSum` has only the trivial row bound
`O(max(nk,mh) · log #s)`. The analytic engine for the off-diagonal is the shifted divisor sum, whose
generating function is Estermann's zeta function.

## What is proved

Module [`EstermannZeta`](../../../../../../formal/GaloisForLFunctions/RHTower/EstermannZeta.lean):

- `RHTower.estermannZeta q a s = q^{-s} Σ_{c mod q} expZeta(ac/q, s) · hurwitzZeta(c/q, s)` — the
  definition, meromorphic on all of `ℂ`.
- `RHTower.estermannZeta_eq_LFunction` — it is the `ZMod q` L-function of the weights
  `c ↦ expZeta(ac/q, s)`, definitionally.
- `RHTower.estermannZeta_eq_LSeries` — for `1 < Re s` it equals the Dirichlet series
  `Σ_m expZeta(am/q, s) m^{-s}`; expanding the inner series and grouping by the product gives
  `Σ_N d(N) e(aN/q) N^{-s}`.
- `RHTower.estermannZeta_one_sub` — **the functional equation**, for every unit `a` mod `q` and every
  `s` with `s ≠ 1 - n` for all `n : ℕ`.
- `RHTower.hasSum_estermannZeta` — **the double series**: for `1 < Re s`,
  `estermannZeta q a s = Σ_{m,n ≥ 1} e(amn/q) (mn)^{-s}`, as a `HasSum` over `ℕ × ℕ`. Absolute
  convergence comes from `‖e(·)‖ = 1` and the product of two `p`-series.
- `RHTower.hasSum_lseries_succ` — a convergent L-series as a sum over positive indices.
- `RHTower.estermannZeta_eq_polar_add_regular` — **the polar decomposition**
  `D(s,a/q) = q^{-s}((ζ(s)+G_a(s))ζ(s) + R_a(s))`, obtained by separating the residue `c = 0`, where
  both factors degenerate to `ζ`, and replacing every remaining Hurwitz zeta by `ζ` plus an entire
  difference.
- `RHTower.differentiable_estermannCharSum`, `RHTower.differentiable_estermannRegularPart` — `G_a`
  and `R_a` are entire for `a` a unit (`differentiable_expZeta_of_ne_zero`,
  `differentiable_hurwitzZeta_sub_hurwitzZeta`).
- `RHTower.differentiableAt_estermannZeta` — holomorphic off `s = 1`.
- `RHTower.tendsto_sq_sub_one_mul_estermannZeta` — **the leading Laurent coefficient** at the double
  pole is `1/q`, independent of `a`.
- `RHTower.unitsMulPerm`, `RHTower.units_inv_mul_cancel`, `RHTower.units_mul_ne_zero` — the two
  permutations of `ZMod q` used to regroup the reflected sum, and the unit cancellation behind them.

Mechanism: the defining sum pairs `expZeta` against `hurwitzZeta`, and the `s ↔ 1-s` reflection
exchanges exactly those two (mathlib's `hurwitzZeta_one_sub`, `expZeta_one_sub`), so the sum is
formally self-dual. The product of the two reflections has four terms with coefficients
`1, e^{iπs}, e^{-iπs}, 1`. Under `c ↦ ac` the first and fourth become the Estermann value at `a⁻¹`,
and under `c ↦ -ac` the second and third become the value at `-a⁻¹`; the two exponentials combine
into `2cos(πs)`.

All audited: `propext`, `Classical.choice`, `Quot.sound` only.

## Open successor

1. Group the double series by the product `mn` to reach `Σ_N d(N) e(aN/q) N^{-s}` literally, using
   `Nat.divisorsAntidiagonal`.
2. Growth of `estermannZeta` on vertical lines, from the functional equation plus convexity — the
   input to the contour shift. The polar structure and holomorphy off `s = 1` are now available, so
   what is missing is a Phragmén–Lindelöf argument on the strip, resting on bounds for `expZeta` and
   `hurwitzZeta` on vertical lines.
3. The off-diagonal of the twisted second moment, replacing the trivial row bound in
   `TwistedOffDiagonalSum`.

## Log
- 2026-09-24 — created; definition, L-series identity, double series and functional equation proved
  in Lean.
- 2026-09-24 — polar decomposition, entireness of both parts, holomorphy off `s = 1`, and the
  leading Laurent coefficient `1/q` proved in Lean.
