# Residual-charge verified-prefix counterexample floor

- **ID:** `residual-charge-verified-prefix-counterexample-floor`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (paper proof sketched; Lean composition target identified)
- **Statement:** For any finite set `S` of nontrivial zeros verified on the critical line, every
  off-line zero `rho = 1/2 + delta + i*gamma` satisfies
  `4*c(delta,gamma) <= C - sum_{rho' in S} c_{rho'}`, hence
  `gamma^2 >= 4/R_S - 1` with `R_S = C - 2*sum_{gamma_j in S} 1/(1/4+gamma_j^2)`.

## Goal

Turn the fixed endpoint-charge budget `C = 2 + gamma_E - log(4*pi)` into a *verification-driven*
height floor: every on-line zero pair provably spends `2/(1/4+gamma_j^2)` of the budget, so any
off-line quartet must fit in the residual. The formalized corpus floor `gamma^2 > 7907/93`
(`xiZeroCopy_offLine_...lt_im_sq`) uses the full budget `C`; this card strengthens it to a floor
that grows with the verified prefix:

| prefix | residual `R_S` | floor `gamma >` |
|---|---|---|
| none (corpus, formalized) | `C ~ 4.619e-2` | 9.22 |
| first zero only | 3.62e-2 | 10.50 |
| first 100 zeros | 6.22e-3 | 25.35 |
| first 100000 zeros | 4.41e-5 | 301.1 |
| Platt–Trudgian height `T = 3e12` | ~2.96e-12 | ~1.16e6 |

Closed form: `gamma_min(T) ~ 2*sqrt(pi*T/(log(T/(2*pi))+1))`. The mechanism is independent of
direct verification above `T` (charge accounting only), and is the only corpus gate whose
strength is *monotone in computable input*.

## Approach

All Lean ingredients exist; the proof is a finite-subtraction composition:

- `tsum_xiEndpointCrossCharge_eq_curvature` (`XiThermalQuartetCubicChargeBound.lean`) — the trace
  identity `sum_rho c_rho = C`.
- `summable_xiEndpointCrossCharge`, positivity of `c_rho` — drop-a-finite-set gives
  `C_offline <= C - sum_S c_rho`.
- `four_mul_xiEndpointCrossCharge_le_offLineCharge` + `four_le_offLineCharge_mul_one_add_im_sq`
  (`XiThermalOffLineChargeSelfCubicBound.lean`) — the quartet height law with the residual in
  place of `C`.

The on-line location and heights of the prefix enter as *hypotheses* (rational interval bounds on
`gamma_j`); the theorem is conditional-on-prefix, unconditional in structure. Numerically
pre-certified 2026-07-14 (mpmath/numpy, 30 dps): trace-identity partial sums match the integral
tail to 7 digits; table above.

## Reverse-localization context (what this card is the provable core of)

Walking every corpus RH-gate backwards under `[assume not RH]` with verification input
`T = 3e12` `[SEARCH: Platt–Trudgian 2021]`:

- admissible region: `gamma > 3e12`, `0 < delta <= 1/2 - 1/(5.5734*log(gamma)) ~ 0.4938`
  `[SEARCH: de la Vallée Poussin / Mossinghoff–Trudgian]`; quartet forced `[PROVED, formalized]`.
- exact inversion (moment space -> zero space): for `u = -1/(R_**(delta+i*gamma)^2)`,
  `gamma^2 + delta^2 = 1/(R_*|u|)`, `delta = gamma*tan(|arg u|/2)`; on-line atoms give `B = 1`
  exactly, so `B - 1 ~ 2*delta^2/(R_**gamma^4)` and `E_* - 1 ~ 4*delta^2/(R_**gamma^4)
  <= 2.6e-49` at the frontier.
- detection costs (derived, one numeric anchor): Bernstein first-negativity degree
  `M0 ~ 0.2/(B-1) = 0.1*R_**gamma^4/delta^2` (predicted 1194 vs measured 1104 at
  `gamma=15, delta=0.45`); at the frontier `M0 >~ 1.5e48`. Prime-window visibility needs
  `x >~ (gamma/2)^(1/delta) >= 10^32.4`. Cold partition `Z_k` is the unique log-cost detector:
  `k0 ~ 2*log(gamma)/delta >= 115`.
- entry mechanism: a counterexample of the real entire `Xi` is born by collision of a
  near-degenerate real pair (wrong-signed extremum of Hardy `Z`). Measured nearest miss in the
  first 100k zeros: pair at `gamma = 71732.9012/71732.9159`, `Z`-extremum margin `-5.46e-4`.
  Rodgers–Tao `Lambda >= 0` makes the deformation distance to a counterexample-bearing function
  zero `[SEARCH]`.

## Open core

`[OPEN CORE]` Constraint-side lower bound on Lehmer margins: express the extremum margin of `Z`
between consecutive zeros as a source/charge functional of the fixed-window machinery, so that
"how close `zeta` can come to a collision" becomes a provable inequality. A second open thread:
a source-side (prime–Gamma) formula computing the cold partition `Z_k` to additive error
`e^(-eps*k)` without zero input would make the `k ~ 115/delta` detector computable.

## Gates

- [x] 0 -> 1 in-progress: mechanism isolated, Lean ingredients identified, numerics pre-certified
- [ ] 1 -> 2 fully-proven: paper proof of the finite-subtraction floor with explicit prefix hypotheses
- [ ] 2 -> 3 formalized: Lean theorem composing the three cited declarations
- [ ] 3 -> 4 publication-ready

## Log

- 2026-07-14 — created from the reverse-localization session (computations A–E on remote box,
  scripts in `/workspace/rhhunt/` there; session log `logs/2026-07-14-counterexample-reverse-localization.md`).
