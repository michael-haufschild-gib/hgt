# Multiplicity grading of one-sided RH receivers

- **ID:** multiplicity-grading-receivers
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Opus loop rows 637–644; frontier map rows Báez–Duarte, MC (Möbius Hilbert form, Liouville).
- **Statement:** Three zero-side receivers each read the order `m` of a critical zero in their growth.
  - Báez-Duarte rate: `liminf d_N² log N ≥ Σ_ρ 2m_ρ²/|ρ|²`. Multiplicity sits in the constant.
  - Möbius Hilbert form: `E_N = Ω((log N)^{2m−1})`, so `E_N = O((log N)^k)` forces `2m ≤ k+1`. Multiplicity sits in the log exponent.
  - Liouville: `J(t) ≥ −C√t(1 + log^k(1/t))` forces RH and `m ≤ k+1`. Multiplicity sits in the log loss of a one-sided bound.

## Goal
Separate, in each receiver, the RH content from the multiplicity content.
- ε-lossy (power) forms are RH-equivalent.
- Exact (constant or logarithmic) forms cost RH plus a multiplicity bound.
- At the simple-zero constant or exponent, they cost RH plus simplicity of all critical zeros.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 (all standard axioms):
  - `eventually_le_bdDistDiscrete_sq_mul_log_of_lt_tsum_order` (MUST-874)
  - `riemannHypothesis_and_simple_of_frequently_le_tsum` (MUST-876)
  - `not_forall_hilbert_le_log_pow_of_analyticOrderAt` (MUST-875)
  - `exists_pos_forall_not_hilbert_le_log_pow_of_analyticOrderAt` (MUST-877)
  - `le_of_liouvilleExpSum_lower_logPow` (MUST-879)

## Approach
- **Báez-Duarte.** The derivative duals `(−log k)^j k^{−ρ}ψ(k/Y)`, `j < m`, are admissible (Cauchy estimates on disc-uniform Perron asymptotics). The optimal combination is the Legendre endpoint extremal `p_m(log k/log Y)` with `∫₀¹p_m² = 1/m²`. Distinct zeros are asymptotically orthogonal (bilinear Abel summation over the phases `ρ ± ρ̄'`). See card `baez-duarte-burnol-multiplicity`.
- **Hilbert form.**
  - `(log N)^k ≤ k!a^{−k}N^a` with explicit power-tail constants gives line energy `≤ A r^{−k} + B` on `Re s = ½ + r`.
  - The order-`m` window floor `‖Γ/ζ‖ ≥ c₀ r^{−m}` gives line energy `≥ 2c₀² r^{1−2m}`.
- **Liouville.**
  - The weight is `e^{−u/2}(1 + u^k)`. Its transform is the Laplace transform of a measure with abscissa `−½`, which gives holomorphy and the bound `≪ r^{−k−1}`, with no closed form needed.
  - Landau and the continuation identity then give `O(r^{m−k−1})` against `Γ(ρ)Z(2ρ) ≠ 0`.

## Modules
- RHTower: `ZetaSmoothedPartialSumsDisc`, `BaezDuarteLogDualDefect`, `BaezDuarteLogDualEnergy`, `BaezDuarteLogDualCrossEnergy`, `BaezDuarteBurnolMultiplicity`, `BaezDuarteBurnolMultiplicityAllZeros`, `MobiusHilbertMultiplicityLogExponent`, `LiouvilleExponentialSumMultiplicity`.
- HTGeometry: `LegendreEndpointExtremal`.

## Open
- Upper halves under RH:
  - `d_N² log N → Σ 2m²/|ρ|²` (Burnol's conjecture);
  - `E_N = O((log N)^{2m_max−1})`;
  - `J(t) ≥ −C√t log^{m_max−1}(1/t)`.
- Each needs residue sums over all zeros (Perron across infinitely many poles plus lower bounds for `ζ^{(m)}(ρ)`).

## Log
- 2026-10-09 — created at stage 3, collecting MUST-872/874–877/879.
- 2026-10-09 — MUST-881: the ε-lossy Liouville form is now an exact RH equivalence, `riemannHypothesis_iff_forall_liouvilleExpSum_isBigO`. Both directions are in Lean.
