# PNT with power-log error — quantitative elementary route

## Goal
`[TARGET]` Formalize UNCONDITIONALLY: ∃ C, ∀ x ≥ 2:
  |ψ(x) − x| ≤ C·x/(log x)²
(any fixed power B ≥ 2 suffices; B = 2 is the target). Consumer: the
growing-order oversampling nodes of the parent card
`weighted-euler-tangent-global-graph-decoupling` (primes in every
window [y, y + K/log y] of the log line, i.e. multiplicative gaps
[X, X(1+Θ(1/log X))]).

## Banked infrastructure (3-formalized card
`elementary-pnt-power-log-error-infrastructure` + corpus)
- Selberg symmetry formula ≤ 410N; second inequality (800NlogN+2900N);
  exact Tatuzawa–Iseki; ψ-recursion 400N; fiber transfer machinery
  (m-space ladders, window contractions); ψ ~ x (qualitative);
  θ-PNT; window prime supply; all sqrt-log/threshold tooling.

## Route candidates (rng-pick on next session; read 5-failed first)
1. **Wirsing iteration**: quantify the descent a_{k+1} = a_k − c·θ(a_k)
   with EXPLICIT threshold bookkeeping x₀(k) — the naive descent gives
   tower-growth thresholds (useless); Wirsing's averaged/smoothed
   version turns the recursion into an integral inequality for
   V(u) := sup-ratio at scale e^u with V(u) ≤ (1/u)∫₀ᵘ V(t)dt·(1−gain)
   ⟹ V(u) = O(u^{−B}) after B bootstraps. Formalization surface:
   discrete integral inequalities over the banked recursion.
2. **Bombieri higher-energy**: the ψ₂ = Λ·L + Λ*Λ second-order symmetry
   (BANKED as selberg_symmetry_formula/W-machinery!) + the E-functional
   iteration gives O(x/log^B x) for all B. Heavier combinatorics, more
   reuse of banked Selberg weights.
3. **Analytic dlVP**: mathlib ζ + 3-4-1 quantitative zero-free region +
   Perron. Least corpus reuse; large new complex-analytic surface.

## Status
- [2026-07-24] Card created from the parent-card rate audit (fixed-order
  (8a) cap min(σ, δ/2) < β — see parent card entry). No Lean yet.
- NEXT: rng-pick route (1) vs (2); write the quantitative recursion
  statement in the chosen form; numerically certify the iteration
  constants (log-space, print trial counts); first brick = the smoothed
  ratio functional definition + its recursion inequality from
  `psi_ratio_recursion_step`.

## Progress
- [2026-07-24] **Route locked by rng: analytic-dlvp** (seed
  1588581942809745547). Scouting: mathlib has NO quantitative zero-free
  region (ZetaZeros.lean is qualitative discreteness only) but HAS the
  quantitative 3-4-1 seed `norm_LSeries_product_ge_one` (public, in
  LSeries/Nonvanishing) and `riemannZeta_residue_one`; corpus has Perron
  rectangle machinery (PerronMellinSeamResidue, PerronBoundaryCharge,
  PerronCarrierFlankMass) reusable for the contour step. KEY RELIEF: a
  zero-free region of ANY log-power width c/log^a t yields
  ψ error O(x·exp(−c′(log x)^{1/(1+a)})) ≪ x/log^B x ∀B — crude
  constants suffice throughout.
- [2026-07-24] **(Z1a) DONE — sawtooth tail** (`ZetaSawtoothTail.lean`,
  umbrella-registered, build clean, standard axioms, index regenerated).
  `zetaSawtoothTail N s := ∫_{Ioi N} {u}·u^{−s−1}`;
  `integrableOn_sawtooth_cpow` (Re s > 0; AEStronglyMeasurable via
  measurable fract-cast × ContinuousOn cpow — NOTE: `Measurable.cpow`
  does NOT exist in mathlib, and `Complex.continuousAt_ofReal_cpow` is
  the PAIR version needing explicit (f := ...) in .comp);
  `norm_zetaSawtoothTail_le`: ‖tail‖ ≤ N^{−Re s}/Re s (exact rpow
  integral `integral_Ioi_rpow_of_lt`).
- NEXT (Z1b): the truncated representation identity on Re s > 1:
  `ζ(s) = Σ_{n≤N} n^{−s} + N^{1−s}/(s−1) − s·zetaSawtoothTail N s` —
  via Abel/partial summation of the tsum tail Σ_{n>N} n^{−s}: write
  n^{−s} = s∫_n^{n+1}⌊u⌋? standard: Σ_{n>N}n^{−s} = s∫_N^∞⌊u⌋u^{−s−1}du
  (Re s > 1) and ∫_N^∞ u·u^{−s−1} = N^{1−s}/(s−1) + ... assemble with
  ⌊u⌋ = u − {u}. Formalization: interval-sum decomposition of the
  integral over ⋃[n, n+1) (corpus `IocPartitionSum`-style / mathlib
  `integral_Ioi` σ-additivity + per-interval constant ⌊u⌋ = n), then
  geometric/telescoping. Then (Z1c) holomorphy of the tail in s on
  Re > 0 (parametric holomorphic integral — mathlib
  `hasDerivAt_integral_of_dominated...`; or Morera via corpus tooling);
  (Z1d) identity-theorem extension of the representation to Re > 0
  (mathlib `AnalyticOnNhd.eqOn` on the connected set {Re > 0}\{1});
  (Z2) vertical growth |ζ(σ+it)| ≤ C log|t|; then 3-4-1 region, ζ'/ζ,
  Perron.
- [2026-07-24] **(Z1b-i) DONE — unit-interval integration core**
  (`ZetaUnitIntervalIntegrals.lean`, umbrella-registered, build clean,
  standard axioms, index regenerated).
  `integral_Ioc_ofReal_cpow` (exact FTC: ∫_{Ioc a b} u^r =
  (b^{r+1} − a^{r+1})/(r+1), r ≠ −1, via
  `hasDerivAt_ofReal_cpow_const'`);
  `eq_head_of_hasSum_telescope` (HasSum of telescope of null sequence =
  head, via `Finset.sum_range_sub'` + uniqueness of limits);
  `integrableOn_Ici_ofReal_cpow` (Re r < −1);
  `iUnion_Ico_unit` + `hasSum_integral_Ico_unit` (unit-interval HasSum
  decomposition of ray integrals via `hasSum_integral_iUnion` — NO
  summability side conditions needed);
  `integral_Ici_ofReal_cpow` (∫_c^∞ u^r = −c^{r+1}/(r+1)).
  LEAN GOTCHAS RECORDED: `ring` treats cpow bases as opaque atoms — the
  ℝ-level bases `c+k+1` vs `c+(k+1)` must be bridged by an explicit
  cast-equality rw BEFORE ring (assoc differences inside casts are
  invisible to ring's normalization); `intervalIntegral.integral_eq_sub_
  of_hasDerivAt` with ?_ placeholders can't infer its bounds — state
  the FTC as a fully-typed have and apply.
- NEXT (Z1b-ii): the floor-weighted pieces:
  ∫_{Ico(N+k, N+k+1)}⌊u⌋₊·u^{−s−1} = (N+k)·(piece) (floor constant on
  Ico via `Nat.floor_eq_iff` + `setIntegral_congr_fun`), telescoping sum
  via the SECOND decomposition (N+k)(g k − g(k+1)) = (f k − f(k+1)) +
  g(k+1) with f k := (N+k)·g k (HasSum arithmetic: `hasSum_nat_add_iff`
  for the ζ-tail + HasSum.sub + eq_head telescope, avoiding raw
  summability of f); Int.fract u = u − ⌊u⌋₊ on u ≥ 0
  (`Int.self_sub_floor`… probe `Int.fract` vs Nat.floor cast); assemble
  `zeta_eq_truncated`: ζ(s) = Σ_{n≤N}n^{−s} + N^{1−s}/(s−1) −
  s·zetaSawtoothTail N s on Re s > 1 (`zeta_eq_tsum_one_div_nat_cpow`).
  Then (Z1c) tail holomorphy, (Z1d) identity-theorem extension to
  Re > 0, (Z2) growth bounds.
