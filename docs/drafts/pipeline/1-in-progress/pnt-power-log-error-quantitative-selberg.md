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
- [2026-07-24] **(Z1b-ii) DONE — the truncated ζ-representation**
  (`ZetaTruncatedRepresentation.lean`, umbrella-registered, build clean,
  standard axioms, index regenerated).
  **`zeta_eq_truncated`**: for Re s > 1, 1 ≤ N:
  ζ(s) = Σ_{n∈Icc 1 N} n^{−s} + N^{1−s}/(s−1) − s·zetaSawtoothTail N s.
  Proof: floor-weighted tail telescope (unit-interval HasSum from
  Z1b-i + floor constant on Ico via `Nat.floor_eq_iff` +
  `A_{k+1} = A_k + 1` rw-then-ring at the atom level +
  `eq_head_of_hasSum_telescope`) gives s·T = N^{1−s} + Tζ; fract split
  {u} = u − ⌊u⌋₊ (`Int.self_sub_floor` + `Int.natCast_floor_eq_floor`)
  + exact power integral (Z1b-i) gives tail = N^{1−s}/(s−1) − T; ζ-side
  from `zeta_eq_tsum_one_div_nat_cpow` + `Summable.sum_add_tsum_nat_add`
  (bottom-peel `Finset.sum_range_succ'`, 0-term dies by `zero_cpow`);
  closed by linear_combination with the explicit inverse-cancellation
  witness `(s−1)(s−1)⁻¹ = 1` (ring1 can't cancel inverse atoms without
  it). GOTCHAS: rw-show on exponents rewrites its own subterms (state
  product→power direction instead); `↑↑N` (ℕ→ℝ→ℂ) vs `↑N` (ℕ→ℂ) are
  distinct ring atoms — push_cast before final ring; paren-balance in
  multiline have-types (2 rounds lost).
- NEXT (Z1c): holomorphy of `zetaSawtoothTail N ·` on Re s > 0
  (parametric integral: dominated derivative via
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`-family; integrand
  ∂_s = −log u·{u}·u^{−s−1}, dominated by log u·u^{−σ₀−1} locally).
  Then (Z1d) identity-theorem extension of `zeta_eq_truncated` to
  Re s > 0, s ≠ 1 (`AnalyticOnNhd.eqOn` on the connected open set —
  corpus may have identity-theorem tooling from the Paley–Wiener work:
  rg eqOn_of before building); (Z2) vertical growth
  |ζ(σ+it)| ≤ C·log|t| from the N := ⌊|t|⌋ instance.
- [2026-07-24] **(Z1c) DONE — sawtooth tail holomorphy**
  (`ZetaSawtoothHolomorphy.lean`, umbrella-registered, build clean,
  standard axioms, index regenerated).
  `differentiableAt_zetaSawtoothTail` (Re s₀ > 0) via
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the ball
  radius Re s₀/2: parameter-derivative −{u}·log u·u^{−s−1}
  (`HasDerivAt.const_cpow` on w ↦ −w−1), dominating bound
  log u·u^{−σ₁−1} with the log absorbed by `Real.log_le_rpow_div`
  into u^{σ₁/4−σ₁−1}; `analyticOnNhd_zetaSawtoothTail` on {Re > 0}
  via `DifferentiableOn.analyticOnNhd`.
  GOTCHAS: `Complex.continuousAt_log` doesn't exist — route Complex.log
  ∘ ofReal continuity through `Complex.ofReal_log` congruence to
  Real.log; an anonymous `(by positivity)` for a ball radius lets the
  metavariable unify WRONG (picked s₀.re, not s₀.re/2) — pin with
  `show` type ascription.
- NEXT (Z1d): identity-theorem extension: define
  `zetaTruncated N s := Σ_{n≤N} n^{−s} + N^{1−s}/(s−1) −
  s·zetaSawtoothTail N s`; prove AnalyticOnNhd on U := {0 < re} \ {1}
  (finite sum entire-in-s via const_cpow; N^{1−s}/(s−1) analytic off 1;
  tail by Z1c); ζ analytic on U (`differentiableAt_riemannZeta`);
  agreement on {re > 1} (Z1b-ii) + U preconnected (PROBE mathlib for
  punctured-convex connectivity: e.g. `Convex.isPathConnected` minus
  point — search `isConnected_compl_singleton` / build via two convex
  overlapping pieces {re>0, im>−ε}∪{re>0, im<ε} minus... or halfplane
  minus point path-connectedness by hand) + accumulation point 2 ⟹
  `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` gives
  ζ = zetaTruncated on U. Then (Z2) growth: at s = σ+it, |t| ≥ 2,
  σ ≥ 1 − 1/log|t|, N := ⌊|t|⌋: |Σ_{n≤N}n^{−σ}| ≤ Σ n^{−σ} ≤
  e·(log N + 2)-ish (n^{−σ} ≤ e/n for n ≤ N ≈ |t|), |N^{1−s}/(s−1)| ≤
  e/|t|·… , |s·tail| ≤ (|t|+2)·N^{−σ}/σ ≤ e·(1+2/|t|)/σ… — assemble
  |ζ(σ+it)| ≤ C·log|t|. Use banked `sum_inv_le` (ScaleSigmaSum) for the
  harmonic head.
- [2026-07-24] **(Z1d) DONE — the truncated representation on the
  punctured half-plane** (`ZetaTruncatedExtension.lean`,
  umbrella-registered, build clean, standard axioms, index regenerated).
  `zetaTruncated N s` def; **`zeta_eq_truncated_of_re_pos`**:
  ζ(s) = zetaTruncated N s for ALL Re s > 0, s ≠ 1, 1 ≤ N.
  Mechanism: `isPreconnected_halfplane_punctured` — the punctured
  half-plane as a CHAINED UNION OF FOUR CONVEX PIECES ({Re>1} ∪
  upper-quadrant ∪ lower-quadrant ∪ strip {0<Re<1}) glued by
  `IsPreconnected.union` at witnesses 2+I, 2−I, 1/2+I (each piece
  convex via `convex_halfSpace_gt/lt` on the ℝ-linear re/im); both
  sides analytic (`differentiableAt_riemannZeta`, Z1c tail +
  `DifferentiableAt.const_cpow`/`fun_sum`); agreement near z₀ = 2 from
  Z1b-ii; `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` closes.
  GOTCHA: rintro top-level alternation pattern needs full outer parens.
- NEXT (Z2 — vertical growth): `abs_riemannZeta_le_log`:
  ∀ s = σ+it with |t| ≥ 2, 1 − 1/log|t| ≤ σ ≤ 2:
  |ζ(s)| ≤ C·log|t| (C explicit, e.g. 20). Instance N := ⌊|t|⌋₊ of
  zeta_eq_truncated_of_re_pos; pieces:
  (i) |Σ_{n≤N} n^{−s}| ≤ Σ n^{−σ} ≤ Σ e·n^{−1} ≤ e(log N + 2)
  (n^{−σ} = n^{−1}·n^{1−σ} ≤ n^{−1}·N^{1−σ} ≤ n^{−1}·e since
  N^{1/log|t|} ≤ e for N ≤ |t|: log N/log|t| ≤ 1); banked `sum_inv_le`.
  (ii) |N^{1−s}/(s−1)| ≤ N^{1−σ}/|t| ≤ e/2 (|s−1| ≥ |Im| = |t|).
  (iii) |s·tail| ≤ (2+|t|)·N^{−σ}/σ ≤ (2+|t|)·e/(N·σ) ≤ C
  (N ≥ |t|−1, σ ≥ 1/2 for |t| ≥ e²-ish — CAREFUL σ ≥ 1−1/log|t| ≥ 1/2
  for log|t| ≥ 2 i.e. |t| ≥ e²: restrict |t| ≥ 8 or handle σ-floor via
  the bound's monotonicity; also N ≥ 1 needs |t| ≥ 2 ✓ ⌊2⌋=2).
  Also needed for the zero-free region: ζ′ bound — same machinery on the
  DERIVATIVE of the truncated representation (differentiate the finite
  sum: Σ log n·n^{−s}, pole term, tail-derivative with the Z1c formula)
  OR Cauchy estimate from the ζ-growth bound on discs of radius
  1/log|t| (SIMPLER: |ζ′(s)| ≤ sup_{|w−s|=r}|ζ(w)|/r ≤ C·log²|t| —
  one-line from Cauchy + the Z2 bound; needs mathlib
  `norm_deriv_le_of...` Cauchy inequality: `Complex.norm_deriv_le_aux`?
  probe `DiffContOnCl.norm_deriv_le`-family). Then 3-4-1 region.
- [2026-07-24] **(Z2) DONE — ★ THE VERTICAL GROWTH BOUND ★**
  (`ZetaVerticalGrowth.lean`, umbrella-registered, build clean, standard
  axioms, index regenerated).
  **`abs_riemannZeta_le_log`**: |ζ(σ+it)| ≤ 14·log|t| for |t| ≥ 8,
  1 − 1/log|t| ≤ σ ≤ 2. Instance N := ⌊|t|⌋₊ of
  `zeta_eq_truncated_of_re_pos`; head ≤ e(logN+2) via the pointwise
  n^{−σ} ≤ e/n (helper hpow: x^{1−σ} ≤ |t|^{1/log|t|} = e via
  `Real.rpow_def_of_pos`, case split at σ vs 1) + BANKED `sum_inv_le`;
  pole ≤ e/8 (|s−1| ≥ |t| via `Complex.abs_im_le_norm`); tail ≤ 5e
  (`norm_zetaSawtoothTail_le` + N ≥ |t|/2 + σ ≥ 1/2 from log|t| > 2 =
  log e² < log 8); final nlinarith with the (14−e)(log−2) ≥ 0 product
  hint. Certified 200k trials (C = 14, slack ~8%).
  Gotchas: `le_or_lt` → `le_or_gt`, `div_le_div_iff` → `div_le_div_iff₀`
  (recurring renames); exp2 < 8 needs the explicit square hint.
- NEXT (Z3 — ζ′ growth via Cauchy): |ζ′(σ+it)| ≤ C′·log²|t| for
  |t| ≥ 16?, σ ≥ 1 − 1/(2log|t|): Cauchy estimate on the disc of radius
  r := 1/(2log|t|) centered at s (disc stays inside the Z2 region:
  σ − r ≥ 1 − 1/log|t| ✓ and |Im| ≥ |t| − r ≥ 8 ✓, Re ≤ 2 + r —
  EXTEND Z2's σ-ceiling to 3 (same proof, hpow unaffected; hσ2 ≤ 3
  and |σ| ≤ 3 in (iii): redo constant → C = 15?) or shrink the disc.
  Mathlib Cauchy bound: `Complex.norm_deriv_le_of_forall_mem_sphere...`?
  probe `norm_deriv_le` variants / `Complex.deriv_eq_smul_circleIntegral`;
  simplest: `Complex.norm_deriv_le_max_of_...`? Check
  DiffContOnCl.norm_deriv_le or use the corpus Cauchy machinery
  (WeightedEulerLambertDerivativeBound used a Cauchy estimate —
  `norm_iteratedDeriv_le_of...`? rg the corpus for the Cauchy-disc
  derivative bound it used and REUSE). Then (Z4) the 3-4-1 zero-free
  region: mathlib `norm_LSeries_product_ge_one` at χ = 1 (check its
  ζ-specialization: `norm_zeta_product_ge_one`? probe) + Z2 + Z3 ⟹
  ∃c>0: ζ(β+it) ≠ 0 for β > 1 − c/log⁹|t|; then ζ′/ζ bounds and Perron.
- [2026-07-24] **(Z3) DONE — ζ′ growth** (`ZetaDerivGrowth.lean`,
  umbrella-registered, build clean, standard axioms, index regenerated).
  **`abs_deriv_riemannZeta_le_sq_log`**: |ζ′(σ+it)| ≤ 112·log²|t| for
  |t| ≥ 9, 1 − 1/(4log|t|) ≤ σ ≤ 3/2. Cauchy estimate
  (`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` at
  order 1 — REUSED from the corpus Lambert-derivative pattern) on the
  disc radius 1/(4log|t|); disc points satisfy Z2's hypotheses AT THEIR
  OWN HEIGHT via log|w.im| ≤ 2log|t| (|w.im| ≤ |t|² — the key
  observation that kills the height-drift problem), sphere bound
  28·log|t|; the ≤ 3/2 σ-ceiling keeps discs under Z2's ceiling 2 —
  and suffices for the zero-free region (only σ near 1 needed).
  Certified 200k trials incl. all four disc corners.
  Gotcha reconfirmed: nested-abs `||a|−|b||` must be parenthesized
  `|(|a|−|b|)|`; `div_one_div` doesn't exist — field_simp identity have.
- NEXT (Z4 — the 3-4-1 zero-free region): probe mathlib's
  `norm_LSeries_product_ge_one`/ζ-specialization
  (`norm_zeta_product_ge_one`?) for the quantitative seed
  ‖ζ(σ)³ζ(σ+it)⁴ζ(σ+2it)‖ ≥ 1 (σ > 1); combine with:
  (a) |ζ(σ)| ≤ 1/(σ−1) + C₀ near 1⁺ (from the truncated representation
  at N = 1! zetaTruncated 1 s = 1 + 1/(s−1) − s·tail with |tail| ≤
  1/σ: |ζ(σ)| ≤ 1/(σ−1) + 1 + 2·2 = 1/(σ−1) + 5 for real σ ∈ (1, 2] —
  easy corollary);
  (b) zero at β+it with β close to 1: |ζ(σ+it)| = |ζ(σ+it) − ζ(β+it)|
  ≤ (σ−β)·sup_{[β,σ]}|ζ′| ≤ (σ−β)·112·log²|t| (mean value / FTC along
  the real segment: mathlib `Complex.norm_sub_le_of_...`?
  `norm_image_sub_le_of_norm_deriv_le_segment` ✓ exists for segments);
  (c) |ζ(σ+2it)| ≤ 14·log(2|t|) ≤ 28log|t| (Z2 at height 2t ✓);
  then 1 ≤ (1/(σ−1)+5)³·((σ−β)112log²)⁴·28log ⟹ optimize σ := 1 +
  c₁/log⁹|t| ⟹ 1 − β ≥ c/log⁹|t|. CERTIFY the optimization constants
  in log-space FIRST (print trial counts). State:
  `riemannZeta_ne_zero_of_re_gt`: ∃c>0 explicit (e.g. c = 10⁻¹²), ∀t,
  |t| ≥ 9 → ∀β, 1 − c/log⁹|t| < β → ζ(β+it) ≠ 0. Then (Z5) ζ′/ζ and
  the Perron assembly toward ψ.
- [2026-07-24] **(Z4a) DONE — 3-4-1 seed + pole bound**
  (`ZetaThreeFourOne.lean`, umbrella-registered, build clean, standard
  axioms, index regenerated).
  **`norm_zeta_product_ge_one`**: 1 ≤ ‖ζ(1+x)³ζ(1+x+iy)⁴ζ(1+x+2iy)‖
  (x > 0) — mathlib `DirichletCharacter.norm_LSeries_product_ge_one` at
  the trivial character mod 1, bridged by `one_pow` + simp
  `modOne_eq_one` + `LSeries_one_eq_riemannZeta` at the three points.
  **`abs_riemannZeta_one_add_le`**: ‖ζ(1+x)‖ ≤ 1/x + 2 (x > 0) — the
  truncated representation at N = 1 (head = 1, pole = 1/x, |s·tail| ≤
  (1+x)/(1+x) = 1). Also noted: mathlib HAS
  `riemannZeta_ne_zero_of_one_le_re` (β ≥ 1 case free) and
  `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` (the −ζ′/ζ Dirichlet
  series — the (Z5) Perron input!).
- NEXT (Z4b — the region): certify in log-space then formalize
  `riemannZeta_ne_zero_of_re_gt_one_sub`: for |t| ≥ 9, ζ(β+it) ≠ 0
  whenever 1 − c/log⁹|t| < β, c := 1/(2·216·28·224⁴). Proof by
  contradiction: β ≤ 1 wlog (mathlib covers ≥ 1); x := 2·c/log⁹? — set
  x := c₀/(2L⁹) hmm use exact scheme certified earlier: assume zero
  with δ := 1−β ≤ c/L⁹ (c = c₀/2, c₀ := 1/(216·28·224⁴)); pick
  x := c₀/(2L⁹) ≥ δ; mean value on [β, 1+x]: |ζ(1+x+it)| ≤
  (x+δ)·112L² ≤ 2x·112L² = 224xL²; pole: (1/x+5... we have 1/x+2 ≤
  3/x for x ≤ 1... recompute constants: (1/x+2)³ ≤ (3/x)³ = 27/x³
  (x ≤ 1 ⟹ 2 ≤ 2/x): TIGHTER: 27 not 216! K := 27·28·224⁴; recert);
  height-2t: |ζ(1+x+2it)| ≤ 14log|2t| ≤ 28L; product:
  1 ≤ 27/x³·(224xL²)⁴·28L = 27·28·224⁴·x·L⁹ = x/c₀·... contradiction
  when x < c₀/L⁹ ✓ x = c₀/(2L⁹) gives 1 ≤ 1/2 ✗✓.
  Mean-value formalization: f := fun σ' : ℝ => ζ(↑σ'+↑t·I) via
  W(w) := ζ(w+↑t·I) (HasDerivAt.comp with translation) then
  `HasDerivAt.comp_ofReal`; `norm_image_sub_le_of_norm_deriv_le_segment`
  with `HasDerivAt.derivWithin` + `uniqueDiffOn_Icc`; Z3 bounds the
  derivative on [β, 1+x] ⊂ [1−1/(4L), 3/2] ✓.
- [2026-07-24] **(Z4b) DONE — ★ THE DE LA VALLÉE POUSSIN ZERO-FREE
  REGION ★** (`ZetaZeroFreeRegion.lean`, umbrella-registered, build
  clean, standard axioms, index regenerated).
  **`riemannZeta_ne_zero_of_re_gt_one_sub`**: ζ(β+it) ≠ 0 for |t| ≥ 9,
  β > 1 − zetaZeroFreeC/log⁹|t|, `zetaZeroFreeC := 1/(2·27·28·224⁴)`.
  Also `norm_riemannZeta_le_of_zero` (mean value from a hypothetical
  zero along horizontal segments, via `HasDerivAt.comp_ofReal` +
  `norm_image_sub_le_of_norm_deriv_le_segment` + Z3). Proof: β ≥ 1
  killed by mathlib `riemannZeta_ne_zero_of_one_le_re`; else at
  x := c/log⁹: pole cube (3/x)³, mean-value fourth power (224xL²)⁴,
  height-2t factor 28L, and the Z4a product inequality give 1 ≤ 1/2.
  Certified 200k trials. GOTCHA (major, recurring): bare `↑(expr)`
  coercions on compound real expressions mis-elaborate (HAdd ℝ ℝ ℂ
  failures) — ALWAYS write `((expr : ℝ) : ℂ)`; also
  `HasDerivAt.derivWithin` doesn't exist — go through
  `.hasDerivWithinAt.derivWithin`.
- NEXT (Z5 — from the region to ψ): the Perron/Tauberian arc:
  (Z5a) ζ ≠ 0 on the closed region ⟹ bounds on ζ′/ζ = −Σ Λn^{−s}
  (mathlib `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` ✓ noted):
  need |ζ′/ζ(σ+it)| ≤ C log²|t|·(σ−σ_zf)⁻¹-type on the region interior
  — via |1/ζ| bounds: classical: |1/ζ(s)| from the 3-4-1 machinery
  (|ζ(σ+it)| ≥ c(σ−1)^{3/4}log^{-1/4}-type) OR the borel-caratheodory/
  landau approach. SUBSTANTIAL — design next session; alternatively
  investigate the SMOOTHED Perron route that only needs the zero-free
  region + growth bounds via contour shift with explicit kernels
  (corpus Perron rectangle machinery: PerronMellinSeamResidue etc.).
  Target: ψ(x) = x + O(x·exp(−c(log x)^{1/10})) ⟹ x/log^B x ∀B ⟹
  growing-order oversampling nodes ⟹ parent card (8a) full form.
- [2026-07-24] **(Z5a) DONE — ζ lower bounds, part 1**
  (`ZetaLowerBound.lean`, umbrella-registered, FIRST-COMPILE CLEAN,
  build clean, standard axioms, index regenerated).
  **`pow_four_norm_riemannZeta_ge`**: x³/(756·log|t|) ≤ ‖ζ(1+x+it)‖⁴
  (0 < x ≤ 1, |t| ≥ 9) — the 3-4-1 inequality solved for the middle
  factor against the pole cube (3/x)³ and the height-2t bound 28L;
  stated in FOURTH-POWER form (root-free — the division extraction is
  pure field algebra via div_le_iff₀/le_div_iff₀).
  **`norm_riemannZeta_sub_le_segment`**: two-point form of the mean
  value bound (‖ζ(σ'+it) − ζ(β+it)‖ ≤ 112L²(σ'−β) on
  [1−1/(4L), 3/2]) — generalizes the zero-anchored version.
- NEXT (Z5a2 — the region lower bound): choose η := A/L⁹ (A concrete,
  certify: need A^{3/4}/756^{1/4} > 448A i.e. A < 1/(756·448⁴)-ish);
  ‖ζ(σ+it)‖ ≥ (η³/(756L))^{1/4} − 112L²(η+(1−σ)) ≥ c₅/L⁷ for
  σ ≥ 1 − A/(2L⁹): needs the fourth-root extraction from the quartic
  form: y⁴ ≥ z ⟹ y ≥ z^{1/4} (Real.rpow_le_rpow at 1/4 +
  rpow_natCast); THEN (Z5b) |ζ′/ζ| ≤ C₇·L⁹⁺⁷=L¹⁶?? recompute: |ζ′|/|ζ|
  ≤ 112L²·(L⁷/c₅) = C₈L⁹ — wait c₅/L⁷ lower ⟹ ratio ≤ 112L²/(c₅/L⁷)
  = (112/c₅)L⁹ ✓ on the strip σ ≥ 1 − A/(2L⁹), |t| ≥ 9. Then (Z5c) the
  smoothed Perron: kernel x^s/s², identity Σ Λ(n)(log(x/n))⁺ =
  (1/2πi)∫_{(a)}(−ζ′/ζ)x^s/s²ds (termwise: the ABSOLUTELY convergent
  kernel integral (1/2πi)∫_{(a)}y^s/s²ds = (log y)⁺ for y>0 — a
  self-contained contour brick; corpus Perron rectangle machinery for
  the shift); (Z5d) unsmooth via monotonicity of ψ (banked ψ facts).
- [2026-07-24] **(Z5a2) DONE — the strip lower bound**
  (`ZetaStripLowerBound.lean`, umbrella-registered, build clean,
  standard axioms, index regenerated).
  **`pow_four_norm_riemannZeta_ge_strip`**:
  A³/(12096·log²⁸|t|) ≤ ‖ζ(σ+it)‖⁴ on |σ−1| ≤ A/log⁹|t|, |t| ≥ 9,
  `zetaLowerA := 1/(2·448⁴·756)`. Root-FREE: the quartic edge bound
  survives the leftward drift via `le_of_pow_le_pow_left₀` (2D ≤ W from
  (2D)⁴ ≤ Z ≤ W⁴), then ‖ζ(σ)‖ ≥ W/2 by triangle, fourth-powered back.
  The (2D)⁴ ≤ Z reduction is the exact identity 448⁴·756·A = 1/2.
  Cert 200k trials. Gotchas: positivity can't see through the def
  `zetaLowerA` unless `have hA0 := zetaLowerA_pos` is in context;
  `le_of_pow_le_pow_left` → `le_of_pow_le_pow_left₀`.
- NEXT (Z5b): |ζ′/ζ| on the strip: `norm_deriv_div_riemannZeta_le`:
  for |σ−1| ≤ A/(2·log⁹|t|)?, |t| ≥ 9:
  ‖deriv ζ/ζ (σ+it)‖ ≤ 112L²·(12096L²⁸/A³)^{1/4} — the fourth root of
  the strip bound NOW needed for the linear quotient: ‖1/ζ‖ =
  1/‖ζ‖ ≤ (12096L²⁸/A³)^{1/4}: from ‖ζ‖⁴ ≥ q: ‖ζ‖ ≥ q^{1/4}
  (le_of_pow_le_pow_left₀ with (q^{1/4})⁴ = q — rpow or: state the
  BOUND in the form C·L^7 with C⁴ := 12096/A³ as another def constant +
  prove (C·L⁷)-form via the same root-free trick: want ‖1/ζ‖ ≤ B·L⁷
  ⟺ 1 ≤ B·L⁷·‖ζ‖ ⟸ 1 ≤ B⁴L²⁸‖ζ‖⁴ ⟸ B⁴·A³/12096 ≥ 1: define B with
  B⁴ = 12096/A³: B := (12096/A³)^{1/4} irrational... OR define
  zetaInvB via its FOURTH POWER: state ζ′/ζ bound as
  ‖deriv ζ (s)/ζ(s)‖⁴ ≤ (112L²)⁴·12096L²⁸/A³ = C₉L³⁶ — QUARTIC-form
  ζ′/ζ bound! The Perron edge estimates consume ∫‖ζ′/ζ‖ — linear —
  so at SOME point a root is needed; cleanest: take B := 20/A
  (check numerically B⁴ ≥ 12096/A³ ⟺ 160000/A⁴ ≥ 12096/A³ ⟺
  160000 ≥ 12096·A ✓ trivially): so ‖1/ζ(σ+it)‖ ≤ (20/A)·L⁷ with a
  CLEAN rational constant, root-free proof (1 ≤ (20/A)L⁷‖ζ‖ ⟸
  ((20/A)L⁷‖ζ‖)⁴ ≥ (20/A)⁴L²⁸·A³/12096 ≥ 1 ✓). Then |ζ′/ζ| ≤
  112L²·(20/A)L⁷ = (2240/A)L⁹ ✓ ALL RATIONAL. Then (Z5c) Perron.
- [2026-07-24] **(Z5b) DONE — 1/ζ and ζ′/ζ on the strip**
  (`ZetaLogDerivBound.lean`, umbrella-registered, build clean, standard
  axioms, index regenerated).
  **`norm_inv_riemannZeta_le`**: ‖1/ζ(σ+it)‖ ≤ (20/A)·log⁷|t| on
  |σ−1| ≤ A/log⁹|t| — root-free via the rational witness: 1 ≤
  (BL⁷‖ζ‖) from its fourth power ≥ 160000/(12096A) ≥ 1
  (`le_of_pow_le_pow_left₀`), nonvanishing of ζ on the strip extracted
  from the quartic bound.
  **`norm_deriv_div_riemannZeta_le`**: ‖ζ′/ζ(σ+it)‖ ≤
  (2240/A)·log⁹|t| — product of Z3's derivative bound with the inverse
  bound (strip ⊂ derivative region via A/L⁹ ≤ 1/(4L)).
  Gotcha: `simp at` a hypothesis containing `log |t|` rewrites to
  `log t` (log_abs is simp) splitting linarith atoms — use targeted rw.
- NEXT (Z5c — the smoothed Perron). Sub-bricks:
  (Z5c1) the kernel identity: for y > 0, a > max 1 (log y-safe):
  (1/2π)∫_{ℝ} y^{a+iτ}/(a+iτ)² dτ = (log y)⁺ — real-variable form of
  (1/2πi)∫_{(a)}y^s/s²ds; formalization via differentiation under the
  integral in log y? CLASSICAL proof: contour/residues; ALTERNATIVE
  elementary: Fourier inversion of the triangle... Actually the
  cleanest formal route: BOTH sides as functions of u := log y satisfy
  F(u) = e^{au}·(1/2π)∫ e^{iuτ}/(a+iτ)²dτ and the inner integral is the
  Fourier transform of a known L¹ function: (a+iτ)⁻² = FT of
  t·e^{−at}·1_{t>0} (Gamma integral: ∫₀^∞ t e^{−(a+iτ)t}dt =
  (a+iτ)⁻²): Fourier inversion ⟹ inner = 2π·u·e^{−au}·1_{u>0} ⟹
  F(u) = u⁺ ✓. Mathlib has Fourier inversion
  (`MeasureTheory.Integrable.fourier_inversion`?) and the Gamma-type
  integral (`integral_exp_neg_mul...`/`Real.Gamma` at 2). CHECK CORPUS
  Perron modules FIRST (PerronMellinSeamResidue may already have kernel
  evaluations!). (Z5c2) sum-integral swap: Σ_n Λ(n)·kernel(x/n) with
  absolute convergence at a := 1+1/log x; mathlib
  `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` connects Σ to −ζ′/ζ.
  (Z5c3) contour shift to σ₀ := 1 − A/(2log⁹T) up to height T +
  optimization T := exp((log x)^{1/10}).
- [2026-07-24] **(Z5c1-i) DONE — the Laplace kernel integral**
  (`PerronLaplaceKernel.lean`, umbrella-registered, build clean,
  standard axioms, index regenerated).
  **`integral_mul_exp_neg_mul_Ioi`**: ∫₀^∞ t·e^{−ct}dt = 1/c² for
  Re c > 0 — improper FTC (`integral_Ioi_of_hasDerivAt_of_tendsto`,
  module path: Mathlib.MeasureTheory.Integral.IntegralEqImproper!)
  with antiderivative −((t/c + 1/c²)·e^{−ct}); integrability via the
  elementary `le_exp_half` (v ≤ e^{v/2} from (v/4+1)² squares) taming
  t·e^{−rt} ≤ (1/r)e^{−rt/2}; vanishing at ∞ via `squeeze_zero_norm'`
  (eventual form — the pointwise form forced a FALSE |s| ≤ s claim at
  negative s; eventual + `eventually_ge_atTop` is the right tool).
  Gotchas: keep exp-derivative value in mathlib's order (exp·(−c)) to
  avoid atom flips; `rw [← exp_add]` leaves exp 0 artifacts — chain
  the zero-argument show + exp_zero + one_mul explicitly;
  `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero` is Real-namespaced.
- NEXT (Z5c1-ii — the Fourier inversion step): identify
  (a + 2πiξ)⁻² = 𝓕(fun u => u·e^{−au}·1_{u>0})(ξ) (from THIS brick at
  c := a + 2πiξ — the FT integral ∫e^{−2πiuξ}g(u)du restricts to Ioi 0
  and equals the Laplace integral; mathlib `Real.fourierIntegral`
  conventions: 𝓕 f ξ = ∫ e^{−2πi x ξ} f x); then inversion
  (`MeasureTheory.Integrable.fourier_inversion` — probe exact name/
  hypotheses: g continuous ✓ (0 at 0), g integrable ✓, 𝓕g integrable
  (decay ξ⁻²) ✓) gives the kernel identity
  (1/2π)∫ y^{a+iτ}/(a+iτ)²dτ = (log y)⁺ after τ := 2πξ change of
  variables (mathlib `integral_comp_mul_left`-family). Then (Z5c2)
  sum-swap with Λ, (Z5c3) contour shift.
- [2026-07-24] **(Z5c1-ii) DONE — the tent transform**
  (`PerronTentTransform.lean`, umbrella-registered, build clean,
  standard axioms, index regenerated; one-name fix round: `neg_le_abs`).
  `perronTent a := 1_{u>0}·u·e^{−au}` (indicator form matching the
  Laplace lemma's integrand exactly);
  **`fourier_perronTent`**: 𝓕(perronTent a)(w) = (a+2πiw)⁻² — via
  `Real.fourier_real_eq` + indicator/character fold + the banked
  Laplace integral at c := a+2πiw;
  `integrable_perronTent` (indicator↔IntegrableOn);
  `continuous_perronTent` (trichotomy at 0: squeeze with
  |u|e^{|a||u|}; ContinuousAt.congr_of_eventuallyEq on both open
  sides).
- NEXT (Z5c1-iii — inversion assembly): (i) integrability of the
  transform: ‖(a+2πiw)⁻²‖ = 1/(a²+4π²w²) ≤ C/(1+w²) with C :=
  max(1/a², 1/(4π²))-style (comparison against
  `integrable_inv_one_add_sq` — probe exact mathlib name);
  (ii) `MeasureTheory.Integrable.fourierInv_fourier_eq`
  (integrable_perronTent, (i), continuous_perronTent) gives
  𝓕⁻(𝓕 tent) = tent pointwise;
  (iii) unfold 𝓕⁻ (`Real.fourierInv_real_eq`? probe) to the kernel
  identity: ∫ e^{2πiuw}(a+2πiw)⁻²dw = u·e^{−au}·1_{u>0}; at u := log y
  multiply by y^a = e^{au}: ∫ y^{a+2πiw}... — the (log y)⁺ kernel
  identity in ξ-normalized form (SKIP the τ=2πξ change of variables:
  state the Perron identity in the 2πξ convention throughout — the
  contour parametrization is ours to choose!). Then (Z5c2) Λ-sum swap.
