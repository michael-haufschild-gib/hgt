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

### (Z5c1-iii) DONE — Perron kernel identity via Fourier inversion
`RHTower/PerronKernelIdentity.lean` [PROVED HERE], axioms [propext, Classical.choice, Quot.sound], `lake build` clean:
- `integrable_fourier_perronTent` : `Integrable (𝓕 (perronTent a))` — dominate `‖(a+2πiw)⁻²‖ = 1/(a²+(2πw)²)` by `C·(1+w²)⁻¹`, `C := 1/a² + 1/(4π²)`; cross-multiplied comparison `1+w² ≤ C(a²+(2πw)²)` from `C·a² = 1 + a²/(4π²)` and `C·(2πw)² = (2πw)²/a² + w²` (field_simp identities + nlinarith).
- `perron_kernel_identity` : `∫ w, e^{i·2π(wu)} • (a+2πiw)⁻² = perronTent a u` — `Integrable.fourierInv_fourier_eq` (pin `(v := u)`!) + `Real.fourierInv_eq'` + integral_congr_ae with `fourier_perronTent`; inner product folded by `simp [RCLike.inner_apply]; ring`.
- GOTCHAS: (1) `FourierTransformInv.fourierInv` is a CLASS METHOD on function types — applying it to a literal lambda in a theorem STATEMENT stalls instance synthesis (`FourierTransformInv ((w:ℝ) → ?m) ?m` timeout). State kernel identities in ∫-form via `fourierInv_eq'`, never through the 𝓕⁻ symbol applied to a lambda. (2) `𝓕`/`𝓕⁻` notations live in `open scoped FourierTransform`; `fourierInv_eq'`/`fourier_eq'` are `Real.`-namespaced. (3) `open ... in` cannot sit between a docstring and its theorem.

NEXT (Z5c2 — Λ-sum swap): with kernel K_a(u) := perronTent a u at u = log(x/n), build
`Σ' n, Λ(n)·K_a(log x − log n) = ∫ w, e^{i·2πw·log x}·(a+2πiw)⁻²·Σ Λ(n)n^{−(a+2πiw·… )}` —
concretely: (i) absolute convergence of Σ Λ(n)/n^a · (kernel at log(x/n)) for a := 1+1/log x
(compare Σ Λ(n)n^{−a} = −ζ′/ζ(a) < ∞ via mathlib `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`,
`ArithmeticFunction.LSeries_vonMangoldt` names to re-probe); (ii) swap Σ and ∫ by dominated
convergence / `MeasureTheory.integral_tsum` with the integrable dominator from
`integrable_fourier_perronTent` scaled by Σ Λ(n)n^{−a}; result: smoothed explicit-sum
`ψ_tent(x) = (1/…)∫ (−ζ′/ζ)(a+2πiw)·x^{a+2πiw}/(a+2πiw)² dw` in the 2πξ convention.

### (Z5c1-iv + Z5c2) DONE — weighted kernel + smoothed Perron explicit formula
Numeric certificates: (i) kernel convention, 7 trials, err ≤ truncation tail (~2.5e-4), Im ≈ 0 — the `dw`-parametrization s = a+2πiw absorbs 1/2πi exactly; (ii) FULL identity Σ Λ(n)(log(x/n))⁺ = ∫(−ζ′/ζ)(s)x^s/s² dw at x=20, a=1.3, W=400: 13.8868 vs 13.8877, diff 8.3e-4 < tail 0.019, 12 trials.
`RHTower/PerronWeightedKernel.lean` [PROVED HERE], standard axioms, built:
- `perron_weighted_kernel` : `∫ w, exp((a+2πiw)u)/(a+2πiw)² = ((max u 0 : ℝ):ℂ)` for a > 0 — pull `e^{au}` out via `integral_const_mul` (unconditional, no integrability needed), then `perron_kernel_identity`; tent collapse case-split on u ≤ 0 / u > 0.
`RHTower/PerronVonMangoldtSwap.lean` [PROVED HERE], standard axioms, built, FIRST-TRY clean compile (280 lines):
- `one_add_sq_le` (private), `norm_perron_integrand` (‖e^{su}/s²‖ = e^{au}/(a²+(2πw)²)), `integrable_perron_integrand` (mono vs (e^{au}C)(1+w²)⁻¹), `def perronVonMangoldtTerm`,
- **`smoothed_chebyshev_eq_perron_integral`** : for x > 0, a > 1: `∑' n, Λ(n)·(log(x/n))⁺ = ∫ w, (−ζ′/ζ)(a+2πiw)·x^{a+2πiw}/(a+2πiw)² dw`.
- Working names: `integral_tsum_of_summable_integral_norm` (plain real summability — NO ENNReal needed, avoid `integral_tsum`), `ArithmeticFunction.LSeriesSummable_vonMangoldt`, `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`, `summable_norm_iff` (finite-dim: ℂ-summable → norm-summable), `Complex.mul_cpow_ofReal_nonneg`, `Complex.inv_cpow` (arg ≠ π via `arg_ofReal_of_nonneg` + `pi_ne_zero.symm`), `Complex.norm_cpow_eq_rpow_re_of_pos`, `Real.rpow_def_of_pos`, `Real.div_rpow`, `tsum_mul_right` (unconditional), `LSeries f s = ∑' term` is rfl.
- GOTCHA: `Complex.mul_cpow_ofReal_nonneg` matches `(↑a*↑b)^r` (product of casts) — must first split `↑(x/n)` into `↑x * ↑((n)⁻¹)` by a `show`-cast identity, THEN apply.

NEXT (Z5c3 — contour shift): move the w-integral from Re s = a := 1+1/log x to σ₀ := 1 − A/(2·log⁹ T) up to height T, using: zero-freeness `riemannZeta_ne_zero_of_re_gt_one_sub`, strip bound `norm_deriv_div_riemannZeta_le` (‖ζ′/ζ‖ ≤ (2240/A)log⁹|t| on |σ−1| ≤ A/log⁹|t|, |t| ≥ 9). Plan: (i) split ∫_ℝ = ∫_{|w|≤T/2π} + tails; tail bound directly: |integrand| ≤ ‖ζ′/ζ(a+2πiw)‖·x^a/(a²+4π²w²) with ‖ζ′/ζ‖ ≤ crude bound on Re = a (∑Λ(n)n^{-a} ≤ ζ′/ζ(a) ~ log x — corpus probe: bound −ζ′/ζ(a) ≤ 1/(a−1)+C via truncated rep? simpler: ‖ζ′/ζ(a+it)‖ ≤ −ζ′/ζ(a) = Σ Λ n^{-a}, monotone domination — need a Lean lemma `norm_LSeries_le_LSeries_of_nonneg`); (ii) rectangle: Cauchy–Goursat on [σ₀, a]×[−T, T] for the function F(s) := (−ζ′/ζ)(s)·x^s/s² — holomorphic on the zero-free rectangle EXCEPT s=1 pole of ζ′/ζ (residue −1·x/1² → main term x·(…)? CAREFUL: −ζ′/ζ has simple pole at s=1 residue +1, kernel x^s/s² at s=1 → residue x). Corpus rectangle machinery to probe FIRST: `formal_tools.py research "rectangle contour Cauchy"` — PerronMellinSeamResidue, PerronBoundaryCharge, RectangleIntegral (mathlib `Mathlib.Analysis.SpecialFunctions.Complex.RectangleIntegral`? or corpus HolomorphicOn rectangle lemmas). Optimization T := exp((log x)^{1/10}) LAST (Z5c3-final).

### (Z5c3a) DONE — low-height zero-free margin
Numeric cert: min |ζ| on |s−1| = 1/8 circle = 7.43 (provable bound 8 − 16/7 = 40/7 ≈ 5.71 > 0), 128 trials.
`RHTower/ZetaLowHeightZeroFree.lean` [PROVED HERE], standard axioms, built:
- `riemannZeta_ne_zero_of_near_one` : ζ(s) ≠ 0 for s ≠ 1, ‖s−1‖ ≤ 1/8 — from banked `zeta_eq_truncated_of_re_pos` at N=1 (ζ = 1 + 1/(s−1) − s·tail): 8 ≤ ‖1/(s−1)‖ = ‖s·tail − 1‖ ≤ (9/8)(8/7)+1 = 16/7, contradiction. `linear_combination -htr` extracts the pole identity cleanly after `Complex.one_cpow` simplifications.
- `exists_low_height_zeta_zero_free` : ∃ δ ∈ (0,1/8], no zeros in {1−δ ≤ Re, |Im| ≤ 9} ∖ {1} — by_contra + sequence of zeros at δₙ = min(1/8, 1/(n+1)); zeros forced into compact box [7/8,1]×[−9,9]∖B(1,1/8) (near-pole lemma + mathlib `riemannZeta_ne_zero_of_one_le_re` push them off both exclusions); `IsCompact.tendsto_subseq` → limit zero on Re = 1 → contradiction.
- GOTCHAS: (1) `push_neg` now DEPRECATED (warning breaks lint gate) — use `push Not at`. (2) `one_cpow` needs `Complex.` prefix here. (3) `tendsto_one_div_add_atTop_nhds_zero_nat` + `StrictMono.le_apply` + `squeeze_zero` for the subsequence rate; min-limit via `(continuous_const.min continuous_id).continuousAt.tendsto.comp`. (4) box boundedness via `Complex.re_add_im` + `norm_add_mul_I` + `sqrt_le_sqrt` to closedBall 0 10.

NEXT (Z5c3b — analytic scaffolding for the rectangle): F(s) := (−ζ′/ζ)(s)·x^s/s². Sub-steps: (i) DifferentiableOn ℂ F on {rectangle} ∖ {1} given zero-freeness (deriv ζ analytic: `differentiableAt_riemannZeta` + `DifferentiableAt.deriv`? need analyticity of deriv ζ — ζ analytic on open ℂ∖{1} → deriv analytic: mathlib `AnalyticOnNhd.deriv`/`DifferentiableOn.deriv` route via `Complex.analyticOnNhd_iff_differentiableOn` on open sets); (ii) the pole split: −ζ′/ζ − 1/(s−1) has REMOVABLE singularity at 1 (mathlib only has `riemannZeta_residue_one`/`tendsto_riemannZeta_sub_one_div` — build E(s) := ζ(s) − 1/(s−1) with `Complex.differentiableOn_update_limUnder_of_isLittleO`/removable-singularity API `Complex.analyticAt_of_differentiable_punctured...`? probe `Mathlib.Analysis.Complex.RemovableSingularity`: `Complex.differentiableOn_update_limUnder_insert_of_isLittleO`, `Complex.analyticAt_update_of_bounded`? exact names TBD); then Z := (s−1)E+1 entire, Z(1)=1, −ζ′/ζ = 1/(s−1) − Z′/Z near 1. (iii) Goursat on rectangle for the regular part (mathlib `Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`), explicit rectangle integral of x^s/((s−1)s²)'s pole term → residue x — check corpus `rectIntegral` def in XiGuinandWeilContourSynthesis (`rectIntegral_regularizedCauchySynthesis_entire` gives 2πi·g(p) pattern to imitate). (iv) edge estimates with `norm_deriv_div_riemannZeta_le` + T-tail of the a-line integral.

### (Z5c3b-ii) DONE — entire pole unit + log-derivative split
Numeric cert: −ζ′/ζ = 1/(s−1) − Z′/Z at 3 points, err ≤ 1e-16.
`RHTower/ZetaPoleSplit.lean` [PROVED HERE], standard axioms, built:
- `zetaRegularized` := update (ζ − 1/(s−1)) 1 γ; `differentiable_zetaRegularized` (removable singularity: `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` + `continuousAt_update_same` + mathlib `tendsto_riemannZeta_sub_one_div`).
- `zetaPoleUnit` Z := (s−1)·zetaRegularized + 1, ENTIRE (`differentiable_zetaPoleUnit`), `zetaPoleUnit_of_ne` (= (s−1)ζ off 1), `zetaPoleUnit_one` (= 1), `zetaPoleUnit_ne_zero`.
- **`neg_zeta_logDeriv_eq`** : −ζ′/ζ(s) = 1/(s−1) − Z′/Z(s) for s ≠ 1, ζ(s) ≠ 0 — via `EventuallyEq.deriv_eq` (ζ =ᶠ Z/(·−1) on {1}ᶜ), `HasDerivAt.div`, field_simp+ring.
- GOTCHAS: `Function.update_noteq`→`Function.update_of_ne`, `Function.update_same`→`Function.update_self`; `differentiableAt_id'`/`differentiable_id'` gone — use `differentiableAt_id`/`differentiable_id`; `Differentiable.analyticAt` gives entire→AnalyticAt (for deriv-of-entire use `.analyticAt.deriv`).

NEXT (Z5c3b-iii — rectangle Goursat for the regular part): G(s) := (Z′/Z)(s)·x^s/s² is DifferentiableOn the zero-free rectangle [σ₀,a]×[−T,T] (Z ≠ 0 there: zetaPoleUnit_ne_zero + zero-freeness incl. Z(1) = 1 ≠ 0 — note Z′/Z is differentiable AT s=1 too, no puncture needed!); apply `Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`. Then the pole part x^s/((s−1)s²): rectangle integral = 2πi·x (residue at s=1; s=0 outside rectangle since σ₀ > 0) — imitate corpus `rectIntegral_regularizedCauchySynthesis_entire` (XiGuinandWeilContourSynthesis) which proves exactly the 2πi·g(p) rectangle-residue pattern; probe its `rectIntegral` def for reuse. Assemble: a-line integral = σ₀-line integral + horizontal edges + 2πi·x·(1/2πi → dw normalization: CAREFUL — our ∫dw parametrization vs rectIntegral's ds = idw on vertical edges; the vertical-edge integral in s-coords is I·∫dw so the dw-integral of F equals (1/i)·vertical-edge; track factors numerically before writing).

### (Z5c3b-iii part 1) DONE — relative rectangle Cauchy formula
`RHTower/RectangleCauchyFormulaOn.lean` [PROVED HERE], standard axioms, built:
- `rectIntegral_cauchyFormula_analyticOnNhd` : ∮_rect g(z)/(z−p) = 2πi·g(p) for g `AnalyticOnNhd ℂ g U` with closed rectangle ⊆ U, p strictly inside — generalizes corpus `rectIntegral_cauchyFormula_entire` (dslope argument relativized; edge continuity from AnalyticAt.continuousAt with pinned `ContinuousAt.comp (f := edge-map)` — the unifier mis-splits `fun x => q (↑x + ↑c*I)` unless f is pinned).
- CORPUS BANK for rectangles (RectangleResidue.lean): `rectIntegral` def (mathlib boundary orientation), `rectIntegral_cauchyKernel` (2πi winding), `rectIntegral_eq_zero_of_analyticOnNhd` (Goursat, hypothesis: closed rect `uIcc ×ℂ uIcc ⊆ U`, AnalyticOnNhd — U need NOT be open), `rectIntegral_add` (8 edgewise IntervalIntegrable hypotheses), `rectIntegral_const_mul`, `rectIntegral_congr (S := edge-superset)`.

NEXT (Z5c3b-iii part 2 — Perron rectangle assembly), file `PerronRectangleResidue.lean`:
theorem: for x > 0, corners z₁ z₂ with 0 < z₁.re < 1 < z₂.re, z₁.im < 0 < z₂.im, and zero-freeness `∀ s, s.re ∈ uIcc → s.im ∈ uIcc → s ≠ 1 → ζ s ≠ 0` on the closed rectangle:
  `rectIntegral (fun s => (-(deriv riemannZeta s / riemannZeta s)) * ((x:ℂ)^s / s^2)) z₁ z₂ = 2πi·x`.
Proof plan: (i) g := fun s => (x:ℂ)^s/s² AnalyticOnNhd on U₀ := {0 < re} (rewrite cpow via funext `Complex.cpow_def_of_ne_zero` (x≠0) to exp(log x·s), Differentiable exp∘linear, div by s² ≠ 0, `DifferentiableOn.analyticAt`/`(hdiff).analyticAt` pointwise; (ii) pole part: `rectIntegral_cauchyFormula_analyticOnNhd` at p := 1 with g → 2πi·x^1/1² = 2πi·x (`Complex.cpow_one`); (iii) regular part G := (deriv zetaPoleUnit/zetaPoleUnit)·g on U_G := {0<re} ∩ {zetaPoleUnit ≠ 0} (open: Z continuous; closed rect ⊆ U_G: s=1 → `zetaPoleUnit_one`=1≠0, else `zetaPoleUnit_ne_zero` + zero-free hyp): AnalyticAt via `(differentiable_zetaPoleUnit.analyticAt s).deriv.div (…analyticAt s) hZne` then Goursat → 0; (iv) edges avoid s=1 (im ≠ 0 on verticals? NO — vertical edges at re = z₁.re < 1 and z₂.re > 1 have im sweeping through 0 but re ≠ 1 ✓; horizontal edges have im = z₁.im < 0, z₂.im > 0 ✓ so all edge points ≠ 1); congr on S := {s | s.re ∈ uIcc ∧ s.im ∈ uIcc ∧ s ≠ 1}? simpler S := edges' union… use S := closed rectangle ∖ {1}: on it, `neg_zeta_logDeriv_eq` (hyp gives ζ ≠ 0) rewrites F = g·(s−1)⁻¹ − G, then `rectIntegral_congr` + `rectIntegral_add` (integrabilities: kernel·g continuous on edges — g continuous, (s−1)⁻¹ continuous off 1; G continuous on edges via analyticity). (v) 2240/A edge BOUNDS come later (Z5c3c) — this brick is exact identity only.

### (Z5c3b-iii part 2) DONE — the Perron rectangle residue
`RHTower/PerronRectangleResidue.lean` [PROVED HERE], standard axioms, built:
- `intervalIntegrable_analytic_horizontal` / `_vertical` — reusable: analytic-on-U edge sections are IntervalIntegrable (feeds `rectIntegral_add`'s 8 obligations in 1 line each).
- `analyticOnNhd_perron_kernel` : x^s/s² analytic on {0 < re} (cpow → exp(log x·s) by funext + `Differentiable.analyticAt`).
- **`rectIntegral_perron_eq`** : for x > 0, corners with 0 < z₁.re < 1 < z₂.re, z₁.im < 0 < z₂.im, and ζ ≠ 0 on the closed rectangle ∖ {1}: `∮ (−ζ′/ζ)·x^s/s² = 2πi·x`. Split via `neg_zeta_logDeriv_eq` on edges (rectIntegral_congr on rect∖{1}; edges avoid 1 by strict coordinate inequalities), `rectIntegral_add`, Goursat-zero for (−Z′/Z)·x^s/s² on {0<re} ∩ {Z ≠ 0}, and `rectIntegral_cauchyFormula_analyticOnNhd` at p = 1 → 2πi·x^1/1².
- GOTCHAS: (1) `- a / b * c` parses `((-a)/b)*c` — bridge to `-(a/b)*c` with `rw [neg_div]` before applying neg_zeta_logDeriv_eq. (2) AnalyticAt.div's first subgoal eta-contracts `fun s => ↑x ^ s` to `HPow.hPow ↑x` — `show` the lambda form before funext-rw. (3) `rfl`-branch membership `1 ∈ {s | P s}` blocks rw — `simp only [Set.mem_setOf_eq, …]`. (4) After rw with a lemma whose RHS applies a lambda (`2πi·(fun s => …) 1`), finish with `simp [...]` (beta).

NEXT (Z5c3c — edge estimates → the ψ₁ asymptotic): connect `smoothed_chebyshev_eq_perron_integral` (∫dw over ℝ at Re = a) to the rectangle. Chain: (i) vertical-edge dictionary: rectIntegral's right edge is `I • ∫_{z₁.im}^{z₂.im} F(z₂.re + iy) dy`; our ∫dw at Re = a is ∫_ℝ F(a + 2πiw)·? — SUBSTITUTION y = 2πw: ∫_ℝ F(a+2πwi) dw = (1/2π)∫_ℝ F(a+iy) dy, so ∑Λ(log(x/n))⁺ = (1/2π)∫_ℝ F(a+iy)dy where the rectangle gives ∫_{−T}^{T}. (ii) TAIL: |∫_{|y|>T} F(a+iy)dy| ≤ 2·x^a·C_a/T with ‖−ζ′/ζ(a+iy)‖ ≤ Σ Λ n^{-a} = |ζ′/ζ(a)| ≤ 1/(a−1) + O(1) (NEED a Lean lemma: norm_LSeries_le at real point: ‖L ↗Λ (a+iy)‖ ≤ L ↗Λ a via `LSeries` term-norm — build `norm_LSeries_vonMangoldt_le_of_re_eq`; then bound −ζ′/ζ(a) ≤ 1/(a−1) + 8 say via truncated rep? or use existing ZetaLogDerivBound at... simplest: −ζ′/ζ(a) real ≤ 1/(a−1) + c₀ from zeta_eq_truncated N=1 derivative? alternative CRUDE: Σ_n Λ(n) n^{-a} ≤ Σ_n log n·n^{-a} ≤ ∫ known — pick easiest at build time). (iii) left edge at σ₀: length 2T, bound (2240/A)log⁹T·x^{σ₀}/(σ₀²+y²)... integrate ≤ (2240/A)log⁹T·x^{σ₀}·π/σ₀; horizontal edges: length ≤ 1, height T: integrand ≤ (2240/A)log⁹T·x^a/T². (iv) assemble ψ₁-type: ∑Λ(n)(log(x/n))⁺ = x + E with |E| ≤ explicit; σ₀ := 1 − min(δ₀, A/(2log⁹T)) using `exists_low_height_zeta_zero_free` + `riemannZeta_ne_zero_of_re_gt_one_sub` + `riemannZeta_ne_zero_of_near_one` to discharge hzf on the rectangle (three regimes: |t| ≤ 9 low-height δ₀; |t| ≥ 9 log-region; near-pole ball). (v) then unsmoothing (Z5d).

### (Z5c3c-i) DONE — the a-line ζ′/ζ bound
Numeric cert: −ζ′/ζ(a) vs 8/(a−1)² at a ∈ {1.1, 1.3, 1.9}: 9.44 ≤ 800, 2.81 ≤ 88.9, 0.67 ≤ 9.9, 3 trials ✓.
`RHTower/ZetaLogDerivLineBound.lean` [PROVED HERE], standard axioms, built:
- `tsum_add_one_rpow_le` : Σ'(n+1)^{−b} ≤ 1 + 1/(b−1), b > 1 — partial sums via `AntitoneOn.sum_le_integral_Ico` + `integral_Ioi_rpow_of_lt` + `setIntegral_mono_set`; tsum via `Summable.tsum_le_of_sum_range_le`; summability via `Real.summable_one_div_nat_add_rpow`.
- `tsum_vonMangoldt_div_rpow_le` : Σ' Λ(n)/n^a ≤ 8/(a−1)², 1 < a ≤ 2 — `vonMangoldt_le_log` + `Real.log_le_rpow_div` at ε=(a−1)/2 + `Real.summable_nat_rpow` + `Summable.tsum_eq_zero_add` shift.
- **`norm_zeta_logDeriv_le_line`** : ‖ζ′/ζ(s)‖ ≤ 8/(Re s−1)² for 1 < Re s ≤ 2 — `norm_tsum_le_tsum_norm` over the Λ L-series + term-norm identity + `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`.
- GOTCHAS: `div_add_div_same` gone → `← add_div`; `field_simp` can't clear −b+1 denominators without an explicit `hne` in context; `norm_div` in a two-sided norm goal rewrites the LHS first — for ‖dζ/ζ‖ = ‖−dζ/ζ‖ use `rw [neg_div, norm_neg]`; `setIntegral_mono_set` ae-nonneg goal needs `filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]` (rpow of NEGATIVE base can be negative — t>0 needed); set-membership ae goals arrive as raw applications `Ioc a b t` — `obtain ⟨h,-⟩ := ht; show (1:ℝ) < t`.

NEXT (Z5c3c-ii — tail of the a-line integral): with C_a := 8/(a−1)², prove
`‖∫_{|w| ≥ W} (−ζ′/ζ)(a+2πiw)·x^{a+2πiw}/(a+2πiw)² dw‖ ≤ C_a·x^a·(2/(4π²W))` (i.e. ≤ C_a·x^a/(2π²W)) for W > 0, 1 < a ≤ 2:
integrand norm ≤ C_a·x^a·(a²+(2πw)²)⁻¹ ≤ C_a·x^a·(2πw)⁻²; ∫_{|w|≥W}(2πw)^{-2} = 2·(1/(4π²W)). Pieces: `norm_perron_integrand`-style norm computation but with the ζ′/ζ factor (norm_mul + `norm_zeta_logDeriv_le_line` at re = a: (a+2πiw).re = a ✓ ≤ 2); `Complex.norm_cpow_eq_rpow_re_of_pos` for ‖x^s‖ = x^a; `integral_Ioi_rpow_of_lt`-analog on Ioi W for w^{-2} (or `integrableOn_Ioi_rpow_of_lt` + explicit value at c=W: −W^{−1}/(−1) = 1/W); symmetric Iio piece by `integral_comp_neg`/substitution or handle |w| via evenness: split ∫_{|w|≥W} = ∫_{Ioi W} + ∫_{Iio (−W)} and bound each by C_a x^a/(4π²W). Then (Z5c3c-iii): truncated a-line ↔ right rectangle edge dictionary (substitution y = 2πw: mathlib `intervalIntegral.integral_comp_mul_left`/`integral_comp_smul_deriv` or `MeasureTheory.integral_comp_mul_left` : ∫ f(cw) dw = c⁻¹∫f — track the 2π factor NUMERICALLY first), then horizontal+left edge bounds via `norm_deriv_div_riemannZeta_le` (strip) + `norm_zeta_logDeriv_le_line`… note LEFT edge needs the ζ′/ζ bound INSIDE the strip at σ₀ < 1 — that is `norm_deriv_div_riemannZeta_le` (banked, needs |t| ≥ 9 — the |t| ≤ 9 part of the left edge needs a low-height ζ′/ζ bound: NEW SUB-BRICK — bound ‖ζ′/ζ‖ on the compact set [σ₀,1]×[−9,9]∖B(1,r) by sup-compactness (continuity of Z′/Z on the zero-free compact + explicit near-pole part 1/(s−1) ≤ 8): existential constant OK).

### (Z5c3c-ii) DONE — Perron a-line tail bounds
`RHTower/PerronTailBound.lean` [PROVED HERE], standard axioms, built:
- `norm_perron_zeta_integrand` : ‖(−ζ′/ζ)(a+2πiw)·x^{a+2πiw}/(a+2πiw)²‖ ≤ (8/(a−1)²)·x^a·(a²+(2πw)²)⁻¹ for 1 < a ≤ 2 (uses `norm_zeta_logDeriv_le_line` — REMEMBER `rw [hre] at hζbound` to rewrite the .re in ITS bound too).
- `norm_integral_perron_tail_Ioi` / `_Iic` : each tail over Ioi W / Iic (−W) ≤ (8/(a−1)²)·x^a/(4π²W) — `norm_integral_le_of_norm_le` with dominator C·w^{−2:ℝ}, `integrableOn_Ioi_rpow_of_lt`, value via `integral_Ioi_rpow_of_lt` + `Real.rpow_neg_one` + `neg_div_neg_eq`.
- GOTCHAS: (1) Left tail via `integral_comp_neg_Ioi W f` INSTANTIATED with the explicit lambda then `rw [← hcomp]` — do NOT hand-write the negated integrand (↑(−w) vs −↑w cast shapes differ); close the pointwise goal with `refine le_trans (norm_perron_zeta_integrand … (−w)) ?_` (beta-defeq unification) + `rw [show (2π(−w))² = (2πw)² by ring]`. (2) `inv_le_inv_of_le` → `inv_anti₀`. (3) Tail sets chosen as Iic (−W)/Ioi W so ℝ splits as Iic ∪ Ioc ∪ Ioi cleanly for (Z5c3c-iii).

NEXT (Z5c3c-iii — split + dictionary): (1) `integral_ℝ = ∫_{Iic(−W)} + ∫_{Ioc(−W,W)} + ∫_{Ioi W}` for the Perron–zeta integrand: need Integrable on ℝ (dominator C_a·x^a·(a²+(2πw)²)⁻¹ ≤ …·C(1+w²)⁻¹ as in `integrable_perron_integrand`; measurability: continuity — ζ′/ζ continuous at a+2πiw (ζ ≠ 0 by `riemannZeta_ne_zero_of_one_le_re`, s ≠ 1 since a > 1... careful a+0i at w=0 is real a ≠ 1 ✓; `differentiableAt_riemannZeta` + deriv continuity: deriv ζ continuous on {s ≠ 1} — via analyticity `(differentiableAt… )`: deriv ζ = deriv of analytic: AnalyticAt.deriv.continuousAt with AnalyticAt ζ s from DifferentiableOn.analyticAt on open {≠1}); then `MeasureTheory.integral_Iic_add_integral_Ioc_add_integral_Ioi`-style names — probe `integral_Ioc_add_integral_Ioi` etc. (2) dictionary middle ↔ right rectangle edge: ∫_{Ioc(−W,W)} F(a+2πiw)dw = (1/(2π))·∫_{−2πW}^{2πW} F(a+iy)dy = (1/(2π))·(1/I)·[right-edge of rectIntegral with z₂.im = 2πW] — probe `intervalIntegral.integral_comp_mul_left` for the 2π substitution and verify factor NUMERICALLY (∫dw vs ∫dy: y = 2πw, dy = 2πdw: ∫f(2πw)dw = (1/2π)∫f(y)dy ✓); rectIntegral right edge is `I • ∫ y in z₁.im..z₂.im, g(z₂.re + y·I)` — so ∫_{−T}^{T} F(a+iy)dy = (1/I)·(that edge term) = −I·(…). Assemble: ψ_tent(x) = ∫_ℝ = tails + (1/2π)(1/I)·[rectIntegral − other three edges] = tails + (1/2π)(1/I)·[2πi·x − left−edge − horizontals] = x + errors. Numeric check the final constant assembly BEFORE writing.

### (Z5c3c-iii part 1) DONE — line integrability + three-way split
`RHTower/PerronLineSplit.lean` [PROVED HERE], standard axioms, built:
- `integral_split_three` : ∫_ℝ f = ∫_{Iic(−W)} + ∫_{Ioc(−W,W)} + ∫_{Ioi W} for Integrable f — `setIntegral_union` twice with `Set.Iic_disjoint_Ioc/Iic_disjoint_Ioi/Iic_union_Ioc_eq_Iic/Iic_union_Ioi` + `setIntegral_univ`.
- `continuous_perron_zeta_integrand` (a > 1): deriv ζ continuity via `DifferentiableOn.analyticAt (s := {z | z ≠ 1})` + `.deriv.continuousAt`; cpow factor via `Continuous.const_cpow (Or.inl …)`; pinned `ContinuousAt.comp (f := …) (x := w)` throughout.
- `integrable_perron_zeta_integrand` (1 < a ≤ 2): mono vs (8/(a−1)²·x^a·C)·(1+w²)⁻¹.
- GOTCHA: `riemannZeta_ne_zero_of_one_le_re` needs explicit `import Mathlib.NumberTheory.LSeries.Nonvanishing` (Dirichlet chain doesn't reexport it).

NEXT (Z5c3c-iii part 2 — the substitution dictionary): equate `∫_{Ioc(−W,W)} F(a+2πiw)dw` with the rectangle's right vertical edge. Target: for T := 2πW: `∫ w in Ioc(−W,W), F(a+2πiw) dw = (1/(2π))·∫ y in (−T)..T, F(a+iy) dy` (interval integral!) via `intervalIntegral.integral_comp_mul_left` (probe exact: ∫ y in a..b, f (c*y) dy = c⁻¹ • ∫ y in c*a..c*b, f y for c ≠ 0 — CHECK exact form/name: also `intervalIntegral.smul_integral_comp_mul_left`); bridge Ioc-set-integral ↔ intervalIntegral via `intervalIntegral.integral_of_le`. Then rectIntegral's right edge = `I • ∫ y in z₁.im..z₂.im, F(z₂.re + y·I)` with z₂.re = a: edge integrand F(a+yI) needs cast-shape alignment: rectIntegral uses `g ((z₂.re : ℂ) + y*I)` with our F's argument written `(a:ℂ) + 2π·w·I` — at the dictionary point define the rectangle with corner z₂ := (a : ℂ) + (2πW)·I so z₂.re = a needs `Complex.add_re`-sim: corners as explicit ofReal constructions: z₁ := (σ₀:ℂ) − (2πW)·I? BUILD the final assembly statement with corners `Complex.mk`-free: use (σ₀ : ℂ) + (−(2*π*W) : ℝ)·I and (a:ℂ) + (2πW:ℝ)·I, then z₁.re = σ₀ etc via edgePt-style simp lemmas. Numerically verify the 1/(2π) factor AND the I-orientation sign before writing (mini-check: ∫_{−W}^{W} e^{2πiw}dw vs edge parametrization).

### (Z5c3c-iii part 2) DONE — the 2πξ→iy dictionary
Numeric cert: ∫_{−W}^{W}f(2πw)dw = (1/2π)∫_{−2πW}^{2πW}f(y)dy exact to machine precision; 1/i = −i orientation confirmed.
`RHTower/PerronMiddleDictionary.lean` [PROVED HERE], standard axioms, built:
- **`integral_middle_eq_interval`** : ∫_{Ioc(−W,W)} F(a+2πiw) dw = (2π)⁻¹ • ∫_{−2πW}^{2πW} F(a+iy) dy (intervalIntegral) — `intervalIntegral.integral_of_le` + `integral_congr` (pointwise cast bridge `↑(2πw) = 2↑π↑w` via show + push_cast; ring) + `intervalIntegral.integral_comp_mul_left` (MUST pass f EXPLICITLY — underscore stalls unification with beta-redex/instance diamond `instInnerProductSpaceRealComplex.toNormedSpace`).
- NOTE: statement RHS uses ℝ-smul `(2π)⁻¹ •` — downstream convert to ℂ-mul via `Complex.real_smul`/`Complex.ofReal_inv` when assembling.

NEXT (Z5c3d — THE ASSEMBLY): statement sketch (all pieces now banked):
For x > 0, 1 < a ≤ 2, W > 0, T := 2πW, σ₀ ∈ (0,1), zero-freeness on rectangle [σ₀,a]×[−T,T]∖{1}:
`∑' Λ(n)(log(x/n))⁺ − x = E` with `‖E‖ ≤ tails (2·(8/(a−1)²)x^a/(4π²W)) + (2π)⁻¹·(‖left edge‖ + ‖two horizontals‖)`.
Chain: `smoothed_chebyshev_eq_perron_integral` = ∫_ℝ = [split `integral_split_three` with `integrable_perron_zeta_integrand`] = tails + middle; middle = (2π)⁻¹•∫_{−T}^{T} F(a+iy)dy [dictionary]; ∫_{−T}^{T}F(a+iy)dy = (1/I)·(I•edge) = −I•[rectIntegral F z₁ z₂ − bottom + top + I•left…] — careful exact rectIntegral orientation: rectIntegral g z₁ z₂ = (∫bottom − ∫top) + I•∫right − I•∫left, so I•∫right = rectIntegral − ∫bottom + ∫top + I•∫left, and ∫_{−T}^{T}F(a+iy)dy = ∫right (with z₂.re = a, z₁.im = −T, z₂.im = T; corner choice z₁ := (σ₀:ℂ) − T·I?? NO: rectangle needs z₁.re = σ₀ < a = z₂.re: z₁ := (σ₀:ℂ) + (−T:ℝ)·I, z₂ := (a:ℂ) + (T:ℝ)·I; edge-coordinate simps via `Complex.add_re/add_im` on these corners). rectIntegral F z₁ z₂ = 2πi·x [`rectIntegral_perron_eq`]; so middle = (2π)⁻¹•(1/I)·(2πi·x + [∫top − ∫bottom − I•∫left]) = x + (2π)⁻¹•(−I)·(edge-errors). Then ψ_tent − x = tails + (2π)⁻¹(−I)(errors) and take norms. Write the assembly THEOREM with the three edge integrals appearing EXPLICITLY in the error bound (no estimation of them yet — separate final brick (Z5c3e) bounds them with `norm_deriv_div_riemannZeta_le` + low-height compact sup + `exists_low_height_zeta_zero_free`).

### (Z5c3d) DONE — THE PERRON CONTOUR ASSEMBLY
`RHTower/PerronContourAssembly.lean` [PROVED HERE], standard axioms, built:
- **`smoothed_chebyshev_contour_assembly`** : for 0 < x, 1 < a ≤ 2, 0 < σ₀ < 1, W > 0, and ζ ≠ 0 on [σ₀,a]×[−2πW,2πW]∖{1}:
  `∑' Λ(n)(log(x/n))⁺ = x + (Iic-tail + Ioi-tail) + (2π)⁻¹ • (i·(Bottom − Top) + LeftEdge)`
  where Bottom/Top = ∫_{σ₀}^{a} F(t ∓ 2πW·i)dt, LeftEdge = ∫_{−2πW}^{2πW} F(σ₀+iy)dy, tails on the a-line in w-coordinates. All error integrals appear EXPLICITLY (norm bounds deferred to Z5c3e).
- Proof: explicit formula → `integral_split_three` → `integral_middle_eq_interval` → corners z := ↑σ₀ + ↑(−2πW)·I etc (coordinate simps) → `rectIntegral_perron_eq` → `unfold rectIntegral` + simp[coords, smul_eq_mul] → `set` all four edges (Bv/Tv/Rv/Lv) → `hRight : Rv = 2π↑x + (I(Bv−Tv) + Lv)` via `linear_combination (−I)·hrect + (Rv − Lv − 2π↑x)·Complex.I_sq` → fold `← hRv`, rw, ONE `smul_add`, hxterm ((2π)⁻¹•(2π↑x) = ↑x via `Complex.real_smul` + field_simp), `abel`.
- GOTCHAS: (1) `linear_combination` treats I as an atom — supply `Complex.I_sq` with coefficient (goal_diff − c·h_diff must be divisible by (I²+1); coefficient = the I²-cofactor). (2) `abel` treats ℝ-smul as OPAQUE atoms — smul_add splitting must match the target's association EXACTLY; state intermediate identities with parens `2πx + (rest₁ + rest₂)` and apply `smul_add` once. (3) `set` AFTER `unfold + simp at hrect` folds both hrect and the goal; later-introduced copies refold with `rw [← hRv]`.

NEXT (Z5c3e — edge norm bounds): three lemmas, each ≤ explicit constant:
(e1) LeftEdge: ‖∫_{−T}^{T} F(σ₀+iy) dy‖ ≤ x^{σ₀}·(∫_{−T}^{T} ‖ζ′/ζ(σ₀+iy)‖/(σ₀²+y²)…) — strategy: pointwise ‖F(σ₀+iy)‖ ≤ M·x^{σ₀}/(σ₀²+y²) given a SUP hypothesis M on ‖ζ′/ζ‖ over the left edge (TAKE M AS A HYPOTHESIS — the concrete M = (2240/A)log⁹T + low-height-sup comes later in Z5c3f); then ∫ (σ₀²+y²)⁻¹ ≤ π/σ₀ (arctan; mathlib `integral_inv_one_add_sq`-analog: ∫ (b²+y²)⁻¹ dy over ℝ = π/b — probe `integral_inv_sq_add_sq`? or substitute y = σ₀u → (1/σ₀)∫(1+u²)⁻¹ ≤ π/σ₀ via `integral_univ_inv_one_add_sq = π`); norm_intervalIntegral_le: `intervalIntegral.norm_integral_le_of_norm_le_const`? better ≤ (2T)·max — NO, use the (σ₀²+y²)⁻¹ decay: ‖·‖ ≤ M x^{σ₀} π/σ₀ (T-uniform!). ‖x^{σ₀+iy}‖ = x^{σ₀} `norm_cpow_eq_rpow_re_of_pos`; ‖(σ₀+iy)²‖ = σ₀²+y² (norm_add_mul_I pattern).
(e2) Bottom/Top: ‖∫_{σ₀}^{a} F(t ± iT)dt‖ ≤ M'·x^a·(a−σ₀)/T² ≤ M'·x^a/T² (length ≤ 1) given sup M' of ‖ζ′/ζ‖ on the horizontal edge: pointwise ‖F(t±iT)‖ ≤ M'·x^t/(t²+T²) ≤ M'x^a/T²; `intervalIntegral.norm_integral_le_of_norm_le_const` (name: norm_intervalIntegral_le?) with constant M'x^a/T², length (a−σ₀) ≤ 1 if we ALSO hypothesize a − σ₀ ≤ 1 (true in instantiation: a = 1+1/log x, σ₀ ≥ 7/8).
(e3) then (Z5c3f) instantiate M, M' via banked `norm_deriv_div_riemannZeta_le` (strip, |t| ≥ 9) + NEW low-height compact sup on [7/8,1+ε]×[−9,9]∖B(1,r): sup exists by compactness+continuity of Z′/Z (differentiable_zetaPoleUnit) + pole part explicit; produces EXISTENTIAL constant — fine.

### (Z5c3e) DONE — edge norm bounds (sup-parametrized)
`RHTower/PerronEdgeBounds.lean` [PROVED HERE], standard axioms, built:
- `norm_perron_integrand_at` : ‖F(σ+iy)‖ = ‖ζ′/ζ(σ+iy)‖·x^σ·(σ²+y²)⁻¹ (x > 0).
- `integral_inv_sq_add_sq_le` : ∫_{−T}^{T}(b²+y²)⁻¹ ≤ π/b (b > 0; substitution + `integral_inv_one_add_sq` = arctan, `arctan_lt_pi_div_two`).
- **`norm_perron_left_edge_le`** : given sup M on the edge, ‖∫_{−T}^{T} F(σ₀+iy)dy‖ ≤ M·x^{σ₀}·π/σ₀ — T-UNIFORM (`intervalIntegral.norm_integral_le_of_norm_le`).
- **`norm_perron_horizontal_edge_le`** : ‖∫_{σ₀}^{a}F(t+ci)dt‖ ≤ M·x^a/c²·|a−σ₀| (`norm_integral_le_of_norm_le_const`, x^t ≤ x^a via `rpow_le_rpow_of_exponent_le`, uIoc_of_le).
- GOTCHA: `Continuous.inv₀`'s nonvanishing arg as `fun y => ne_of_gt (by positivity)` inline FAILS (unification order) — build the continuity `have` separately with `apply Continuous.inv₀; · fun_prop; · intro y; positivity`.

NEXT (Z5c3f-1 — low-height ζ′/ζ sup): 
theorem exists_low_height_logDeriv_bound : ∃ δ₀ M₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1/8 ∧ 0 ≤ M₀ ∧
  (∀ s : ℂ, 1 − δ₀ ≤ s.re → |s.im| ≤ 9 → s ≠ 1 → riemannZeta s ≠ 0) ∧
  (∀ s : ℂ, 1 − δ₀ ≤ s.re → s.re < 1 → |s.im| ≤ 9 → ‖deriv riemannZeta s / riemannZeta s‖ ≤ M₀ + (1 − s.re)⁻¹).
Proof: obtain δ₀ from `exists_low_height_zeta_zero_free`; K̄ := {1−δ₀ ≤ re ≤ 1} ∩ {re ≤ 1?} ∩ {|im| ≤ 9} compact (closed∩bounded, reuse box-compactness pattern from ZetaLowHeightZeroFree); Z := zetaPoleUnit ≠ 0 on K̄ (s=1: `zetaPoleUnit_one`; else `zetaPoleUnit_ne_zero` + margin, incl. re = 1 via `riemannZeta_ne_zero_of_one_le_re`); Z′/Z ContinuousOn K̄ ((differentiable_zetaPoleUnit.analyticAt).deriv.continuousAt etc → ContinuousOn via continuousAt; div needs Z ≠ 0 pointwise: ContinuousOn.div with pointwise); M₀ from `IsCompact.exists_bound_of_continuousOn`; then s in region (re<1): ζ s ≠ 0 (margin, s≠1 auto from re<1), ζ′/ζ = Z′/Z − (s−1)⁻¹ (from `neg_zeta_logDeriv_eq` negated: ζ′/ζ = Z′/Z − 1/(s−1) — derive by linear_combination −(neg_zeta_logDeriv_eq …)); ‖·‖ ≤ M₀ + ‖(s−1)⁻¹‖; ‖(s−1)⁻¹‖ = ‖s−1‖⁻¹ ≤ (1−re)⁻¹ since 1−re ≤ |re(s−1)| ≤ ‖s−1‖ (`Complex.abs_re_le_norm`, `one_div_le_one_div_of_le`-analog for inv: `inv_anti₀? needs 0 < 1−re ✓`).
THEN (Z5c3f-2): the strip sup for |y| ∈ [9, T]: M_strip := (2240/A)·log⁹T via banked `norm_deriv_div_riemannZeta_le` (hypotheses: |t| ≥ 9, |σ−1| ≤ A/log⁹|t|: for σ = σ₀ := 1 − A/(2log⁹T) and 9 ≤ |y| ≤ T: need A/(2log⁹T) ≤ A/log⁹|y| ⟺ log⁹|y| ≤ 2log⁹T ✓ |y| ≤ T; and bound (2240/A)log⁹|y| ≤ (2240/A)log⁹T ✓); COMBINE into total left-edge sup M_edge := max(M₀ + (1−σ₀)⁻¹, (2240/A)log⁹T) = max(M₀ + 2log⁹T/A, …) — then instantiate `norm_perron_left_edge_le`. Horizontal edges: |c| = 2πW = T ≥ 9: all t-points have |im| = T ≥ 9: strip bound applies if |t−1| ≤ A/log⁹T for t ∈ [σ₀, a]... CAREFUL: horizontal edge t ranges over [σ₀, a] with a = 1+1/log x — need a ≤ 1 + A/log⁹T as a SIDE CONDITION at instantiation (choose T accordingly: log⁹T ≤ A·log x — fine since T = exp((log x)^{1/10}): log⁹T = (log x)^{9/10} ≤ A log x for log x ≥ A^{-10}). So horizontal sup = (2240/A)log⁹T under side conditions σ₀ ≥ 1−A/log⁹T ∧ a ≤ 1+A/log⁹T.

### (Z5c3f-1) DONE — low-height ζ′/ζ sup
`RHTower/ZetaLogDerivLowHeight.lean` [PROVED HERE], standard axioms, built, FIRST-TRY compile:
- **`exists_low_height_logDeriv_bound`** : ∃ δ₀ ∈ (0,1/8], M₀ ≥ 0 with the δ₀-margin zero-free AND ‖ζ′/ζ(s)‖ ≤ M₀ + (1−Re s)⁻¹ on [1−δ₀,1)×[−9,9] — compact box + `IsCompact.exists_bound_of_continuousOn` (in `Mathlib.Analysis.Normed.Group.Bounded`; the primed version is multiplicative) on Z′/Z; pole part explicit via ζ′/ζ = Z′/Z − (s−1)⁻¹ (`linear_combination -neg_zeta_logDeriv_eq`), ‖(s−1)⁻¹‖ ≤ (1−re)⁻¹ via `abs_re_le_norm` + `abs_of_neg` + `inv_anti₀`.

NEXT (Z5c3f-2 — strip sup for the left edge, |y| ∈ [9,T], and horizontals): lemma
`norm_zeta_logDeriv_le_strip_range` : for T ≥ 9, A := zetaLowerA, σ with 1 − A/(2·log⁹T) ≤ σ ≤ 1 + A/(2·log⁹T)?? (two-sided for horizontals: t ∈ [σ₀,a]), and y with 9 ≤ |y| ≤ T:
  ‖ζ′/ζ(σ+iy)‖ ≤ (2240/A)·log⁹T.
Proof: banked `norm_deriv_div_riemannZeta_le` (needs |σ−1| ≤ A/log⁹|y|, |y| ≥ 9): A/(2log⁹T) ≤ A/log⁹|y| ⟺ log⁹|y| ≤ 2·log⁹T ⟸ |y| ≤ T (monotone log, log⁹ mono via pow_le_pow_left₀, log T ≥ log 9 > 0); then (2240/A)log⁹|y| ≤ (2240/A)log⁹T. CAREFUL: banked lemma's argument form is `(↑σ + ↑t·I)` with |t| ≥ 9 — check ZetaLogDerivBound signature: `norm_deriv_div_riemannZeta_le {σ t : ℝ} (ht : 9 ≤ |t|) (hσl : 1 − A/log⁹|t| ≤ σ) (hσu : σ ≤ 1 + A/log⁹|t|) : ‖deriv ζ (↑σ + ↑t*I)/ζ (↑σ + ↑t*I)‖ ≤ 2240/A·log⁹|t|` ✓ shape matches edge lemmas' `(σ₀:ℂ)+(y:ℂ)·I` ✓.
THEN (Z5c3g): the MASTER error bound combining everything: define σ₀(T) := 1 − min(δ₀, A/(2log⁹T)) hmm — need σ₀ satisfying BOTH low-height margin (σ₀ ≥ 1−δ₀) and strip containment (σ₀ ≥ 1−A/(2log⁹T)): σ₀ := 1 − min δ₀ (A/(2·log⁹T)). Left-edge sup M_edge := max (M₀ + (1−σ₀)⁻¹) ((2240/A)·log⁹T) — with (1−σ₀)⁻¹ = (min δ₀ (A/2log⁹T))⁻¹ ≤ max(δ₀⁻¹, 2log⁹T/A). All ≤ C₁·log⁹T for T ≥ T₀ (existential C₁ fine). Split the left edge ∫_{−T}^{T} = ∫_{|y|≤9} + ∫_{9≤|y|≤T}?? — NO NEED: `norm_perron_left_edge_le` takes ONE sup over the whole edge: M_edge := max(low-height-bound, strip-bound) works pointwise: ∀ y ∈ Ioc(−T,T): |y| ≤ 9 → low-height (need σ₀ < 1 ✓, σ₀ ≥ 1−δ₀ ✓); |y| > 9 → strip. ✓ single application. Horizontal sup: M_horiz := (2240/A)log⁹T (needs [σ₀,a] ⊆ strip at |c| = T: σ₀ ≥ 1−A/(2log⁹T) ✓ and a ≤ 1+A/(2log⁹T) as HYPOTHESIS). Assemble via `smoothed_chebyshev_contour_assembly` + `norm_perron_tail_Ioi/Iic` + edge bounds → `‖ψ_tent(x) − x‖ ≤ …` fully explicit in (x, a, T, δ₀, M₀, A). Then (Z5c3h) choose a := 1+1/log x, T := exp((log x)^{1/10}), W := T/2π → ψ_tent(x) = x + O(x·e^{−c(log x)^{1/10}}).

### (Z5c3f-2) DONE — strip ζ′/ζ sup over height range
`RHTower/ZetaLogDerivStripRange.lean` [PROVED HERE], standard axioms, built, first-try compile:
- **`norm_zeta_logDeriv_le_strip_range`** : for 9 ≤ |y| ≤ T, |σ−1| ≤ A/(2log⁹T): ‖ζ′/ζ(σ+iy)‖ ≤ (2240/A)·log⁹T — via banked `norm_deriv_div_riemannZeta_le` at own height + `div_le_div_of_nonneg_left` + `pow_le_pow_left₀`/`Real.log_le_log`.

NEXT (Z5c3g — THE MASTER BOUND). Statement plan:
theorem exists_smoothed_chebyshev_error_bound : ∃ δ₀ M₀ : ℝ, 0 < δ₀ ∧ 0 ≤ M₀ ∧ ∀ x a T : ℝ (W := T/(2π) i.e. take W and set T := 2πW), hyps:
  1 ≤ x, 1 < a ≤ 2, T := 2πW ≥ 9, a ≤ 1 + A/(2log⁹T), σ₀ := 1 − min δ₀ (A/(2·log⁹T)):
  ‖∑'Λ(n)(log(x/n))⁺ − x‖ ≤ 2·(8/(a−1)²)·x^a/(4π²W)                                    [tails]
    + (2π)⁻¹·( M_edge·x^{σ₀}·π/σ₀ + 2·M_horiz·x^a/T²·|a−σ₀| )                            [edges]
  where M_edge := max (M₀ + (min δ₀ (A/(2log⁹T)))⁻¹) ((2240/A)·log⁹T), M_horiz := (2240/A)·log⁹T.
Proof: obtain δ₀,M₀ from `exists_low_height_logDeriv_bound` FIRST (fixes constants); apply `smoothed_chebyshev_contour_assembly` (zero-freeness hzf: three regimes — |im| ≤ 9: δ₀-margin (σ₀ ≥ 1−δ₀ ✓ since min ≤ δ₀; covers re up to a > 1 too? margin thm has NO upper re bound ✓); |im| > 9: `riemannZeta_ne_zero_of_re_gt_one_sub`? WAIT that needs re > 1 − c/log⁹|t| with c = zetaZeroFreeC — but our σ₀ uses A = zetaLowerA! CHECK: is A ≤ c·(compat)? The strip bound norm_deriv_div uses zetaLowerA-strip whose zero-freeness was PROVEN inside (strip lower bound pow_four_norm_riemannZeta_ge_strip > 0 forces ζ ≠ 0 on |σ−1| ≤ A/log⁹|t|) — so for the RECTANGLE zero-freeness at |im| ∈ (9, T] use: σ ≥ σ₀ ≥ 1−A/(2log⁹T) ≥ 1−A/log⁹|y|: points with σ ≤ 1+... rectangle top re ≤ a ≤ 1+A/(2log⁹T) ≤ 1+A/log⁹|y|?? A/(2log⁹T) ≤ A/log⁹|y| ✓ same halving trick → inside the A-strip at own height → ζ ≠ 0 there via... need an explicit nonvanishing lemma for the A-strip: DERIVE from `pow_four_norm_riemannZeta_ge_strip` (ZetaStripLowerBound): if ζ = 0 then LHS quartic = 0 < A³/(12096log²⁸) contradiction — 5-line helper lemma `riemannZeta_ne_zero_of_strip` : |σ−1| ≤ A/log⁹|t|, |t| ≥ 9 → ζ(σ+it) ≠ 0. Add it in the master file (or check ZetaStripLowerBound already has it — rg first!). Also re > 1 and re = 1: mathlib. CAREFUL the hzf quantifier in assembly is over COMPLEX s with bounds via s.re/s.im — transport w/ Complex.re_add_im-style: s = ↑re + ↑im·I for the strip lemma's (σ+ti) form: rw [← Complex.re_add_im s] to apply — or state helper in s-form directly.
Then: tails via norm_perron_tail_Iic/Ioi; edges via norm_perron_left_edge_le (M_edge: pointwise case |y| ≤ 9 → low-height bound ≤ M₀+(1−σ₀)⁻¹ = M₀+(min…)⁻¹ ≤ max-left [need σ₀ < 1 ✓ min > 0; and σ₀ ≥ 1−δ₀ ✓]; |y| > 9 → strip-range ≤ max-right) + norm_perron_horizontal_edge_le ×2 (c = ±T: |σ−1| ≤ A/(2log⁹T) for t ∈ [σ₀,a] ✓ hypotheses); norm-triangle over the assembly identity: ‖ψ−x‖ = ‖tails + (2π)⁻¹•(i(B−Tp)+L)‖ ≤ ‖Iic‖+‖Ioi‖ + (2π)⁻¹(‖B‖+‖Tp‖+‖L‖) [norm_smul: ‖r•z‖ = |r|·‖z‖ = (2π)⁻¹‖z‖; ‖i·w‖ = ‖w‖ Complex.norm_I·mul].

### (Z5c3g) DONE — THE MASTER PERRON ERROR BOUND
`RHTower/PerronMasterBound.lean` [PROVED HERE], standard axioms, built:
- **`exists_smoothed_chebyshev_error_bound`** : ∃ δ₀ ∈ (0,1/8], M₀ ≥ 0, ∀ x ≥ 1, 1 < a ≤ 2, T := 2πW ≥ 9 with a ≤ 1 + A/(2log⁹T), σ₀ := 1 − min δ₀ (A/(2log⁹T)), Medge := max (M₀+(1−σ₀)⁻¹) ((2240/A)log⁹T):
  `‖ψ_tent(x) − x‖ ≤ 2·(8/(a−1)²)x^a/(4π²W) + (2π)⁻¹·(Medge·x^{σ₀}·π/σ₀ + 2·(2240/A)log⁹T·x^a/T²·|a−σ₀|)`.
- Fully unconditional; constants δ₀, M₀ existential (compactness), rest explicit.
- Key steps: 16·A = C (`zetaLowerA = zetaZeroFreeC/16` by norm_num — so the A/2-strip is strictly inside the C zero-free region: rectangle zero-freeness at 9 < |im| ≤ T via `riemannZeta_ne_zero_of_re_gt_one_sub` after `rw [← Complex.re_add_im s]`); |im| ≤ 9 via margin; re > 1 via mathlib. Edge sups: `norm_zeta_logDeriv_le_strip_range` (σ pinned explicitly `(σ := σ₀)`; the second bound needs the positivity of A/(2log⁹T) as a linarith hint) + low-height `hlow` with (1−σ₀)⁻¹. set-abstraction of the 5 integrals before norm-chaining; `norm_smul` + `Complex.norm_I`.
- GOTCHA: `norm_perron_horizontal_edge_le` at c := −T: c ≠ 0 via `intro h; nlinarith [neg_eq_zero.1 h]`; c² = (−T)² bridged by ring-show.

NEXT (Z5c3h — instantiation/optimization): theorem
`exists_smoothed_chebyshev_power_log : ∃ c₀ C₀ x₀ : ℝ, 0 < c₀ ∧ ∀ x ≥ x₀, ‖ψ_tent(x) − x‖ ≤ C₀·x·exp(−c₀·(log x)^{1/10})`.
Choices inside proof: a := 1 + 1/Real.log x (1 < a ✓ for x > e; a ≤ 2 for log x ≥ 1); T := exp((log x)^{1/10}); W := T/(2π) (2πW = T ✓ T ≥ 9 for x large); side condition a ≤ 1+A/(2log⁹T): 1/log x ≤ A/(2(log x)^{9/10}) ⟺ 2(log x)^{9/10} ≤ A·log x ⟺ (log x)^{1/10} ≥ 2/A ✓ x ≥ x₀. Error pieces: x^a = x·x^{1/log x} = e·x (rpow: x^{1/log x} = exp(log x/log x) = e); tails: 2·8log²x·e·x/(4π²W) = (4e/π²)·x·log²x·2π/T ~ x·log²x·e^{−(log x)^{1/10}} ≤ C x e^{−c₀(logx)^{1/10}} (absorb log²x: log²x·e^{−u} ≤ C e^{−u/2} with u = (logx)^{1/10}, log²x = u^{20}: u^{20}e^{−u} bounded... wait need e^{−u}·u^{20} ≤ C·e^{−u/2}: u^{20} ≤ C e^{u/2} ✓ polynomial vs exp — use banked-style `le_exp_half`-iterations or `Real.add_pow_le_pow_mul_pow_of_sq_le`… simplest: u^{20} ≤ (40/e·…)... make a helper lemma `pow_le_exp_half`-style: ∀ n u ≥ 0: u^n ≤ (2n)!·e^{u/2}? or use iterate of banked `le_exp_half (v ≤ e^{v/2})`: u^{20} = (u)^{20} ≤ (e^{u/40})^{20}·(40)^{20}... from log-space: u^n ≤ C_n e^{u/2} ⟺ n log u ≤ log C_n + u/2 ⟸ log u ≤ u/(2n) + log C_n/n: `Real.log_le_rpow_div`-style: log u ≤ u^ε/ε... take exp route: mathlib `Real.pow_le_exp`? probe `Real.pow_natCast_le_exp`? there might be `Nat.factorial`-free: `Real.pow_le_exp_mul_factorial`? Alternatively banked `le_exp_half` gives u ≤ e^{u/2}: then u^{20} ≤ e^{10u} — TOO WEAK (need coefficient < 1). Correct helper: u^n ≤ (4n)^n·e^{u/4}·… hmm: log u ≤ u^{1/2}·2?? Simplest formal route: u^{20}·e^{−u} ≤ C·e^{−u/2} ⟺ u^{20} ≤ C·e^{u/2}: use e^{u/2} ≥ (u/2)^{21}/21! (single Taylor term: mathlib `Real.add_one_le_exp` iterated? or `Real.exp_ge_pow_div_factorial`? probe `Real.pow_div_factorial_le_exp`? mathlib HAS `Real.sum_le_exp_of_nonneg` (partial Taylor sum ≤ exp for nonneg arg) → (u/2)^{21}/21! ≤ e^{u/2} → u^{20} ≤ 2^{21}·21!·e^{u/2}/(u/2)·… careful: (u/2)^{21}/21! ≤ e^{u/2} gives u^{21} ≤ 2^{21}21! e^{u/2}: then u^{20} ≤ u^{21} for u ≥ 1 ✓. So C := 2^{21}·21!·(constants).); left edge: Medge·x^{σ₀}π/σ₀: Medge ≤ M₀ + max(δ₀⁻¹, 2log⁹T/A) + (2240/A)log⁹T ≤ C₁·(log x)^{9/10} (+M₀+δ₀⁻¹ const); x^{σ₀} = x·x^{−(1−σ₀)} = x·e^{−(1−σ₀)log x}; 1−σ₀ = min δ₀ (A/(2(logx)^{9/10})): for x large the min is the A-term: (1−σ₀)·log x = A(log x)^{1/10}/2 → x^{σ₀} = x·e^{−(A/2)(logx)^{1/10}} — THE MAIN ERROR TERM ✓ (if min = δ₀ instead — only for small x, excluded by x₀); horizontals: ≤ (2240/A)log⁹T·e·x/T² tiny ✓. Total: c₀ := A/4 say after absorbing the polynomial prefactors. All real-analysis; the exp-vs-poly absorption needs the Taylor-term helper — probe mathlib `Real.quadratic...`/`sum_le_exp` names first. Numerically certify the CHAIN of inequalities at x = e^{100} before writing.

### (Z5c3h-i) DONE — polynomial–exponential absorption helpers
`RHTower/PerronPolyExpAbsorb.lean` [PROVED HERE], standard axioms, built, first-try:
- `pow_le_factorial_mul_exp_half` : u^n ≤ n!·(2/b)^n·e^{bu/2} (b>0, u≥0) — from mathlib `Real.pow_div_factorial_le_exp` at bu/2.
- `pow_mul_exp_neg_le` : u^n·e^{−bu} ≤ n!·(2/b)^n·e^{−bu/2}.

NEXT (Z5c3h-ii — the power-log PNT for ψ_tent), file `PerronPowerLogPNT.lean`. Statement:
`exists_smoothed_chebyshev_power_log : ∃ c₀ C₀ x₀ : ℝ, 0 < c₀ ∧ 0 ≤ C₀ ∧ 3 ≤ x₀ ∧ ∀ x, x₀ ≤ x → ‖ψ_tent(x) − ↑x‖ ≤ C₀ * x * Real.exp (−(c₀ * Real.log x ^ ((1:ℝ)/10)))`.
Proof skeleton: obtain δ₀ M₀ + master bound; set c₀ := zetaLowerA/4 (0 < A/4 ✓ ALSO need A/4 ≤ 1/4 < 1/2 for tail-rate domination ✓ A ≤ 1/2 banked `zetaLowerA_le...`? A = 1/(2·448⁴·756) tiny: A ≤ 1 by norm_num on def).
Instantiate master with: u := Real.log x ^ ((1:ℝ)/10) (rpow!), a := 1 + 1/Real.log x, W := Real.exp u/(2π), so 2πW = e^u (needs 2π ≠ 0 field_simp; `mul_div_cancel₀`), log(2πW) = u (`Real.log_exp`), log⁹(2πW) = u⁹ (pow of rpow).
x₀ := Real.exp ((max 3 (max (2/zetaLowerA) ((zetaLowerA/(2*δ₀)) ^ ((1:ℝ)/9)))) ^ (10:ℕ)) — then for x ≥ x₀: log x ≥ u₀^10 (log mono + log_exp) → u ≥ u₀ := max… (rpow mono: `Real.rpow_le_rpow` (1/10-power of both sides) + `Real.rpow_natCast` juggling: u = (log x)^{1/10} ≥ (u₀^{10})^{1/10} = u₀ via `Real.rpow_natCast u₀ 10` and `← Real.rpow_mul`: (u₀^{10})^{1/10} = u₀^{10·(1/10)} = u₀^1: needs u₀ ≥ 0 ✓).
Derived facts: u ≥ 3; log x = u^{10} ≥ 3^{10} hmm — log x = u^10? (u = (log x)^{1/10} with log x ≥ 0: u^{10} = log x via ← rpow_natCast + ← rpow_mul: DO have hlogx : Real.log x = u ^ (10:ℕ) as the KEY rewrite equation.); log x ≥ 1 → 1 < a; a ≤ 2 (1/log x ≤ 1); a − 1 = 1/log x → 8/(a−1)² = 8·log²x = 8u^{20}; T ≥ 9: e^u ≥ e^3 > 9 (from `Real.exp_one_gt_d9`-cubing or: e^u ≥ e^3 ≥ 2.71³ > 9: have via exp mono + nlinarith on exp_one_gt_d9 pattern — BANKED pattern in ZetaLogDerivBound (hexp2 : e² < 8): analog e³ > 9: e³ = (e)³ > 2.7182818283³ ≈ 20.08 > 9: nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1] with exp 3 = (exp 1)^3 via ← Real.exp_nat_mul? `Real.exp_nat_mul`? exp(3) = exp(1·3) = (exp 1)^3: Real.exp_nat_mul: exp(n·x) = (exp x)^n: rw [show (3:ℝ) = (3:ℕ)·(1:ℝ) …]; a ≤ 1 + A/(2u⁹): 1/log x = 1/u^{10} = (1/u⁹)·(1/u) ≤ (1/u⁹)·(A/2) ⟸ 1/u ≤ A/2 ⟸ u ≥ 2/A ✓; σ₀: 1−σ₀ = min δ₀ (A/(2u⁹)) = A/(2u⁹) for u⁹ ≥ A/(2δ₀) ⟸ u ≥ (A/(2δ₀))^{1/9} ✓ (min_eq_right); σ₀ ≥ 7/8 (min ≤ δ₀ ≤ 1/8).
x-powers: x^a = x·x^{1/log x}, x^{1/log x} = e (Real.rpow_def_of_pos: x^{1/logx} = exp(logx·(1/logx)) = exp 1; needs log x ≠ 0 ✓): so x^a = e·x (rpow_add hx0: x^{1+1/logx} = x^1·x^{1/logx} = x·e ✓ `Real.rpow_add (0<x) 1 (1/log x)` + rpow_one). x^{σ₀} = x^{1−A/(2u⁹)} = x·x^{−A/(2u⁹)} = x·exp(−(A/(2u⁹))·u^{10}) = x·exp(−A·u/2)·(exponent algebra: (A/(2u⁹))·u^{10} = A·u/2 ✓ field_simp with u ≠ 0): via rpow_def/rpow_natCast: x^{−A/(2u⁹)} = exp(log x·(−A/(2u⁹))) = exp(−(A/2)·u) ✓.
Assemble the three error pieces with pow_mul_exp_neg_le (b := 1 for tails: u^{20}e^{−u}·[const] ≤ 20!·2^{20}·e^{−u/2} ≤ …e^{−(A/4)u} since A/4 ≤ 1/2 ✓ monotone exp; b := A/2 for left edge u⁹-prefactor: u⁹·e^{−(A/2)u} ≤ 9!(4/A)⁹e^{−(A/4)u} ✓; horizontals: e^{−2u}-scale trivially ≤ e^{−(A/4)u}·bounded… but has u⁹·e·x·e^{−2u}: u⁹e^{−2u} ≤ 9!·1⁹·e^{−u} ≤ … ✓). Medge ≤ (M₀ + 2u⁹/A? (1−σ₀)⁻¹ = 2u⁹/A) and (2240/A)u⁹: Medge ≤ (M₀ + 2/A + 2240/A)·u⁹ for u ≥ 1 (M₀ ≤ M₀u⁹ ✓). C₀ := explicit combination (just take C₀ := big sum of the constants; final linarith).
NUMERIC pre-cert: check the assembled inequality chain symbolically at u = 5, A = 1/(2·448⁴·756), δ₀ = 0.05, M₀ = 100 (plug into both sides of each absorption step) — script before writing.

### (Z5c3h-ii) DONE — **THE POWER-LOG PNT FOR ψ_tent (Z5c COMPLETE)**
Numeric cert: 12 trials of the full absorption chain (scaled constants), all pass; C₀-pieces as coded.
`RHTower/PerronPowerLogPNT.lean` [PROVED HERE], standard axioms, built, lint clean:
- **`exists_smoothed_chebyshev_power_log`** : ∃ c₀ > 0 (:= zetaLowerA/4), C₀ ≥ 0 (explicit modulo M₀), x₀ ≥ 3, ∀ x ≥ x₀:
  `‖∑' Λ(n)·(log(x/n))⁺ − x‖ ≤ C₀·x·exp(−(c₀·(log x)^{1/10}))`.
  THE UNCONDITIONAL de la Vallée Poussin PNT (smoothed/Cesàro form) with tenth-root exponent. Choices: u := (log x)^{1/10} (rpow; u^{10} = log x via `← rpow_natCast + ← rpow_mul`), a := 1+1/log x (x^a = e·x), T := e^u, W := e^u/(2π), σ₀ := 1 − A/(2u⁹) (x^{σ₀} = x·e^{−Au/2}), x₀ := exp(u₀^{10}), u₀ := max 3 (max (2/A) ((A/2δ₀)^{1/9})).
- GOTCHAS: (1) big-numeral defs (zetaLowerA) inside nlinarith → isDefEq TIMEOUT — replace nlinarith by linarith with explicit `hdist` ring-identities; `set_option maxHeartbeats 3200000 in` for the theorem. (2) 9 < e³ via `pow_lt_pow_left₀ Real.exp_one_gt_d9` on 2.7182818283³ + nlinarith. (3) u₀ ≤ u from u₀^10 ≤ u^10 via `le_of_pow_le_pow_left₀`. (4) e^{−2u} = ((e^u)²)⁻¹ via `← Real.exp_nat_mul + exp_neg + norm_num`. (5) field_simp often closes goals fully — orphan `ring` = "No goals".

NEXT (Z5d — UNSMOOTHING to ψ(x) = x + O(x·e^{−c(log x)^{1/10}})):
The tent sum is S(x) := Σ Λ(n)·(log(x/n))⁺ = ∫_1^x ψ(t)/t dt (Abel; or use directly). Standard two-sided trick WITHOUT integrals: for h > 0:
  S(x·e^h) − S(x) = Σ Λ(n)·[(log(xe^h/n))⁺ − (log(x/n))⁺] ≥ Σ_{n ≤ x} Λ(n)·h = h·ψ(x) (each term ≥ h for n ≤ x since both logs shift by h and (·)⁺ diff ≥ h when log(x/n) ≥ 0; ≥ 0 always).
  Similarly S(x) − S(x·e^{−h}) ≤ h·ψ(x) (terms ≤ h·[n ≤ x indicator] + 0…: for n ≤ xe^{−h}: diff = h; for xe^{−h} < n ≤ x: diff = (log(x/n))⁺ ≤ h; n > x: 0. So ≤ h·ψ(x) — CHECK: sum of diffs ≤ h·#{n ≤ x}-weighted = h·ψ(x) ✓).
  ⟹ [S(xe^h) − S(x)]/h ≥ ψ(x) ≥ [S(x) − S(xe^{−h})]/h.
  With S(y) = y + E(y), |E(y)| ≤ C₀ y e^{−c₀(log y)^{1/10}}: ψ(x) ≤ [xe^h − x + |E|+|E|]/h = x·(e^h−1)/h + 2C₀·xe^h·e^{−c₀(log x)^{1/10}}/h; (e^h−1)/h ≤ 1+h for h ≤ 1 (banked-style exp ineq: e^h ≤ 1+h+h² for h ≤ 1: from add_one_le_exp-type + quadratic bound — mathlib `Real.exp_le_one_add...`? need e^h − 1 ≤ h + h² for 0 ≤ h ≤ 1: `Real.exp_bound`? probe `Real.exp_bound : |x| ≤ 1 → |exp x − (1+x)| ≤ x²`-form exists: `Real.exp_bound'`/`Real.abs_exp_sub_one_sub_id_le : |exp x − 1 − x| ≤ x²` for |x| ≤ 1 ✓ I recall this). Choose h := e^{−(c₀/2)(log x)^{1/10}}: error x·h + 2C₀x·e·e^{−c₀u}/h ~ x·e^{−(c₀/2)u} ✓. Also (log xe^{±h})^{1/10} vs (log x)^{1/10}: log(xe^{−h}) = logx − h ≥ logx/2: monotone rpow — the E-bound at xe^{±h} transfers with constant adjustments (e^{−c₀(log xe^h)^{1/10}} ≤ e^{−c₀·…}: (log xe^h)^{1/10} ≥ (log x)^{1/10}?? for e^h ≥ 1 ✓ log grows ✓ fine for the upper; for xe^{−h}: (log x − h)^{1/10} ≥ ((log x)/2)^{1/10} = 2^{−1/10}u: rate c₀·2^{−1/10} — absorb into c/2). FINAL: `exists_psi_power_log : ∃ c C x₀, ∀ x ≥ x₀, |ψ(x) − x| ≤ C·x·exp(−c·(log x)^{1/10})` where ψ is the corpus's Chebyshev function (find banked name: rg "def chebyshevPsi|psiRemainder" — the elementary-PNT files (psiRemainder_eventually_le) define ψ — REUSE that def for connectivity!). Then: growing-order window primes → parent card (8a) full-rate → 5b-iii → capstone.

### (Z5d-1) DONE — the unsmoothing sandwich
Numeric cert: 3 trials (one exact-equality boundary case), sandwich holds.
`RHTower/PerronUnsmoothingStep.lean` [PROVED HERE], standard axioms, built:
- `perronTentSum` def (real tent sum), `perronTent_term_eq_zero` (support ≤ ⌊x⌋), `summable_perronTent` (`summable_of_ne_finset_zero`),
- `norm_perron_sum_sub_eq` : ‖ℂ-Perron-sum − ↑x‖ = |perronTentSum x − x| (realification via `Complex.ofReal_tsum`) — CONNECTS `exists_smoothed_chebyshev_power_log` to the real tent sum.
- **`log_mul_psi_le_perronTent_sub` / `perronTent_sub_le_log_mul_psi`** : log(y/x)·chebyshevPsi ⌊x⌋₊ ≤ S(y) − S(x) ≤ log(y/x)·chebyshevPsi ⌊y⌋₊ for 0 < x ≤ y — termwise collapse on Icc 1 ⌊·⌋₊ (`Summable.sum_le_tsum`, `Summable.tsum_le_tsum` vs if-then-else comparison seq, `tsum_eq_sum`), log-quotient algebra via `← Real.log_div` + field_simp.
- GOTCHA: chained `rw […, mul_zero, mul_zero, sub_self]` over-rewrites (first mul_zero hits both) — end case branches with `norm_num`.

NEXT (Z5d-2 — FINAL: ψ power-log PNT), file `ChebyshevPsiPowerLogPNT.lean`:
`exists_chebyshevPsi_power_log : ∃ c C x₀ : ℝ, 0 < c ∧ 0 ≤ C ∧ 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → |chebyshevPsi ⌊x⌋₊ − x| ≤ C * x * Real.exp (−(c * Real.log x ^ ((1:ℝ)/10)))`.
Proof: obtain c₀ C₀ x₀' from `exists_smoothed_chebyshev_power_log`; via `norm_perron_sum_sub_eq`: |perronTentSum z − z| ≤ C₀ z e^{−c₀(log z)^{1/10}} for z ≥ x₀'. Choose h := exp(−(c₀/2)·(log x)^{1/10}) ∈ (0,1]; y := x·e^h... simpler symmetric: UPPER: ψ(⌊x⌋₊)·log(y/x) ≤ S(y) − S(x) ≤ |S(y) − y| + (y − x) + |S(x) − x| with y := x·e^h: log(y/x) = h: ψ ≤ [C₀y·E(y) + x(e^h −1) + C₀x·E(x)]/h; LOWER: with x' := x·e^{−h} (≥ x₀' needs x ≥ x₀'·e): ψ(⌊x⌋₊) ≥ [S(x) − S(x')]/log(x/x') = [x − x' − |errors|]/h ≥ [x(1−e^{−h}) − 2C₀x·E(x')]/h. Then |ψ − x|: e^h−1 ≤ h + h² (for h ≤ 1: `Real.abs_exp_sub_one_sub_id_le : |x| ≤ 1 → |exp x − 1 − x| ≤ x^2` — probe exact name; gives x(e^h−1)/h ≤ x(1+h)) and 1−e^{−h} ≥ h − h² (same lemma at −h). E(y) ≤ E(x) (log y ≥ log x → rpow mono → exp anti) and E(x') ≤ E(x)·(rate at logx − h ≥ logx/2: (logx−h)^{1/10} ≥ (logx/2)^{1/10} = 2^{−1/10}(logx)^{1/10} ≥ (1/2)·u: so E(x') ≤ e^{−(c₀/2)u} hmm exact: exp(−c₀(log x')^{1/10}) ≤ exp(−(c₀/2)u) ⟸ (log x − h)^{1/10} ≥ u/2 ⟸ log x − h ≥ (u/2)^{10} = u^{10}/1024 ⟸ log x − 1 ≥ log x/1024 ✓ easily for log x ≥ 2); y-side e^h ≤ e. Collect: |ψ(⌊x⌋₊) − x| ≤ x·h + x·h² + 3C₀·e·x·e^{−c₀u}/h ≤ x·h·(1+h) + 3eC₀·x·e^{−c₀u+ (c₀/2)u} = … with h = e^{−(c₀/2)u}: ≤ (2 + 3eC₀)·x·e^{−(c₀/2)u}. Final constants c := c₀/2, C := 2 + 3e·C₀, x₀ := max(x₀'·e, exp(2·…)) with the log x − h ≥ … side conditions (x₀ := max (Real.exp 1 * x₀') (exp of threshold)). All elementary; watch: ψ(⌊x⌋₊) needs x ≥ 1 for floor sanity; h ≤ 1 ✓ automatic (exp of negative).
AFTER: window-prime corollaries (parent card growing-order nodes: primes in [X, X(1+Θ(1/log X))] from ψ-increments: ψ(X(1+δ)) − ψ(X) = Xδ + O(Xδ·small) > 0 …) → (8a) full form → 5b-iii → capstone.
