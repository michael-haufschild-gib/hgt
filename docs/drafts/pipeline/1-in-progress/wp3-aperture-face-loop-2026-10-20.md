# WP3 aperture-face contribution loop (ACT, APT, OWU)

- **ID:** wp3-aperture-1020
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** docs/reports/work-packages.md §WP3
- **Statement:** Prove `μ(A) ≥ 0` for all profiles at apertures beyond the present one, and pass from
  the critical factorial family to the compact receiver tests without the archimedean gain `log M`.

## Goal
100 significant contributions in the sense of WP3: aperture increase for all profiles; compact
critical approximants with truncation-stable, `log M`-free margin; complete payment of the odd sector
(reflected prime, cosh pole, negative sinh moment) at a stated aperture class; a realization theorem
naming Hilbert space and Schatten class of the prime modification; selectivity against
`ζ(s−a)ζ(s+a)`.

## Gates
- [x] 0 → 1  in-progress: loop started 2026-10-20
- [ ] 1 → 2  per contribution
- [ ] 2 → 3  per contribution (Lean module, `lake env lean` audit, axioms standard, lint)

## Rules in force
Unconditional Lean statements only; one foreground Lean process; `lake env lean` audit and
`lake --old env lean -j 1 -o … -i …` for oleans; wire modules into umbrellas; no full or umbrella
builds; no numerical experiments; corpus search tool first; READMEs are mathematics only.
Knowledge ledger: `logs/wp3-aperture-face-knowledge.md`.

## Starting frontier (2026-10-20)
- Full zero form on all profiles: `Ẑ ≥ (1/30)∫F²` on `[−21/200, 21/200]` (ACT C27/C32), limited by
  the Z-type threshold `log ρ ≈ 0.2812` of the density `ω − 2cosh(t/2)` and crude constants.
- Pole-vanishing tests: corpus certificate `μ₀ ≥ 1/20` through `(log 2 + 1/50)/2`.
- APT: compact doubly collared critical sources positive on high blocks (C20–C22), margin from
  `log M`.

## Conjecture queue
1. Markov window past the plastic threshold (absorb the negative density on `(t₀, 2R]`): aperture
   `29/200`.
2. Curved even gauges (ground-state transform with `M = 1 − β x²/R²`): aperture ≈ 0.18–0.2.
3. Odd sector folded Z-type form; pointwise potential `A₀ + Ω(R−s) + 2Ω(s) − Ω(R+s)` minimal near
   `s = R/φ`; odd aperture ≈ 0.29; then past `log 2/2` with the reflected prime 2 paid by the edge
   killing (criterion 3).
4. APT: `log M`-free margin from the sign of the critical prime channel plus low-band exclusion.

## Contribution ledger (append-only)
- **C1 · Markov window past the plastic threshold: all-profile aperture 21/200 → 29/200** —
  `ArithmeticCriticalityTheory/MarkovWindowPastPlasticThreshold.lean` (compiled, olean, standard
  axioms, wired, lint clean for this module). `two_mul_cosh_le_archLevyDensity_of_le_plastic`
  (`ω ≥ 2cosh(t/2)` on `(0, 0.28]` via `a⁴ + a⁶ ≥ 1`, `a = e^{−t/2}`),
  `two_mul_cosh_sub_archLevyDensity_le` (negative density ≤ 0.07 on `(0, 0.292]`),
  `gaugeJumpProfile_le_four_mul_integral_sq`, sharp constants `log π < 1.1449`, `γ + log π < 1.722116`.
  Capstones `fullZeroForm_ge_of_support_le_pastPlastic` (`Ẑ(F) ≥ (1/125)∫F²` on `[−29/200, 29/200]`),
  `zetaZeroConfig_re_W_ge_of_support_le_pastPlastic`, `one_div_125_le_ccmRestrictedWeilGroundEnergy`
  (`μ(A) ≥ 1/125` for `A ≤ 29/200`), `lt_of_ccmRestrictedWeilGroundEnergy_nonpos_pastPlastic` (contact
  apertures exceed `29/200`). Criterion 1. Insight: the Z-type threshold `log ρ` is not a barrier for
  the aperture; the negative pole-minus-Lévy density beyond it is small and is paid by the potential.
  The binding constraint is the centre value of the window potential (exact limit ≈ 0.1526).
  Selectivity: archimedean (prime-free window); the same argument holds for `ζ(s−a)ζ(s+a)` at small
  `a` with modified constants — nonselective, as every prime-free window statement.
- **C2 · Curved window gauge: all-profile aperture 29/200 → 39/200, past every flat gauge** —
  modules `CurvedGaugeWindowCalculus` (general ground-state representation of `Ẑ(M u)` in a curved
  window gauge, pole identity with profile, negative density as a potential via Fubini),
  `CurvedGaugeArchimedeanBounds` (`½ + u/4 − u²/16 ≤ uω ≤ ½ + u/4`, `ω − ν ≤ 3/4 − u/6`, sharp one-sided
  killing `N(a) − 3a/4 + a²/12`, `N(s) ≥ −½log 2s + s/2 − s²/12` via `sinh s ≤ s e^{s²/6}`,
  `2cosh(t/2) − ω ≤ 6.5(t − 0.275)` on `[0.275, 0.4]`, `log(5/2)`, `log(4/3)`),
  `QuadraticGaugeWindowWeilPositivity` (gauge `M = (1 − 15y²)·plateau(1/5)`, potential bound with regional
  gain `15[G(a)+G(b) − 11x²/5]`, cost `6.5(1/5 + |x| − 0.275)₊²`, pole mass `2∫q`, 10-anchor
  piecewise window inequality). Capstones `fullZeroForm_ge_of_support_le_curved` (`Ẑ(F) ≥ (1/50)∫F²` on
  `[−39/200, 39/200]`), `zetaZeroConfig_re_W_ge_of_support_le_curved`,
  `one_div_fifty_le_ccmRestrictedWeilGroundEnergy` (`μ(A) ≥ 1/50`, `A ≤ 39/200`),
  `lt_of_ccmRestrictedWeilGroundEnergy_nonpos_curved`. All compiled, oleans, standard axioms, wired.
  Criterion 1. Insight: the flat gauge reproduces Suzuki's main term without `μ₁` (ACT C34); the curved
  gauge recovers part of `μ₁` — the regional log-Laplacian energy — explicitly, and the second-order
  killing (`−s²/12`) and density (`+a²/12`) terms cancel exactly, leaving the bracket
  `log(5/2) − 1/10 − (γ + log π) − ½log(1 − 25x²)`. The binding point is the window centre (centre gain
  `β(½ − 7R/6)` per unit curvature: the pole density `2cosh ≈ 2` eats most of the log-Laplacian gain).
  Selectivity: for `ζ(s−a)ζ(s+a)` the all-profile statement fails at every support for large `a`
  (pole at `1+a`; AIP ledger), so the statement is not true for the shifted pair.
- **C3 · Parity fold: all-profile aperture 39/200 → 6/25; the negative pole density is free on even
  tests** — modules `CurvedGaugeWindowPotential` (curved gauge `(1 − c y²)·plateau(R, δ)` for every
  `c ≥ 0`, `cR² ≤ 1`, `0 < δ < R ≤ 1/4`: potential bound, bracket `−log 2R − R/2 − (γ+log π) −
  ½log(1 − x²/R²)`, pole mass `2r − (2c/3) r³`; C2 now an instance), `EvenGaugeFoldedConductance`
  (for every measurable density `κ` with `|κ(t)| ≤ C/t`: even jump energy `∫κ I = 2∫_{x>0}[∫κ(s)J_s +
  ∫κ(s+2x)J_s]`, hence `∫κ I ≥ 0` whenever the folded conductance `κ(s) + κ(s+2x) ≥ 0` on `x + s < B`),
  `ParityFoldedCurvedGaugeWeilPositivity` (`Ẑ(F) = Ẑ(F_e) + Ẑ(F_o)`, `∫F² = ∫F_e² + ∫F_o²`; folded Weil
  conductance `ω(s) − 2cosh(s/2) + ω(s+2x) − 2cosh((s+2x)/2) ≥ 0` for `x + s < 241/1000`; even gauge
  `c = 13`, `R = 241/1000`, `δ = 1/1000`; nine-anchor window inequality ≥ 1/250; odd sector from AIP
  `fullZeroForm_ge_of_odd_support_le`). Capstones `fullZeroForm_ge_of_even_support_le_folded`,
  `fullZeroForm_ge_of_support_le_parityFolded` (`Ẑ(F) ≥ (1/250)∫F²` on `[−6/25, 6/25]`),
  `zetaZeroConfig_re_W_ge_of_support_le_parityFolded`, `one_div_250_le_ccmRestrictedWeilGroundEnergy`
  (`μ(A) ≥ 1/250` for `A ≤ 6/25`), `lt_of_ccmRestrictedWeilGroundEnergy_nonpos_parityFolded`. All
  compiled, oleans, standard axioms, wired; lint clean for ACT. Criterion 1. Insight: on even tests the
  crossing pair `(−a, b)` carries the same jump as `(a, b)`, so the long-lag negative density is paired
  with a short-lag positive one; the binding pair is `(x, s) → (0, R)`, giving the sharp fold aperture
  `R = log ρ` — twice the unfolded Z-type aperture `log ρ / 2`. Below it the even sector is limited only
  by the gauge (the centre potential; quadratic gauges stop near `R ≈ 0.25`). Selectivity as C2.
- **C4 · Quartic even gauge: all-profile aperture 6/25 → 13/50 (0.925 of the fold boundary log ρ)** —
  modules `QuarticGaugeWindowPotential` (sharp Lévy density `½ + u/4 − u²/48 − u³/32 ≤ uω ≤ ½ + u/4 −
  u²/48` on `(0, 1]` from `ω = 1/(4 sinh(u/2)) + 1/(4 cosh(u/2))`; Lévy moments `P_k − E_k ≤ ∫_a^b u^k ω ≤
  P_k` for all `k ≥ 1`; `uν ≥ ½(1 − u²/6)·T₅(−u)` from `ν = e^{−u}/(2 sinh u)`, hence `ω − ν ≤ 3/4 −
  3u/16 + u³/48` and the cubic killing `N(a) − 3a/4 + 3a²/32 − a⁴/192` (exact to second order, true value
  `Ω(a) − κ`); general profile-gauge potential `q(x)·killing + ∫_0^a ω(q(x) − q(x+u)) + ∫_0^b ω(q(x) −
  q(x−u))` for any `C²` profile; quartic gauge `1 − c y² + d y⁴` potential via signed moments; pole mass
  with `cosh ≥ 1 + z²/2`), `QuarticGaugeParityFoldedWeilPositivity` (gauge `c = 13.1`, `d = 20`,
  `R = 261/1000`, `δ = 1/1000`; ten-piece window inequality ≥ 1/250 with tangent cube and chord fourth
  power; even sector, all profiles, complex tests, ground energy). Also: `CurvedGaugeArchimedeanBounds`
  domains widened (`uω` bounds to `(0, 1]`, `ω − ν` to `(0, 3/5]`, linear deficit to `[0.275, 0.55]`),
  fold condition `weilJumpDensity_fold_nonneg` widened to `x + s < 27/100`, `|ω − 2cosh| ≤ 4/t` on
  `(0, 1]`. Capstones `fullZeroForm_ge_of_even_support_le_quartic`,
  `fullZeroForm_ge_of_support_le_quarticFolded` (`Ẑ(F) ≥ (1/250)∫F²` on `[−13/50, 13/50]`),
  `zetaZeroConfig_re_W_ge_of_support_le_quarticFolded`,
  `one_div_250_le_ccmRestrictedWeilGroundEnergy_quartic` (`μ(A) ≥ 1/250` for `A ≤ 13/50`),
  `lt_of_ccmRestrictedWeilGroundEnergy_nonpos_quarticFolded`. Compiled, oleans, standard axioms,
  wired; lint clean for ACT. Criterion 1. Insight: the quadratic gauge's edge penalty is the asymmetric
  regional term `−∫_0^{2R} ω(u)(q(R−u) − q(R)) du` (inward neighbours higher); a positive quartic term
  costs `≈ 3·10⁻⁴ d` at the centre and gains `≈ 4·10⁻³ d` near the edge, so the curvature can grow
  and the centre (`D_R + 4r + c(R²/2 − 7R³/6) ≈ −0.16 + 0.0134 c`, nearly `R`-independent) is lifted.
  The bound chain is tight: sharp moments recover `u²/48` per moment, the cubic killing `a²/96` per side.
  Selectivity as C2.
- **C5 · The even fold at the plastic boundary: all-profile aperture 13/50 → 7/25 (0.996 of log ρ)** —
  module `FoldBoundaryQuarticGaugeWeilPositivity`: sharp minorant `κ(t) ≥ f(t) = 1/(2t) − 7/4 − t/48 −
  9t²/32 − t⁴/192 − t⁵/1600` (`weilJumpDensity_ge_poly`), midpoint convexity `f(s) + f(t) ≥ 2f(m) +
  x²/R³ − x²(9/16 + …)` with `m = s + x`, `f(281/1000) ≈ 0.0013 > 0`, hence the folded conductance
  `κ(s) + κ(s + 2x) ≥ 0` on every pair `x + s < 281/1000` (`weilJumpDensity_fold_nonneg_boundary`);
  quartic gauge `1 − 13.2y² + 37.5y⁴`, `R = 281/1000`, `δ = 1/1000`, with the sign-changing
  second-moment coefficient absorbed by `max(c − 6dx², 0)` (`neg_poleFreeWeilOperator_quarticWindowGauge_ge_max`,
  added to `QuarticGaugeWindowPotential`; the old lemma is now its corollary); anchors `(3/4)^k` and
  `(7/8)(3/4)^k` (`log(8/7) > 0.13352`); fifteen-piece window inequalities (inner `[0, 0.242]`, outer
  `[0.242, 7/25]`); potential `≥ 1/500` on `[−7/25, 7/25]`; odd sector AIP `fullZeroForm_ge_of_odd_support_le`.
  Capstones `fullZeroForm_ge_of_even_support_le_foldBoundary`, `fullZeroForm_ge_of_support_le_foldBoundary`
  (`Ẑ(F) ≥ (1/500)∫F²` on `[−7/25, 7/25]`), `zetaZeroConfig_re_W_ge_of_support_le_foldBoundary`,
  `one_div_500_le_ccmRestrictedWeilGroundEnergy` (`μ(A) ≥ 1/500` for `A ≤ 7/25`),
  `lt_of_ccmRestrictedWeilGroundEnergy_nonpos_foldBoundary`. Compiled, olean, standard axioms, wired;
  lint clean for ACT. Criterion 1. Insight: with a large quartic term (`d ≈ 37.5`) the quartic gauge's
  potential is nearly flat (`0.0062–0.0080` on `[0, 0.23]`): the gauge is close to optimal within its
  family; the remaining limit is the fold boundary itself, where `2κ(R) → 0`. Beyond `log ρ` the folded
  conductance is negative exactly on pairs whose right point lies in `(log ρ, R)` and whose left point
  is within `≈ 0.54 √(y − log ρ)` of the centre (`f(s) + f(t) ≥ 2f(y) + 44x²`). Selectivity as C2.
- **C6 · The shifted pair has no positive window: even tests at every radius** — module
  `EvenWindowShiftedPairSelectivity`: even extension `F_a = G_a + G_a(−·)`, `G_a = e^{−ay}H`,
  `A_{F_a} = 2A_{G_a} + e^{−at}(H ∗ H)` (`autoCorr_add_reflect`); comparison identity
  `Ẑ_a(F_a) = 2Ẑ(F_a) + 8∫(cosh(at) − 1)κ A_{G_a} − 2∫(1 − e^{−at})² f (H ∗ H)`
  (`shiftedPairZeroForm_evenShiftTest`); same-side term `≤ 0` below the plastic threshold
  (`integral_sameSide_evenReweighted_nonpos`); Hankel term `≥ (3/2)(1 − e^{−aε/2})² m²`
  (`integral_hankel_evenBump_ge`, screw weight `≥ 3/2` on `(0, 0.15]`). Capstones
  `exists_even_shiftedPairZeroForm_neg` (for every `r > 0` and every large `a` an even test on `[−r, r]`
  has negative `ζ(s−a)ζ(s+a)` zero form) and `foldBoundary_window_selective` (with C5). Compiled, olean,
  standard axioms, wired; lint clean for ACT. Criterion 5. Insight: on even tests the shifted pair
  turns the negative off-diagonal coupling of `Ẑ` between a bump and its reflection,
  `−∫∫ f(x+y) H(x) H(y)`, into its diagonal; no Hankel indefiniteness is needed (contrast the odd
  case, AIP, which needs support ≥ 13/125). So window positivity of `ζ` at every aperture is selective,
  and the selectivity is carried by the even sector at small radii.

- **C7 · Past the plastic fold boundary: all-profile aperture 7/25 → 29/100** — module
  `PastPlasticFoldWeilPositivity` (+ `EvenGaugeFoldedConductance`: `integral_kappa_mul_gaugeJumpProfile_eq_fold_sum`,
  section integrability lemmas, and the **fold with a cost** `integral_kappa_mul_gaugeJumpProfile_ge_foldCost`:
  if `κ(s) + κ(s + 2x) ≥ −G(x + s)` on `x + s < B` with `0 ≤ G ≤ G₁`, then
  `∫κI ≥ −4(∫_{y>0} G M)(∫_{x>0} u²M) − 4B ∫_{y>0} G M u²`, via `J_s(x) ≤ 2M(x)M(x+s)u(x)² + 2M(x+s)u(x+s)²`).
  Pointwise fold `κ(s) + κ(s + 2x) ≥ 1/m + 2(−7/4 − m/48 − 9m²/32 − m⁴/192 − m⁵/1600)`, `m = x + s < 291/1000`
  (`weilJumpDensity_fold_ge_two_mul_poly`), and `≥ −13.03 (m − 281/1000)⁺` (tangent of `1/m`, chord of
  `m²`; `weilJumpDensity_fold_ge_neg_pastFoldCost`); cost constant `∫_{y>0} G M ≤ 0.000285`
  (`integral_pastFoldCost_mul_gauge_le`). Quartic gauge `1 − 12.98y² + 38.5y⁴`, `R = 291/1000`,
  `δ = 1/1000`; anchors `(3/4)^k (15/16)^j` (`log(16/15) > 0.06453`, `neg_half_log_one_sub_ge_anchor_grid`);
  fourteen pieces (`pastFoldGauge_window_inequality_inner_low/inner_high/outer/edge`); potential
  `≥ 1/1000 + 0.00057 + 2R G(|x|)` on `[−29/100, 29/100]` (`pastFoldGauge_potential_ge`); odd sector AIP
  `fullZeroForm_ge_of_odd_support_le_curved` (17/50). Capstones `fullZeroForm_ge_of_even_support_le_pastFold`,
  `fullZeroForm_ge_of_support_le_pastFold` (`Ẑ(F) ≥ (1/1000)∫F²` on `[−29/100, 29/100]`),
  `zetaZeroConfig_re_W_ge_of_support_le_pastFold`, `one_div_1000_le_ccmRestrictedWeilGroundEnergy_pastFold`
  (`μ(A) ≥ 1/1000` for `A ≤ 29/100`), `lt_of_ccmRestrictedWeilGroundEnergy_nonpos_pastFold`. Compiled, olean,
  standard axioms, wired; lint clean for ACT. Criterion 1. Insight: the plastic threshold `log ρ`, where the
  free even fold ends, is not a boundary of Weil positivity. Past it the negative folded conductance is a
  function of the outer point only (midpoint convexity), so it is paid by potentials: a constant
  `2∫GM ≈ 0.0006` (the gauge is small, `q ≈ 0.21`, on the strip `(log ρ, R)`) and an edge potential
  `≤ 0.07` that the edge logarithm of the gauge (`≥ 0.044` there) absorbs. The binding constraint is
  again the bulk potential `≈ 0.003` of the quartic gauge, not the fold; quartic limit ≈ 0.295.

## Log
- 2026-10-20 — loop started; frontier read (ACT/APT READMEs, ACT/APT ledgers, frontier map).
- 2026-10-20 — overlap: another agent (WP1/AIP) is building the odd-sector folded plateau result
  `AIP/OddPlateauFoldedWindowPositivity` (`[−7/25, 7/25]`, golden point); WP3 leaves the odd sector to
  it and works on the even sector (the all-profile bottleneck), APT criterion 2 and realization.
- 2026-10-21 — C3 done (parity fold, `[−6/25, 6/25]`). AIP agent has an unwired curved-fold odd module
  reaching `17/50`; the even sector remains the all-profile bottleneck. Next: flattened (quartic)
  even gauges toward `R ≈ 0.26`, then the fold boundary `log ρ`.
- 2026-10-21 — C4 done (quartic even gauge, `[−13/50, 13/50]`). Remaining room for the fold method:
  `13/50 → log ρ ≈ 0.2812`; beyond `log ρ` the folded conductance is negative at `(x, s) → (0, R)`.
- 2026-10-21 — C5 done (`[−7/25, 7/25]`, fold boundary). AIP has wired the curved-fold odd window
  `[−17/50, 17/50]` and works past `½ log 2`; the all-profile bottleneck is still the even sector.
  Next: even sector past `log ρ` (fold cost absorbed on the strip `y ∈ (log ρ, R)`, richer gauge).
- 2026-10-21 — C7 done (`[−29/100, 29/100]`, past `log ρ` with the fold cost). Even and odd sectors
  now both pass the plastic threshold; next even limit is the quartic gauge family (≈ 0.295); beyond it
  a richer gauge or a non-pointwise (Schur/Ritz) certificate is needed.
