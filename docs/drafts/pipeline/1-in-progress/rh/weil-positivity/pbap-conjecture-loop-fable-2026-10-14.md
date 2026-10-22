# PBAP conjecture loop (archimedean value function, blind cone geometry)

- **ID:** pbap-loop-fable-2026-10-14
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop) with THEOREM (Lean) rows 1–6 (MUST-1478, 1479, 1480, 1483, 1485)
- **Source:** docs/reports/rh-current-frontier-map.md (route HF, "Needs: prove PBAP"); STATUS MUST-1431/1437/1439
- **Statement:** PBAP (pole + archimedean energy ≥ 0 on every nonnegative blind combination of autocorrelations) is RH; this card runs a conjecture → Lean → learn loop on its structure.

## Goal
Find the mechanism by which the archimedean place (symbol `A(r) = Re ψ(¼+ir/2) − log π`, pole `k̂(±i/2)`) and the
positions `log n` force positivity on the blind cone. Every row is either a Lean theorem (unconditional) or a
recorded failure with the exact obstruction.

## Gates
- [x] 0 → 1  in-progress: well-posed (RH ⟺ PBAP is [L]); attack = structure of the blind cone and its dual
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Reading of the corpus (frontier map + STATUS only): PBAP is a sharp LP with unique dual `Λ`, infinite-dimensional
equality face (Ξ²-divisible tests), node-critical at every prime power, pole-critical (β = 1, depth ½), trivial on
the nonnegative and support-blind sectors. A direct proof must be primal (no certificate other than `Λ` exists).

## Synthesis after rows 1–6 (2026-10-14)
The prime-blind LP is now described completely at the level of its value function and duality:
* **Gradient law.** `inf {A(c) − P(c) : L(c) = v, P(c) = p} = Σ Λ(n) v_n − p` under RH (rows 1–2); the primes are
  the node prices and the pole has price exactly `−1`. Every fibre is unbounded below without RH.
* **Where the RH content sits.** RH ⟺ the archimedean symbol integral is ≥ 0 on blind combinations of total pole
  mass zero (row 2). Unconditionally the symbol alone is ≥ `−3.37·mass` on blind combinations (row 3, one prime)
  and negative somewhere on them (pole-weight rigidity). So the symbol has a definite negative part on the blind
  cone, bounded between `M₁* ∈ (0, 3.37]`, and the single constraint `P(c) = 0` must remove it entirely; pointwise
  (periodization) certificates cannot see that constraint. All RH content is on pole-light tests
  (`P(c) < 3.37·mass`); pole-heavy blind tests are unconditionally positive.
* **Null face.** Every `Ξ`-divisible blind test is pole-light: pole ≤ `3.37·mass` (row 4).
* **Finite levels.** The admissible pole weights at level `L` form a compact interval shrinking to `{1}`
  unconditionally; RH ⟺ no window is empty (row 5). Determinant form: RH ⟺ the pole weight demanded by
  pole-positive blind combinations never exceeds the one allowed by pole-negative ones (row 6).
* **What a proof of PBAP must do.** It must use `P(c) = 0` (equivalently `K̂(i/2) = 0`, the `s(1−s)` factor of `ξ`)
  in a non-pointwise way, at every prime power, and it must beat the symbol's negative part exactly. The only
  known such mechanism is the explicit formula itself. The small-level windows (`2L < log 2`) are nonempty iff the
  signed window positivity holds (open, numeric margin ≈ 0.15; other agents on the Lévy–cosh route).

## Log
- 2026-10-14 — created. Mission: contribute to PBAP.
- 2026-10-14 — **Row 1 [L]. The archimedean node value function is linear with gradient `Λ`.**
  Module `RHTower/ArchimedeanNodeValueFunction` (standard axioms, `lake env lean` clean, wired).
  For a finitely supported node vector `v` let `nodeFibre v` = energies `A(c)` of nonnegative combinations `c`
  with node vector `L(c) = v`, and `nodeValue v = inf nodeFibre v`.
  * `nodeFibre_nonempty`: every `v` is attained.
  * `nodeValue_eq_vonMangoldtPairing`: under RH, `nodeValue v = Σ_n Λ(n) v_n` for every `v`
    (Hahn–Banach `exists_extension_of_le_sublinear` on the sublinear `V`, then full-cone uniqueness
    `eq_vonMangoldt_of_weilPositiveFull`). So `V` is linear and `∇V = Λ`.
  * `nodeValue_single`: mass `t` at one node `m` costs `t Λ(m)` (both signs).
  * `not_bddBelow_nodeFibre`, `riemannHypothesis_iff_bddBelow_nodeFibre`: without RH every fibre is unbounded
    below; RH ⟺ one fibre bounded below.
  * `riemannHypothesis_iff_nodeFibre_add_neg_nonneg`, `riemannHypothesis_iff_unitNode_two_sided`:
    RH ⟺ `A(c₊) + A(c₋) ≥ 0` for all `c₊` with `L(c₊) = v` and `c₋` with `L(c₋) = −v` (any single `v`,
    e.g. `v = e_m`): the least energy carrying mass `+1` at `m` and the least energy carrying mass `−1` at `m`
    add to zero.
  Reading: MUST-1439 (single node, positive mass) is the restriction of a linear law. The convex value function
  of the archimedean LP has no kinks; its gradient is the von Mangoldt function. Composite nodes are free in both
  directions, prime powers cost `log p` one way and refund `log p` the other way.
- 2026-10-14 — **Row 2 [L]. The value function with the pole as a coordinate has gradient `(Λ, −1)`;
  RH ⟺ zero-pole blind positivity.** Module `RHTower/ArchimedeanPoleValueFunction` (standard axioms,
  `lake env lean` clean, wired).
  * Blind tests of both pole signs by support (`adjTestFn ±1`: two bumps at `±1/5`, autocorrelation inside
    `(−log 2, log 2)`): `pole_adjTestFn_one_pos`, `pole_adjTestFn_neg_one_neg`; every real pole mass is
    realised by a blind nonnegative combination (`exists_blind_nodePoleMass_eq`).
  * `poleFibre v p` = values `A(c) − P(c)` (archimedean symbol only) over nonnegative `c` with node vector `v`
    and total pole mass `p`; nonempty for every `(v, p)`.
  * `poleValue_eq` (RH): `inf poleFibre v p = Σ_n Λ(n) v_n − p`. Proof: sublinearity, Hahn–Banach on
    `(LogIndex →₀ ℝ) × ℝ`, then the touching linear functional `g₁(v) + b p` makes the weights `g₁(e_n)`
    Weil-positive at pole weight `−b`, so `b = −1` (`eq_one_of_weilPositiveAt`) and `g₁ = Λ` (cone uniqueness).
    Special case `poleValue_zero_left`: blind combinations of pole mass `p` have archimedean part ≥ `−p`, sharply.
  * `riemannHypothesis_iff_zeroPoleBlindPositive`: RH ⟺ `(1/2π)∫ A(r) dμ_c ≥ 0` for every nonnegative blind `c`
    with total pole mass `0`. Proof: Farkas (`exists_of_nonneg_on_null_cone`) on `Option LogIndex`, generators
    = pole-corrected pair tests (pair test + blind adjuster) and the two adjusters; the dual weights are
    Weil-positive at pole weight `1 − lam none`, forced to `1`, then full-cone positive ⟹ RH.
  * `riemannHypothesis_iff_forall_le_poleFibre`, `not_bddBelow_poleFibre`, `riemannHypothesis_iff_bddBelow_poleFibre`.
  Reading: MUST-1439 (node prices `Λ`) and MUST-1463 (pole weight exactly `1`) are the two components of one
  gradient. The pole is a coordinate with marginal price `−1`; under ¬RH there is a blind, pole-free
  combination with negative archimedean symbol integral. The polar-constrained PBAP of the corpus (each test
  pole-free) is the special case of the zero-total-pole criterion.
- 2026-10-14 — **Row 3 [L]. One-prime certificate and the slack invariants.** Module
  `RHTower/BlindArchimedeanNodeTwoCertificate` (standard axioms, `lake env lean` clean, wired).
  * Pointwise: `2(1 − cos(r log 2)) ≤ γ(r) − γ(0)` for all real `r`, from the first two Gauss terms of the
    vertical digamma expansion (`two_mul_one_sub_cos_le_gammaBracket_sub`).
  * Integrated: for every test, `Re P(k) + (γ(0) + 2)‖f‖² − √2 ℓ₂(f) ≤ weilArchRe k`
    (`node_two_certificate_le_weilArchRe`); on combinations blind at `2`, `P(c) + (γ(0)+2) mass(c) ≤ A(c)`
    (`sum_node_two_certificate_of_blind_two`). The anomaly `γ(0) ≈ −5.37` of `WeilBlindPoleSignLaw` becomes
    `γ(0) + 2 ≈ −3.37` from the single prime `2`.
  * Slack invariants: `BlindSymbolSlack M` (symbol integral ≥ `−M·mass` on blind combinations) holds for
    `M = −γ(0) − 2 ≈ 3.37` (`blindSymbolSlack_node_two`) and fails for every `M ≤ 0`
    (`not_blindSymbolSlack_of_nonpos`, from `exists_blind_arch_add_mul_pole_neg` at `ε = −1`). So the symbol alone
    has a definite negative part on the blind cone, of relative size in `(0, 3.37]`.
    `ZeroPoleBlindSymbolSlack M` (total pole mass zero) holds for all `M > 0` iff RH
    (`riemannHypothesis_iff_forall_pos_zeroPoleBlindSymbolSlack`).
  Reading: two zeta-free numbers `M₁* = inf{M : BlindSymbolSlack M} ∈ (0, 3.37]` and
  `M₀* = inf{M : ZeroPoleBlindSymbolSlack M} ∈ [0, M₁*]` with RH ⟺ `M₀* = 0`. Periodization certificates
  (finitely many primes, pointwise in `r`) can only lower the upper bound on `M₁*`; they cannot see the pole
  constraint, which must remove the entire negative part. This is CANNOT-539/MUST-1447 in quantitative form.
  Next: sharpen the certificate with more nodes (3, 4 = 2², 5, 7) to locate `M₁*`; a certificate for `M₀*`
  needs the pole constraint, i.e. a non-pointwise mechanism.
- 2026-10-14 — **Row 4 [L]. Decay-class certificate and the pole of (N1) witnesses.** Module
  `RHTower/BlindDecayClassPoleCertificate` (standard axioms, `lake env lean` clean, wired). Also appended to
  `ArchimedeanPoleValueFunction`: `riemannHypothesis_iff_forall_blind_archOnly_add_posPart_nonneg` (RH ⟺ the
  symbol's deficit on a blind combination never exceeds its positive pole mass) and the sector criteria
  `riemannHypothesis_iff_blind_nonposPole_sector`, `riemannHypothesis_iff_blind_nonnegPole_sector`.
  * Truncation (`truncTest`, `tendsto_paperFT_truncTest`, `tendsto_crossCorr_truncTest`,
    `tendsto_archPoleEnergy_truncTest`) transfers the node-two certificate to the exponential decay class:
    `2 Re(F̂(i/2) conj F̂(−i/2)) + (γ(0)+2)∫F² − 2 (F⋆F̃)(log 2) ≤ archPoleEnergy F`
    (`pole_add_anomaly_sub_node_two_le_archPoleEnergy`).
  * For `Ξ`-divisible prime-blind tests (`archPoleEnergy = 0`): pole ≤ `(−γ(0) − 2)∫F²`
    (`pole_le_of_xiDivisibleBlindTest`), and with `F̂ = Ξ g`, `Ξ(±i/2) = ½`:
    `Re(g(i/2) conj g(−i/2)) ≤ 2(−γ(0) − 2)∫F²` (`re_g_mul_conj_g_le_of_xiDivisibleBlindTest`).
  Reading: every (N1) witness has pole-to-mass ratio ≤ 3.37, a bound coming from the prime 2 alone; the null
  face is "pole-light". Under RH the maximal pole-to-mass ratio on the null face equals `M₁*` (Row 3).
- Failed/abandoned conjectures this session (for the record):
  * C-even: "RH ⟺ PBAP on even tests" — not attempted in Lean; obstacle: even tests cannot realise `−e_j` exactly
    (negative node values drag in `e_{j²}, e_{j³}`), so the two-sided Farkas lemma does not apply as stated.
  * C-ξ-form: writing zero-pole tests as `k = (¼ − ∂²)k₁` with `k₁` compactly supported (the `s(1−s)` factor of
    `ξ`) gives no new certificate: the periodization family becomes `(r²+¼)cos(r log n)`, the same LP.
  * C-min-at-0: "the blind clock `Z_k(r) = ⟨T, k e^{irx}⟩` is minimised at `r = 0`" — false (spectral mass near
    `r₀ = 30` makes `Z_k(30) < Z_k(0)` under RH via the zero-free ordinate range below `14`).
- 2026-10-14 — **Row 5 [L]. The pole-weight window at finite level squeezes to `{1}`; RH ⟺ every level window
  is nonempty.** Module `RHTower/PrimeBlindPoleWeightLevelWindow` (standard axioms, `lake env lean` clean, wired).
  * `PrimeBlindPositiveAtLevel L β`: `A(c) + (β − 1)P(c) ≥ 0` on nonnegative blind combinations of tests supported
    in `[−L, L]`; `levelWindow L` = admissible `β`. Antitone in `L`, an interval, closed; for `L ≥ 3/10` contained in
    the explicit compact interval `[windowLower, windowUpper]` cut out by the two-bump tests of both pole signs.
  * `exists_level_not_mem_levelWindow`: every `β ≠ 1` is excluded beyond some level (MUST-1463 at the primal level:
    the violating blind combination has finite support).
  * `exists_level_forall_abs_sub_one_lt`: for every `ε > 0` all windows beyond some level lie in `(1−ε, 1+ε)`,
    unconditionally (nested compact sets intersected with the bands `[1+ε, β₊]`, `[β₋, 1−ε]`).
  * `riemannHypothesis_iff_forall_level_exists_mem_levelWindow`: RH ⟺ ∀ L ∃ β, β ∈ levelWindow L. The pole weight
    is free at each finite level and determined only in the limit; RH says the squeeze never empties the window.
  Reading: a finite-level RH criterion in which the pole weight is a free parameter — "at every level some pole
  weight works". Under ¬RH the windows become empty at a finite level `L₀`, a zeta-free measure of RH failure;
  under RH they contain `1` and shrink to it. Next: locate the window at small levels explicitly (`L < log 2/2`,
  no nodes), where `levelWindow L` is the set of `β` with `βP(f) + arch(f) ≥ 0` on `[−L, L]`.
- 2026-10-14 — **Row 6 [L]. Determinant criterion.** Appended to `PrimeBlindPoleWeightLevelWindow`:
  `riemannHypothesis_iff_forall_blind_det_nonpos`: RH ⟺ for all blind `c₁` (`P(c₁) > 0`) and `c₂` (`P(c₂) < 0`),
  `arch(c₁) P(c₂) ≤ arch(c₂) P(c₁)`. With `q(c) = −arch(c)/P(c)` (the pole weight making `c` null): the weight
  demanded by every pole-positive blind combination is at most the weight allowed by every pole-negative one;
  under RH both sandwich `1`. Proof ⟸: a zero-pole violator `c` plus `s·adj₊` against `adj₋` gives
  `arch(c)P(adj₋) ≤ s·K` for all `s > 0`, impossible since `arch(c)P(adj₋) > 0`.
  Reading: the level windows are `[β⁻(L), β⁺(L)]` with `β⁻(L) = sup q` over pole-positive, `β⁺(L) = inf q` over
  pole-negative level-`L` blind combinations; `β⁻` increases, `β⁺` decreases; RH ⟺ `β⁻(L) ≤ β⁺(L)` for all `L`,
  and then both tend to `1` (Row 5). Under ¬RH they cross at a finite level.
- 2026-10-14 — **Row 7 [L]. Window nonemptiness = two finite-level inequalities.** Appended to
  `PrimeBlindPoleWeightLevelWindow`: `levelWindow_nonempty_iff` (for `L ≥ 3/10`): the level-`L` window is nonempty
  iff (i) level-`L` blind zero-pole combinations have nonnegative energy and (ii) the determinant inequality
  `arch(c₁)P(c₂) ≤ arch(c₂)P(c₁)` holds for level-`L` blind `c₁` (`P > 0`), `c₂` (`P < 0`). The admissible weight is
  `sSup` of the demanded weights `1 − A(c)/P(c)` over pole-positive combinations. With Row 5:
  RH ⟺ ∀ L, (i)_L ∧ (ii)_L — a family of finite-level, pole-weight-free criteria.
- 2026-10-15 — **Reading `docs/notes.md` against the LP structure (judged conjectures, no Lean needed).**
  * Track 2 of the notes ("add a Poisson/Mayer counterterm `Σ w_n (k(log n)+k(−log n))` so the combined kernel is
    PSD without sign restrictions") is RH itself: any `k`-independent counterterm making `W_∞ + Σ w_n ℓ_n ≥ 0` on all
    autocorrelations is a Weil-positive weight vector, hence `w = Λ` by `eq_vonMangoldt_of_weilPositiveFull`, and the
    resulting "positive form" is the zero sum `Σ_ρ |f̂(γ_ρ)|²`, which is a measure, not a function. `k`-dependent
    (nonlinear) counterterms do not help either: on a blind spectral measure every counterterm integrates to `0`, so a
    pointwise certificate `γ + D ≥ −M` can only lower `M₁*`, never see the pole constraint. Row 8 below records the
    finite-counterterm version in Lean.
  * Perspective A of the notes (Poisson collapse of `Σ_n φ(ny)` to `n = 1` on the blind cone) is realised by the other
    agents' MUST-1481: on the blind cone the pole mass is the critical-line ζ-defect
    `P = (1/π)∫|f̂|²(1 − Re ζ(½+it))`, so PBAP ⟺ `∫ s dμ ≥ 0` for blind `μ` with `s = γ/2 + 1 − Re ζ(½+it)`; `s(0) ≈ −0.23`
    and `s` is unbounded below (large values of `ζ`), so no pointwise proof; elementary form of the same defect:
    Euler–Maclaurin on the multiplicative lift `h(y) = (1+1/y) y^{−1/2}·2Re k(log y)`, `P = 2k(0) − ∫_1^∞ ({y}−½) h'`
    `= (5/3)k(0) − ½∫_1^∞ B̃₂(y) h''(y) dy` (not formalised; same content as MUST-1481).
  * The pole coordinate is the ζ-mean: `P/k(0) = 2(1 − ⟨Re ζ⟩_μ)`. The sector criteria of Row 4 read: RH ⟺ blind
    spectral measures with ζ-mean `≥ 1` have nonnegative `γ`-mean; the pole-light RH-critical sector is `⟨Re ζ⟩_μ > 0.2`.
  * Track 1 of the notes (nonnegative-cone `WindowPositive` on `(0, log 2)`, deficit `−0.1448` at the plastic crossover)
    is not implied by the corpus `√2` theorem `one_tenth_le_ccmRestrictedWeilPolarGroundEnergy_halfLogTwo`: that result
    lives on the pole-vanishing subspace (`IsPolarConstrained`, `F(±½) = 0`), while nonnegative tests have `P > 0`.
    Judged: RH-irrelevant (support `< log 2` sees no zero), other agents active; not pursued.
  * The Markov additions (`WeilMarkovOddPositivity`, `WeilMarkovPrimitiveHyperplane`) are the Λ-weighted parallels of
    Row 4's sectors: on blind tests `W_Λ = W_∞`, odd tests and the primitive hyperplane `F(½)+F(−½) = 0` have `P ≤ 0`,
    so they sit inside the nonpositive-pole sector. The full form splits by parity without cross term
    (`k_f = k_{f_e} + k_{f_o}` for real `f`), the blind constraint couples the parities (MUST-1501–1504 parity–sign table).
  * Single-test PBAP: every nonnegative blind combination is `g⋆g̃` for an `L²` function `g` (take `ĝ = √(Σ c_i|f̂_i|²)`), but
    `g` compactly supported needs Krein's spectral factorisation of nonnegative entire functions of exponential type —
    not in the corpus or Mathlib; a multi-session project with reformulation value only. Not started.
- 2026-10-15 — **Row 8 [L]. No finite certificate (CANNOT-557).** Module `RHTower/PrimeBlindFiniteCertificateObstruction`
  (standard axioms, `lake env lean` clean, `lake build --old` built, wired after `PrimeBlindPoleWeightLevelWindow`).
  `not_weilPositiveFull_of_finite_support`, `not_weilPositiveFull_of_eventually_zero`,
  `not_weilPositiveFull_of_eventually_const`, `infinite_support_of_weilPositiveFull`,
  `not_exists_finite_support_weilPositiveFull`: a weight vector with finite support, or vanishing beyond some node, or
  eventually constant, is never Weil-positive (uniqueness pins `lam(2^k) = log 2`, `lam(3^k) = log 3`).
  Reading: PBAP cannot be certified by `W_∞` plus finitely many node terms, nor by `W_∞` plus a constant-coefficient
  Dirichlet tail (the shape of the ζ-defect rewriting). Together with Row 3 (`M₁* > 0`) and MUST-1490 this closes every
  "symbol + counterterm" approach: the only Weil-positive correction is the full `Λ`, i.e. RH.
- 2026-10-15 — **Row 9 [L]. Finite-level Farkas and strong duality (MUST-1508).** Module
  `RHTower/PrimeBlindFiniteLevelFarkas` (standard axioms, `lake env lean` clean, `lake build --old` built, wired after
  `PrimeBlindFiniteCertificateObstruction`).
  * Two-bump tests with prescribed centres (`pairTestAt j σ a b`): autocorrelation
    `(1+σ²)K + σ(K(·+d) + K(·−d))`, `d = b − a`; node values (`logValue_pairTestAt`): if `|d − log j| < 2r_j` the only node
    value is at `j` and equals `σ(K(log j − d) + K(d − log j))/√j > 0·σ` (bump autocorrelation positive below the diameter,
    `bumpCorr_pos`); the node gap `1/(j+1) = 4r_j` kills every other node.
  * Level producers (`levelPairTestFn L n σ`): centred at `±log n/2` when `log n ≤ 2L − 2r_n`, at the ends `±(L − r_n)`
    otherwise; level `L`, node vector `σ·levelWeight L n · e_n` with positive weight, for every `log n < 2L`.
  * Level-`L` autocorrelations vanish at all lags `|Y| ≥ 2L` (`weilTest_eq_zero_of_levelTest`, endpoint included: the
    integrand lives on one point), so node vectors of level-`L` combinations are supported on `log n < 2L` and the projection
    `levelProj L` fixes them.
  * Generic level Farkas (`levelBlindNonneg_iff_exists_weights`): for any per-test functional `Φ`, nonnegativity on the blind
    level-`L` cone ⟺ ∃ node weights with `Σ lam ℓ(f) ≤ Φ(f)` on level-`L` tests; weights supported below `2L`
    (`exists_weights_support_of_levelBlindNonneg`). Proof: level value function + lift + Hahn–Banach with the zero functional.
  * Instances: `primeBlindPositiveAtLevel_iff_exists_weights` (pole weight `β`), `levelFloors_eq_levelMargins` (strong
    duality: floors of the blind functional = margins of level Weil forms, as sets), RH ⟺ ∀L ∃(β, lam) level-Weil-positive
    ⟺ ∀L ∃lam level-Weil-positive at β = 1.
  Reading: PBAP is a tower of finite semi-infinite LPs indexed by the level, each with finitely many dual variables; RW's
  aperture certificates with node counterterms are level-`L` dual feasibility witnesses; under ¬RH the tower fails at a
  finite level. Open: the exponential rate at which the level floors go to `−∞` under ¬RH should be `2(Θ − ½)` (needs the
  explicit formula); under RH the floors stay `≥ 0` and tend to `0`.
- 2026-10-15 — **Row 10 [L]. The level value (MUST-1511).** Module `RHTower/PrimeBlindLevelFloor` (standard axioms, clean, built,
  wired). Pole bound `|Re P(k_f)| ≤ 4Le^L‖f‖²` for level-`L` tests (`norm_paperFT_sq_le` at `±i/2`, product ≤ mean of
  squares); floor `γ(0) − 4|β|Le^L ∈ levelFloors L β`; floors bounded above by the energy-to-mass ratio of the blind two-bump
  test (its mass is positive: value `1` at `1/5`); floors closed; so `levelFloors L β = Iic (levelValueAt L β)` for
  `L ≥ 3/10`, blind positivity ⟺ `0 ≤ levelValueAt`, window `= {β : 0 ≤ p_L(β)}`, antitone in `L`, RH ⟺ ∀L ≥ 3/10,
  `0 ≤ p_L(1)`. Reading: `p_L(1)` is THE zeta-free finite-level RH observable; its a priori bound `−4Le^L` is the
  PBAP shadow of the trivial bound `Θ ≤ 1`.
- 2026-10-15 — **Row 11 [L]. Certificates squeeze onto Λ (MUST-1512).** Module `RHTower/PrimeBlindLevelCertificateSqueeze`
  (standard axioms, clean, built, wired). `levelCertificates L := weilBox ∩ {LevelWeilPositiveAt L 1}` with the canonical box
  from `coordBound` (pair tests); compact, antitone; `Λ ∈` at every level under RH; RH ⟺ all nonempty (Cantor + uniqueness);
  unconditional squeeze `∀n ε ∃N ∀L ≥ N ∀μ ∈ levelCertificates L, |μ n − Λ n| < ε`; any choice `μ_L` tends to `Λ`
  coordinatewise. Reading: the von Mangoldt function is the limit of finite-level archimedean LP certificates — the primes are
  recovered from the archimedean tower; node-weight analogue of Row 5.
- Conjecture queue after rows 8–11 (not attempted): (i) rate law `p_L(1) ≍ −e^{2(Θ−½)L}` under ¬RH (needs explicit formula);
  (ii) `p_L(1) → 0` under RH via truncated Ξ-divisible blind tests; (iii) make the squeeze quantitative: an explicit level
  `N(n, ε)` would be a zeta-free effective statement about `Λ(n)` — its proof needs the compactness argument replaced by
  explicit tests, which is where the arithmetic re-enters.
- 2026-10-15 — **Direct attack on the pole dichotomy. Row 12 [L] (MUST-1514): blind pole floor in mass and curvature.**
  Module `RHTower/PrimeBlindPoleCurvatureFloor` (standard axioms, clean, built, wired).
  * `P(c) = ∫ K_c · 2cosh(x/2)` with `K_c` the even real autocorrelation; blind ⟹ `K_c(log n) = 0`; gap estimate
    `|K_c(x)| ≤ M·gap²` (Rolle + mean value), `gap ≤ 1/n ≤ 2e^{−x}` ⟹ `|K_c(x)| ≤ 4Me^{−2x}` for `x ≥ log 2`;
    tails `≤ 6Me^{−x}`, middle `≤ (5/2)·mass` on `|x| ≤ log 2`; total `P(c) ≥ −(4·mass + 6·M)`;
    `A(c) ≥ (γ(0) − 2)mass − 6M` with Row 3.
  * Analysis of the dichotomy (bounded pole floor?): (i) pair tests, two-bump and multi-point configurations have
    `P/mass → 0` at large lag (bump width ≤ node gap `e^{−x}` kills the `e^{x/2}`); (ii) chirp-type kernels
    `−a(x)(1 − cos 2πe^{x})` carry negative lag mass but need covering spectral mass `≈ 2∫a e^{x/2}` (stationary phase,
    density `t^{−1/2}`), the same order as the pole gain, and the covering generates second-generation node values at
    doubled lags — exact blindness with large negative lag content is expensive; (iii) under RH the null face at height
    `T` has `P/mass = −arch/mass ≈ −γ(T) ≈ −log T`, so a bounded floor (weight `t^0`) is NOT expected even under RH:
    the sharp pole-floor weight is `log⁺|t|` with coefficient exactly that of `γ` (that statement is PBAP). Known
    rigorous weights: elementary gap argument gives `t²` (this row; refinable to `t^{1/2}` by a frequency split per
    gap), ζ-defect + convexity (MUST-1481) gives `t^{1/4+ε}`, Lindelöf would give `t^{ε}`.
  * Consequence for the tower: the question "is `p_∞ = inf_L p_L(1)` finite" is NOT decided by the pole alone; the
    heuristic (balanced dimension count: blind tests of level `L` resolve zeros at height `e^{2L}` with resolution
    equal to their spacing; peaked blind densities exist by projection) favours `p_L(1) → −∞` at rate `e^{2(Θ−½)L}`
    under ¬RH, i.e. RH ⟺ `p_L(1)` bounded below, and any unconditional floor `−Ce^{aL}` with `a < 1` would be a
    zero-free strip. Rigorously open in both directions.
  * Appended to the module: `nodeArchEnergy_ge_of_blind_of_curvature_le`, `div_nodeArchEnergy_ge_of_blind_of_curvature_le`
    — on the sub-cone of blind combinations with curvature ≤ κ·mass the energy ratio is ≥ γ(0) − 2 − 6κ at every level;
    a blind family with energy ratio → −∞ must have curvature/mass → ∞ (spectral mass escaping to high frequency).
- 2026-10-15 — **Row 13 [L]. Spectral tail of the blind pole (MUST-1516).** Two modules, standard axioms, clean, built, wired.
  * `PrimeBlindKernelSpectral`: spectral density `ρ_f = ‖f̂‖²/(2π)` (via `integral_normSq_paperFT_mul_cos_eq`),
    `K_c(x) = ∫ ρ_c cos(τx)`, integrability of `ρ_c`, `|τ|ρ_c`, `√|τ|ρ_c`, `τ²ρ_c` (decay `‖f̂‖ ≤ C/(1+|τ|)²`), split gap
    estimate `|K_c(u)| ≤ 2∫_{|τ|≥T}ρ + (b−a)∫_{|τ|<T}|τ|ρ` on `[a,b]` with `K_c(a) = K_c(b) = 0` (interpolation defect of the
    cosine, Lipschitz constant `|τ|`; no derivative of `K_c` needed).
  * `PrimeBlindPoleSpectralTail`: telescoping sums `Σ_{n≤m} n^{−1/2} ≤ 2√m`, `Σ_{n∈[m,N)} n^{−3/2} ≤ 2/√(m−1)`; per gap
    `∫_{gap_n}|K|2cosh ≤ (2√2/√n)(2μ_{≥n} + I_{<n}/n)`; gap sums as one spectral integral `∫ρ Σ gapWeight`; pointwise
    `Σ_{n∈[n₀,N)} gapWeight n τ ≤ 20√|τ|` for `|τ| ≥ n₀`, `≤ 6|τ|/√(n₀−1)` below; localized tail theorem and the global
    floor `P(c) ≥ −(4·mass + 58∫√|τ|ρ_c)`.
  * Observation during the proof: the first-order (Lipschitz) split gives the same weight `√|τ|` as the second-order
    (curvature) split would — the loss of one gap factor is exactly compensated by one less power of `|τ|` in the moment;
    the elementary gap method saturates at `√|τ|`. Beating `|τ|^{1/4}` (ζ-defect + convexity) needs the node vanishing on
    the high-frequency part, i.e. the anti-resonance statement; the chirp cost heuristic (covering mass `2∫a e^{x/2}` vs
    pole gain `2∫a e^{x/2}`) is the `√|τ|`-weight statement read at the exponential scale `τ ≈ e^x`: it is now a theorem
    in the form of the localized tail bound, not a bounded pole floor.
