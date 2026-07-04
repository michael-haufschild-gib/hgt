# MWM lane worklog — important findings and failures only

Convention: one dated entry per finding (F) or failure/dead-end (X). Fine-grained session
notes stay in `logs/rh-mwm-worklog.md`; raw computation outputs + RESULTS.md in
`computations/` here. Everything below is register-marked.

## 2026-07-03

- **F [PROVED, Lean]** Arc A banked: `formal/GaloisForLFunctions/RHTower/` — RH ⟺ coherent
  ℤ₂-Kummer tower of ξ on Re s > ½ ⟺ ∀k RHLadder k, and RHLadder k ⟺ analytic 2^k-th root of
  ξ, machine-checked against mathlib's `RiemannHypothesis`. Six capstones axiom-clean
  [propext, Classical.choice, Quot.sound]; card `3-formalized/new/rh-tower-obstruction-language.md`.
  Generic layer reusable: root⟺divisibility on convex exhaustions, derivative-free root
  rigidity, global peeling, ℕ∞-dvd descent helper.
- **F [MEASURED]** R2: all 237 off-line zeros of Davenport–Heilbronn in t ≤ 5002 are SIMPLE
  (odd winding); the single w=2 box bisected into two simple zeros. Off-line count ≈ T/21,
  linear in T — quantifies the DH-test separation against Ingham's o(T) for ζ. Gaps median 18,
  bounded at sample scale (defects recur robustly in the FE family).
- **F [MEASURED — session's main find]** R3: in the pencil f_k = (1−ik)/2·L(χ)+(1+ik)/2·L(χ̄)
  (FE exactly at k = κ ≈ 0.28408), the off-line defect count over a fixed window has a sharp
  MINIMUM at the FE fiber; the minimum's plateau shrinks LINEARLY in σ₀ − ½ (coeff ≈ 3–4.5)
  with κ centered at every band ⟹ the FE fiber is a regular transversal minimizer; measured
  defect-velocity dσ/dk ≈ 0.2–0.35. Computed one-constraint-down instance of the banked B7
  shape ("constraint = defect minimizer"). Data: `computations/R3-chunk1-RESULTS.md`.
- **X [REFUTED, banked import]** Mechanism M3 as positivity-alone: DMV Beurling systems are
  positive with generic off-line zeros (door bucket X5) — only FE ∧ positivity remains live.
- **X [DOWNGRADED, banked no-go]** Mechanism M2 (coarse Bohr continuity): the parent ledger's
  projection-blindness result (pure_facts ~9994) — ambient torus data cannot decide winding;
  any M2 must inject source data. Burden on M1 (explicit-formula weight mismatch).
- **X [dead shapes, do not retry]** ζ(s)/ζ(2s) log-positivity fails (coefficient 1/(2j)−1/j < 0
  at p^{2j}); shifted ζ(s−δ) keeps positivity but its zeros sit on its OWN symmetry line (the
  parity statement is FE-relative).
- **X [tooling]** `lake build | tail` masks failures (pipeline exit = tail's) — three modules
  were falsely "green"; gate builds need `set -o pipefail`. Lean traps hit: `h⊤` invalid
  identifier; `WithTop.ne_top_iff_exists` coercions don't match `Nat.cast` (use
  `ENat.coe_toNat`); no ℕ∞ dvd-descent in mathlib (wrote `natCast_dvd_natCast_of_enat`);
  `dite` under a lambda needs simp-beta; `analyticOrderAt_pow` is `n •` with explicit `n`.
- **F [instrument]** Winding engine validated (ζ boxes ≡ nzeros exactly; ξ residuals 1e-31;
  banked 18-digit D–H zero reproduced at 3.5e-17). Parallel mpmath on the pod: full t ≤ 5000
  survey in minutes. Engines: `computations/mwm/engine.py`, `engine2.py` (repo root).

Open checks (see 00-approach §8): #1 Bagchi (GATING — decides novelty of the cocycle
coarsening), #2 random-Euler a.s. nonvanishing, #3 Hamburger exact hypotheses, #4 DRH/partial
Euler, #5 off-line multiplicity-parity literature, #7 Bohr a.p. statements, #8 D–H off-line
density theorem (our T/21 wants its known counterpart). #6 resolved in-house (zeros computed
and certified ourselves).

## 2026-07-03 (wave 2)

- **F [VERIFIED READING — C2, gating check #1 resolved]** Bagchi confirmed as recalled: strong
  recurrence (sup-norm self-approximation on compacts of ½<Re s<1, shifts of positive lower
  density) ⟺ RH; proof route = Rouché + FULL-magnitude count (≥ cT → ∞) + zero-density. NO
  mod-2^k/parity/divisibility coarsening anywhere in the fetched line; follow-ups
  (Nakamura–Pańkowski et al.) generalize the shift, not the invariant. **Novelty verdict for
  the ladder package (mod-2^k cocycle + RH_{2^k} + analytic-root equivalence):
  ABSENT-FROM-LITERATURE.** Caveats: the two primary Bagchi texts auth-walled (read via
  secondary expositions); load-bearing quote spot-checked verbatim against ar5iv 2308.07031.
  Full note: `checks/c2-bagchi-note.md`; §8.1/§9.1/§10.2 of 00-approach updated. P2 unblocked.
- **F [PROVED HERE (paper) — C1]** The Reduction banked in `06-reduction.md`: (D) density
  o(T) [Ingham/Carlson, named input] × (R_k) conditional relative-density of coarse defects
  ⟹ RHLadder k; ∀k + banked tower collapse ⟹ RH. Care points now explicit: single-(σ₀,H)
  windows only force CLUSTER sums ≡ 0 mod 2^k (orders 1 and 2^k−1 can cancel) — per-zero
  divisibility needs (R_k) over all clean σ₀ and small H + left-edge telescoping; boundary
  zeros handled by co-countable parameter choice. Sharp level-1 corollary: "odd-count windows
  recur ⟹ no simple off-line zeros" is the lane's minimal open statement. Division of labor
  made precise: **the Euler product enters RH only through (D)** — (D) is measurably FALSE
  for D–H (T/21), while D–H's defect gaps are consistent with (R). Opened: [CHECK #9] where
  exactly density-theorem proofs consume multiplicativity.
- **F [MEASURED — R3b]** Window-2 replication (t∈[150,200)) CONFIRMED on all three
  pre-registrations: floor = 2 (boxes exactly [166,168], [176,178]), κ inside every plateau,
  plateau width linear in σ₀−½ with coefficient 4.0 (window 1: 3–4.5). The FE-fiber minimum
  is not a window artifact. Data: `computations/R3b-R5-RESULTS.md`.
- **F [MEASURED — R5, session's main find]** Euler-approach profile (c-path D–H → pure
  L(s,χ), σ₀=0.51, t≤200): n(u) = 4 → hump ≈ 29 mid-segment (neither constraint holds) →
  **0 exactly at the Euler point** (anomaly gate passed, family picture stands). Two-minimizer
  geometry computed: FE cut = transversal minimizer (floor 4 > 0), Euler cut = exact
  minimizer (floor 0). Near-Euler decay is LINEAR: n ≈ 120·(1−u) across the final fifth —
  a constant zero-flux through the σ₀ wall, no threshold. Euler-resistance ranking of last
  survivors (u=0.95): t ≈ 24, 70, 98, 116, 178, 196. Opened: R5b (per-zero wall-crossing u*,
  mobility distribution). Engine: `computations/mwm/engine3.py` (complex-c path).
- **F [VERIFIED READING — C0, checks #2/#3/#4/#5/#7/#8 resolved]** Full note
  `checks/c0-checks-note.md` (delegated; I spot-checked Lamzouri–Lee and the Sourmelidis
  claims against fetched pages). Verdicts: **#5 ABSENT-FROM-LITERATURE** — nothing anywhere
  on multiplicity of hypothetical off-line zeros ⟹ §10 item 1 (RH_{2^k} ladder) upgraded to
  VERIFIED-ABSENT; with C2, BOTH gating novelty items survived verification. #2 VERIFIED —
  random Euler product a.s. analytic + zero-free σ > 1/2 (three-series; HNR 1505.01443).
  #3 VERIFIED — Hamburger rigidity needs the EXACT ζ-FE (Perelli 1605.02354 Thm 2.1); Arc B's
  grafting question sits in the open gap. #4 VERIFIED — DRH (1210.1216, 2206.02612 Conj 5.1):
  the √2^{ν(ρ)} factor is the one literature place zero multiplicity enters an Euler-product
  law — bridge hook to the ladder. #7 PARTIAL — Bohr's theorem verified; "a.p. in σ>1/2 ⟺ RH"
  UNRESOLVED (book-source via C4). #8 PARTIAL — near-line asymptotic K₀TG(T)/√log G(T) fetched
  (Lamzouri–Lee 2010.10490) but (my caveat) its uniformity needs G(T)→∞; the fixed-strip
  linear law rests on the unfetched Bombieri–Hejhal pointer. **237/237 off-line simplicity has
  NO literature counterpart — genuinely new data.**
- **F [amendment — (R_k) weakened to Bagchi's register]** Second reader (GPT, user-relayed)
  flagged the limsup/liminf nuance; verified verbatim against ar5iv 2308.07031 ("Bagchi proves
  only (1)⇔(3)..."): Bagchi's original equivalence is the LIMSUP / positive-UPPER-density
  recurrence; the liminf form is the later, mostly-cited variant. 06-reduction.md §2/Step 1
  restated: (R_k) = conditional positive upper density (strictly weaker than bounded gaps;
  proof adapted via maximal H-separated extraction). The open core now sits in exactly the
  register Bagchi proved, one coarsening down. C2 note carries the addendum + Springer bib.
- **F [MEASURED — R5b: the Euler moat]** Fine scan u ∈ [0.90,1]: linear flux n ≈ 120(1−u)
  tracks to u ≈ 0.955 (±1), then COLLAPSE (4→1→0 across 0.960→0.980) and a defect-free MOAT
  u ∈ [0.980, 1.0] (σ > 0.51, t ≤ 200). Pre-reg: n(0.995)=0 ✓, but "uniform crossings"
  REFUTED at the tail — crossings cluster then stop. New structure: the Euler point sits
  inside an OPEN zero-free basin of the pencil (width ≈ 0.025), vs the FE fiber's nonzero
  floor — Euler positivity acts as an open condition, FE as a thin one. Most resistant zero
  t≈178 (u*≈0.975); full mobility ranking banked for R3c. Opened: R5c moat-scaling in T.
- **F [PROVED HERE (paper) — C3]** M1 made conditional in `07-index-formula.md`:
  Rouché-transfer lemma (boundary data of a defect box returning within its margin
  transfers the exact count, hence the defect) ⟹ Theorem: (H_k) ⟹ (R_k); with (D):
  (H_k ∀k) ⟹ RH. Isolated open core (H_k) = conditional positive-upper-density of
  sup-norm returns of 1-D contour data at ONE defect box — margin automatically positive
  (contour avoids zeros: the RH-hard near-zero approximation regime is dodged),
  counterfactual branch only, and symmetry slack: returns up to the FE/reality dihedral
  orbit suffice (what the mod-2^k coarsening buys on the mechanism side). §1: cocycle =
  coboundary of S(σ₀,·) mod 2^k. §2: linear/statistical channels certified blind by the
  three banked no-gos — transfer is the only faithful route. Register note: (H_k ∀k) sits
  at RH strength given the proven parts; the gain is the SHAPE (recurrence-rigidity of
  zero-avoiding boundary data), not logical strength. Opened: R6 (launched, pre-registered
  in §5.1), companion-cocycle [CONJECTURE] parked on C4's Speiser/Levinson–Montgomery
  verdicts.
- **X→F [MEASURED, registered prediction REFUTED — R6, the session's sharpest datum]**
  Boundary-data returns at the certified defect box [0.53,1.2]×[166,168]: margin 0.0235,
  deepest return over τ ∈ (1,400] is 0.556 ≈ 24× margin (zero sub-margin returns), while
  the defect population recurs ≈ 19× in the same range. **Defect recurrence ⇏ data
  recurrence**: the causal reading of the (H)-mechanism is refuted in the family (the C3
  theorem stands as mathematics; the negative is robust to the sampling proxy in both
  directions; (H) itself is not finite-window-refutable). M1's primary open core re-cut to
  **(P_k) population-forcing**: one coarse defect ⟹ linear off-line count — (P_k) + (D)
  kills defects with NO recurrence input; the family realizes (P) unconditionally
  (Bombieri–Hejhal regime, exact hypotheses pending C4). Files: `computations/R6-RESULTS.md`,
  07-index-formula §6. Engine: `computations/mwm/engine4.py`.
- **F [Lean probe — B3 scoping]** No conjugation lemma at the zeta layer on this toolchain
  (riemannZeta_conj / completedRiemannZeta(₀)_conj / Gammaℝ_conj all absent). Ingredients
  PRESENT and verified: Complex.Gamma_conj, Complex.cpow_conj/conj_cpow (arg ≠ π side
  condition), tsum_star, Complex.exp_conj. Route for xi_conj: Dirichlet series conj on
  Re > 2 + identity theorem; missing piece = analyticity of s ↦ conj(xi(conj s))
  (reflection lemma) — mathlib candidates under Analysis/Calculus/Deriv/Star.lean, to be
  checked before writing the card.
- **F [VERIFIED READING — C4: check #9 + Speiser/LM resolved]** Full note
  `checks/c4-density-speiser-note.md` (delegated; I spot-checked the Ivić quotes verbatim
  against the ar5iv full text). **#9 RESOLVED:** the Euler product enters density proofs at
  exactly ONE load-bearing step — the mollifier's Möbius coefficients (= coefficients of
  1/ζ = ∏(1−p^{−s})); mean-value theorems and the approximate FE are orthogonality/FE-only
  (Tao 2024 zero-density notes, fetched). Ivić (math/0311162, fetched verbatim) names the
  missing Euler product as the cause of the D–H off-line population — our 06-reduction §4
  division of labor now has a literature anchor. **CORRECTION to prior framing:** the ≫T
  off-line count in any fixed strip ½<σ₁<σ₂<1 is an UNCONDITIONAL theorem (Voronin;
  Lee–Nakamura–Pańkowski for combinations) — Bombieri–Hejhal's actual result is the
  OPPOSITE direction (conditional 100%-on-line under GRH + spacing, assumptions A1/A2/A3/A5).
  For linear combinations the population needs NO seed; ζ is a "combination of one" where
  the theorem gives nothing — (P_k) stays genuinely open for ζ. **Speiser VERIFIED:** RH ⟺
  no non-real ζ′-zeros in OPEN 0<Re s<½ (two independent fetched sources). **LM VERIFIED
  verbatim:** N₁⁻(T) = N⁻(T) + O(log T) — but note the pairing is blunt below log T
  resolution: one seed zero is invisible to it; the companion-cocycle idea must work at
  box level, not global-count level. Bonus (a.p. ⟺ RH): still UNRESOLVED.
- **F [PROVED, Lean — B3]** Real-structure equivariance banked:
  `formal/GaloisForLFunctions/RHTower/Reflection.lean` (in the umbrella, MainTheorems
  green, lint green after index regen). Five theorems, all axiom-clean
  [propext, Classical.choice, Quot.sound]: `xi_conj` (ξ(s̄) = conj ξ(s), Schwarz reflection
  via Dirichlet series on Re>1 + identity theorem — mathlib had NO zeta-layer conj lemmas;
  built from Gamma_conj/cpow_conj/tsum_star), generic `analyticOrderAt_conj_conj` and
  `analyticOrderAt_comp_one_sub` (order equivariance under reflection and s ↦ 1−s,
  reusable), and the two pairings `xi_orderAt_conj`, `xi_orderAt_one_sub`. Consequence:
  the level-k cocycle is dihedral-equivariant; level-1 obstruction lives on classes
  separating ρ from ρ̄ — the symmetry-slack input of 07 §3 is now machine-checked.
  Lesson repeated the hard way: `| tail` masked the lint exit AGAIN (stale generated
  index) — pipefail on every gate, no exceptions.
- **F [DERIVATION + re-cut doc — B-arc opened]** `08-population-and-local-returns.md`:
  (i) sub-Bagchi constraint [DERIVATION] — in the seed-world strong recurrence already
  fails (Bagchi + density), so any propagation mechanism is necessarily weaker than
  full-data recurrence; R6's negative is the family-side echo. (ii) (P_k) population
  forcing + DROVES DICHOTOMY [CONJECTURE]: FE + Dirichlet-series ⟹ off-line zeros linear
  or absent; the P(s)·ζ(s) surgery counterexample is excluded by the class axiom itself
  (polynomial×Dirichlet-series is not a Dirichlet series — Dirichlet-series rigidity as
  the analogue of bounded-critical-orbit). B1 reframed: hunt FE + o(T)-density + one
  off-line zero; either exit terminalizes. (iii) (H-loc) [OPEN CORE candidate]: the
  transfer lemma is shape-free — small-circle returns are a FINITE-dimensional jet
  value-recurrence event (sub-Bagchi, evades the R6 negative); rates subtlety recorded
  (Bohr–Courant denseness has no rates — can neither manufacture zeros nor prove
  (H-loc); fixed-margin circle is the right register). R6-loc (pre-registered) decides
  the mechanism ranking. P1 retired (mailbox unused, single-agent context).

## 2026-07-03 (wave 2b + rigidity bricks)

- **F [PROVED HERE (paper) — quantified Reduction]** 06-reduction §6: master counting lemma
  (H-separated defects ≤ N(σ₀, T+H)) ⟹ the open core weakens from positive upper density to
  **(R_k^θ): T^{θ(σ₀)}·polylog defect recurrence i.o.**, θ = 3(1−σ₀)/(2−σ₀) < 1 — the burden
  is GRADED in σ₀ (θ(3/4) = 3/5; θ → 0 as σ₀ → 1). Downstream: droves dichotomy relaxes to
  power-droves; D–H overshoots every threshold by a full power (linear).
- **F [PROVED, Lean — surgery no-go]** `RHTower.no_polynomial_surgery` banked
  (`RHTower/DirichletRigidity.lean`, axiom-clean [propext, Classical.choice, Quot.sound],
  umbrella + MainTheorems + lint green): no somewhere-convergent L-series agrees on a right
  half-line with P(s)·(another L-series), deg P ≥ 1. The droves dichotomy's first
  unconditional fragment: the Dirichlet-series class admits NO finite divisor surgery — one
  cannot insert a lone off-line zero quadruple into ζ within the class. Engine: mathlib's
  `LSeries.tendsto_cpow_mul_atTop` + three-case norm asymptotics (new reusable helpers:
  eventual poly bound, poly×rpow-decay→0, cpow-prefactor norm).
- **F [VERIFIED READING — C5, spot-checked verbatim]** Beurling calibration
  (`checks/c5-beurling-density-note.md`): Révész–Pintz (2407.12746): "contrary to zeta
  functions with a functional equation, there is no asymptotic formula for the number of
  zeroes of a Beurling zeta function"; sparse-but-nonempty IS realized FE-free
  (Broucke–Debruyne–Vindas: RH-true systems; finitely-many-zero systems exist, in regions
  Re s > θ). ⟹ the FE is the load-bearing axiom of the droves dichotomy — exactly the
  forbidden regime exists once FE is dropped. GOLD lead: Hilberdink–Lapidus (math/0410270)
  "generalised functional equation" for Beurling zetas = candidate FE-carrying testbed class
  for the dichotomy (exact conditions unresolved/paywalled → B1' first move).
- **F [MEASURED — R3c: anti-correlated mobility spectra]** Fine k-scan: plateau coeff 3–4
  replicates at σ₀ = 0.5025; NEW two-population asymmetry (k<κ and k>κ excite disjoint
  defect families; only the banked zero t≈84.5 pinned both sides); and the pre-registered
  cross-question ANSWERED: FE-pinning and Euler-resistance orders are nearly OPPOSITE (the
  most FE-pinned zero is among the least Euler-resistant) — the two constraints carry
  distinct mobility spectra. Data: R3b-R5-RESULTS.md.
- **F [MEASURED — R5c: moat scaling]** Moat persists at T = 200/500/1000 but shrinks
  (0.025 → 0.02 → 0.01), FASTER than 1/log T at T=1000; inf_T width > 0 open, trending 0.
  New most-resistant zero t ≈ 686. (T=1000 row partial 13/17 — job killed as oversized.)
- **X [tooling — job sizing]** Wave-2b chained an oversized late stage (t ≤ 1000 cpath ≈
  hours): violated the minutes-per-batch rule; killed at user request, partials salvaged.
  Rule appended to runpod memory: winding cost scales with t; ≤ ~10 min/job; never chain a
  10× stage behind small ones; per-stage DONE flags. Also regressed on cwd drift (gate ran
  outside formal/ after terminal restart) — explicit cd in every gate command.
- **F [MEASURED — R6-loc/b/c: the local transfer channel is REAL; certified transfer
  instance]** τ-scan at the banked zero: no strict sub-margin return in τ ≤ 200 BUT kill
  clause not triggered (min ratio 1.70 vs threshold 3) and the local channel is ≈ 14×
  deeper than R6's global one; near-returns land EXACTLY on the other population zeros
  (τ = 91.0 → t≈176.7 etc.) — the off-line zeros' local jets are approximate copies
  ("species similarity"). Radius scan (pre-registered, both clauses CONFIRMED): ratio
  d/m falls monotonically in r (4.11 → 0.64); at r = 0.12, 0.15 the return is STRICTLY
  SUB-MARGIN (hardened 192 pts/dps 20: 0.769, 0.639 at τ = 91.005) ⟹ via the 07 §3
  transfer lemma, **the zero at t ≈ 176.70 is the certified local Rouché-transfer image
  of the banked zero at t ≈ 85.699 — first non-counterfactual instance of the M1
  transfer mechanism.** R6's negative was a contour-size artifact: transfer works locally
  where it fails globally. Mechanism ranking updated in 08 §4; opened R7 (transfer graph
  = the population's recurrence skeleton). Data: `computations/R6LOC-RESULTS.md`.

## 2026-07-03 (wave 3 — theory-first tick)

- **F [THEOREM modulo imports — 09 §1, the family (H-loc) proven]**
  `09-joint-universality-and-the-principal-wall.md`: for the D–H combination, at any seed
  disc where BOTH component L-functions are zero-free ((Z), machine-checkable per disc),
  Voronin joint universality of the two distinct non-principal characters gives
  positive-lower-density sup-returns of the pair ⟹ every ε < margin return transfers the
  seed (07 §3) ⟹ (H-loc) HOLDS in the family. The measured recurrence is now explained,
  the R6 big-box negative reinterpreted as sample-scale, and R7 upgraded to a
  falsification test of the imports. Imports marked [CHECK]: exact joint-universality
  statement (positive-lower-density form).
- **F [structural — the principal wall]** 09 §2: transposing to ζ via
  ζ = q^{−s}Σ ζ(s,a/q) fails at exactly one point — the change of basis puts ζ itself in
  the PRINCIPAL-character direction, where universality demands a nonvanishing target,
  and the seed vanishes there. Every modulus erects the same wall; consistency with
  Bagchi re-derived (else RH would follow). Open core renamed in representation terms:
  **(H-loc for ζ) ⟺ principal-direction self-approximation at a vanishing target.**
  Opened: the universality-blind cone of jet functionals; primitivity grading of the
  family (non-primitive ⟹ provable (H-loc); primitive ⟹ walled) — testable.
- **F [PROVED, Lean — ζ surgery corollary]** `RHTower.no_polynomial_surgery_zeta` banked
  (DirichletRigidity.lean, axiom-clean, umbrella+Main+lint green): no somewhere-convergent
  L-series agrees on a right half-line with P(s)·ζ(s), deg P ≥ 1 — the surgery no-go
  instantiated at ζ via `LSeries_one_eq_riemannZeta`. Also probed: mathlib has NO Rouché
  theorem (A3's transfer-lemma formalization must build the argument principle route).
- **F [MEASURED — R7 chunk 0 + the β-proximity law]** Four off-line zeros localized
  (winding-certified ±0.01): β = 0.8065, 0.6555, 0.5693, 0.7202 at t = 85.695, 114.164,
  166.477, 176.695. Cross-referencing R6-loc return depths vs |Δβ| exposed a quantitative
  law: **d_min ≈ (1.1–1.3)·|Δβ|**, hence sub-margin transfer ⟺ r ≳ |Δβ| — vertical
  shifts cannot move β, so the transfer graph is a β-proximity graph; measured ratios
  match Δβ/r to ~10% (0.72 pred / 0.769 meas; 0.575 / 0.639). Coheres with the known
  density of D–H zero real parts (C0 #8): tiny-ε universality returns must land on
  β-near zeros, which exist by density. Chunk 1 (all six pairs, law-testing,
  pre-registered on board) launched. Caught + killed a mis-parametrized first attempt
  (guessed centers) before it produced garbage — localization first, always.
- **F [VERIFIED READING — C6: 09's imports closed]** `checks/c6-joint-universality-note.md`
  (delegated; Thm 7 + Thm 10 spot-checked verbatim against ar5iv 1407.4216). Import 1
  VERIFIED: joint universality for pairwise non-equivalent Dirichlet characters, positive
  LOWER density, targets nonvanishing/analytic — 09 §1's usage covered in FULL (r = 2,
  χ ≠ χ̄ mod 5, self-targets nonvanishing by (Z)). The family (H-loc) theorem now stands
  with verified imports + one machine-checkable hypothesis (Z). Import 2 VERIFIED (single
  Hurwitz strong universality, Bagchi/Gonek, α rational ≠ 1, 1/2); joint-STRONG needs
  ℚ-independence of {log(n+α_j)} (Matsumoto Thm 15) which FAILS for common-denominator
  families — the tool needed to push a seed through the ζ-decomposition is provably
  unavailable in exactly our case (nuance kept honest: unavailability verified;
  impossibility not printed; Bagchi-consistency carries the wall). 09 §1/§2 updated in
  place.
- **F/X [MEASURED — R7 chunks 0–1: β-law partially refuted → jet-proximity law]** Four
  zeros localized (β = 0.8065, 0.6555, 0.5693, 0.7202; winding-certified). Law test
  (pre-registered): ρ₁-anchored pairs OBEY d_min ≈ 1.1|Δβ| (ratios within ~10%;
  **new certified transfer edge ρ₁ → ρ₃ at r = 0.285, Δβ = 0.237**, second after
  ρ₁ → ρ₄); every ρ₂-pair FAILS with an r-independent ratio floor tracking the
  derivative mismatch (|f′(ρ₂)| ≈ 0.75 vs 1.16). Refined law: ratio ≈ Δβ/r + δ′(jet
  mismatch) — **transfer condition = JET proximity; the graph stratifies into jet
  classes; within a class it is a β-proximity graph.** ρ₂ is transfer-isolated in
  t ≤ 200 (its class partners live at other heights — consistent with 09 §1). Chunk 2
  (rebased 4→3, 4→2) in flight. Data: `computations/R7-RESULTS.md`.
- **F [MEASURED — R7 complete on t ≤ 200]** Chunk 2: **third certified edge ρ₄ → ρ₃**
  (r = 0.181, τ = −10.22, law-conforming); 4→2 fails with the same floor as 2→4 (ρ₂'s
  isolation intrinsic). Final fragment: jet classes {ρ₁, ρ₃, ρ₄} (complete) and {ρ₂}
  (isolated). The transfer graph is a jet-class-stratified β-proximity graph — the
  family's recurrence skeleton is now measured, certified, and law-governed. Caveat:
  margin/r misestimates |f′| at small radii (measure f′ directly in the census).
  `computations/R7-RESULTS.md` final.

## 2026-07-03 — wave-4: the blind cone answered + the phase law (seed 382100489098707208)

- **R8 chunk 0 [MEASURED]** (`computations/r8c0.out`, `R8-RESULTS.md`): direct f′ at the four
  R7 centers. |f′|-magnitude REFUTED as jet-class carrier (ρ₃ lowest |f′| yet transfers; ρ₂
  middle |f′| yet isolated). Carrier = PHASE: arg f′ separates the transfer graph perfectly
  ({ρ₁,ρ₃,ρ₄} at −0.32..−0.19, ρ₂ at +0.32; certified edges |Δarg| ≤ 0.13, failures ≥ 0.51).
  Law refined and first-order DERIVED: ratio ≈ Δβ/r + |Δ arg f′| (measured c ≈ 1.0–1.4,
  model c = 1). Pre-registration scorecard: clause (i) marginal fail (24–26% < 30%),
  proxy-was-bad clause confirmed, falsifier fired at the |f′| reading.
- **10-blind-cone.md — 09 §3.1 ANSWERED (B2 target)**: blind cone = union of canonical
  coordinate lines. Theorem A (support ≥ 2 ⟹ (H-loc), r-component 09 §1); Theorem B (single
  lines: (Z′) unsatisfiable at seeds + (H-loc) ⟹ RH(χ) via quantified Reduction — blindness
  is intrinsic and RH-grade); Theorem C (ζ collects to the trivial line for EVERY q —
  yes-branch: wall representation-independent, primitivity grading now a theorem in the
  Dirichlet world, multi-modulus covering impossible). §5: the wall's carrier in Hurwitz
  coordinates = unique factorization — ζ(s,1/3)+ζ(s,2/3) = (3^s−1)ζ collapses to the
  principal line; the missing tool (joint-strong at self-targets) MUST fail, and does:
  explicit witness log(2/3)+log(8/3)=2log(4/3) (2·8=4²); transcendental shifts free. §6
  chiasmus: multiplicativity powers (D) [mollifier] and blocks (R_k) [log-relations]. §7
  opened: phase-weighted universality (R8 data), Beurling trichotomy (B1×B2 merged), minimal
  relation-blindness.
- **Lean banked** (`RHTower/LogIndependence.lean`, umbrella updated, build 9008 jobs green,
  lint gate green): `log_third_shifts_dependent`, `log_shifts_independent`,
  `log_prime_shifts_independent` (+ private `padicValRat_prod`, `padicValRat_zpow`) — all
  [propext, Classical.choice, Quot.sound]. The wall's two sides machine-checked; the prime-
  support freedom lemma is the Beurling-design clause of 10 §7.2.
- 09 §3.1 marked ANSWERED in place. Board: wave-4 pre-registration block. Tasks: #109
  (R8, chunk A census running), #110 done, #111 done; #96/#97 redirected at the trichotomy.
- X (fixed): pod launch used `python3` (no mpmath) instead of `python3.13` — job died at
  import; relaunched. Check the interpreter when launching pod jobs.

## 2026-07-03 — q62/Böttcher lane cross-read (user-requested; files read, nothing edited there)

Read: pipeline/1-in-progress/q62-p6-noncontinuability-assembly.md (today's +40 lines),
Bottcher/STATUS.md (tail), Bottcher/DyadicMonodromy.lean. Findings for THIS lane:

1. **A3 un-deferred by the deck pattern.** A3 (cocycle Lean) was deferred because mathlib
   lacks Rouché/argument principle. The q62 lane formalizes ℤ/2^k monodromy WITHOUT contour
   integrals — deck/torsor classes (DyadicMonodromy.lean: exact Prüfer multipliers with
   dyadicRoot_succ_sq coherence — literally our RHTower ℤ₂-tower structure realized as deck
   data; their "technical correction" note: the loop/period route is delicate, the deck
   route handles monodromy abstractly). RE-CUT A3: define w_k as the deck class of the
   2^k-th-root torsor of ξ on an annulus around the box (RHTower root-existence + deck
   pattern), NOT as ∮ξ′/ξ. No argument principle needed.
2. **The KW mechanism (BottcherArcExtension.lean, today, axiom-clean) = modulus→argument
   upgrading.** |β| = exp(Green) + harmonic conjugate (mathlib HAS
   HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq) ⟹ β itself continues, pinned up to ONE
   unimodular constant κ on a connected lune. Structural echo for the phase law: modulus
   data determines everything except one phase constant per patch; our measured phase
   floor is the distribution of exactly that constant. Consistent with (not beyond) our
   Cauchy-estimate derivation — noted, no overclaim.
3. **Index-formula engine as population-forcing shape.** Their Zdunik-free route:
   holomorphic fixed-point index ∑ 1/(1−λ) = exact pinned value ⟹ one anomalous multiplier
   FORCES compensation from the rest — a worked, formalized instance of "lone term cannot
   balance an exact identity ⟹ companions exist." That is precisely the logic shape
   #112's rung program needs (not positivity — exactness/quantization). Concrete MWM
   transposition to try: Landau's formula ∑_{0<γ≤T} x^ρ = −(T/2π)Λ(x) + O(log T) — budget
   analysis of how a lone x^{β₀}-sized term at level 1−δ coexists with the pinned main
   term as x varies. Added to #112.
4. **Shared mathlib-gap ledger.** Their hu-interface names the gap: Poisson/Dirichlet
   solution operator + harmonic max principle + harmonic Schwarz reflection (they built
   the KW mechanism around it). Ours: Rouché/argument principle. Adjacent developments —
   whoever builds Poisson first serves both (harmonic measure ↔ winding).

## 2026-07-03 — proof tick (user directive: prove/disprove, not compute)

- **11-recurrence-degrees.md — the droves dichotomy PROVED at one level and REFUTED at
  ζ's level, full proofs in-doc:**
  - Theorem A [PROVED HERE]: holomorphic + strip-S² a.p. ⟹ Bohr on interior substrips
    (mean-value upgrading, elementary) ⟹ one zero forces relatively dense zeros — linear
    droves at Stepanov regularity.
  - Theorem B [PROVED HERE]: explicit counterexample f = g + h (g = 2 + 2^{−s} + ½·2^s,
    FE-exact, |g| ≥ ½; h = FE-symmetrized gaussian-localized bump): holomorphic on the
    strip, EXACT FE f(s)=f(1−s), Weyl/B²-a.p. on every line, and a FINITE nonempty
    off-line zero set. Zero-existence via a max-modulus trick (g/f < 1 on ∂D but = 1 at
    the bump's zero) — NO Rouché needed, so it is Lean-formalizable with current mathlib.
  - Corollary: ζ is B²-a.p. but provably NOT strip-S²-a.p. in (1/2,1) (S²⟹Bohr⟹bounded
    vs Ω-results) — ζ's regularity is exactly the degree where the dichotomy fails.
  - Verdicts: the dichotomy's burden = CLASS RIGIDITY, not recurrence strength; dual-pillar
    necessity now complete (FE necessary by Révész–Pintz/C5; series-structure necessary by
    Theorem B). Growth bounds alone also insufficient (same example — h bounded).
    Projection-blindness realized in the a.p. category (f's B² spectrum = g's).
  - My own 08 §7.1 boundary-leakage conjecture REFUTED as a bare mechanism (marked in
    place); rung program (#112) redirected at approximate-FE/Euler-grade pointwise input.
- R8 CLOSED (chunk D): 4th certified edge ρ₄→ρ₇ (τ=154.355, largest Δt yet); must-pass
  passed; final law ratio ≈ 1.25·(|Δf′|/|f′| + amp·Δβ/r), hard jet gate, line-proximity
  cutoff. No further census computation — theory took over.
- Earlier same day: 10-blind-cone.md (09 §3.1 answered), LogIndependence.lean banked,
  08 §7 rung + C7 verdicts (budget T^{cδ^{3/2}}, c<1/2; DH guard vacant in t-aspect),
  q62 cross-read (deck-class re-cut of A3 → #113; index-formula shape → #112).

## 2026-07-03 — C8 verdict + 00-approach wave-4 refresh + PerturbationZero.lean
- C8 (checks/c8-turan-taspect-note.md, spot-checked): Turán second main theorem fetched
  verbatim (+ Kadiri–Ng–Wong Thm 2.2, Révész Lemma 3 working variants). The t-aspect
  "one ζ-zero forces other zeros" object is ABSENT — but BOTH flanks are proved by power
  sums: q-aspect Deuring–Heilbronn (KNW Thm 2.6, exceptional zero repels, C≈14.14) and
  t-aspect zero→ψ-oscillation (Turán/Pintz/Révész, |ψ(x)−x| ≥ (1−ε)x^{β₀}/|ρ₀|). The
  MISSING HYBRID = the rung mechanism's precise target (#112).
- Lean banked: RHTower/PerturbationZero.lean — exists_zero_of_sphere_domination (the
  Rouché-free zero-planting engine of 11 Thm B), axiom-clean, build 9012 jobs, lint green.
- 00-approach.md refreshed for wave-4 (user request): M1 annotated (single-test form
  closed, Turán hybrid open), M2 marked refuted-as-soft (11 Thm B), §10 item 8 updated to
  the final jet law, NEW §11 state-of-the-map (closed routes with proofs; open routes:
  Turán hybrid, Goldilocks class, deck cocycle, jet-guide; the wall triangulated 3 ways).

## 2026-07-03 — the race, run (12 §3)
- Full-line sup-recurrence of −ζ′/ζ(1+η+i·): DEAD — loglog L_full ≈ (1/δ)log(4/εδ) vs
  ceiling c₁/δ with c₁ = log(1/ε₀)/4 ≈ 0.17: inner-exponent deficit ≈ 43–53×. Death
  certificate = the first measured constant on the exact-structure side of the wall.
- WINDOWED recurrence: time-bandwidth collapse N_eff ≈ (1/2πδ)log(4/εδ) ⟹
  log L_win ≈ (1/2πδ)log²(1/εδ) ⟹ T₁ ≪ T_forge for δ ≲ 0.02 — ALIVE exactly in the rung
  regime. Would-be region (loglog γ)²/(2πlog γ): between Littlewood and VK (consistent,
  region reduce-to-known); the new object = FORCED CLUSTERING at recurrence sites (the
  (Rung_δ) step, which no zero-free-region method provides). Numerics banked in 12 §3.
- Promotion checklist opened: (a) Gram/prolate time-bandwidth lemma for Dirichlet
  frequencies on unit windows [the load-bearing new lemma]; (b) effective windowed
  Kronecker, positive density; (c) spike-detection converse constants; (d) = 11 Thm A ✓.
- C9 queued: Littlewood zero-free-region method (Diophantine flavor) — adjacency audit.

## 2026-07-03 — 12 §4: block structure + C9 audit
- Lemma-(a) attack: Fejér window ⟹ band-diagonal ⟹ block split; blocks are INDEPENDENT
  under Haar (disjoint primes); concentration frees all blocks j ≳ log(1/ρ):
  μ(A_ε) ≥ exp(−C log²(1/εδ)) generic; worst-case γ₀ degrades to exp(−poly(1/δ)) — still
  under the forging ceiling for small δ (race-close at δ=0.01: 1.6e7 vs 2.4e7). Positive
  visit density is FREE (Weyl equidistribution + open set) — no effective Kronecker needed.
- Chain now claims (heuristic grade) a c₁/loglog γ region — beyond VK ⟹ QUARANTINED as a
  conjecture factory; links proven/refuted one at a time (ladder L1–L4 in 12 §4.5).
- C9 (checks/c9-littlewood-method-note.md): Littlewood = dVP 3-4-1 + upper bounds, NO
  Diophantine step (explicit in two sources) ⟹ our mechanism is a different method family;
  literature recurrence tools only ever give large values/Ω-results; the
  recurrence→zero-clustering bridge is ABSENT from the corpus — novel as a method.
- Next: L1 (block small-ball/concentration for random Euler block sums) — self-contained
  probability, first rigorous link.

## 2026-07-03 — 12 §5 + 13: L1 attacked, half proved
- 12 §5: TWO structural discoveries. (1) ROTATION INVARIANCE: u_p·x_p uniform ⟹ block law
  independent of γ₀ entirely — the reference height enters only through ball centers;
  half of L1's difficulty evaporates, and the worst-case-γ₀ equidistribution machinery
  (incl. the 5/3-power loss) is obsolete. (2) SELF-REPAIR DICHOTOMY: large block means
  |m_j| ≫ s_j would break small-ball — but block means are block sums of −ζ′/ζ(1+η+iγ₀),
  and by Perron large block sums CERTIFY zeros near γ₀: the adversarial case is the
  clustering conclusion by another route. Mechanism forces companions EITHER WAY.
- 13-block-lemmas.md: L1a (concentration) PROVED (Hoeffding, complete; deep blocks free).
  L1b reduced to ONE named estimate (D): local-CLT lower bound for Pearson random-flight
  densities f_Y(y) ≥ c₀e^{−C₀|y|²/s²}/s² — pure Bessel analysis, no arithmetic; sparse
  early blocks by compactness. All extremal/mean cases route to L5.
- L5 promoted to second pillar: Perron converse (zero-free disc at 1+iγ₀ ⟹ block-mean
  decay; spike + pole shares separated). Next attack: L5, then (D).

## 2026-07-03 — 13 §4: L5 attack ⟹ mean-size correction, chain absorbs (3rd audit)
- L5's moderate-means branch UNOBTAINABLE: needed square-root cancellation ⟺ zero-free
  disc radius > 1 (crosses the line — impossible). Honest accounting: block means are
  FORCED to |m_j| ≈ s_j·logγ₀/√(2j) by the on-line zeros' own residues; earliest
  ~loglogγ₀ blocks near-extremal.
- Chain ABSORBS it: μ ≥ exp(−Clog²γ₀·polyloglog), T_contra = exp(Clog²γ₀) ≤ T_forge ⟺
  δ ≤ c₁/((2+o(1))loglogγ₀) — region degrades only in the constant: (c₁/2)/loglog γ.
  Third audit survived (ambient burial, forging ceiling, mean size).
- Pillars revised, all with NAMED classical toolsets: (D′) LDP lower bounds for Pearson
  flights (Cramér/Gärtner–Ellis — replaces (D)); L5′ mean-size as a THEOREM (contour,
  shares separated); L2 Fejér constants; L3 spike converse. Next: (D′).

## 2026-07-03 — (D′) PROVED (13 §5): the probability half of the mechanism is done
- Tilted Cramér lower bound for Pearson blocks: von Mises tilt, likelihood ratio ≥
  exp(−Λ*−λt) on the ball, Q-Chebyshev for t ≥ 2s, 2d Berry–Esseen for mid blocks,
  one-time compactness for the 3 sparse laws (γ₀-independent by rotation invariance).
  Rate: Λ*(r) = (1+o(1))r²/s² moderate; von Mises rate near-extremal; total measure
  exponent Σ Λ*_j ≈ (1/2)log²γ₀·loglog(1/ρ) — 13 §4.2's μ is now theorem-backed.
- Status: L1a ✓, (D′) ✓ — everything still open in the chain is COMPLEX ANALYSIS:
  L5′ (mean-size contour theorem), L2 (Fejér constants), L3 (spike converse).

## 2026-07-03 — L5′ FOUND THE BUG: 12-chain terminated with a priced death certificate
- Exact Perron mean formula: the SPIKE'S OWN SHARE of block means = w_j·e^{−2jδ} for all
  2j ≲ 1/δ — missed by the §4.1 audit. Spike replication = large deviation of ~e^{1/δ}
  coherent primes: μ_spike ≈ exp(−c·e^{1/δ}) ≫-dead vs ceiling exp(e^{c₁/δ}), c₁ < 1.
  The bug sat exactly where three survived audits predicted a fourth would be.
- DEATH CERTIFICATE: the Euler/Kronecker flow recurs ambient fields at exp(−log²γ₀) but
  prices width-δ off-line spikes at the random-model rate exp(−e^{1/δ}). Recurrence-based
  forcing of off-line zeros: closed as designed; re-cuts (signature-only, lower fidelity)
  die with it.
- FOUR ASSETS: (1) the wall's 4th derivation — primitivity = large-deviation RATE
  separation (ζ: spikes are e^{−e^{1/δ}}-rare; D–H: bulk events — explains the measured
  family recurrence); (2) threshold-theorem candidate: spike-event density
  exp(−e^{(1+o(1))/δ}) for random Euler products [provable standalone]; (3) L1a + (D′)
  reusable — and the Beurling reading: DESIGNED coherence makes spike events cheap ⟹
  recurrence-forcing works in engineered systems (feeds #96/#97 trichotomy); (4) the
  Perron self-repair dichotomy survives as a free tool.
- Live weight moves to: #113 deck-class monodromy, Goldilocks (11 §5.3), Beurling dial.
  (Rung_δ) mechanism must not factor through the Bohr flow's measure.

## 2026-07-03 — #113 core BANKED: DeckCocycle.lean (w_k without the argument principle)
- RHTower/DeckCocycle.lean, all axiom-clean, RHTower target green (8562 jobs):
  pow_root_ratio (constant-ratio form of pow_root_unique, anchor-based, derivative-free);
  deckClass (g₁ pP/g₂ pP)/(g₁ pM/g₂ pM); deckClass_pow_eq_one (∈ μ_n);
  deckClass_root_indep (independent of both local root choices);
  deckClass_sq (dyadic tower coherence — the q62 dyadicRoot pattern at germ level);
  deckClass_eq_one_iff_exists_root (trivial ⟺ local roots glue to a global root on
  U₁ ∪ U₂ — the RH_{2^k} ladder link, two-chart annulus glue with if-piecewise analyticity).
- The lane's central invariant w_k now EXISTS as a formal object on exact monodromy data —
  the one construction the four-times-derived wall does not touch (it never factors
  through the Bohr flow's measure).
- Remaining A3 chunk (next): the monomial dictionary w_k((z−a)^m·h) = dyadicRoot(k)^m via
  exists_peel + slit-chart cpow branches — Rouché-free zero-counting meaning for w_k.
- Lean traps this file: ₊/₋ are NOT identifier characters (renamed P/M); if-glue needs
  `classical`; analyticAt_const.mul needs the constant named; self-referential rw at the
  anchor point (rewrite only the far-point equalities).
- Full-tree gate deferred: parallel agent's HarmonicMaxPrinciple.lean mid-edit (their
  Poisson development — the shared-gap item — actively growing; do not touch).

## 2026-07-03 — #113 chunk 2 BANKED: the monomial dictionary (DeckMonomial.lean)
- deckClass_monomial: w_n((z−a)^m) = exp(2πi·m/n), computed from explicit clog branches at
  a ± i — pure exp/log arithmetic, no argument principle, axiom-clean, RHTower green 8563.
- Plus deckClass_mul_global (global nonvanishing factors cancel — the peeling interface),
  branch root-properties and analyticity on the slit charts.
- The lane's coarse invariant now has PROVEN zero-counting meaning on the monomial model:
  the deck class realizes the enclosed multiplicity mod n as the q62 dyadic multiplier.
- Chunk 3 (assembly, next): slit-chart preconnectedness (star-convex about a+t, hand
  proof) + root_indep + exists_peel ⟹ ANY roots of a peeled f = (z−a)^m·h carry class
  exp(2πim/2^k) — then w_k(box with one zero) is a theorem, and the RH_{2^k} ladder's
  local obstruction is fully formal.

## 2026-07-03 — A3 COMPLETE: deckClass_single_zero (DeckAssembly.lean)
- CAPSTONE PROVED: any local n-th roots of a peeled single-zero function carry deck class
  exp(2πi·m/n) at a ± (R/2)i. With DeckCocycle's triviality⟺gluing and coherence
  w_{k+1}² = w_k, the lane's obstruction cocycle is now a FULLY FORMAL object with proven
  zero-counting meaning — no argument principle, no Rouché, anywhere in the chain.
- Route: slit-chart star-convexity (linear_combination a*hts' for the affine identity),
  translated half-plane overlaps, chart_inter_eq, generalized dictionary at a ± εi,
  Arc A root existence (vacuous zero set) + mul_global + root_indep.
- The RH_{2^k} ladder's local obstruction is machine-checked end-to-end: w_k(box with one
  zero of order m) = dyadic multiplier^m; w_k trivial ⟺ 2^k-th root extends. Exact
  monodromy data — the invariant the four-times-derived wall does not touch.
- Lean traps: Complex.norm_real lands in ‖·‖_ℝ (insert Real.norm_eq_abs before
  abs_of_pos); simp [sub_im] closes flip-identities (no trailing ring); affine star-convex
  identities need t+s=1 via linear_combination.

## 2026-07-04 — multi-zero ADDITIVITY banked (DeckMultiZero.lean)
- deckClass_multi_zero PROVED, axiom-clean, RHTower green 8565: any local n-roots of
  ∏(z−ρᵢ)^{mᵢ}·h on the slit annulus charts have class exp(2πi·Σmᵢ/n) — the cocycle is
  additive over enclosed zeros. The design discovery that kept it cheap: off-center
  corrections u(z) = 1 − (ρ−a)/(z−a) map the WHOLE annulus into B(1,1) ⊂ slitPlane ⟹
  their roots are global and invisible to the class; every zero contributes exactly its
  monomial class at the common anchor.
- New infrastructure: deckClass_mul/prod (unconditional field identities);
  slit-annulus charts with polar-image preconnectedness (convex rectangle → continuous
  image; arg/norm_mul_exp_arg_mul_I bookkeeping); corrRoot with slitPlane containment.
- w_k is now: μ_n-valued, choice-independent, coherent in k, trivial ⟺ root-glues,
  counts single zeros, ADDS over multiple zeros. Remaining wiring: the ξ layer (per-box
  invariant of the actual completed zeta — peel ξ's zeros via analyticOrderAt +
  exists_peel, feed deckClass_multi_zero). Next tick.

## 2026-07-04 — ξ-LAYER WIRED (XiDeck.lean): the lane's reformulation is formal end to end
- Five theorems, axiom-clean, RHTower green 8566: xi_orderAt_ne_top; xi_peel_ball;
  xi_deckClass (any local n-roots of ξ at any zero count multiplicity mod n, all small
  radii); exp criterion (trivial ⟺ n ∣ m); xi_deckClass_eq_one_iff_ladder_dvd (at
  n = 2^k the class triviality IS RHLadder k's divisibility clause).
- THE CHAIN, machine-checked with no argument principle at any step:
  RiemannHypothesis ⟺ ∀k RHLadder k ⟺ (∀ zeros ρ₀ of ξ right of the line, the deck
  class of local 2^k-th roots is trivial, ∀k). The MWM cocycle w_k = the ladder's local
  obstruction = a computable-in-principle formal invariant of completedRiemannZeta.
- 00-approach §3.2–3.4's [REDUCTION — to be formalized] markers are now discharged in
  full: tower (Arc A), ladder (Arc A), cocycle + zero-counting meaning (A3 arc, today).

## 2026-07-03 — TWO-FRONT PLAN + CONSERVATION LAW FORMALIZED (M2)

Task board rewritten around the two live fronts (tasks #114–#120): **Arc B re-armed**
(parity stratum: FEDescent central-parity brick #114, D–H filter + exact-identity audit
#115, correspondence-monodromy conjecture #116, re-cut Beurling foil #96 and w_1-lemma
#97) and **M1 final form** (conservation: DeckHomotopy #117, far-field anchor #118,
15-conservation-program.md #119). rng pick chose deckhomotopy-first.

**M2 DONE — `DeckHomotopy.lean` banked, axiom-clean, RHTower green (8567 jobs).** The
deck class is a deformation invariant with NO argument principle: `deckClass_step`
(‖f−g‖ < ‖g‖ on the annulus charts ⟹ the principal root of f/g is a GLOBAL correction —
f/g lands in B(1,1) ⊆ slitPlane — so the class cannot move), `deckClass_perturb`,
`deckClass_chain`, `deckClass_deformation_invariant` (any roots of F N vs any roots of
F 0). This is the formal version of the R3-measured charge dynamics: enclosed
multiplicity mod 2^k is CONSERVED while no zero touches the charts. Note the step lemma
needs no basepoint geometry at all (hR dropped) — the conservation inequality is purely
about domination on the charts.

Next: far-field anchor (#118) gives the endpoint the conservation argument drains to;
then the program doc (#119) states where annihilation consumes Arc B's parity.

## 2026-07-03 — waves banked (M3, B4) + q62 cross-read yields three transpositions

**M3 DONE — FarFieldAnchor.lean** (deckClass_of_nonvanishing = the m=0 instance;
xi_deckClass_far_field: boxes right of Re s = 1 carry zero charge at every rung).
Conservation now has its drain endpoint.

**B4 DONE — ReflectionParity.lean**, and the planned FEDescent construction was
REPLACED by a five-line reflection-cancellation argument (peel, reflect, cancel the
monomial off the puncture, evaluate at the fixed point): analyticOrderAt_even_of_reflection
(generic — applies to every FE-symmetric pencil member), xi_central_order_even,
xi_central_ladder_two, xi_deckClass_central_sq_trivial (w₁ trivial at s = 1/2, from FE
alone). Mechanism named: parity is seen at the FIXED/RAMIFIED locus of a constraint
symmetry; D–H certifies FE alone cannot force it off-line.

**q62 cross-read (their new formal work):** SchwarzReflection.lean (Painlevé/Morera:
continuous + holomorphic-off-a-line ⟹ holomorphic; affine and biholomorphic-preimage
forms; compiles standalone, mathlib-only) + in-flight PoissonHarmonic/HarmonicMaxPrinciple
(Dirichlet stack). Three transpositions carded:
- **#121 u-plane descent**: F(w) = ξ(1/2 + √w) is continuous across the slit by evenness,
  their Painlevé engine makes it ENTIRE — the global descent #114 skipped becomes cheap.
  Capstone: RH ⟺ F ≠ 0 on the slit plane ⟺ ℤ₂-tower of F on the slit plane. The critical
  line becomes the SLIT; the deck charts' local slitPlane geometry goes GLOBAL.
- **#122 seam cocycle**: reflection gluing of the two half-plane towers across the
  critical line; on-line zeros enter as seam jumps exp(2πi·m/2^k) — M4's seam-absorption
  account made formal.
- **#123 [CONJECTURE] modulus-only holography**: deck class = period of the harmonic
  conjugate of (1/n)log|f| — the charge from |ξ| alone on boundary circles; waits on
  their Dirichlet stack landing.

## 2026-07-03 — #121 BANKED: the u-plane descent (first cross-lane consumption)

UPlaneDescent.lean, axiom-clean, RHTower green (8571 jobs). The q62 agent's Painlevé
engine did exactly what the cross-read predicted: xiDescent(w) = ξ(1/2 + √w) is
continuous across the slit because evenness matches the two one-sided branch values
(the lower limit is xi(1/2 − √|w|·i·…) = reflected, bridged by xi_half_sub), and
differentiableOn_of_off_horizontal_line upgrades it to ENTIRE — the global descent
that #114 skipped, at ~250 lines with zero power-series surgery.

Capstone: **RH ⟺ xiDescent ≠ 0 on the slit plane** (rh_iff_xiDescent_ne_zero_slitPlane).
The critical line is now the SLIT; on-line zeros are absorbed into the boundary; the FE
involution is quotiented away; the deck charts' local slitPlane geometry is the GLOBAL
domain. Descent identity xi_eq_xiDescent holds with no branch bookkeeping — evenness
absorbs the square-root sign, so the two roots of (s−1/2)² give the same value.

What this opens: (i) the seam cocycle (#122) now has its natural carrier — the slit
boundary of the u-plane, where the two-sided boundary values of F-roots meet; (ii) the
ladder on the u-plane — the ℤ₂-tower of xiDescent on the star-convex slit plane (needs
root-existence off convexity: star-convex version of exists_root_iff_orders_dvd, or
direct via simply-connectedness); (iii) B6's correspondence hunt gains a straight target:
in the u-plane the FE is already used up, so any residual exact-identity transport acts
on the slit geometry alone.

## 2026-07-03 — #115 BANKED: 14-parity-stratum.md (three filters + audit)

The parity front's discipline document. Three filters a w₁-detector must pass BEFORE
proof attempts: **I (D–H)** — must consume genuine multiplicativity (kills FE-only,
reality, growth, a.p. in every packaging; certified by the banked simple off-line
population); **II (symmetry discount, PROVED from xi_orderAt_conj + xi_orderAt_one_sub)**
— quadruples force symmetric-region charge ≡ 0 mod 4, so symmetric aggregates are blind
at k ≤ 2: detectors must be QUADRANT-LOCAL (first structural justification for the
per-box deck class); **III (regularity wall)** — imported from docs 10–12.

Audit outcomes: FE-covers = base case only (ramified locus is the mechanism); dyadic/
Adams family = ORDER-BALANCED at off-line zeros (elementary telescope; affine transport
can move w₁ but never anchor it — affine identity families exhausted as detectors);
positivity class = real-locus-only mechanism, retargeted to the seam (#122), off-line
use doubly dead (M3/DMV + Filter II). SURVIVORS: (1) conservation+family (M-lane #119 —
quadrant-local ✓ exact ✓ Euler-moat-separated ✓), (2) constructed quadrant-ramified
covers (#116 re-aimed: build a two-sheeted cover of the u-plane branched at a movable
far-field-anchored point; q62's biholomorphic-preimage reflection is the local model).
New [CHECK] candidate C10: literature absence of nonlinear ζ-identities beyond FE∧Adams.

## 2026-07-03 — #120 + #119 BANKED: the two-front map + the conservation program

**00-approach §12** appended: wave-5 state — Turán arc concluded (priced), A3+ξ wired,
u-plane capstone, the two fronts (M conservation / B parity) and their coupling at the
quadrant-local charge, live-route priority list, the wall's four derivations confined to
registers the deck charge does not factor through.

**15-conservation-program.md** written. The pencil pinned from R3/R3b/R5/R5b/R5c
(f_c = c·L(χ) + (1−c)·L(χ̄); FE fiber = transversal minimizer floor > 0; Euler moat =
open basin floor 0; disjoint two-side populations, box 84 the lone exception). The
LEDGER identity (L): charge difference ≡ boundary multiplicity flux mod 2^k — no-flux
case banked (deckClass_deformation_invariant), jump case = cheap Lean target
deckClass_jump (ratio of two deckClass_multi_zero evaluations). Interior events FREE at
k=1 (annihilation changes counts by 2m — the whole mod-2 burden is boundary flux).
Program: rung ⟸ (P-flux) even mod-2 flux per upper-quadrant box; open core itemized:
OC1 band-edge crossing PAIRING ([CONJECTURE] two-coloring by FE-fiber side, per R3c's
disjoint populations; box 84 = designated counterexample candidate for attack-as-false),
OC2 seam accounting (#122), OC3 anchor below σ=1 (tall boxes / certified windows /
u-plane). Honesty clause: (P-flux) is RH-grade by Bagchi-consistency — reshaped burden
(discrete pairing structure), not shrunk. 07's (H_k) transfer = the t-translation
instance of (L).

## 2026-07-03 — #124 BANKED: deckClass_jump — the ledger (L) is theorem-grade

LedgerJump.lean, axiom-clean, RHTower green (8572 jobs), first-compile clean. One
transversal crossing multiplies the box charge by exp(2πi·m'/n) — proved as the ratio
of two deckClass_multi_zero evaluations over ι vs Option ι (new zero at none). Combined
with deckClass_deformation_invariant, identity (L) of 15-conservation-program.md holds
for piecewise-generic paths: between crossings the class is constant; at each crossing
it jumps by the crossing zero's factor. The conservation front's formal spine is
complete: conservation + additivity + jump + far-field anchor + central anchor. The
open mathematics is now exactly OC1 (crossing pairing / two-coloring, box 84 the
designated counterexample candidate) and OC2 (seam, #122).

## 2026-07-03 — #122 BANKED: SeamCocycle.lean — OC2 has its instrument

The seam ledger is formal, on the u-plane carrier as planned: seam classes = gluing
ratios of bank roots (overlapU/overlapD half-disks) against the chart roots (analytic
across the right/left seam segments); crossing an on-seam zero multiplies the class by
exp(2πi·m/n) (seam_jump — VALUE-LEVEL identity, reduces to deckClass_basepoint_indep +
deckClass_single_zero, zero new analysis); instantiated on xiDescent at every u-plane
point, where on-slit points ARE the on-line ξ-zeros (xiDescent_seam_jump). RHTower
green 8573 jobs, axiom-clean, lint passed.

The three ledger accounts of 15-conservation-program.md are now ALL theorem-grade:
interior conservation (DeckHomotopy) + crossing jumps (LedgerJump) + seam jumps
(SeamCocycle), draining to the far-field anchor (FarFieldAnchor). The conservation
front has zero formal debt. The open mathematics of the program is now exactly OC1
(crossing pairing / two-coloring at the band edge) — everything else is bookkeeping
with banked bricks. Next: OC1 formulation + attack-as-false at box 84, or #116
(quadrant-ramified cover construction), or #96 (Beurling foil).

## 2026-07-03 — #123 BANKED: ModulusHolography.lean — the charge from |ξ| alone

The M6 conjecture is a THEOREM, and it needed less than expected: mathlib's new
JensenFormula/ValueDistribution development already contains the zero-free mean value
(AnalyticOnNhd.circleAverage_log_norm_of_ne_zero), so the whole module is single-zero
Jensen (A(r) = m·log r + log‖h(a)‖) + slope elimination of the unknown constant +
deckClass_single_zero. Capstone: deckClass = exp(2πi·slope/n) with slope read from the
circle-averages of log‖f‖ at two radii — the charge is a boundary-MODULUS functional:
no phases, no root choices. Instance on ξ: |ξ| on two circles determines the box charge
(xi_deckClass_eq_circleAverage_slope) — retroactively formalizes the R-series winding
measurement method. RHTower green 8574 jobs, axiom-clean, lint passed.

The holography clause of the charter ("bulk fixed by boundary") is now a theorem chain:
charge = boundary-modulus slope (M6) — conserved under deformation (M2) — jumping by
quantized units at crossings (M7) and at the seam (M5) — draining to the far field (M3)
— with parity pinned at the FE fixed locus (B4). Open mathematics: OC1 pairing, #116
cover construction, #96 foil.

## 2026-07-03 — #125 BANKED: 16-pinning-and-emission.md — OC1 re-cut, two theorems, one new object

**Pinning lemma [PROVED, paper]:** FE ∧ reality pin simple on-line zeros against any
FE-preserving deformation (reflection + local uniqueness, 5 lines). **Emission ports:**
off-line charge is created only at on-line multiple points — (P-flux) for FE∧real
families = parity of emission events + lateral flux; the k=1 rung along such families
is exactly "no odd emission count per quadrant box".

**Mirror identity [PROVED + VERIFIED 30 digits, R9]:** on the two-character family
G_{c,d} = cΛ(χ) + dΛ(χ̄), reflection across the line = parameter involution; on the
k-pencil, k' = tan(2·arctan κ − arctan k). Pre-registered pod test: first Muller run
FAILED (converged to the wrong zero — root-finder artifact, recorded); the exact
linear-pencil solve confirmed the identity to 8.5e-30 and verified the κ closed form
(√(10−2√5)−2)/(√5−1) against the certified zero (3.5e-17). **Two-coloring theorem:**
R3c's disjoint populations = sign classes of unpinning velocity; box 84 DERIVED (the
one box with the pre-existing off-line zero; measured dβ/dk ≈ 0.50, mirror partners
are separate left-strip zeros). OC1 relocated to (OC1′) emission parity at Euler
endpoints, with honest dBN-shape + GSH-interaction clauses.

**Opened — the INCIDENCE MAP r(s) = −L(s,χ̄)/L(s,χ):** the pencil is linear, so the
member vanishing at any point is exact algebra; the entire measured family dynamics
(trajectories, FE fiber, mirror, moat, velocities) is the level-set geometry of this
ONE meromorphic function. Natural carrier for (OC1′) beyond the model family; candidate
composition with the u-plane descent. Lean targets: mirror identity (needs mathlib
Dirichlet FE names); pinning lemma blocked on counting — NOTE the large-n deck-class
counting trick (ledger at level n > a priori bound pins exact counts) as a possible
full Rouché substitute for both lanes.

## 2026-07-03 — #116 TERMINALIZED: 17-cover-no-go.md — compositional rigidity closes the hunt

Attack-as-false WON. **Affine no-go [PROVED]:** the compositional symmetry group of ξ
is exactly {id, 1−s} (zeros→strip pins a real; N(T) ~ T log T pins |a| = 1 and kills
translations via the linear-count contradiction; composition with FE pins the rest) ⟹
the FE descent is the UNIQUE degree-2 polynomial factorization; Möbius deck
involutions die on the essential singularity. **Higher-degree/rational no-go
[PROVED]:** rational π accumulates zero-fibers at finite poles (Z discrete ✗);
polynomial π of degree d spreads fibers along d asymptotic directions vs Z in a
horizontal strip ⟹ d ≤ 2 ⟹ §2. u-plane: zeros hug ONE ray ⟹ no degree ≥ 2 at all.
**Survivor (Pólya):** only G(order 0) ∘ π(transcendental, order ≤ 1/2, fibers on the
negative ray — cos√-type tract) remains ⟹ **(RittΞ) [OPEN CORE]: compositional
primeness of Ξ** — decision-complete for #116 (holds ⟹ covers fully dead, parity
burden all on OC1′; fails ⟹ a new hidden symmetry of ζ and a genuine detector).
(RittΞ) is hgt-NATIVE: compositional rigidity of a seed object = the composition-
monoid analogue of hypertranscendence — a new gatekeeper candidate for the main
branch, attackable with mathlib's new Nevanlinna stack. [CHECK C11 at promotion:
Gross–Yang/Urabe factorization literature for Ξ pseudo-primeness.]

**Novelty-ledger correction (doc 17 §1):** xiDescent = the classical Ξ₁ (Pólya–Jensen
guise); rh_iff_xiDescent_ne_zero_slitPlane's STATEMENT is classically known — the new
content is the machine-checked descent + the graded deck/ladder calculus on it.

## 2026-07-03 — #127 BANKED: MirrorPencil.lean — the incidence-map/mirror structure is formal

Doc 16 §3, formalized on both layers: abstract FE-pair pencils (mirror involution,
ε·ε' = 1, zero-set involution, reality, THE INCIDENCE MAP with its exact-algebra
characterization) + the Dirichlet instantiation (dirichletXi = N^{s/2}-renormalized
completed L has CONSTANT root number; dirichlet_pencil_mirror on the R3/R5 family via
mathlib's IsPrimitive.completedLFunction_one_sub). RHTower green 8575 jobs, axiom-clean,
lint passed. The R9-measured 30-digit identity is now a theorem; the two-coloring's
algebraic layer is machine-checked (trajectory layer waits on M9's counting).

## 2026-07-03 — #126 opened: doc 17 §7 correction + the strip-fiber attack; C11 delegated

Self-audit found a GAP in 17 §4: "G has infinitely many zeros" is unjustified for
transcendental π (infinite fibers) — the survivor list is (i) POLYNOMIAL left factor
Q(deg ≥ 2) ∘ π transcendental (pseudo-primeness sector) and (ii) order-0 transcendental
G ∘ π. §7 records the correction plus two new closures: repeated-root Q dies on
UNCONDITIONAL simple zeros (Levinson–Conrey positive proportion); and the STRIP-FIBER
CONSTRAINT: all xiDescent zeros lie in the parabolic region P = {Re √u < 1/2}, so π
omits BOTH roots of Q on the huge complement Ω — Edrei/Baernstein radial-value-
distribution territory, with the model computation: cos√-type fibers confined to the
width-1 strip force their values into a COMPACT set (|Im arccos w| ≲ 1/2) ⟹ cos√-type
π can carry only finitely many zero-values in any case. Open heart: upgrade cos√-type
to all order ≤ 1/2 with two omitted values on Ω. C11 literature check (Gross–Yang/
Urabe primality of ζ/Ξ) delegated, pending.

## 2026-07-03 — #128 BANKED: CountingSubstitute.lean — Rouché substitute + pinning lemma formal

The large-n deck-class trick works even better than carded: NO a priori bound needed
(both counts are concrete naturals; compare classes at n = N_f + N_g + 1).
enclosed_count_eq_of_close = Hurwitz-type count stability under dominated perturbation,
no argument principle anywhere; pinned_zero_on_line = doc 16 §1 formal (count-1 + the
reflection q = 1 − conj(ρ') is a zero in the hole ⟹ no off-line zero survives).
First-compile clean, 8576 jobs, axiom-clean. The shared mathlib gap (no Rouché) is now
CLOSED for dominated-perturbation counting inside the deck calculus.

## 2026-07-04 — #103 BANKED: rhtower-paper-surface.md (P2); C12 + B-foil delegated

Publication surface written (formal/docs/drafts/rhtower-paper-surface.md): title
candidates (method-led recommended: "zero counting without the argument principle"),
the 16-module result surface organized in five arcs (ladder / deck calculus / ledger /
potential-theory+counting / continuation+families), gate-checked novelty positioning
(primary claim = the contour-free counting METHOD — mathlib lacks argument principle,
Rouché, Hurwitz; scope vs Isabelle's Li–Paulson Rouché flagged for verification),
the three honesty clauses (ladder classically trivial as statement; xiDescent = Ξ₁;
no rung mechanism claimed), venue split (ITP/CPP method paper + optional expository
note; RittΞ/pseudo-primeness material = separate classical paper pending C12), and
the five blocking pre-submission items (full-tree gate on q62 landing; delegated-note
spot-checks; naming pass; R-series stays out).

Delegated in parallel: C12 (two-fibers-on-a-line classification — Edrei/Ozawa/
Kobayashi exact statements; decides the (RittΞ) endgame) and the B-foil literature
component (#96: multiplicity/simplicity of off-line zeros in Beurling/DMV
constructions — is a genuine-Euler-product simple off-line zero exhibited anywhere?).

## 2026-07-04 — USER DIRECTIVE + #18 BANKED: the window relation (family variable dissolved)

DIRECTIVE (Michael): no paper without progress on RH — P2 surface is PARKED as an
internal map; all effort on the path itself; the target is RH through
"constraint, not flow".

**18-window-relation.md:** pushing (OC1′) through the constraint filter dissolved the
family entirely. In any line-centered disk window with zero-free edges, FE ∧ reality
give the identity D = L + 2N (total order = on-line order + twice the right-half
order), and hence the LADDER REFORMULATION:

  RH ⟺ ∀k, ∀ line-centered windows: D ≡ L (mod 2^{k+1})   (WR_k)

— shrunk windows give the per-zero rung exactly (D = 2m, L = 0). Both sides are exact
boundary invariants with BANKED dictionaries: D = deck class at n = 2^{k+1} (readable
from |ξ| on two circles by holography); L = seam ledger at level k+1 (at k = 1
literally Hardy's sign sequence of Ξ; higher k = ℤ/2^{k+1} gluing refinement). No
family, no flow, no events — the bulk pinned by two boundary strata of one window.
Filter checks pass: D–H VIOLATES (WR_1) at its certified zero (D=2, L=0) ⟹ the
ζ-instance needs Euler; the symmetry discount is explained (right-parity costs one
extra rung — the coherent tower appearing inside the bookkeeping).

Carded: #129 (Lean: window_relation_iff_ladder + dictionary wiring — all ingredients
banked) and #130 [OPEN CORE] (the bridge identity: Euler structure ⟹ WR_1; the
sharpest constraint-not-flow form the lane has produced). C12 + B-foil delegations
still pending.

## 2026-07-04 — B-foil ANSWERED (#96): the Révész filter — the detector lives on the weld

Delegated check returned with primary-source verification: **Révész (IMRN 2023,
arXiv:2202.01837 §7 Thm 8) and Broucke–Debruyne–Révész (TAMS 378 (2025), arXiv:
2309.01567 Thm 3.2): discrete Beurling systems with GENUINE Euler products realizing
ANY prescribed finite symmetric zero multiset in the strip — certified SIMPLE off-line
zero included, proved not numerical.** (No FE in these systems. DMV/Zhang leave
multiplicity unaddressed; Broucke–Vindas 2024 = Balazard Problem 24, zero at s = 1.)
Verified complement: Euler + FE + certified simple off-line zero exists NOWHERE.

Doc 14 §6 (the PINCER): D–H (FE, no Euler) and Révész (Euler, no FE) BOTH carry simple
off-line zeros ⟹ neither constraint alone forces parity ⟹ **any w₁-detector lives
strictly in the FE × Euler interaction — the weld of the hgt charter**. Goldilocks
sharpened from the counterexample side: bump surgery keeps FE and kills Euler; Beurling
freedom keeps Euler and kills FE; JOINT-preserving surgery is the missing
counterexample technology — the wall seen from the other side. Window relation
consistency: (ID) is FE-predicated, the bridge must consume Euler — WR is a weld
statement by construction, breaking correctly on both foils.

## 2026-07-04 — #129 BANKED: WindowRelation.lean — doc 18's core is machine-checked

window_identity (D = L + 2N under reflection closure), window_modEq_iff,
xi_window_relation_of_ladder (rung ⟹ relation for every reflection-closed ξ
configuration), pair_window_relation_iff (shrunk window = per-zero rung). 8577 jobs,
axiom-clean, lint green. The lane's sharpest reformulation now has its counting core
formal; remaining wiring (W1b): the two dictionary readings + the sign(Ξ) base case.

## 2026-07-04 — (RittΞ) RESOLVED (#126): Ξ(√·) is compositionally PRIME (doc 17 §9)

C12 returned the black box: **Kobayashi 1977 Thm 4** (entire, finite lower order, zeros
AND 1-points in a strip ⟹ order ≤ 1 MEAN TYPE ⟹ n(r,c) = O(r) ∀c; strip version
verbatim, source linked). The last open sector (f rational with two distinct special
values ∘ h transcendental) dies by: both fibers of h in the critical strip +
Valiron–Mohon'ko T(r,h) ≍ r log r vs Kobayashi's O(r). Combined with §2–3 (polynomial
h), §8 (Chuang pseudo-primeness), and Levinson–Conrey (repeated-value f):

  **ξ = f∘h forces f or h affine beyond the FE descent — Ξ(√·) is PRIME.**

Cover route dead permanently; the parity burden rests provably and solely on the
window/conservation front: (WR-core) is the lane's UNIQUE open core. Free-ground
theorems (unclaimed in print per C11; PARKED per no-paper directive): Ξ pseudo-prime,
Ξ prime mod FE descent, Ξ(√·) prime — an hgt-native gatekeeper result (compositional
rigidity of a seed object = composition-monoid analogue of hypertranscendence).
Bonus instrument pointer: Marchenko–Ostrovskii comb representation (real entire with
real ±1-points = cos θ(z), θ comb-conformal) — exactly the class where the k=1 seam
ledger lives; potential (WR_1) instrument.

## 2026-07-03 — #130 attack round 1: the square class (doc 19)
rng seed 1749846374244417905; move: extreme-cases; domains: ant-foraging × glassblowing.
- BANKED `SquareLadder.lean`: global-extreme window relation — RH_2 ⟺ Ξ₁ (= xiDescent) is a
  square on slitPlane; full tower rh_iff_forall_root_slitPlane. First-compile clean, axiom-clean.
- Square class ε(Ξ₁) ∈ ⊕_{non-real pairs} ℤ/2 defined; RH_2 ⟺ ε = 0; RH = depth-∞ = Pólya frame
  [KNOWN at the top; the graded intermediate object is ours — novelty audit in doc 19 §3].
- No-go (a): the window-preserving symmetry subgroup is {id, mirror} — spent by (ID); even-team
  enforcement cannot be geometric. No-go (b): zero-free comparisons (all Euler truncations) can
  never dominate on zero-enclosing window boundaries (counting substitute forces count ≡ 0);
  (ANNEAL) survives only as hybrid Euler×zero products.
- NEW instrument (DISC): sign(disc) = (−1)^{#non-real pairs} — the polynomial shadow of the
  square class; one inequality per Jensen-type section vs Sturm-chain hyperbolicity; regimes
  beyond GORZ. Foil prediction: D–H sections go disc < 0; Révész has no real carrier.
- Weld layering sharpened: FE builds the carrier, Euler must kill the class on it.
Next: (DISC) window↔section dictionary (#132); residue-parity pairing (#133); hybrid domination (#134).

## 2026-07-03 — #132 → #133 → #134 (the three coordinates of the bridge)
- #132 (DISC, doc 20 + DISC-RESULTS.md): pre-registered synthetic runs — no spurious
  pairs anywhere; P4 FAILED (load-bearing): global shift-n does NOT localize (cost
  d ≳ c·x_pair); recentering IS localization (pair visible at d = 4 once expansion
  sits at the window). POD run on the real objects: degree-4 n=0 recentered jet
  section reads disc < 0 at the certified D–H off-line zero and disc > 0 for ζ at the
  identical window — first measured finite square-class detector. Literature delegate:
  (SPUR) 2k-exactness unpublished; disc-sign literature stops at d=3 (= higher-order
  Turán, Dimitrov–Lucas 2011, global center only). Recentered program is open ground.
- #133 (doc 21): (SMOOTH) no-go shaped exactly — pairings output ℝ, target is ℤ/2;
  only known sign-extraction is conjugate-pair positivity (L-side). Reroute (GERM):
  Euler product = the whole formal ℤ₂-tower as convergent Dirichlet series on Re s>1
  (a_{p^j} = C(2j,j)/4^j etc.); RH_{2^k} ⟺ the arithmetic germ continues to
  Re s > 1/2. Landau route dead (pole caps σ_c). Cheap Lean repackaging carded.
- #134 (doc 22 + ANNEAL-RESULTS.md, pod): exact FE of the symmetric truncation
  g_N(1−s) = χ(1−s)g_N(s) (one line); domination 7/7 rng windows at r=0.20 up to
  T≈2800 (PE PASS; single r=0.35 failure at a g-zero 0.003 from the circle);
  reduction: ζ's window parity = truncation's window parity on dominated windows
  (modulo seam-transport wiring, with #131). Convergence: (DISC-fin) — the fully
  finite bridge target: disc > 0 for recentered jet sections of the truncation.
Next: (SPUR-R) stability theorem; (DISC-fin) first instance on a g_N off-line pair;
(GERM)-Lean packaging.

## 2026-07-03 — #135 → #136 → #137 (SPUR-R bricks, the finite instance, the germ bank)
- #135 (doc 23): identity stack derived (one-step / three-term / Appell / POLAR CHAIN —
  consecutive Jensen sections are polar derivatives at pole 0, not in print per delegate /
  generating e^u f(xu)). Bricks proved: universal rescaling + Hurwitz visibility; pointwise
  Turán for the chain (e^u g(xu) ∈ LP(u) + Laguerre inequality); one-sided interlacing with
  measured two-sided breakdown. (HBJ) = THEOREM via Levin's angle theorem (UHP = angle at
  vertex 0; {(d)_k} nonneg MS; delegate-verified route) — probes had found all-strictly-upper
  before the theorem was located. BB symbol of the Jensen operator = homogenized Laguerre
  (real stable) — independent route, unpublished per delegate. Two failed intermediates
  recorded (half-step stability: sign error, probe-refuted; PJ/PK superseded).
  THEOREM-M TRANSFER (user pointer): sign-transfer-at-critical-points + energy skeleton →
  the critical-point collapse (CPI): A_{d−1}(c) = A_d(c) and J^d_{Pg}(c) = q_d(c)A_d(c) +
  c⁴A_d''(c), q_d positive definite for d > 1 + a²/b² (verified 41 digits, pod). Residual
  named (AMP): transfer inequality at all-but-one extremum. #135 stays open at (AMP).
- #136 (DISC-RESULTS run 5, pod): box-count found 5 off-line-zero boxes of g_N; refined
  ρ_g = 0.60941068066067 + 221.0788841113159i (g₅). Reader counts 1 pair at d = 4,6,8 on the
  truncation's own carrier (PM′ PASS) — first fully finite window-relation instance. PN PASS:
  domination fails (q = 4.72 / 1.17) at the odd-parity window, as banked transport + verified
  RH force. (ANNEAL) exceptional set = square-class defects of the truncation, not noise.
- #137 BANKED: GermExtension.lean (exists_farHalf_root, rhLadder_iff_germ_extends) — the
  ladder as continuation of the Euler germ, machine-checked. 8579 jobs, axiom-clean.
Next: (AMP) via the two-variable energy on e^u g(xu); then the finite (DISC-fin) inequality
on truncation jets with (CPI) as the evaluation tool.

## 2026-07-03 — (AMP) attack: the two-variable energy and the single crossing (doc 24)
- PROVED: transport PDE xG_x − uG_u + uG = 0 ⟺ polar chain (characteristic form);
  energy factorization E_G = (G_u)² − G·G_uu = x²e^{2u}L_g(xu), L_g/g² = Σ(w−x_k)^{−2}
  — theorem-m's ODE energy reappears as the PULLBACK of the carrier's electrostatic
  zero-energy (no ODE exists for the ζ-carrier: hypertranscendence forces the energy
  to be a constraint on the configuration, not an evolution — constraint, not flow).
- PROVED: electrostatic reduction — at critical points Σ(c−α_k)^{−1} = 0 (Stieltjes
  equilibrium) and −A″/A = Σ(c−α_k)^{−2}: sign transfer ⟺ margin q_d/(c⁴ℰ) > 1,
  amplitudes cancel.
- PO REFUTED (pod, pre-registered): copy-everywhere is false — permanent far flip
  block (failures ~0.4d, margin_min → 0.28). The refutation produced the CORRECTED
  counting lemma: strict failure forces the flipped sign (still alternating);
  Z_c ≤ 2 + T, T = #copy↔flip crossings; T = 1 + evenness ⟹ Z_c ≤ 2 (doc 23 §3
  corrected in place).
- PQ/PR PASS (pod): T = 1 at ALL d ≥ 10 (model 1) / d ≥ 4 (model 2); zero outer
  monotone violations; no negative-side crossings; T = 2 transient at d = 8 sits in
  the q_d-dip and clears at the definiteness threshold d > 1 + a²/b² — matching
  doc 20's measured visibility threshold.
- Kernel re-cut: (AMP-mono) — single crossing (sufficient: tracking + dip clearance
  [proof-shaped Hurwitz estimates] + outer monotonicity of c⁴ℰ/q_d [open, measured
  0 violations]). Application: u-plane slit carrier recentered at −T² has the
  one-sided-far shape ⟹ T = 1 ⟹ theorem-grade DISC reader lives on the u-plane.
Archives: AMP-RESULTS.md; scripts amp_margin_landscape.py, amp_crossing_probe.py.
Next: prove tracking/dip clearance; attack outer monotonicity via the equilibrium
constraint; u-plane reader on the #136 truncation window.

## 2026-07-04 — Tracking clearance PROVED: (AMP-mono) parts (i)+(ii) closed (doc 25)
- PROVED (Thm A): margin ≥ κ_A·d² at every window critical point off the zero set of g.
  The expected obstruction — the far-zero tail of ℰ needing a spacing input — does not
  exist: at critical points ℰ = −A″/A exactly (E1), and the identity carries the tail.
  Proof = rescaling brick + Cauchy + the exact identity; ~15 lines.
- PROVED (E4/E5): operator identity Ã_d = φ_d(θ)g, θ(θ−1) = z²∂² — the section chain is
  a BACKWARD-HEAT smoothing of the carrier at time 1/d with diffusion z² (flow on the
  approximants, constraint on the object); elementary two-sided bound
  |φ_d(j) − 1 + C(j,2)/d| ≤ C(j,2)²/2d² for ALL j, d (Weierstrass + e^{−S} ≤ 1−S+S²/2).
- PROVED (Lemma W): at every zero k of He_m′: −He_m″(k)/He_m(k) = m — Hermite equilibrium
  energy = charge count (two lines from the recurrence). Makes the cluster constant
  universal.
- PROVED (Thm B, m ≤ 3; proof-shaped m ≥ 4 via Lemma R): an m-fold zero x* of g splits at
  the SINGLE scale σ = |x*|/√d into the He_m configuration; cluster margins
  = |x*−τ|²d/(m·x*²)·(1+O(d^{−1/2})) — rate d, multiplicity enters linearly. The heat
  resummation forbids the Newton-cascade that would have violated clearance from m = 4.
- PROVED (Cor C): the q_d-dip z_c → a sits INSIDE the tracking window — part (ii) is
  subsumed by part (i); the d = 8 transient = the definiteness threshold's shadow.
- P-B PASS (pod, pre-registered, run 3 in AMP-RESULTS.md): half-gap and ALL margin ratios
  → 1 at O(d^{−1/2}) over d = 10²…10⁵, m = 2 and m = 4 (three critical points, uniform
  constant 4 = Lemma W's prediction).
- Residual of (SPUR-R): (AMP-mono)(iii) ALONE — outer single crossing of c⁴ℰ/q_d.
  Registered attack [CONJECTURE]: equilibrium constraint near-symmetrizes neighbors ⟹
  c⁴ℰ increases between consecutive equilibria while q_d grows only quadratically.
Archives: doc 25; AMP-RESULTS.md run 3; script amp_cluster_hermite.py. New pod
157.157.221.30:31867. Next: (iii) via the equilibrium constraint; u-plane reader on #136.

## 2026-07-04 — #140 u-plane theorem-track instance PASS; #138 attack: the reversal (doc 26)
- #140 DONE (DISC-RESULTS run 6, all four predictions PASS): the #136 truncation
  off-line pair reads identically on the u-plane one-sided-far carrier (1 pair,
  disc < 0 at d = 4, 6, 8; ζ control clean at the same u₀; refined zero certified to
  1.9e−196). The finite instance now lives on the carrier shape with PROVED tracking
  legs (doc 25) and T = 1 counting.
- #138 round 1 (entropy: reverse / ant-foraging / percolation) — doc 26 banked:
  - PROVED (REV): at equilibria, F̂(1/c) = dc and c⁴ℰ(c) = ℰ̂(1/c) − dc²;
    margin > 1 ⟺ ℰ̂ < |F̂ − τ|² — intrinsic in the reversed configuration.
  - PROVED (OSC): V = Âe^{−ay}: copy ⟺ (V″+b²V)V > 0 — theorem-m's oscillator
    energy E_b = b²V²+V′² reappears exactly (E_b′ = 2V′(V″+b²V)), frequency b = Im τ.
  - PROVED (ΞSUM): pole weights ξ_k = y/(y−β_k) obey Σξ_k = d at EVERY equilibrium;
    flip ⟺ Σξ² > (d−ay)²+b²y² ≈ d² — copy→flip = delocalization→localization
    transition (participation ratio) under a conserved budget.
  - P-C/P-D PASS (identity exact to 63+ digits; oscillator ≡ margin pointwise, single
    transition). P-E REFUTED load-bearing: outer log-gaps NOT monotone (≈0.15d
    violations) yet crossing stays single — gap monotonicity is the wrong mechanism.
    P-F: O(1) race (d·δ* ≈ 3.7, θ ≈ 0.27, far margin saturates ≈ 0.28).
  - P-H: full majorization REFUTED (Schur route dead in full strength); dominant
    weight ξ_max monotone at ZERO violations; S = Σξ² monotone at ZERO violations.
  - Kernel re-cut: **(S-mono)** — S_i strictly increasing along outer equilibria ⟹
    T = 1 ⟹ (SPUR-R) closes with doc 25. Proof shape: dominant-weight drift lemma
    (θ-drift from the one-sided trail) + sum-rule remainder control; wild route =
    monotone-event coupling (percolation).
Archives: DISC-RESULTS run 6; AMP-RESULTS runs 4–5; scripts uplane_reader_136.py,
amp_reversal_probe.py, amp_majorization_probe.py. Next: the θ-drift law (equilibrium
position vs trail mass — closed-form monotone bound from the ant-trail kernel sum).

## 2026-07-04 — #138 round 2: the θ-drift attack (doc 27) — (S-mono) reduced to (LEG)
- PROVED: weight flow η_k = c/(c−α_k), η′ = −η(η−1)/c; hierarchy p_r′ = −(r/c)(p_{r+1}−p_r);
  S = d + p₂ = d + c²ℰ(c) exact — (S-mono) ⟺ c²ℰ increasing along outer criticals.
- PROVED: pole removal — S_{i+1} − S_i = ∫Φ̃′ over the smooth reduced path, with the
  signed integrand Φ̃′ = −(2/c)Σw_k(η_k + p̃₁), w_k = η_k(η_k−1) > 0 (weights never in
  (0,1)); endpoint signs (dip at c_i, rise at c_{i+1}).
- PROVED: midpoint-push lemma — nondecreasing gaps + outer half ⟹ θ_i < 1/2 (termwise
  pairing at the gap midpoint + left surplus).
- PROVED (representation): log-time t = log c makes the flow autonomous logistic;
  weights = translated sigmoids ½ + ½coth((t−t_k)/2), interaction w = 1/(4sinh²) —
  hyperbolic CALOGERO kernel; equilibria at Σcoth = −d; S = ¾d + ¼Σcoth²; flip ⟺
  Σcoth² ≳ 4d². Whole outer problem now translation-invariant in the log-zeros.
- P-I/P-J/P-K ALL PASS at 0 violations (AMP-RESULTS run 6): dip-then-rise shape +
  net-positive integral on every outer interval; outer gap growth; θ < 1/2 with the
  drift deepening (θ_last = 0.19/0.16/0.14 at d = 16/24/40).
- Residual named: (LEG) — the leg-comparison integral (rise beats dip); length
  asymmetry already proved (θ < 1/2 + gap growth ⟹ up-leg longer). Next: integrate
  the coth/csch² legs in closed form → a two-variable inequality in (θ, Δ_i/Δ_{i+1}).

## 2026-07-04 — #138 round 3 (doc 28, all by reasoning): operator identity, winding, no-go
- PROVED: Ĵ = R[J^d_{Pg}] = (D−τ)(D−τ̄)Â — the pair acts as theorem-m's oscillator
  operator on reversed sections; B = (D−τ̄)Â UHP-stable; Z_c(J) = 2·wind(F_B(ℝ), τ):
  the DISC reader is exact ⟺ the Stieltjes field curve winds ONCE around τ — the
  lane's deck-class/winding language closes at the section level.
- PROVED (first order): every petal of the field curve is TANGENT to τ at leading
  order — the enclosure (winding) is decided by the dressed-background drift; explains
  the O(1) race, 0.28 saturation, and why all one-parameter proxies failed.
- PROVED (no-go): Â = y²(y−K)² with D²+1 has 4 non-real zeros — "operator adds ≤ 1
  pair" is FALSE in general; the one-sided window shape is a necessary hypothesis of
  (SPUR-R). Degenerate cluster re-derives the (CPI) threshold d > 1 + a²/b².
- Lattice skeleton for (LEG): θ-drift law is a ONE-LINE consequence of the constraint
  (swap jump coth > 1 exact ⟹ Δθ ≤ −1/(δW)); (L1) dW/dθ < 0 proved in outline
  (φ = csch²coth termwise domination, cubic head vs exponential tail); (L3) far-end
  direct. Residual = adiabatic comparison (#142): bound the loss 2∫W̃dt against the
  swap gain on nondecreasing-gap fields (q-digamma sums).
- Anti-theatre correction (user): round 3 done entirely by hand; unused probe deleted.

## 2026-07-04 — #143 Lean: first two SPUR bricks banked (standing order: formalize proven)
- SpurHermite.lean (8580 jobs, axiom-clean, lint passed): derivative_hermite (Appell
  He_{n+1}′ = (n+1)He_n — absent from mathlib, proved by induction), hermite_rec
  (three-term recurrence), aeval_hermite_ne_zero_of_succ (adjacent Hermites share no
  real zero, descent), hermite_equilibrium_energy (Lemma W division-free:
  He_m″(k) = −m·He_m(k), He_m(k) ≠ 0 at critical points), hermite_energy_eq_charge
  (−He″/He = m — doc 25 §3's universal cluster constant, machine-checked).
- SpurRescale.lean (8581 jobs, axiom-clean, lint passed): one_sub_sum_le_prod_one_sub
  (Weierstrass), prod_one_sub_le_exp_neg_sum, exp_neg_le_quadratic (e^{−x} ≤ 1−x+x²/2,
  monotonicity route), sum_range_id_cast, phi_first_order ((E5): |φ_d(j) − 1 + C(j,2)/d|
  ≤ (C(j,2)/d)²/2 for ALL j, d ≥ 1 — incl. the j > d zero-product branch via S ≥ 1).
- Umbrella RHTower.lean extended; queue next: operator identity Ĵ = (D−τ)(D−τ̄)Â
  (doc 28 §1, Polynomial.reflect route), UHP-stability, weight sum rules, no-go instance.

## 2026-07-04 — #143 Lean round 2: the operator identity machine-checked
- SpurOperator.lean (8582 jobs, axiom-clean, lint passed):
  - polarStep n A := n·A − X·A′ (denominator-cleared polar companion) + coeff formula
    + natDegree_polarStep_le;
  - reflect_polarStep: **reflect (n−1) (polarStep n A) = derivative (reflect n A)** —
    the polar/derivative duality (doc 26 §0), coefficient-wise proof;
  - reflect_pair_operator: **reflect d (u·A − v·X·B₁ + X²·B₂) = Â″ − v·Â′ + u·Â** over
    any CommRing (doc 28 §1's three-term reflection identity, general form);
  - reflect_pair_operator_complex: the (D−τ)(D−τ̄) factorized ℂ-form — the pair as
    theorem-m's damped oscillator, machine-checked;
  - helpers: reflect_zero_eq, reflect_X_pow_self, reflect_C_mul'.
- #143 queue remaining: UHP-stability of B (doc 28 §2a), weight sum rules (docs 26–27),
  two-cluster no-go instance (doc 28 §4), doc 25 Thm A (heavy), winding formula
  (argument-principle coverage in mathlib to be checked).

## 2026-07-04 — #143 Lean round 3: UHP-stability banked + doc 28 §2a corrected
- CORRECTION (caught at formalization, banked in doc 28 §2a): an m-fold real root of Â
  is an (m−1)-fold REAL zero of B = Â′ − τ̄Â — strict UHP-stability needs simple roots;
  the right hypothesis-free statement is "every zero z of B with Â(z) ≠ 0 has Im z > 0";
  the winding formula's boundary bookkeeping for multiple roots goes by perturbation.
- SpurStability.lean (8583 jobs, axiom-clean, lint passed):
  - im_derivative_mul_conj_nonneg: division-free Hermite–Biehler positivity
    Im(P′(z)·conj P(z)) ≥ 0 for Im z ≤ 0, P = ∏(X−r) over a real root multiset —
    proved by multiset induction, no log-derivative machinery;
  - uhp_of_pair_shift_root: the corrected doc 28 §2a statement, machine-checked.
- Formal stack for the SPUR arc now: SpurHermite + SpurRescale + SpurOperator +
  SpurStability (4 files, 16 theorems, all axiom-clean).

## 2026-07-04 — #143 Lean round 4: two-cluster no-go machine-checked
- SpurNoGo.lean (8584 jobs, axiom-clean, lint passed, index regenerated):
  twoCluster := (X(X−100))² (hyperbolic, roots 0,0,100,100); twoCluster_operator_expand
  ((D²+1)-image as explicit quartic); twoCluster_operator_pos (strictly positive on ℝ —
  SOS-certificate via nlinarith); twoCluster_operator_no_real_root (degree 4 + no real
  zeros ⟹ two non-real pairs). Doc 28 §4's shape-necessity no-go is machine-checked:
  "the operator adds ≤ 1 pair" is FALSE for two-cluster hyperbolic carriers.
- SPUR formal stack complete for this round: 5 files (SpurHermite, SpurRescale,
  SpurOperator, SpurStability, SpurNoGo), 20 theorems, all axiom-clean
  [propext, Classical.choice, Quot.sound].

## 2026-07-04 — #142 rounds 2–3 (doc 30): exact adiabatic ledger + the cushion finding
- PROVED (exact): the step comparison ΔG(s) = G_{i+1}(s) − G_i(s) decomposes into two
  swap extras (each coth > 1) + termwise gap-increment coth-differences (behind vs
  ahead drift pairs) — no approximation; constant lattice recovers doc 29(b).
- Orientation: measured section fields have DECREASING log-gaps (δ_j ~ c/j — P-E's
  refutation now load-bearing again): behind drift = gains, ahead = losses; both sums
  log-divergent with k-wise pairing cancelling to log(i/(d−i)) ≥ 0 outer.
- ROUND-3 FINDING (doc 30 §5): the near swap extra is coth((δ+s)/2) ~ 2i/c — the march
  cushion is O(1/δ), NOT O(1); drift losses are O(log i/c): monotonicity clears by
  ~ i/log i. The measured O(1)-tightness (0.28, dδ* ≈ 3.7) is about the crossing LEVEL,
  which the theorem never needs. Closing inequality re-cut as (ADB-crude):
  total-variation-weighted spectator energy < near-swap cushion — crude-provable for
  |Δδ| = O(δ²) fields.
- (LEG) proof shape COMPLETE: (b′) march via cushion domination + (c) dW/ds < 0
  [proved, gap-shape-free] + (d) exp tail + (e) assembly. Remaining = doc 31 write-up
  with one constant chase; then (S-mono) ⟹ (SPUR-R) on one-sided-far carriers with
  doc 25. Promotion gated by #141 (citations).

## 2026-07-04 — doc 31: (S-mono) assembled as a theorem on (F)-fields
- Field class (F): one-sided + midpoint-push input (x-gaps nondecreasing) + regularity
  |Δδ| = O(δ²). Theorem: S-mono on outer equilibria ⟹ T = 1 ⟹ Z_c = 2 ⟹ DISC reader
  exact on one-sided-far carriers. Proof = 5 assembled pieces (docs 27, 29, 30), all
  proved except two marked constant-chases (χ1: cushion-domination summation; χ2:
  disjoint-interval nesting on general (F2) fields).
- Consequence map: reader side of the bridge identity CLOSED modulo (χ1)(χ2)(#141);
  remaining structural inputs of #130 = seam transport (#131) + doc 22 exceptional-set
  bookkeeping. Next: chase (χ1)/(χ2); Lean the doc 30 ledger; back to the ladder front.

## 2026-07-04 — #142 round 5: (χ1)/(χ2) chased + citation audit (doc 31 §5–§6)
- (χ2) CHASED: k-th behind/ahead pairing intervals have length ≤ 2s; bracket sum
  ≤ 26s/δ⁴ vs near term ≥ 512/δ³ at worst s = δ/2 — dW/ds < 0 clears by factor ≈ 40.
- (χ1) CHASED: drift losses ≤ 2C₀log d + O(C₀) vs cushion ~ 4/(3δ) ~ O(d/c) —
  clears by factor ~ d/log d.
- CITATION AUDIT: the (SPUR-R) critical chain (docs 24, 25, 26–31) is
  delegate-citation-FREE (in-lane proofs + machine-checked Hermite facts); Levin/CC
  gate only doc 23's (HBJ) context brick — #141 downgraded to LOW, no longer blocks
  the (S-mono) promotion path. Also: the #136/#140 instance has simple zeros ⟹ needs
  only m ≤ 3 tracking — Lemma R (#139) is for Ξ₁-grade generality only.
- (S-mono) on (F)-fields: proved in outline at EVERY step with explicit margins.
  Remaining: per-carrier (F2)/(F3) verification, final polished write-out, then
  promotion; and the ladder front (#131 seam wiring) is now the binding structural
  input of #130.

## 2026-07-04 — #131 unblocked (doc 32): seam transport = banked homotopy invariance
- PROVED (2 lines + banked #117): dominated windows transport deck classes — segment
  homotopy under |f−g| < |g| on ∂W + DeckHomotopy invariance. Rouché with no argument
  principle: the deck-class language makes transport a homotopy statement; the bulk is
  fixed by its boundary (lane holography). Doc 22's reduction wiring gap is closed at
  the paper level.
- #131 remainder made executable: SeamTransport.lean (plumbing), k = 1 base via
  ReflectionParity, L-as-seam-product via SeamCocycle + MirrorPencil.
- #130 residue after that: exceptional-set traversal + cofinality of dominated windows.

## 2026-07-04 — #131 item 1 DONE: SeamTransport.lean machine-checked
- SeamTransport.lean (8585 jobs, axiom-clean, lint passed): seam_transport (strict
  boundary domination transports level-n deck classes — deckClass_perturb packaged in
  the doc-32 vocabulary) + seam_transport_ladder (level 2^k: each RUNG of the RH ladder
  can be read off the finite truncation wherever domination holds).
- The ANNEAL reduction's transport step is now Lean-checked end to end; #131 remainder:
  (2) k = 1 base case via ReflectionParity; (3) L-as-seam-product via SeamCocycle +
  MirrorPencil.

## 2026-07-04 — #144 round 2: (LOW) reduced to good-lines (doc 32 §5)
- (DOM) divides out: |ζ − g_N| < |g_N| pointwise (arch + polynomial factors cancel).
- (LOW) routes assessed: Boutroux–Cartan gives T^{−C loglog T} (fallback, insufficient
  vs the T^{−1/4+r/2} AFE error); GOOD-LINES (Titchmarsh/Ramachandra inverse bounds on
  chosen horizontal lines) gives |g_N| ≥ ½T^{−ε} on contours through good segments —
  the route; second moment supports. Window centers at good heights: the Lean charts'
  center is already free — no new machinery.
- #144 now = two classical cite-and-check items ((AFE) HL remainder; (LOW) good-lines)
  + center-selection bookkeeping. Next cycle: verify both statements against sources
  (instrument verification), then #142 write-out, #131(2,3), #143 queue.

## 2026-07-04 — #144 round 3: (LOW) DISSOLVED via symmetrized exponential-AFE (doc 32 §6)
- Good-lines route honestly refuted (classical strength e^{C log²T} insufficient vs
  T^{−1/4} HL error; fixed-power near-line minima = small-values/negative-moment depth).
- Corrected: (AFE-exp) exponential-error AFE (1910.05754-type, O(e^{−ωt})) + (SYM) free
  symmetrization preserving exact even FE (ξ(1−s) = ξ(s), one line) + (LOW-BC)
  Boutroux–Cartan T^{−C loglog T} ≫ e^{−ωT} ⟹ (DOM) UNCONDITIONAL. No small-values
  input anywhere. Citation checks logged: HL-AFE error shape confirmed via web.
- The failure was load-bearing: the free degree of freedom is the truncation FAMILY,
  not the contour. Architecture family-agnostic; g₅ instances remain valid HL-family
  measurements.

## 2026-07-04 — #144 round 4: (DOM) unconditional end to end (doc 32 §7)
- (AFE-exp) VERIFIED from the source PDF (Jerby 1910.05754v2, Thm 1.1 read pages 1–4):
  Hasse–Sondow finite side, O(e^{−ωt}) with explicit ω > 0, degenerate y excluded;
  fixed y ⟹ constant ω along height families; prefactor poles on σ = 1 only.
- (SYM) and (LOW-BC) written paper-grade and PROVED (σ = 2 Euler anchor + Jensen count
  + Cartan minimum modulus; e^{−C log T loglog T} ≫ e^{−ωT}).
- Sole remaining #144 item: σ-uniformity fine print in Jerby Sections 2–4 + eventual
  exponential-family instance run. The reduction's analytic side is otherwise closed.

## 2026-07-04 — #144 CLOSED (doc 32 §8): σ-uniformity structural, (DOM) stands
- Read Jerby §2 from the source PDF: saddle PHASE f(w;α) is σ-independent (σ only in
  the amplitude e^{−w}w^{σ−1}) ⟹ saddle equation, w_k(α), and ω(α) carry no σ ⟹
  compact-strip uniformity of the O(e^{−ωt}) constant is automatic; same phase governs
  Ĩ₁/Ĩ₂ (Thms 3.1/4.1). Fine print resolved; promotion-grade re-read of §§3–4 noted as
  optional prudence.
- #144 completed at SEARCH grade: the ANNEAL reduction's analytic side stands
  unconditionally on the symmetrized Jerby family. Board: #142 write-out, #131(2,3),
  #143 queue, #139, exp-family instance run.

## 2026-07-04 — #131(2,3) made precise (doc 33): the dictionary base
- (K1) k = 1 base case stated + outlined: deckClass(W;2) = sign ratio of Ξ at seam
  basepoints (deckClass_pow_eq_one n=2 + Ξ real + central triviality + IVT gluing).
- (K2) L as seam product stated + outlined: L mod 2^k = composed xiDescent_seam_jump
  data along ∂W ∩ line; mod-4 relation = cocycle identity (seam_jump ∘ window_identity).
- #131 remainder = DictionaryBase.lean plumbing only; every ingredient is a banked
  theorem. Board: #142 write-out, #143 queue, #139, DictionaryBase.lean, exp-family
  instance run.

## 2026-07-04 — pipeline card created: smono-reader-exactness (stage 1)
- The (S-mono)/(SPUR-R) arc is now a pipeline card with explicit gates: 1→2 needs the
  line-by-line constant write-out + per-carrier (F)-checks; 2→3 lists the remaining
  Lean items. The claim, its status, and its full doc chain are pinned in the kanban.

## 2026-07-04 — #143: SpurWeights.lean banked (8586 jobs, axiom-clean, lint passed)
- eval_derivative_rootProd (product-form log-derivative sum, multiset induction);
  weight_sum_rule (Ση = 0 — the Stieltjes constraint in weight form);
  energy_eq_neg_second_derivative ((E1): Σ(c−r)⁻² = −P″(c)/P(c), via HasDerivAt.unique
  on the eventually-equal product identity — the exactness that dissolved the far-tail
  obstruction, doc 25 §1, now machine-checked);
  S_eq_card_add_energy (S = d + c²ℰ — doc 27 §0's scale-invariant energy identity).
- Formal SPUR stack: 8 modules, 26 theorems, all axiom-clean. #143 queue remaining:
  ledger identity (doc 30 §1), doc 25 Thm A, counting lemma, DictionaryBase.lean.

## 2026-07-04 — #139 proved in outline (doc 34): Lemma R by the elementary ladder
- (R1) iterated-(E5) cumulant expansion with explicit remainder; (R2) degree filtration
  (only j-degree 2p survives at scale σ; heat semigroup emerges); (R3) freezing costs
  d^{−1/2}; (R4) exact Hermite resummation. All pieces elementary; composition =
  bookkeeping. Doc 25 Thm B now multiplicity-blind in outline — Ξ₁-grade clearance
  without simplicity hypotheses. Remaining = constants (same register as card 1→2).

## 2026-07-05 — #131(2) algebra layer banked: DictionaryBase.lean (8587 jobs, axiom-clean)
- deckClass_level_two (k=1 dichotomy ±1); deckClass_eq_neg_one_iff (flip criterion);
  sq_root_real_of_pos / sq_root_im_of_neg (roots over real values are real/imaginary
  by carrier sign — the Ξ-realness bridge); real_root_ratio.
- Formal stack: 9 modules / 31 theorems, all axiom-clean. Remaining #131(2): the
  seam-continuation lemma (pow_root_ratio chained along overlapping discs on the line
  segment — converts Ξ's sign changes into the deck class); #131(3): seam_jump chain.

## 2026-07-04 (cont.) — doc 35 Part I: constants write-out (a)+(b′)

The 1→2 gate began. Doc 35: (F1)-(F4) with fixed constants (C₀ ≤ 1/2, δ ≤ 1, NEW (F4)
ahead-span comparability — automatic from one-sidedness for c/j fields, the structural
content of the outer condition); toolbox (T1)-(T6) with complete elementary proofs
(partial-fractions coth bound, e²−1 cushion constant 0.313, csch² exponential 5.36);
Lemma A (midpoint, constant-free — pairing MUST run in x-coordinates, AM-GM ports);
Lemma B (losses ≤ 8C₀(1+log(5/δ̂)) + 4.4C₀, two ranges, no far-tail range — (F4) kills
it); Lemma C (cushion ≥ 0.417/δ); Theorem B′ with per-index criterion
(M): 8C₀log(28/δ) + 4.4C₀ ≤ 2 + 0.417/δ. Honest evaluation: on c/j models i₀ ≈ 150
(c=2), ≈ 120 (c=4); the i < i₀ band is covered by doc 25 tracking clearance, not
(S-mono). CAUGHT during write-out: first-draft far-tail chain broke at C₀ ~ 1/2 (real
carriers!) — fixed structurally by (F4), which the outer condition supplies free.
Remaining: doc 36 Part II — (c) response bound (χ2 exact), (d) tail, (e) assembly,
per-carrier protocol, Lemma R constants.

## 2026-07-04 (cont.) — doc 36 Part II: response/tail/assembly constants

Doc 36 banked. Content: Lemma A′ — the endpoint margin is EXACT, δ/2 − s_i ≥
log cosh(δ/2) ≥ δ²/9 (the AM-GM gap itself; constant-free). (T7) |φ′| two-sided.
Lemma D — dW/ds ≤ −5/(12δ²) on the band M ≥ ⌈2/√δ⌉ via the SHIFTED pairing
(pole↔behind₁ then ahead_{k−1}↔behind_k: every bracket ≤ 0 termwise under (F2)).
Lemma E — swap bound (folding deferred, mechanical). Theorem S — assembly with
two-case split (path integral vs direct-jump), criterion (M′). CORRECTIONS FOUND:
doc 31 §5 (χ2) constants wrong (φ ~ 1/u³ not 8/u³ variable slip; factor-40 claim
dead); doc 29(c) unbanded claim false near field edge (dW/ds > 0 possible at
M = O(1)) — band restriction + doc 28 (L3) delegation repair it, as doc 29(e) had
anticipated. Gate remainder: (α) Lemma E folding; (β) per-carrier protocol run on
#136/#140 window (pre-register); (γ) Lemma R constants (#139).

## 2026-07-04 (cont.) — doc 36 §7: Lemma E folded → swap SIGN lemma + closure map

(α) done, and the folding upgraded the result: every drift term of the W-ledger is
≥ 0 (both behind and ahead distances SHRINK under the step) — the swap is positive
except for the single removed far-ahead term R ≤ 16/(M²δ²). No gap-variation lower
bounds needed; §3's magnitude estimate superseded by sign structure. Sharpened
W ≤ 1/s² + 31/δ². Theorem S′ three-regime closure: deep band s ≤ δ/3 closes for
M ≥ 9 (margin 0.2/δ²); endpoint band closes for M ≥ 86/√δ (margin 2.2e−3/δ);
residual = (E-band), the last ~87√(d/c) indices at the far tip — (L3)-extension or
per-carrier direct evaluation. (S-mono) now PROVED WITH EXPLICIT CONSTANTS on the
outer half minus (E-band). New task: (E-band) closure. Then: (β) per-carrier
protocol pre-registration, (γ) Lemma R constants, Lean queue.

## 2026-07-04 (cont.) — doc 37: LEDGER CORRECTED — the gate catches its biggest fish

Re-deriving doc 30 §1's ΔG for the Lean queue exposed a bookkeeping error: the
matched-index regrouping leaves TWO FAR-FIELD extras (far-behind + far-ahead,
matching doc 29(b)'s lattice terms); the "near swap extra coth((δ̂+s)/2)" was a
mislabel — it is a paired drift term. The O(1/δ) bulk cushion (doc 30 §5's
ADB-crude) is therefore phantom; doc 35 Lemma C/Thm B′ inherited it and are
superseded. REPAIR (doc 37): convexity hypothesis (F5) ⟹ termwise gain ≥ loss up to
k* = √(2s/C₀δ²) (increment ordering × weight nearness), reversal remainder ≤ 200C₀²
⟹ Theorem B″: march unconditional for C₀ ≤ 1/10 (+ tip cushion 0.63/(t_d−t_{i+1}) at
the far end — the cushion is a TIP phenomenon, matching measurements). For c < 10
carriers the bulk march = finite per-index evaluation (per-carrier protocol).
Theorem S′ renumbered (deep band M ≥ 6/√δ; endpoint M ≥ 56/δ but endpoint band is an
INITIAL march segment since s decreases). Lean of the §1 regrouping identity queued —
it would have caught the error mechanically. Next: that Lean brick, then Lemma H
constant folding + per-carrier pre-registration.

## 2026-07-04 (cont.) — LedgerIdentity.lean: the corrected ledger machine-checked

Doc 37 §1's regrouping identity banked in Lean (8589 jobs, axiom-clean, lint green):
`ledger_regroup` — ΔG's leftovers are EXACTLY the far-behind and far-ahead extras,
generic in kernel f and positions t (pure Finset algebra; the theorem doc 30's
display violates and doc 29(b) satisfies). Plus sign lemmas `ledger_gain_nonneg` /
`ledger_loss_nonpos` (antitone kernel + nonincreasing gaps). The formal statement is
now the authoritative ledger; any future march argument must type against it.
Remaining board: Lemma H constant folding, per-carrier protocol pre-registration
(bulk march γᵢ + regime map + (E-band) tip, #145), Lemma R constants (#139), doc 25
Thm A + doc 24 counting lemma (Lean, #143), exp-family run.

## 2026-07-04 — #146 Euler-suppression discrimination run (pod) + #148 answered
Session seed 1920367149821033252. Main run banked (`computations/mwm/es146.out`,
script `euler_suppression_boxcount.py`, pre-registration in docstring BEFORE run):
exact-FE carriers Φ_a with toggled coefficients, E (a_n=1) / M (random completely
multiplicative ±1) / R (iid ±1), 8 CSPRNG seeds each, box sweeps band1 [200,1030)
N=5..12, band2 [5000,5830) N=28..30 (primary). Outcomes: P-A PASS (E band1 = 5,
first hit (220,5,1) — exact run-5 replication through the Φ symmetric form).
P-B PASS (R band2 mean 138 ≫ 15). P-C FAIL AS REGISTERED — but not null: M band2
mean 91 vs R 138, every M below every R (~10σ), ratio 0.66 (registered ≤ 0.5);
dose-response REVERSED (band1 ratio 0.55). P-D PASS (reader count = 1 at
d=4,6,8 AND exploratory 10,12,16 on M/R off-line zeros; one R refinement converged
on-line, skipped). P-E PASS (ζ disc > 0 at d=10,12,16, n=0,1 at both banked
windows — SPUR stable to degree 16; card #146(a) closed). Structural half settled
by reasoning (doc 19 §5): Révész foil admits no real carrier; pincer stays with
doc 14 §6. KEY UNPREDICTED FINDING: E ≪ M (4 vs 91): M seed 894929634 has
f(p)=+1 ∀p≤12 ⟹ band1-identical to E, scores exactly 5; in band2 THREE flipped
primes (13,19,29) take it to 77. Off-line rate is nearly all-or-nothing in
χ-coherence, not graded in multiplicativity. Q control launched (a_{n²}=+1 forced,
else iid — matches M's mean vector, kills dependence; P-F prior 0.5 registered in
script). #148 answered same session: doc 38-hermite-ladder.md — disc = determinant
shadow of the Hermite–Hankel form; Jacobi minor chain reads exact pair count;
(HANK-fin)_k generalizes (DISC-fin); lane NOT intrinsically RH_2; GORZ = the n≥2
blindness band; recentered Turán = isolated provable fragment.

## 2026-07-04 (addendum) — #146 controls landed; verdict = COHERENCE, not multiplicativity
Q control (a_{n²}=+1, else iid): band2 mean 150.8 ≈ R's 138 — P-F PASS,
dependence-dominant (mean bias explains nothing). X-frame isolation: χ₋₄ stream in
its OWN frame = 2 off-line zeros (band2); the SAME stream in ζ's frame = 54 —
P-G/P-H both PASS. Full measured gradient: weld-coherent 2–5 ≪ wrong-frame
character 54 < random multiplicative 91 < structureless 138–151. Run 7 appended to
computations/DISC-RESULTS.md (raw: es146*.out archived). #130's arithmetic clause
re-cut: the bridge must consume the AFE/weld identity, not coefficientwise Euler
structure. #146 CLOSED.

## 2026-07-04 (cycle 6, push) — E-band closed as architecture: doc 42
Audit catch #3 of the arc: S′ regime 2 (M ≥ 56/δ) VACUOUS on one-sided windows
for c ≤ 56 (needs c > 56; doc 37's renumbering silently emptied doc 36's
satisfiable 86/√δ band) — the endpoint band had NO theorem coverage at actual
carriers. Fix: Lemma E″ [PROVED, (F8) added: lower drop regularity c₈ ≥ 1/(2c)]:
retain the k = 1 behind drift in Lemma E′'s all-positive ledger:
swap ≥ c₈/(4δ) − 16/(M²δ²) ≥ 0 for M ≥ 8/√(c₈δ). P-R14 certified on c = 2
fields (d up to 2000): bound holds everywhere; TRUE swap ≈ 3.3/δ, positive even
at M = 59/99 (full-drift sharpening κ ≈ 3, band ~2.3/√δ, available). THEOREM S″:
single band M ≥ 8/√(c₈δ) replaces the three-regime map — swap and response
decoupled, no balance anywhere; covers all outer indices except the last
~8√(2i) ≈ O(√d). Residual tip = ONE shrinking cluster (m = M poles, span → 0) =
doc 34 Lemma R at m ~ √d; (L3) = its m = O(1) case. #145 CLOSED-as-merged into
#139. Chain now: B⁗ + S″ + #139(m~√d) + (F)-checks ⟹ (AMP-mono) ⟹ #138/#142 ⟹
(SPUR-R) on banked bricks. The exposed wall: (DISC-fin)-unconditional — even
off-line parity of the exact-FE truncation on dominated windows, from the
AFE/weld identity itself (#146 gradient = mechanism; doc 38 minors = instrument).

## 2026-07-04 (cycle 7, attack) — (DISC-fin)-unconditional opened: doc 43
The recast: ζ removed from the bridge's arithmetic input via the UNCONDITIONAL
classical AFE bound E(T) = O(T^{−1/4}) (Hardy–Littlewood symmetric form) —
"self-dominated" windows (min |g_N| > E(T) on ∂W + segment) are a property of
the finite object; target = (SD-parity): self-dominated ⟹ even off-line parity.
The cut: odd pair = TWO zeros straddling the line at ±η, forcing the line dip
|Z_g(t₀)| = η²|H| — (MOAT-shallow): η ≤ η₀ ~ T^{−1/8} pairs self-exclude
(segment fails self-domination; max-principle H-bound checked — no obstacle;
write-out queued). Deep pairs η ≥ 1/4 dig automatic wide moats (Bernstein slope:
valley width ≳ η). Open residue = mid-depth band η ∈ (η₀, 1/4): N^{−η}-atypical
valleys of the coherent sum — large-deviation regime (doc 12 salvage applies;
#146 coherence gradient is the measured mechanism). RS-tower sharpening: carrier
upgrades g^(k) with parity coherent along the tower (consecutive-level
transport, no ζ); one level with cofinal self-dominated windows suffices.
Run-5 q-trend puzzle resolved (failure lives on the segment). Measurement
launched (oddwindow_phase.py, P-D1 p-locus prior 0.5 / P-D2 depth prior 0.7):
odd-event RS-phase statistics on [1030,5000). Routes for the mid-band: p-locus
traversal / large-deviation exclusion / RS-tower balance.

## 2026-07-04 (cycle 7 addendum) — MOAT-shallow PROVED; p-measurement suggestive
Doc 43 §6: (MOAT-shallow) fully proved (max-principle two-zero bound
|Φ(1/2+it₀)| ≤ η²M_r/(r−η)²; corollary: η ≤ η₀(T,r) = (r/2)√(E*/M_r) pairs
self-exclude from (SD-parity)). Sweep [1030,5000): 28 new odd boxes (37 total);
n ≈ 19 clean refinements; mean |p−int| = 0.167 vs 0.25 (≈2.6σ, mass at
.003/.010/.019/.027/.870/.921/.938) — P-D1 FAIL AS REGISTERED (n < 25;
12 refine-failures = selection risk; one filter leak η = 0.000 at T = 1889).
P-D2 PASS: all η ∈ [0.039, 0.178] — no deep pairs; both shallow and mid-band
populated. Next: refinement fix + [5830,12000] extension + per-event η vs
η₀(T,r) classification (measures the exact residual wall).

## 2026-07-04 (cycle 8) — the wall measured: 8 events, all at the truncation seam
Fixed pipeline (guided refinement 76/81 clean; +44 events in [5830,12000)).
P-D1′ PASS (mean |p−int| = 0.1685, ≈4.9σ below uniform, n = 76); P-D2′ PASS
(max η = 0.178 — no deep pairs anywhere); P-D3 PASS: 89% of odd events SHALLOW
(proven lemma kills them); 8 mid-band survivors ≈ 1 per 1500 heights, ALL
lemma-margin ≤ 2.74, and 7/8 within 0.086 of a truncation transition (survivor
mean 0.056): mid-band mechanism = the N → N+1 birth jump. p-central family
(p ∈ [0.2, 0.8], 60% of heights): ZERO measured survivors in [200,12000].
#149 abstract-verified: Gonek–Montgomery IMRN 2013 studies exactly this family;
100%-on-line theorem needs N ≤ T^{o(1)} — AFE-matched regime open in print.
Residue: (1) no mid-depth pairs at p-central heights [hard core, now sharp];
(2) restricted-family cofinality [classical shape + doc 12 (D′) small-ball];
(3) G–M full-text mining. Doc 43 §§8–9; archives oddclass.out.

## 2026-07-04 (cycle 9) — MOAT⁺ proved; its no-go measured; the wall's final form
Route (3) executed: Lemma MOAT⁺ (multi-zero + r-free) proved — and refuted as a
survivor-killer (P-M1/P-M2 FAIL 0/8): survivors sit in wide zero-free gaps
(S-dial empty — pairs consume their flanking on-line zeros), M_r outruns
(r−η)² (r-dial flat), true error = 65–95% of declared E (P-M3 PASS — near-sharp
at transitions, |Ψ(p)| ≈ 0.92). Wall irreducible by window geometry ⟹ re-cut to
(MID-central): fixed Φ_N has no mid-depth pairs at p ∈ [0.2,0.8] of its matched
interval — one rigid polynomial per N; birth-jump mechanism lives at interval
ends. #149 mining now targeted (G–M fixed-N methods on the matched slice).
Next: zero-trajectory tracking across one N → N+1 transition (birth mechanism,
cheap); doc-12 small-ball for the polynomial valley; G–M full text.

## 2026-07-04 (cycle 3) — #147: the reversal is an edge/deficit quantity, NOT C₀²
Certification `computations/mwm/reversal_truth.py` (pre-registered, identity
validated against ledger_regroup to 4e−27; first-run sign slip caught by P-R4):
TRUE reversal at c = 2 (C₀ ≈ 1/2) is ≤ 0.23 vs cushion 2 — doc 37's 200C₀² off by
~250×. P-R3 FAIL (load-bearing): no C₀ scaling — reversal is an (F1)-edge
phenomenon: saturates in d (0.181→0.230, d=150→2500), decays sharply in i/d
(0.21→0.002 over θ=0.50→0.75), max at small s. Doc 39-reversal-edge.md banked:
budget-coupling kills termwise C₀² folding; continuum mechanism = log-compact
ahead field vs log-infinite behind field; §6 same-session correction — near/far
split refuted (per-pair credit/debit = 3/4 uniformly at s→0; the quarter-deficit
sums to the measured 0.21), replaced by single explicit bound Lemma H‡′ via chain
(†). Remaining for Theorem B⁗ (ΔG ≥ 7/4 for ALL C₀ ≤ 1/2, model class): continuum
evaluation of the H‡′ integral with Riemann remainder + the [CONJECTURE] exact-3/4
closed form. #143 (Lean stack) delegated to codex agent by Michael this cycle.

## 2026-07-04 (cycle 4) — #147 closed-form pass: Theorem B⁗ on paper (doc 40)
Exact continuum reversal derived: R(θ,c,s) = ∫ cξ[w(v)/(1+ξ) − w(u)/(1−ξ)]⁺dξ,
sup at s = 0 (discrete-level s-monotonicity, one-line proof). c = 2 collapses
algebraically: integrand 8ξ²/(4−ξ²)² > 0 (every pair net-loss in the limit),
antiderivative 4ξ/(4−ξ²) − log((2+ξ)/(2−ξ)) verified by differentiation;
R(1/2,2,0) = 4/3 − log 3 = 0.2347210447. Certifications (pre-registered): P-R9
quad = closed to 1.7e−19 (after repairing tanh–sinh endpoint cancellation — the
integrand is a difference of ~1/ξ terms; first quad at dps 30 was 1e−3 off);
P-R8 sup_{c≥2} R(1/2,c,0) = 0.247355 at c = 2.5 < 1/4 (interior max, matches
discrete c = 3 > c = 2 observation); P-R7 discrete d = 10⁴ = 0.234071, O(1/i)
remainder K ≈ 3.3, sequence converges to closed form from below. 3/4 conjecture
REFUTED-and-explained (uniform-bound artifact; exact near-ratio → 1). Theorem B⁗:
reversal ≤ B*(θ) + K/i, B*(1/2) < 1/4 ⟹ ΔG ≥ 7/4 − K/i for ALL C₀ ≤ 1/2 —
supersedes B″'s C₀ ≤ 1/10 and the c < 10 delegation. Remaining for 1→2 grade:
(B⁗-a) c-sup calculus lemma, (B⁗-b) remainder constant K write-out. Tip bonus:
R → 0 quadratically as θ → 1 — tip doubly protected; re-price #145 with it.

## 2026-07-04 (cycle 5) — (B⁗-a) PROVED, (B⁗-b) written out (doc 41)
(B⁗-a): Lemma P [PROVED, fully elementary] — (m,r)-frame with the constraint
collapsing to cosh m = e^r; positivity criterion (POS_c):
tanh(cr/2)coth(cm/2) ≥ tanh(m/2); c = 2 case ⟺ cosh m ≥ 1 (one line);
c-monotonicity via y/sinh(cy) decreasing ⟹ integrand ≥ 0 for ALL c ≥ 2 (no ⁺
clipping; class boundary is c > 1). Sup Lemma via the unified single-signed form
c∫2sinh²(z/2)csch²(cz/2) − c∫(1−e^{−z})½csch²(cz/2): independent c = 2
partial-fraction re-derivation of 4/3 − log 3 (6e−27); tail R ≤ 8.16/c² (c ≥ 3);
Lipschitz L₀ ≤ 1.6; certified grid 1601 pts: max 0.2473801 at c* = 2.5275, guard
0.24938 < 1/4 — P-R10 PASS. B*(θ) ≤ B*(1/2) < 1/4 for all θ ≥ 1/2.
(B⁗-b): (K1) Taylor, (K2) per-pair, (E1) ≤ (8.5/(ci))(1.5 + log(2.9i/c)) all
[PROVED]; (K3) digamma-frame Euler–Maclaurin: boundary ≤ (4/9)/i (supΨ = 8/9 at
corner (2,1), P-R12), curvature ≤ 0.24/i² (∫|Ψ″| = 80/27 at c = 2 exactly —
Ψ₂ convex — P-R13), frame gap C_ψ/i (common/asymmetric split route written,
C_ψ ≤ 6 named — the ONE remaining constant; empirical total 3.3/i). THEOREM B⁗
FINAL: ΔG ≥ 7/4 − err(i) on the whole c ≥ 2 class, ΔG ≥ 1 for i ≥ 200.
Next: C_ψ page; Lemma P → Lean brick; (m,r)-frame re-cut of Lemma D/E′ bands.

## 2026-07-04 (cycle 10) — birth mechanism FILMED; the program's halves converge
birth_homotopy.py (P-B1/B2/B3 all PASS): marginal-term homotopy λ·35^{−s} on
the two N = 35 survivors + p-central control. Pairs absent at λ = 0, born in a
filmed on-line collision (gap .295→.101 then count −2, η grows .037→.097);
control at p ≈ .45: the SAME term REPELS (gap .359→.440 monotone). Mechanism =
stationary phase: the marginal term's Z-perturbation 2λ|γ|N^{−1/2}cos(θ_γ −
t log N) is stationary exactly at t = 2πN² — attraction coherent near
resonance, averaged repulsion off it. (MID-central) now has a provable shape:
oscillatory-integral sign profile + selectivity (gap stiffness vs N^{−1/2}
push = doc-12 small-ball with a mechanism anchor). CONVERGENCE: pair birth =
local disc sign flip under one-parameter perturbation = the SPUR arc's native
tracking object (doc 25 clearance, doc 38 minors, B⁗/S″ march) — the arithmetic
wall's final form is a disc-stability statement in the analytic arc's own
format; arithmetic enters only via the explicit phase/amplitude of the marginal
term. Doc 45 banked. Next: σ(p) attraction-boundary run; stationary-phase
write-out; #149 full text.

## 2026-07-04 (cycle 11) — σ(p) refutes pointwise attraction; (HOLD) model fits to 5%
sigma_profile.py P-S1 FAIL (registered fail-branch): uniform p-grids (N=22,35;
19×3 windows) show NO systematic push-sign profile — push sign configurational
(first-order theory right); doc 45 §2's coherent-attraction explanation
superseded; the film's survivor attraction was selection. Replacement: the
HOLDING model — pairs are term-held (λ* ≈ 0.7, load-bearing) and persist only
while the marginal term's beat phase Δφ = 2πp² ≤ Δφ* ≈ 0.2 rad: all 8 survivors
have Δφ ≤ 0.21 (max possible 1.6); predicted p* = 0.18 vs observed 0.19. No
other term can hold (all ≥ 10 rad off their own resonance at p-central).
(MID-central) proof shape = (HOLD-lemma) [oscillatory bookkeeping on the
explicit pair equation, single-term share isolated] + (GEN-valley) [doc-12
small-ball; measured census: ZERO generic-type mid-band pairs in [200,12000]].
Doc 46 banked. Next: τ-share statistic at survivors; (HOLD-lemma) write-out;
T ~ 2–3·10⁴ census decade cross-check.

## 2026-07-04 (cycle 12) — the reach law: 8/8, min margin 1.10
tau_share.py P-T1 PASS (stronger than registered): reach = |P_N(ρ)|/|Φ′(ρ)| ≥ η
at ALL 8 survivors (ratios 1.10–2.11; transcription Φ_{N−1}(ρ) = −P_N(ρ) to
1e−37). (REACH) conjecture banked: mid-band pairs only within the marginal
term's reach ⟹ subsumes (GEN-valley) if proved. Structural identity: |Φ′(ρ)| =
2η|H(ρ)| exactly (two-zero factorization) ⟹ (REACH) ⟺ |P_N(ρ)| ≥ 2η²|H(ρ)| —
the SAME η²|H| object as (MOAT-shallow); and |P_N| off-line has near-zeros at
rate η·(beat phase) — the amplitude and phase windows are ONE object. Census
decade [20000,30000) running on pod (P-H1/P-H2 registered).

## 2026-07-04 (cycle 12 addendum) — (BVAL): the wall's irreducible form
Exact-identity chain: pair ⟺ B(ρ) = −P_N(ρ), B = Φ_{N−1}; |P_N| on line =
2|γ|N^{−1/2}|cos φ|; ⟹ mid-band pair REQUIRES an N^{−1/2}-deep off-line valley
of the ONE-TERM-UNDER-RESOLVED background at p-central heights. (BVAL) named as
the irreducible statement; film's λ = 0 frames are its first instance checks
(background clean at both survivors). p-mechanism derived at sketch grade:
resonance = frozen-maximum window of |cos φ| ⟹ shallowest-possible valley
requirement ⟹ pairs easiest there; off-resonance the joint (depth ∧ phase)
requirement is deeper on average. G–M connection exact: (BVAL) = one
quantitative step of their under-resolution rigidity (their 100% theorem is the
extreme case). Census decade P-H1/P-H2 pending.

## 2026-07-04 (cycle 13) — (BVAL) REFUTED; the sweep cascade found
bval_scan.py P-V1 FAIL (registered fail-branch): p-central background valleys
40–80× below threshold — and BOTH are genuine off-line zeros of Φ_{N−1}
(0.5156+3148.61i η=.016; 0.5976+7802.42i η=.098 MID-BAND). Under-resolved
carriers are NOT rigid; valleys are not rare. INVERSION measured: the matched
object's winding = 0 at both sites — the marginal term KILLED the background
pairs (2/2). Re-cut: (SWEEP) — each entering term sweeps predecessors' pairs
except in its frozen-phase resonance window; matched cleanliness = sweeping
success, not valley rarity. New irreducible: (SWEEP-margin) — every Φ_{k−1}
pair lies within P_k's reach, uniformly in the k-tower at p-central (measured
margins ≥ 1.10; no multi-sweep survivor in 14k units). The object is BUILT by a
sweep-and-create cascade — the weld as resolvent. Doc 47. Census decade still
running (P-H1/H2 pending). Next: tower census along k at fixed height;
(SWEEP-margin) collision write-out; reach lower bound via η²|H| + rotating
phase.

## 2026-07-04 (cycle 13 addendum) — out-of-sample census: p* replicates at 0.194
census2 [20000,30000): 11 new mid-band survivors (1/900 units). P-H1 FAIL as
registered (max |p−int| = 0.194 vs registered 0.18 — 8% too tight) but the
clustering is decisive: 11/11 within 0.194 (uniform: 3e−5); P-H2 PASS (deepest
η = 0.133 at |p−int| = 0.004). The sweep window p* ≈ 0.19 is SCALE-INVARIANT
(T ~ 10³ → 3·10⁴), consistent with a frozen-phase constant Δφ* ≈ 0.23 rad.
Doc 47 §5. [Also: doc 47/worklog had landed in computations/mwm by cwd drift —
moved/merged to the docs tree.]

## 2026-07-04 (cycle 14) — collision dichotomy EXACT (doc 48); Lean unit next
Doc 48: the sweep criterion made exact — W(v) = v²+η²+εq(v) real-on-reals;
kill ⟺ εq(0) ≤ −η² (IVT + Rouché count, NO local-model error); survive/deepen
⟺ εq > −η² on the real segment. One real number decides; phase enters solely
via sign(cos φ(t_B)). Explains film creation, doc 47 kills, σ(p) noise, frozen
window. Residue isolated: (DEEP-FATE) — wrong-sign survivors deepen to
η ~ N^{−1/4} in the local model yet the census has none (max 0.178/24k units):
the deepen branch must saturate/skew/die outside the disc — THE one question
for a computation. Next: Lean bank of doc 40 closed form (ReversalClosedForm).

## 2026-07-04 (cycle 14 addendum) — ReversalClosedForm.lean BANKED
Doc 40 §2's closed form machine-checked: RHTower/ReversalClosedForm.lean —
hasDerivAt_reversalAntideriv (the 8x²/(4−x²)² antiderivative identity on
(−2,2)), reversal_integral_eq_closed_form (∫₀¹ = 4/3 − log 3, FTC),
log_three_gt_thirteen_twelfths (via e^{13/12} < 3: exp_one_lt_d9 +
exp(1/12) ≤ 12/11 from add_one_le_exp — no fragile names),
reversal_edge_lt_quarter and reversal_integral_lt_quarter (the B⁗ cushion
input). Umbrella 8610 jobs, lint green, axioms [propext, Classical.choice,
Quot.sound]. Codex agent active in-tree (SpurMovingThreshold) — no collision.

## 2026-07-04 (cycle 15) — tower walk + the Gauss phase lattice (doc 49)
Iterated sweep = branching-absorption walk on η² (absorption = first-passage
at 0; shallowing branch noted — kills are NOT coin-flips). PROVED (Taylor):
the tower phase lattice φ_{N−m} ≡ φ_N − 4πpm − πm² mod 2π (+O(m³/N)):
quadratic Gauss structure in the cascade index. Derives: p≈0 anti-phase
alternation (marginal dominance now derived); FULL coherence at p = 1/4, 3/4
(m(m+4p) even ∀m ⟺ 4p odd — sharp new prediction; census clean there ⟹
collective kill zone if real); generic p: √-cancellation of the collective
push (classical Gauss/Weyl bounds; effective tail m ≲ N^{1/3} — SHORT sums).
De-randomized program: dichotomy [proved] + lattice [proved] + Gauss bounds
[classical] + creation-rate [small-ball at rate level]. The bridge's
arithmetic input has become QUADRATIC PHASES — Γ-θ/weld home ground.

## 2026-07-04 (cycle 15 addendum) — SweepDichotomy + GaussLattice BANKED; doc tree repaired
Repair: cwd-drift misplacements found via the user's commit — docs 45/46 moved
to the docs tree, doc 39's MISSING §6 (the near/far-split refutation) merged
from its stray fragment; only RESULTS files remain in computations/mwm.
Lean (per Michael's pointer to the sibling Weyl code — SatoTateMoment.lean has
the Weyl moment-criterion analytic backbone; Q62WeylDischarge is the elliptic
lane): two new RHTower bricks, umbrella 8612 jobs, lint green, axiom-clean:
- SweepDichotomy.lean — doc 48 §2 machine-checked: sweepW = v²+η²+εq;
  sweepW_kill (εq(0) ≤ −η² + positive edges ⟹ on-line zero each side, IVT);
  sweepW_survive (εq > −η² on segment ⟹ pair stays off-line).
- GaussLattice.lean — doc 49 §2 integer skeleton: pi_msq_phase_alternates
  (m² ≡ m mod 2: the p≈0 anti-phase); lattice_coherent_iff (m(m+a) even ∀m ⟺
  a odd: quarter-phase coherence at 4p odd — the sharp p = 1/4, 3/4 law);
  norm_geom_sum_le (unit-circle geometric bound — first Weyl-differencing
  ingredient; cross-referenced to SatoTateMoment's equidistribution side).

## Cycle 16 (2026-07-04) — sweep-cascade exhaustion pass (goal-locked)
- Doc 50 BANKED: lattice COLLAPSE (e^{−i(4πpm+πm²)} = w^m, pure geometric — no
  Gauss sum at lattice order); resonance denominator ‖1−w‖ = 2|cos 2πp|; Abel
  master bound a₀/|cos 2πp| (sharp); drift p_eff certified (P-L1..L4 PASS);
  RS-consonance (RS denominator = ours; stationary value πn₀ − 2πd² + π/8
  certified P-L5, error (2π/3)d³/N); Roy–You (2411.08364) full-text mined —
  their Thm 1.3 reaches matched regime, on-line bound dies in O(U log N):
  the mid-band lives inside the printed error term.
- Census graded (archived only): P-QP2 PASS decisive (0/19 near p = 1/2,
  null 0.004); survivor support = {d(p) ≤ 0.194}; tail-only law REFUTED
  (no re-appearance at 0.35); births 1-periodic (42 vs 14 /106).
- Doc 51 BANKED: de-randomized walk — rotation cannot close (frozen-alignment
  escape PROVED), drift is the de-randomizer; (DRIFT-dip) typed;
  (HOLD-phase) OPEN CORE typed; §9: slip identity (slip = 2πd², window =
  0.236 rad budget), reach coupling cos(slip)·R ≥ 1, naive corollary refuted,
  open kernel isolated to configurational |H|.
- Doc 52 BANKED: births = tangencies of A(t) = −2θ_RS − 2φ; A′ = −2θ_RS′ −
  2Re(F_N′/F_N); creation priced by RIGHT-of-line near-line zeros of the
  NAKED partial sum; (CR-density) typed; §8 audit: bare Jensen no-go recorded.
- Lean BANKED: CascadeGeometric.lean (lattice_collapse, norm_one_sub_exp,
  resonance_denominator, abel_geom_bound, collective_push_le, one_wrap_hit,
  survival_floor) — umbrella 8614 jobs, lint green, axiom-clean. Parallel
  agent's SweepCascade.lean (list-level localization) composes with it.
- OPEN, force order: (HOLD-phase) |H|-kernel; (DRIFT-dip) bookkeeping;
  (CR-density) via log|F_N| variance; (DEEP-FATE) sanctioned computation.
