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

## Cycle 17 (2026-07-04) — the four lemmas formalized + (DEEP-FATE) run (goal-locked)
- Lean BANKED (4 modules, umbrella 8618 jobs, lint green, axiom-clean):
  DriftDip.lean — (DRIFT-dip) core FULLY PROVED (drift_dip + excursion form:
  bounded-step angle walk provably dips (L+1)a/2 within one wrap; drift-robust,
  no lattice needed); HoldPhase.lean — factorization Z′(iη) = 2iηg(iη),
  kill-margin ⟺ cos(slip)·R ≥ 1, coherent accumulation ≥ half-mass;
  CreationRate.lean — finite Chebyshev, far-kernel ≥ −1/c, pricing pigeonhole;
  MidCentral.lean — assembly THEOREM: MidCentralInput (depth_pos + dip_kills +
  creation_rate) ⟹ survivors ≤ K, localized to the slip window; prefix-dip ⟹
  killed bridge into SweepCascade.
- (DEEP-FATE) RUN (deep_fate_tracker.py, pre-registered): P-DF2 PASS
  (runs ≤ 3N^{1/3}); P-DF3 PASS for resonant survivors (6/8 live exactly ONE
  entry epoch: N−1 online → N pair → N+1 online); P-DF1 FAIL informatively —
  the deepen branch is REAL in the over-resolved regime k > N (edge event
  reaches η = 0.425 ≈ N^{−1/4}, doc 48's scale) but SATURATES and dies within
  ~3.3·N^{1/3} entries. No accumulation anywhere. Doc 53 records adjudication.
- Doc 53 BANKED: assembly record; open content isolated to exactly TWO
  hypothesis fields (dip_kills amplitude floor vs |H|; creation_rate K).
- Next: (HOLD-phase) kernel = one inequality (amplitude floor via
  coherent_sum_lower across the window transition); partial-fraction module
  for Re(F_N′/F_N); K-counting in the 0.19-window through the deck relation.

## Cycle 18 (2026-07-04) — walk tier COMPLETE (goal: full MID-central)
- RotationDip.lean BANKED: sum_cos_closed_form (exact circle chord),
  exists_orbit_cos_ge (up-window hit ≥ cos(θ/2) within one wrap, M/M−1
  trick), rotation_dip (misaligned ⟹ first-wrap dip), pushSum bridges,
  birthKilled_of_rotation.
- PerturbedDip.lean BANKED: abs_cos_sub_cos_le; perturbed_rotation_dip
  (phase-error budget M·e₀); birthKilled_of_perturbed_rotation (envelope +
  drift budgets — dip_kills for REAL pushes); log_ratio_bounds;
  one_sub_exp_eq; polar_ratio_explicit (γ = β − θ/2 + π/2, r = 1/(2sin(θ/2))
  — alignment window explicit in (β, θ)). Umbrella 8620 jobs, lint green,
  axiom-clean. One transient sorry-draft caught and replaced same cycle.
- Remaining to full (MID-central): (T1) birth-phase supply (RS-theta
  expansion in Lean), (T2) per-entry dichotomy globalization (IFT), (T3)
  (CR-density) — open math. Walk tier has NOTHING left.

## Cycle 19 (2026-07-04) — (T2) general machinery complete
- DepthUpdate.lean + PairPeel.lean BANKED (8622 jobs, lint green, axiom-clean):
  exact walk update (zeros of v²+D = ±i√D), absorption form, center-over-
  cofactor, double-peel factored form via banked exists_peel with zero-free
  cofactor from order preservation, pair_peel_depth (η² = Z(0)/h(0)).
- Stirling audit (user question): NOT in mathlib (real asymptotic only),
  NOT in our trees; mathlib Complex.digamma stub EXISTS (new) — (T1)
  reframed to digamma vertical-line bounds from GammaSeq + log_ratio_bounds;
  π/8 rides abstractly. Task #163.

## Cycle 20 (2026-07-04) — (T1) bricks banked
- DigammaBounds.lean BANKED (8623 jobs, lint green, axiom-clean):
  digamma_apply_add_nat (iterated recursion — vertical bounds reduce to
  finite sums); re_inv_shift (vertical summand closed form); digamma_reflection
  (digamma(z) − digamma(1−z) = −π·cos(πz)/sin(πz), log-differentiated from
  mathlib's Γ(z)Γ(1−z) = π/sin(πz)).
- (T1) residual: ONE vertical-line asymptotic anchor for Re digamma
  (integral-representation grade, via Complex.Gamma_eq_integral +
  differentiation under the integral — named, not started).

## Cycle 21 (2026-07-04) — doc 54 endgame map + (T1-a) error mass
- Doc 54 BANKED: the complete residual between the banked stack and
  (MID-central), every remaining lemma in Lean-ready statement form:
  (T1-a) vertical_sum_log_bounds [elementary], (T1-b) trigamma series OR
  integral anchor [the ONE analytic input — anchor constant −γ never enters:
  θ″-grade suffices], (T2-a) order-1 instance data, (T2-b) Rouché count,
  (T3) (CR-density) [open math]. Dependency graph included.
- sum_inv_sq_add_le BANKED (DigammaBounds, 8623 jobs, axiom-clean, lint
  green): Poisson-tail error mass ≤ 1/t² + π/(2t) via the arctan telescope
  (FTC + interval monotonicity) — the error engine for (T1-a).

## Cycle 22 (2026-07-04) — (T1-a) vertical log comparison BANKED
- re_kernel_move_le + vertical_sum_log_comparison BANKED (DigammaBounds,
  8623 jobs, axiom-clean, lint green): the Re-digamma finite sums track
  ½·log((σ+N)²+t²) − ½·log(σ²+t²) with total error ≤ 1/t² + π/(2t),
  uniformly in N. Pointwise kernel move is PURELY ALGEBRAIC (no 2nd FTC):
  |u/(u²+t²) − x/(x²+t²)| ≤ 1/(u²+t²) via the numerator factorization.
- (T1) residual now = (T1-b) ALONE: the trigamma limit
  Tendsto (deriv digamma) (comap re atTop) 0 (anchor-FREE; θ″-grade),
  OR the integral anchor. Task #163 continues on (T1-b).

## Cycle 23 (2026-07-04) — DipKillsWiring: (T1) off critical path; honest terminus
- DipKillsWiring.lean BANKED (8624 jobs, axiom-clean, lint green):
  CarrierBirthData bundle + dipKills_of_carrierData +
  midCentralInput_of_carrierData + midCentral_survivors_le_of_carrierData.
  MID-central survivors ≤ K from concrete carrier data + creation bound,
  NO digamma anchor (θ_RS cancels in relative phases; step angles from banked
  log_ratio_bounds; slip elementary).
- HONEST TERMINUS: MID-central machine-checked-reduced to (R2) per-instance
  order-1 + Rouché certificates [execution, formalizable] and (R3) CR-density
  [OPEN mathematics]. The goal "fully proven" is blocked on (R3) being an open
  problem — no Lean closes it. All formalizable-without-solving-open-math is done.

## Cycle 24 (2026-07-04) — CR-density probed + precisely targeted (open core)
- cr_density_probe.py RUN (pre-registered): 3 signals SUPPORT CR-density being
  TRUE — SATURATION (count(c=2)=count(c=4): zeros don't accumulate AT the line),
  bounded near/far σ-density ratio ~2, N-stable slope κ~0.025-0.040. Small-N
  (≤28), preliminary but decisive on "true not false".
- Doc 55 BANKED: (CR-density) ⟸ (AC) small-ball anti-concentration of |F_N| on
  the line. SELF-CORRECTION (attack-as-false): the 4th-moment/Paley-Zygmund
  route was WRONG — it bounds the LARGE-value tail, near-line zeros are the
  SMALL-value tail. Genuine target = value distribution (Selberg-CLT-grade
  small-ball for Σn^{-s} in matched regime) — the frontier GM/RS leave open.
  2nd moment (MV mean value) is the Lean-tractable scale input.
- MID-central open core now cleanly isolated to (AC), numerically true.

## Cycle 26 (2026-07-04) — mollified dip scheme: (CR-density) re-routed through a subcritical kernel
- Doc 56 BANKED (rng-selected route, seed 1488608780175592697): the mollified
  dip scheme. Dip lemma [PROVED (paper), L²-only: CS+Fubini+Chebyshev-on-J];
  counting bookkeeping [PROVED (paper), Markov+Vitali]; MV L² supply (V_pred
  matches V_meas ≤2%); open kernel typed two strengths (K-bdd: meas{|F·M_y|≤r}
  ≤ Cr²U; K-mild: mean (−log|P|)⁺ = O(1)). Theorem: (K-bdd)+(K-mild) ⟹
  (CR-density) with ε(c) = O(√c).
- Certification RUN (pre-registered, runpod, N=50..400): P1 PASS (profile
  LINEAR, maxresid ≤0.148; slope → 1/12π per user-side asymptotic check —
  matches doc 55 §2's independent probe 0.025–0.040: two computations agree on
  the constant); P2 PASS (Q/r² ∈ [0.30,0.48] flat, N-drift ≤1.2×: (K-bdd)
  empirically TRUE, C ≈ 0.5); P3 PASS 1167/1167 (dip intervals at stated
  constants). Side-finding: sharp-μ mollifier V GROWS (2.6→4.0); BV taper
  stabilizes (→2.48) — BV is the theorem object. Winding flag resolved
  (clockwise-contour sign artifact; dense reseed −11% dedupe correction).
- (AC) of doc 55 REFUTED as typed (addendum appended): Harper better-than-√
  cancellation ⟹ typical |F_N| = o(√logN) ⟹ η(λ)→1 at rms scale. The
  mollified (K-bdd) is now the unique living value-distribution route to (R3).
- Doc 57 BANKED (consumer audit): MidCentralInput takes K RAW (no ε-limit in
  the formal skeleton); slip bands are ≍N-length BLOCKS (dp/dT = 1/4πN) ⟹
  traversal must be local; NEW: transport dichotomy (deep survivor ⟹ ζ pair
  by Rouché ⟹ RH forces depth shrinkage ≲ T^{-1/8}, census consistent) + the
  level-shift dodge typed (EPH lemma-shape: ephemerality in the level index,
  measured P-DF3, would collapse the budget to Tier 0 — (CR-density) exits the
  critical path if (EPH) lands). Three-tier budget verdict recorded.
- Bottcher/Brolin/WeylLemma.lean audited for reuse (user pointer): ContDiffBump
  mollification + convolution_mollN_le = the Esseen-smoothing bricks for
  formalizing (K-bdd) consumption; harmonic_reproduction/poissonInt = the
  per-cell Jensen cap substrate. Recorded for the MollifiedDip Lean arc.

## Cycle 26b (2026-07-04) — budget audit, kernel attack map, cofinality, chain audit
- MollifiedDip.lean BANKED (umbrella 8626 jobs, lint green, axiom-clean):
  sublevel_half_of_average (interval Chebyshev), dip_measure_lower (doc 56 §2
  conclusion form), gapped_Icc_disjoint + separated_dips_count_le (Vitali
  counting bridge), sliverCount_le_of_kernel ((K-bdd) ⟹ count, the doc 56 §4
  endpoint). Route B's entire counting layer is machine-checked; the kernel is
  the sole hypothesis.
- Doc 57 BANKED (creation-budget audit): consumer takes K RAW; slip bands are
  ≍N-blocks; NEW transport dichotomy (deep survivor ⟹ ζ-pair per instance ⟹
  RH forces depth shrinkage ≲ T^{-1/8}); (EPH) level-shift dodge typed —
  Tier-0 budget would remove (CR-density) from the critical path.
- Doc 58 BANKED (kernel attack): Esseen interface; degree-2 wall no-go (no
  moment expansion crosses D = 2 in matched windows, any θ, any U ≤ T);
  ergodic×transfer split: (K-bdd-∞) with full proof skeleton (two-phase
  co-area + dyadic-scale induction + Baker-effective base case — the {σ_p}
  transcendence toolbox doing constructive work inside the bridge) ×
  (SPEC-decay) (random-model spectral smoothness); P4/P5 pre-registered, not run.
- Doc 59 BANKED (cofinality): (C1) PROVED-sketch — mean-Littlewood bound
  meas{|g_N| ≤ E*} ≤ C·loglogT/logT per unit via rectangle Littlewood to σ=3 +
  Jensen; retires the (D′) import for the measure clause; vertical threading +
  almost-all-gap test points closed. Residue (C2) horizontal threading — route
  1 (strata match: Ingham for w ≫ 1/logT, windows at w ≍ 1/logT) is an audit,
  not analysis.
- Doc 60 BANKED (full-chain audit): trunk T1–T4 Lean-anchored; Route I parked;
  Route II spine W1–W11 with per-link status; open cores exactly five —
  (CR-density) [two engines], (EPH), (C2), (WR-core), (HANK-fin)_k.
  Consumption order: (EPH) → (K-bdd-∞) → (C2) → (SPEC-decay) → (HANK-fin)_2.

## Cycle 27 (2026-07-04) — doc 55 §§7-8 lead composed: the self-mollified carrier (Route C)
- Doc 55 reread (user flag): Langevin closed form ε(c) = L(c)/4π, ζ(1−2k)
  Taylor tower, variance law ε′_W(0) = Var_μ/π, Casimir strong form refuted,
  and the NEW chirality discovery (decreasing carriers empty the RIGHT
  near-line strip ×8–13, GAF-blind) + E–K design lead.
- Doc 61 BANKED: (i) self-mollification — F_W/W(0) = 1 + G_W is Route B's
  normal form with NO mollifier; MollifiedDip.lean consumes the designed
  carrier verbatim; kernel becomes (SM-bdd) with a designed-small constant;
  (ii) chirality mechanism [CONJECTURE]: mean-share gradient m²/K growing in σ
  (GAF-with-mean e^{−m²/K} factor) — pre-registered P-SM1/2/3 sweep;
  (iii) calibration: elementary E–K reaches only σ ≈ 1 — sliver stays
  kernel-class; the design buys layer-removal + constant-collapse +
  smoothed-AFE E_W(T); (iv) block-static weights as the tower-compatibility
  cut (damped-edge entries at birth scale).
- Doc 60 addendum: Route C inserted at W5; consumption order updated.
- meanshare_probe.py LAUNCHED (runpod): α-sweep W²_α = (α+1)(1−y)^α,
  CCW winding, both sides, c ∈ {1,2}, N=40, U=240.
- P-SM ADJUDICATED (meanshare_probe, archived): P-SM1 PASS decisive — right
  sliver EXACTLY EMPTY from mean-share ≈ 0.54 (0 zeros/240 units at c≤2,
  left side 47); P-SM2 fails-as-registered in the STRONG direction (measured
  suppression beats the crude e^{−m²/(K−m²)} law 4–50× — gradient form is the
  correct one); P-SM3 variance law holds α ≤ 2, breaks α = 4 (both-sides
  emptying, GAF regime exit). NEW typed target (EK-sliver): zero-free right
  sliver for decreasing-weight carriers at ς ≥ ς* — would give creation K = 0
  (midCentral_empty grade) with NO kernel; Abel-mixture (positive mixture of
  sharp partial sums) is the proof handle; next number: ς*(N) scaling.

## Cycle 28 (2026-07-04) — (EK-sliver) as obstruction; mechanism identified = order/Cesàro depth
- Doc 62 BANKED: Abel reformulation [PROVED]: F_W zero ⟹ 0 ∈ conv{Z_n} (hull/
  half-plane obstruction — endpoint event → spread event; E–K = degenerate
  case); Cesàro hierarchy [PROVED, iterated Abel]: convex decreasing weights
  ⟹ zero forces 0 ∈ conv{Cesàro means}; m-fold monotone ⟹ (C,m)-hull;
  mean-share and order-structure = two ends of one ladder; Spitzer-winding
  erosion of the m=0 test predicted BEFORE data.
- P-SC sweep RUN + ADJUDICATED (N ≤ 400, α ∈ {1,2,4}, 0 bad contours):
  P-SC1 = ORDER branch decisively (α=2 emptiness persists to N=400 while
  share decays 0.54→0.385; share-matched prediction 13 zeros, measured 1);
  P-SC2 fails-as-registered exactly as pre-recorded (m=0 hull erodes 57→47/60,
  weak necessary condition) while exploratory (CES-1) is stable: right
  60/60/60/58 vs left 51→36; the 2/60 CES-1 failures at N=400 match the single
  measured zero — obstruction accounting closes. P-SC3: rate N-stable at
  fixed α; invariant = weight order, not share.
- NEW single core for Route C: (CES-1) — winding suppression of the
  Cesàro-averaged matched walk (classical-probability shape; dpoly supplies
  exact L² data). Consumption: exceptional-set count = K via MollifiedDip
  layer; K = 0 where unconditional. ς*(N) question DISSOLVED (no share
  threshold; the invariant is Cesàro depth, N-uniform).

## Cycle 29 (2026-07-04) — (CES-1) random-model argument banked; conjecture corrected; explicit K
- Doc 63 BANKED: EMA/OU representation [PROVED (model)]: Cesàro in log-clock
  = unit-bandwidth EMA, dZ̄/dθ = Z − Z̄, deviation D = OU(1); angular-variation
  density ≲ θ^{−1/2}. ATTACK-AS-FALSE on the session conjecture: "finite
  expected variation" FAILS (TV ≍ √logN); the finite invariant is the
  NEAR-ORIGIN PASS COUNT ≍ logloglog N (dyadic capacitance). Model law:
  δ₁(N) = q₀(a₀ + a₁·logloglogN); m-dial δ_m ≈ q₀^{m−1}δ₁ — m = 2 pins the
  exceptional density below any fixed ε₀ for all sub-astronomical N. First
  explicit K: K_m(N) ≤ δ_m(N)·U·logN, measured calibration q₀a₀ ≈ 0.03 (m=1).
  Transfer NOT degree-2-walled: all functionals quadratic in monomials —
  MV/dpoly grade; typed transfer lemma = block Paley–Zygmund + chaining.
- P-CES2 RUN + PASS (ces2_probe, archived): right m2 60/60 at ALL N; left
  m2 > m1 everywhere (59/56/57/56 vs 52/46/52/47); falsifier silent.
  P-CES1b vacuous (0 m1-fails in 240 fresh samples ⟹ fail rate ≲ 1%).
  Order-2 designed carrier: measured right exceptional density 0/240 pooled.
- Route C status: model-grade K explicit; remaining to theorem-grade =
  §5 transfer lemma (second-moment technology) + Lean of the discrete EMA
  recursion + doc 62 §1 hull exclusion (both Finset-algebra grade).

## Cycle 30 (2026-07-04) — transfer write-out, Lean CesaroHull banked, census: falsifier FIRED productively
- Doc 64 BANKED: the transfer lemma write-out — MV supply exact for the Fejér/
  triangular Cesàro field (covariance, OU deviation, 4th moments off top
  block); occupation-to-pass conversion; residual input typed (TRI-bdd);
  theorem-shape K₁ ≤ C(loglogN)^{3/2} conditional (moments-only price √loglog
  over model).
- CesaroHull.lean BANKED (umbrella 8627 jobs, lint green, axiom-clean):
  abel_pos_mixture (doc 62 §1 exact), pos_mixture_ne_zero (hull exclusion),
  carrier_ne_zero_of_psum_halfplane (m=0), carrier_ne_zero_of_cesaro_halfplane
  (m=1 — the (CES-1) consumer), cesaroPsum_step/speed (exact discrete EMA).
  Route C machine-checked from the obstruction down to midCentral's creation
  bound; sole analytic input = the confinement/pass bound.
- P-TL census RUN (N ≤ 4·10⁴, 1200/side): P-TL1 FALSIFIER FIRED — right m1
  rate rises ×73, triple-log law DEMOTED (small-L heuristic). P-TL2 PASS
  (left linear in loglogN, slope 0.21, residuals <0.01). P-TL3 corrected:
  m-dial ratio CONSTANT ≈ 1/3 per level (0.30/0.36/0.34). Corrected law:
  ln δ₁ linear in 1/loglogN (slopes ≈ −13) = ANGLE-DIFFUSION Gaussian tail
  (D ≈ 0.19/e-fold); global-support hull obstruction degrades as N→∞.
- Design fix forced + registered (HULL-taper, prior 0.7): plateau+taper
  carriers (ΔA support = bounded log-arc) ⟹ N-uniform confinement; same
  object as doc 61 §4's block-static tower AND the smoothed-AFE edge — three
  pressures select one design. Corrected analytic target: bounded-arc
  confinement (strictly easier than the killed global form).

## Cycle 31 (2026-07-04) — plateau split + Selberg endgame: Route C's K on one free z-score
- plateau_split BANKED (CesaroHull.lean, axiom-clean, lint green): zero of a
  plateau+taper carrier ⟹ ‖S_{N′}‖ = ‖T‖/A₀ — the counting route needs no
  hull at all; composes with MollifiedDip's sliverCount_le_of_kernel.
- (HULL-taper) probe RUN + ADJUDICATED (1500/side/N ≤ 4e4, archived): m0
  clause FAILS mildly (2.9→4.9% — bounded arc helps ×3 vs full support but
  raw hull not N-uniform); arc-Cesàro m1 PASSES N-uniform (0.27/0.73/0.40%,
  no trend); arc m-dial ≈ 1/8. THE FINDING (exploratory anchor measurement):
  P(|S_{N′}| ≤ 1) ≈ 0.47 FLAT across logN′ = 5→9.6 — the matched-length sharp
  sum is SELBERG-LOGNORMAL (median-1; AFE made distributional). Gaussian-scale
  decay expectation refuted; m0-rise mechanism explained (constant anchor
  mass at O(1)).
- Doc 65 BANKED: the split + Chebyshev(MV) counting chain; the Selberg
  endgame: λ₀ = e^{−z₀√(½loglogT)}, ℓ = Φ(−z₀)λ₀² ⟹ K ≤ 2Φ(−z₀)·conv·UlogN
  with z₀ FREE — Tier-1-grade smallness, uniform in N, conditional on ONE
  input (SEL-PS): fixed-z-score Selberg-CLT left tail for the matched-length
  sharp sum (ζ-instance = Selberg 1946 unconditional; truth at matched length
  measured flat). The weakest anti-concentration any route has needed.
- Openings: mine Selberg/Steinhaus-CLT literature for the partial-sum CLT
  (method research); back-solve z₀ from the deck margin (bridge demand meets
  route supply in one number); the lognormal two-tails card (self-domination
  = right tail, creation = left tail of the SAME law).

## Cycle 32 (2026-07-04) — ideation: quantum-walk collision banked (doc 66)
- User-injected wild-analogy collision adjudicated: QW-as-vocabulary false
  (affine non-unitary update, diffusive in log-clock); QW-as-structure lands
  on three anchors — kicked-rotor/quantum-resonance dictionary for the
  cascade lattice (doc 50's collapse/denominator = dynamical localization,
  PROVED; survivor support = resonances, MEASURED); AFE = DFT self-duality
  with matched length as fixed point (Landsberg–Schaar as the classical home
  of doc 50's collapse); m-dial = inverse-Grover mean-projection.
- HIT: [CONJECTURE] the measured birth phase π/8 (P-L5) = half the
  Fresnel/Maslov π/4 = the metaplectic phase of the ℤ₂-tower's square-root
  weight (theta-multiplier 8th roots). Cheap symbolic check queued (re-run
  P-L5 stationary phase with symbolic Fresnel phase). If confirmed, (T1)
  birth layer becomes structural and the cascade constants become
  reciprocity phases.

## Cycle 33 (2026-07-04) — mining fired attack-as-false; (SEL-PS) closed UNCONDITIONALLY (ε₀-dial)
- Executing "mine Selberg's method": re-derivation exposed a SIGN/ARG GAP in
  doc 59 §1's Littlewood sketch (horizontal argument terms are O(U·density·
  width) — same order as the zero-sum, cancel only to fluctuation order).
  CORRECTION appended (doc 59 §4); conclusion survives via the repair.
- The repair is stronger than the mined target: window Jensen-function
  CONVEXITY + tangent at σ=3 gives Φ(σ) ≥ −1.36 on [½,3] unconditionally
  (no zero data — zeros only add convexity). With Jensen/MV upper side +
  Markov: (TIGHT) meas{|S_{N′}| ≤ λ} ≤ U(½loglogN+C)/log(1/λ).
- Doc 67 BANKED: (TIGHT) + plateau_split [Lean] + MV-Chebyshev + dip layer
  [Lean] ⟹ K_designed ≤ C′·ε₀·U·logN, ε₀ FREE, UNCONDITIONAL (taper
  ℓ = ε₀λ₀², λ₀ = e^{−(½loglogN+C)/ε₀} — a power of 1/logN; explicit onset).
  Selberg CLT demoted to optional refinement (milder tapers). Route C's
  creation-side analytics CLOSED at sketch grade; residue = write-out pass +
  tower integration + (SWEEP-margin) number (meeting equation doc 67 §6).
- Mining record: Selberg CLT + near-line expansions in print for ζ
  (arXiv:2101.00632, 2301.01925 — σ = ½+(logT)^{-θ} covers sliver
  abscissae); deterministic matched-length partial-sum CLT NOT in print —
  open ground, no longer load-bearing. [CHECK at promotion]
- Tasks: #12 closed (resolved); #13 opened ((SWEEP-margin) write-out +
  back-solve ε₀* — the one number left in the meeting equation).

## Cycle 34 (2026-07-04) — (SWEEP-margin) written; the meeting is an absolute constant; THE BYPASS
- Doc 68 BANKED: M_deck extracted as SUBCRITICALITY — r(N) ≤ c_deck·logN
  (placement bookkeeping: isolation windows H_iso ≍ C₁/logT, edge-threading
  via corrected (C1); the margin was never in-N smallness). Supply is
  p-UNIFORM (plateau split never used p-centrality — the resonance-window
  boundary term is suppressed at source). Meeting: ε₀* = c_deck/C′, absolute;
  both factors extraction-grade.
- THE BYPASS [REDUCTION-conjecture, doc 68 §4]: the designed carrier has
  ε₀-few sliver zeros at EVERY height directly — for the designed tower the
  RH₂ chain drops the entire cascade tier (no dichotomy/walk/DRIFT-dip/
  HOLD-phase/CR-density/EPH): ladder → window relation → (DOM-W) → (MOAT-W)/
  (DEEP-W) → plateau-split bound → cofinality → isolation. Transplant reads:
  MOAT-shallow is literally carrier-generic (doc 43 §6); DEEP-pair argument
  shape-generic (modulus asymmetry + Bernstein — weight enters via bounded
  norms). Residual: (DOM-W) smoothed-AFE for the weighted completion
  [classical-shaped], constants pass (C′, c_deck), C2, k≥2 rungs.
- Doc 60 §7 addendum: Route C-direct spine recorded; cascade tier
  re-classified as explanation layer. Doc 59 correction cross-referenced.
- Tasks: #13 CLOSED (margin written; meeting = absolute constant); next
  executable = (DOM-W) + constants pass.

## Cycle 35 (2026-07-04) — (DOM-W) closed in threading form; constants pass: ε₀* ≈ 1/512; the onset finding
- Doc 69 BANKED. (DOM-W) [PROVED-sketch]: D_W = taper-difference polynomial
  (E|·|² ≤ ℓ by MV) + sharp-AFE error; threading form: off (ε₁+ε₀)U,
  |D_W| < τ < |Z_W| — the SAME (TIGHT) lemma prices the carrier-largeness
  clause (carrier-generic, σ-uniform). No new AFE machinery; IK-class
  smoothed AFEs = luxury upgrade only. No-tension confirmed at inequality
  level: all design pressure lives in the onset.
- Constants pass (first-pass): c_deck ≈ 1/16 (H_iso = 8 spacings);
  C′ ≤ 32 (split 2 × dip 12 × dyadic 4/3); ε₀* = c_deck/C′ ≈ 1/512.
- ONSET FINDING (honest catch): (TIGHT)-only onset N ≥ e^{~650} —
  asymptotic spine closed unconditionally past it, ALL-heights not.
  Doc 67 §3's demotion CORRECTED: (SEL-PS)-lognormal is load-bearing for
  the finite range. With CLT-grade λ₀ at z₀ ≈ 3.1: onset N ~ e^{14},
  T ~ 10^{13} = the classically VERIFIED range boundary — verified range
  below + CLT tower above, no gap (first-pass constants; verify at
  promotion).
- Force order now: (SEL-PS)-lognormal [single load-bearing analytic item;
  = Selberg-method moments; its 2nd moment doubles as doc 59 route-3
  defect variance — prove once, consume twice] → promotion pass →
  C2 → k≥2.

## Cycle 36 (2026-07-04) — (SEL-PS) CLOSED BY TRANSFER: the R–S block pins the carrier's line profile to ζ; Selberg 1946 polices creation
- Doc 70 BANKED. The load-bearing discovery: on Riemann–Siegel blocks
  B_n = [2πn², 2π(n+1)²) the completed matched truncation g_N (doc 22's
  anneal object) has line profile = ζ(½+it) + O(t^{−1/4}) [KNOWN,
  Titchmarsh 4.15] — so the designed completion Z_W = A₀·g_N − completed-Δ
  (Δ = the SAME taper-difference polynomial as doc 69's (DOM-W) defect)
  has NO independent line statistics. Small-ball transfers:
  meas{|Z_W(½+it)| ≤ A₀λ₀} ≤ Selberg-1946 left tail + 4(ℓ/λ₀²)U.
  K_designed ≤ C′(Φ(−z₀)+o(1))·U·logN, z₀ FREE, unconditional — the
  doc 65 §3 endgame FIRES; the not-in-print partial-sum CLT is BYPASSED.
- Attack-as-false catch (structural): fixed cutoff N′ per U≍T window FAILS
  (mismatch to R–S sum has rms ½log2 — above λ₀-scale). Forced fix:
  re-anchor the tower per R–S block (matched length exactly constant on
  B_n). Native-object bonus: R–S block = tower epoch; t = 2πn² is the
  lane's constraint clock-surface.
- Off-line zones for (C2): zone M (σ−½ ≥ 3loglog/logN) damped-mirror
  transfer + classical 2nd moment [CHECK Tsang 1984 uniformity]; zone N
  (narrow, O(loglog) grid pts) by (C1) alone. (C2) route 3 met at
  strength O(loglog) vs demand O((loglog)²); strata-match audit (#10)
  demoted to optimization. Defect 2nd moment at the line: O(loglog) by
  3-range assembly (Selberg 2nd/4th moments + Boutroux–Cartan deep tail).
- Lean BANKED: SelbergTransfer.lean — norm_add_sq_unit_conj_eq (half-sum
  identity), norm_add_sq_unit_conj_le, sublevel_split_subset,
  sublevel_transfer_subset, blockwise_transfer_measure_le. Umbrella green
  (8629 jobs), lint passed, all axiom-clean [propext, Classical.choice,
  Quot.sound]. No computation this cycle: every link is inequality-chained
  from classical theorems (nothing theory-unpredictable to measure).
- Residue is EFFECTIVITY, not existence: (i) Berry–Esseen rate for
  Selberg's CLT at z₀ ≈ 3 (at loglogT = 3.4 the correction is O(1)-grade —
  it decides the onset); (ii) explicit R–S error constant [Gabcke];
  (iii) MV block constants + C′ under χ′-terms. Bracket: any reasonable
  effectivization lands the onset in [10^13, ~10^18] vs (TIGHT)-only
  e^650. Tasks: #15 CLOSED; #16 opened (effectivization pass); #10
  demoted-optional.

## Cycle 37 (2026-07-04) — Effectivization pass, literature half: mining + z₀-optimization + three corrections
- Doc 71 BANKED. z₀-optimization (z0_opt.py, archived computations/): design
  triple at the MOMENT tier = (z₀*, ℓ*, N₀*) = (3.86, 8.1e−9, e^18.6),
  onset T₀ ~ 10^17; flat optimum over moment orders 10–16; α ≈ 43% tail /
  57% taper. Full tier table in doc 71 §3.
- Two delegate literature agents completed (survived a mid-run session
  crash; transcripts salvaged by bounded JSONL extraction — did NOT re-run).
  Citations in doc 71 §1 (all read from fetched sources; Gabcke thesis
  itself 403-blocked, quoted via Kuznetsov arXiv:2312.03261).
- THREE CORRECTIONS the mining forced (doc 71 §6; the wins-and-catches are
  co-equal per the no-terminus rule):
  (i) (EFF-M14) confirmed NOT in print — no numeric ∫(log|ζ(½+it)|)^{2k} for
      any k≥1. Strongest adjacent = Tsang 1986 for S(t)=Im (arg), constant
      un-numerized. So the task is a real effectivization, not a citation.
  (ii) Tier G (Gaussian) is UNUSABLE at finite heights, two independent
      reasons: uniform-in-y Selberg CLT (Selberg 1992/Tsang 1984, via Ivić
      math/0312097) has additive error O((logloglogT)²/√loglogT) = O(1)-grade
      at onset (~400× the 1/512 target), AND its constant isn't numeric.
      Finite-height design is MOMENT-forced — upgrades doc 71 §4 reading 1
      from suspicion to literature fact.
  (iii) Rigorous verified boundary = 3·10^12 = 10^12.48 (Platt–Trudgian 2021,
      interval arithmetic); Gourdon 10^13 NOT interval-certified. Doc 69 §4's
      "10^13, no gap" coincidence CORRECTED: M14-tier onset at ε*=1/512 is
      10^17 (gap +4.5 orders); closing to 3·10^12 needs ε* ≈ 1/32 = factor
      ~16 in c_deck/C′ (not 8). No-gap now a TARGET = (EFF-M14) + 16×.
- ONE clean win (iv): R–S floor constant now NUMERIC — |ζ−g_N| ≤
  1.463 t^{−1/4}+0.127 t^{−3/4} (t≥200, Hiary–Patel–Yang 2024 / Revers 2026),
  <0.127 t^{−3/4} with C₀ (Gabcke). Resolves doc 70 §6's [CHECK Gabcke];
  spectator confirmed (λ₀/floor ≈ 65 at M14 optimum). Doc 70 §6 flags (i),(ii)
  updated to RESOLVED.
- Corrections propagated to doc 69 §4 (inline) and doc 70 §6. Task #16
  literature half DONE; analytic half (EFF-M14 proof + Lean) NOT started per
  user hold. No fresh computation beyond the deterministic optimization
  (nothing theory-unpredictable to measure this cycle).

## Cycle 38 (2026-07-04) — (EFF-M14) attacked and dissolved: two walls, the thickness dodge, the sharp-truncation collapse, and a 5/5 probe
- Doc 72 BANKED. Attack-as-false on (EFF-M14) BEFORE proving it found TWO walls:
  (W1) the ZERO-DIP FLOOR — meas{|ζ(½+it)|≤λ} has a linear floor c_fl·λ from
  on-line zeros that dominates the lognormal tail at design depth; missing
  from docs 65-71's small-ball accounting. (W2) the FINITE-HEIGHT MOMENT
  WALL — Gaussian 2k-moments need s₁ ≫ k²s₂; at X^{2k} ≤ T, T ~ 10^17,
  2k=14: s₁ ≈ 1 ≪ 22 — the M14 tier was a fiction at its own onset; honest
  orders are k ≤ 3. Degree-budget principle: at T ~ 10^13 any polynomial
  method owns only degree ~4 on the dominant small-prime block.
- THE COLLAPSE: sup-norm taper accounting ⟹ taper VESTIGIAL ⟹ carrier =
  the sharp exact-FE truncation g_N (doc 22's anneal object). Domination
  trivial (explicit R–S, no (DOM-W) at all); creation = thick-dip count of
  ζ's own small values; onset = R–S validity T₀ = e^{4A}, A = log(1/λ₀).
  Docs 61-71's design scaffolding (plateau split, taper, ℓ, α) removed.
- THE DODGE (Lean BANKED, ThickDips.lean, 5 thms axiom-clean, umbrella 8631
  green, lint passed): thickPart + thick_dips_count_le (counting vs the
  h-locally-thick part only — NO measurability of E needed, restrict-trick)
  + thickPart_union_measure_le (Fubini-Markov: floor excluded at cost 8) +
  window-mass measurability/Fubini. Typed residue (FLAT-ZERO).
- PROBE 5/5 (pre-registered §6, run on runpod, validation vs mpmath 2e-6,
  archived probe_floor.{py,json}): c_fl = 0.61/0.64/0.68 at 10^{6,7,8},
  FLAT in λ over 1.5 decades; harmonic zero-sum = small-ball slope to THREE
  DIGITS (0.610/0.609 etc) — floor mechanism exact; zerocomp = 100% at
  λ≤0.05 (floor is the whole story at depth); thick-fraction ≈ 1% at design
  λ₀ (dodge removes ≥99%); σ² = ½loglogT + 0.65 (stable offset); moment
  corruption μ₄/3σ⁴ ≈ 1.5, μ₆/15σ⁶ ≈ 3.6-4.1 (Wall 2 confirmed live).
- Corrected design point (doc 72 §8): first-pass k=3 stack A ≈ 8.8-9 ⟹
  T₀ ~ 10^{17.5}; optimization headroom → [10^15, 10^18]; the 3·10^12
  meeting = (TAIL-6): certified meas{log|Z| ≤ −6.1} ≤ 2e-4·T at T ~ 3e12 —
  truth measured ~1e-4 (fine), low-moment Markov is the lossy tool. Named
  routes: non-polynomial input (effective equidistribution of the 168-cosine
  small-prime block) or constant harvest. Dead recorded: mollified detector
  (2×), (EFF-M14)-as-specified, Chebyshev taper pricing.
- Tasks: #16 CLOSED, #17 CLOSED (dissolved into doc 72's re-cut), #18
  opened ((EFF-M4)+(EFF-E)+(TAIL-6) instrument). No terminus: the carrier
  search is OVER (g_N), everything left is ζ's own value distribution.

## Cycle 39 (2026-07-04) — the certified-tail calculus: (EFF-M4/M10) closed exactly; Christoffel upgrade; (TAIL-6) priced to a factor 4-8
- Doc 73 BANKED. (EFF-M4/M10) CLOSED at exact-numerics grade: ReP_X
  (X = T^{1/5} = 313 at T = 3e12, 64 primes, support |ReP| ≤ 8.401) has
  EXACT rational cumulants (κ₄(cos) = −3/8, κ₆ = 5/4, κ₈ = −1155/128, ...)
  and a SUB-Gaussian ladder at every order: m₄/G = 0.945, m₆/G = 0.848,
  m₈/G = 0.727, m₁₀/G = 0.598, m₁₂/G = 0.473. Wall 2 half-reversed:
  collisions LIGHTEN (κ₄ < 0); corruption only pushes ratios below 1.
- SPACING-MV: the actual Montgomery–Vaughan (per-frequency δ_N ≥ 1/2N;
  the 1/N in |c_N|² cancels δ⁻¹) doubles the degree budget: 2k ≤
  2logT/logX = 10 certified (rel. transfer err 2e-4 at k=5; k=6 fails).
  Corrects doc 72 §2's naive X^{2k} ≤ T.
- Chernoff ceiling exact: P(ReP ≤ −4.1) ≤ 2.5e-5, ≤ −6.1: 2.3e-14
  (support-edge collapse) — but certified Chernoff dies at v ≥ 1.2
  (exp-truncation within degree budget); ladder methods win.
- CHRISTOFFEL–MARKOV UPGRADE (new instrument): sharp one-sided moment-
  problem bound 1/K_n(−a) via one Hankel Cholesky of the exact ladder:
  deg-10 at a = 4.1: 1.06e-4 (×5 better than single-m₁₀ Markov; only
  ×3-12 above Gaussian truth at z ≈ 3.5-4 vs ×30-60 for single-moment).
  Prime chunk of (TAIL-6) CERTIFIED under budget with s_B = 2.0 to spare.
- (EFF-E) demand made exact — the VARIANCE MAP at 3e12: p ≤ 313: 1.01
  (deg 10 ✓); (313,10⁴]: 0.235 (deg 6); (10⁴,10⁶]: 0.205 (deg 4);
  (10⁶,√T]: 0.22 (Chebyshev-grade — the leak); offset 0.65 (thin-zero
  mass? [CONJECTURE], decisive + measurable: rerun probe m₂ excluding dip
  nbhds). Joint degree budget SHARED: Σ2k_j·logY_j ≤ 2logT (block degrees
  trade off); union-split preserves the Gaussian exponent only at
  per-block Gaussian grade.
- (TAIL-6) ADJUDICATED: assembled certified stack ~1e-3 at A = 6.1
  (near-optimal for the moment/degree class: union-vs-joint ×10-30 +
  shared budget); target ε₀*/8 = 2.4e-4; GAP = factor 4-8, ALL in named
  constants (thickness 8→~3, ε₀* 1/512→1/256, allocation). Tonight's
  movement: 5.4e-2 (naive k=2 Markov) → ~1e-3 — factor ~50, machine-
  checkable arithmetic. Only open direction beyond constants: effective
  equidistribution of the 64-cosine block (not priced by degree budget).
- Archived: effm_moments.py/.out, christoffel.py/.out. Crash note: local
  terminal died mid-sympy (exit 137); rerun lean on runpod — fractions-
  based series, no sympy. Tasks: #18 CLOSED (delivered M4/M10 + priced
  TAIL-6 + exact EFF-E demand); #19 opened (EFF-E mid-block ladders +
  offset-location probe + harvest: thickness constant, ε₀* audit,
  allocation optimizer + Lean hankel_psd_tail_bound).

## 2026-07-04 — #143 (taken over from codex): the (POS₂)→(POS_c) lift machine-checked
- ReversalPositivity.lean BANKED (8475 jobs, axiom-clean [propext, Classical.choice, Quot.sound],
  lint green, in RHTower umbrella): closes doc 41 §6 item (a), the one analytic step
  LedgerReversalConstants flagged as still open for the (SPUR-R)/(AMP) stack.
- Three Mathlib-absent reusable bricks: `sinh_lt_mul_cosh` (0<x → sinh x < x cosh x, via the
  strictly increasing t·cosh t − sinh t with deriv t·sinh t); `div_sinh_strictAntiOn` (y/sinh y
  strict-anti on (0,∞), deriv (sinh y − y cosh y)/sinh²y < 0 from the first brick);
  `tanh_div_tanh_monotoneOn` (0<a<b ⟹ c↦tanh(ca)/tanh(cb) monotone via log surrogate Φ,
  Φ'(c)=a/(sinh(ca)cosh(ca))−b/(sinh(cb)cosh(cb))>0 from brick 2 at 2ca<2cb + sinh double-angle).
- Capstone `posC_of_posTwo`: the c=2 base `tanh(m/2) ≤ tanh r/tanh m` (= posTwo_algebraic_criterion,
  r=log cosh m) lifts to `tanh(m/2) ≤ tanh(c·r/2)/tanh(c·m/2)` for every c≥2. Doc 41 §1's
  ∂_c-monotonicity argument now machine-checked end to end.
- #143 queue remaining: doc 25 Thm A (heavy), counting lemma, and the certified-numerics
  Sup Lemma (doc 41 §4, interval-arithmetic Lean replication) — item (b). The (S-mono)/(LEG)/AMP
  paper items (#142/#138) promote before their Lean is due.

## 2026-07-04 — doc 22 audit: carrier layer formalized (AnnealCarrier.lean, #143)

Question worked: can doc 22 be expanded/precised/researched/Lean-ified. Audit found the
doc STALE — its named gaps (seam transport; domination) were closed by doc 32 (§1 proof +
SeamTransport.lean; §§6–8 (DOM) unconditional on the symmetrized Jerby family). The one
genuinely unformalized layer was the SYMMETRIZATION itself. Banked:

- `formal/GaloisForLFunctions/RHTower/AnnealCarrier.lean` — 2 defs + 10 theorems, all
  axiom-clean [propext, Classical.choice, Quot.sound], build ✔ 8558 jobs, lint green,
  umbrella wired: `symmetrize`/`chiSymmetrize`; exact FEs (`symmetrize_one_sub`,
  `chiSymmetrize_one_sub`); ξ fixed point; (SYM-err) error preservation; entirety +
  Schwarz structure preserved; order equivariances `symmetrize_orderAt_one_sub`/`_conj`
  (finite-side analogues of the ξ pair — instantiates WindowRelation's (ID) on the
  truncation carrier); `symmetrize_domination` = doc 32 §6 (DOM) assembly emitting
  seam_transport's hdom premise, analytic inputs as hypotheses.
- Doc 22 §6 appended: status refresh + the machine-checked chain
  (AFE-exp)+(LOW-BC) → symmetrize_domination → seam_transport_ladder → (ID) transfer.
- Next generative object: Prop interface for (AFE-exp)/(LOW-BC) so instance runs can
  discharge the two hypotheses per window; consumer remains #130.

## Cycle 40 (2026-07-04) — offset located, optimizer convicts doc 73, (EQD) named; Lean harvest proven through
- Doc 74 BANKED. Offset probe (pre-registered, 6 pass / 1 informative
  fail, archived probe_offset.{py,json}): AWAY FROM ZEROS log|Z| is
  near-Gaussian with prime-model variance — restricted μ₆-ratio 1.43 (vs
  3.6-4.1 full), restricted m₂ − v_pm = 0.18 T-stable, mean +0.45. "The
  corruption is all floor." P-OL5 FAILED: thick-part residual is real —
  σ_R² ≈ 0.23 T-stable, mean +0.36, m₄-ratio 2.0 (deg-4-grade). (EFF-E)
  reframed: certify three measured numbers, not a cascade.
- P-OPT FAILED (record loud): the allocation optimizer with exact
  mid-block ladders (B2/B3 pure-Gaussian: ratios 0.999/1.000) says
  4-block union stack = 1.22e-1 (fragmenting A across blocks puts each at
  z≈2.7 where low-deg Christoffel is weak); 2-block (full prime sum
  deg-4 + residual deg-4) = ~1.5e-2. Doc 73 §5's "~1e-3, factor 4-8"
  CORRECTED: shortfall is ~5-15× and deg-6-full is beyond spacing-MV
  (Σr₃² ≫ T). Fully-certified onset with today's toolkit: T₀ ~
  10^{21}-10^{22}. The 3e12 meeting needs (EQD): effective
  equidistribution / exponential sums for mid-prime blocks at joint
  degree > 4 — THE named open core; first probe = ET-Koksma with
  unique-factorization spacing on the (313,10⁴] torus.
- Lean HARVEST (user order: no deferred placeholders — proven through):
  thickPart_union_subset'/measure_le' (parametric 4/(1−β) replaces 8;
  at measured β=0.006: 4.02) + sq_tail_bound + sq_tail_bound_of_moment
  (certified-tail consumable; premises = genuine inputs only). Umbrella
  8632 green, axiom-clean, lint passed.
- ε₀* audit note: sharp carrier drops doc 69's taper split-factor 2:
  ε₀* = 1/256 available [verify in C′ write-out].
- Onset ladder now: e^650 (TIGHT-only) → 10^{21±1} (certified toolkit) →
  3e12 (with EQD). Tasks: #19 CLOSED; #20 = (EQD).

## Cycle 41 (2026-07-04) — THE FAKE-PROOF AUDIT: the lie located at the contradiction step; (XLD) named
- Doc 75 BANKED. RH₂ walked end-to-end as if done (user's anti-theatre
  challenge → attack-as-false at chain scale). Chain table: Lean tier ✓;
  (WR_k) ✓; D-transport ✓; L-transport = WIRING GAP (doc 22, 15 cycles
  untouched); moat/deep exclusions ✓-sketch; walk tier = COUNTING SHELL
  (MidCentralInput.dip_kills/.creation_rate are hypothesis FIELDS;
  (T2)-general hypothesis-typed); creation density ✓-arc; THE LIE at the
  contradiction step.
- THE LIE (three holes): (H1) level-multiplication accounting (one ζ-pair
  forces births at ~δ√n consecutive tower levels — kill-exempt by Rouché)
  is reconstruction, VERIFY vs banked cascade ledger; (H2) walk/kill
  operates at sliver depth, putative pairs at fixed η sit in the MID-BAND
  above it; (H3) THE KILLER: per-level density bounds cannot contradict
  J-fold forced presence at a FIXED height (bad sets can align) — needs
  CROSS-LEVEL DECORRELATION, unproven, un-density-provable.
- (XLD) NAMED: mid-band deficit events at fixed height cannot persist
  across consecutive levels — the new primes scramble faster than the
  per-level density. Euler-specific, (EQD)-genre, and refuted-by-
  construction for D–H: the FIRST statement in the lane with that
  property. D–H filter run architecturally: the chain currently contains
  NO proven step that fails for D–H — the discriminator ((H3)+budget) is
  exactly the unproven core. Constants war retroactively load-bearing IN
  PRINCIPLE (quantitative discriminator leg) but was polish on a
  subordinate constant while links 4/8/11/12 sat unexamined.
- Honest ledger status: REDUCTION MACHINE — RH₂ ⟸ (XLD) + seam wiring +
  (T2)-general + (EQD) + k≥2. Force order: verify (H1) (reading, hours) →
  state (XLD) at TWO consecutive levels (the +(n+1)^{-s} minimal
  scrambling question — concrete, finite) → seam-transport write-out →
  only then constants. Tasks: #21 CLOSED; #22 = (H1)-verify + (XLD)-2level.

## 2026-07-04 — ZetaCarrier.lean: the concrete carrier, hypotheses → proofs (#143)

Follow-up to the AnnealCarrier round, driven by doc 72 §4 (carrier = g_N). Banked
`formal/GaloisForLFunctions/RHTower/ZetaCarrier.lean` — 24 declarations, all
axiom-clean [propext, Classical.choice, Quot.sound], ✔ 8564 jobs, lint green:
concrete dirichletPoly/zetaChi/gN/completedGN with FE, reality, analyticity, order
equivariance all PROVED on the open strip (χ-identity unconditional via
Gammaℝ_ne_zero_of_re_pos; ζ-FE validator via riemannZeta_def_of_ne_zero);
hypothesis-free analyticOrderAt_one_sub (entirety dropped via
analyticOrderAt_comp_of_deriv_ne_zero); completed_domination_iff (doc 32 §5
cancellation); AFEAccurateOn/CarrierFloorOn interfaces; capstone
anneal_deck_transport = doc 22's reduction on the actual objects, conditional only
on the two interfaces. Doc 22 §7 appended with the discharge routes (interval
instances / Gabcke remainder / Jensen+Cartan — mathlib now HAS JensenFormula.lean).
Key trick: Γ_ℝ analyticity off zeros via inv_inv of the ENTIRE reciprocal
differentiable_Gammaℝ_inv — no half-plane plumbing.

## 2026-07-04 — SeamSignTransport.lean: doc 22 §2's L-transport gap closed (#143)

The seam-side L-transport (doc 22 §2's "one unproven wiring piece") formalized:
`formal/GaloisForLFunctions/RHTower/SeamSignTransport.lean` — 12 declarations,
axiom-clean, ✔ 8569 jobs, lint green, umbrella wired. Shape: (K1) sign-product
dictionary + the atomic fact that domination at a real value forces equal sign ⟹
the k=1 seam datum transports on TWO POINTS of domination (no homotopy). Includes
the generic (K1) `deckClass_eq_sign_product_of_realFE` (real FE localized to the
mirrored chart — what completedGN's strip-only FE supplies via
completedGN_lineReflect) and capstone `anneal_seam_L_transport` (deckClass of ξ's
k=1 roots = completedGN's under two-point on-line domination). Doc 22 §8 appended.
Next: assemble the mod-2 window relation (D-transport + L-transport + (ID)×2) into
one statement; then the #136 instance run.

## 2026-07-04 — AnnealWindowRelation.lean: the mod-2^k window relation assembled (#165)

Composed D-transport + L-transport + (ID)×2 into single statements:
`formal/GaloisForLFunctions/RHTower/AnnealWindowRelation.lean` — 10 declarations,
axiom-clean (window_N_congruence: [propext] only), ✔ 8570 jobs, lint green, umbrella
wired. New engine piece: analyticOrderAt_conj_conj_of_analyticAt (Schwarz order
equivariance localized, entirety dropped) ⟹ completedGN_orderAt_lineReflect — the
finite carrier's full (ID) multiplicity package on the strip. Capstones:
anneal_window_parity_transport (D,L congruences mod 2^{k+1} ⟹ N congruence mod 2^k;
(ID)s derived, not assumed), xi_rung_of_finite_side (2^k ∣ N_g ⟹ 2^k ∣ N_ξ),
anneal_mod_two_window_relation (k=1: mod-4 inputs ⟹ N_ξ ≡ N_g mod 2). Honesty note
banked in doc 22 §9: the hL mod-4 lift is NOT transportable from level-2 boundary
data (deckClass_blind_to_split) — it is finite-side-computable per window instead.
Next: deck↔counting dictionary discharge of hD; #136 instance run for certified
t₂/m₂.

## Cycle 42 (2026-07-04) — (H1) verified against the ledger; (XLD)₂ probed; the RELAY finding (doc 76, task #22)

(1) (H1) READ AND SETTLED (doc 76 §1): the cascade ledger IS cross-level at
fixed height (CascadeBirth.time = tower level; futurePushes = drop time,
SweepCascade.lean:169) — doc 75's fear fails. But J-level forced presence =
ONE walker (budget consumed once), so doc 75 §2's J-fold-budget mechanism is
wrong-shaped. The exact gap: SlipWindow is STATIC (MidCentral.lean:32); all
proven kills fire only on ¬SlipWindow; in-window births are immortal in the
formal ledger. The missing kill exists at proof shape: slip identity (doc 51
§9a) makes the window sub-entry (k* = 0.194 < 1). Ledger upgrade typed:
dynamic slip + relay graph. (2) RELAY RE-CUT (doc 76 §2): a ζ-pair crossing
the domination window must be a chain of ~δN^{1/6} re-creations pinned at one
height — (XLD) localizes to consecutive-level RE-CREATION, one explicit
increment. (3) (XLD)₂ stated + pre-registered P-X1..P-X5, THEN probed
(probe_xld_zeta.py + probe_xld_dh.py, runpod, archived mwm_xld/). ζ: median
lifetime 2 at all N ∈ {63,126,398,1261}; survival/null = 0.94–1.02 (P-X2
strong pass); p95 flat ~21–27, α ≈ −0.09 (P-X5 pass, no window-filling). D–H
self-certified (κ = 0.2840790438 recovered from FE in-script; 83 off-line
zeros findroot-certified): run median 18 (censored at 31), covers matched
81%, cond persistence 0.950 (P-X3/P-X4 pass). THE FINDING: the relay channel
— deaths re-create at same height at 0.46–0.56 vs 0.004–0.025 chance (18×
→128×, growing ~N^{0.6}); deaths are 100% absorption. So naive
creation-set-independence is FALSE for ζ; what holds is SUB-CRITICALITY
(geometric relay chains, N-uniform) vs D–H SUPER-critical (window-covering).
(XLD) restated as a relay-criticality statement — the correct quantitative
open core. Two-channel attack surface: survival channel = phase-null
(provable via log-lattice discrepancy, no zero-density); re-creation rate ~½
(frozen-lattice geometry, doc 51 §2–3). Task #8 (EPH) = the chain-length
object, now with measured targets. Parallel session closed force item (3)
(SeamSignTransport.lean + AnnealWindowRelation.lean — chain link 4 banked).
Next: two-level relay-rate derivation from the frozen lattice; log-lattice
discrepancy for the survival channel; relay-ledger Lean upgrade.

## 2026-07-04 — hD DISCHARGED + doc 76 + #136 instance run (#166)

(i) Deck-side input eliminated: `anneal_D_transport` instantiates the banked Rouché
substitute (enclosed_count_eq_of_close, #128) on ξ vs completedGN — EXACT count
equality under slit-annulus domination, subsuming D mod 2^{k+1} for every k. New
capstone `anneal_mod_two_window_relation_of_domination` (AnnealWindowRelation.lean,
axiom-clean, lint green): strip window + peeled factorizations + domination + hL
(mod 4) ⟹ N_ξ ≡ N_g (mod 2). Remaining analytic inputs: certified zero data +
domination + hL only. (ii) Doc 76 banked (seam mod-4 blindness = structural, not a
missing lemma; work re-types to per-window certified finite-side data). (iii)
window_instance_136.py (pre-registered P-W0..P-W4): first run — window A PASSES the
contrapositive test: off-line pair confirmed (rel. residual 1e-60), D₁=0≠D₂=2, and
domination fails q_max=9.76 at the inner circle toward the pair (the doc 22 §3
exceptional mechanism, measured); window B rerunning after a scale-vacuous assert
fix (completed-scale |Φ| ~ 1e-70 at t≈221 — residual/simplicity now at raw scale).

## 2026-07-04 — #136 instance run COMPLETE (all verdicts in; doc 76 §4)

P-W0/P-W1/P-W2/P-W3 all PASS (P-W2 re-scoped to zero-free control, recorded as
finding). Sharp datum: displacement map shows the #136 off-line pair = merger of
the two flanking on-line slots (220.715, 221.431 both root-find to the same pair
member; L differs by exactly 2) — the (K1)-blind move instantiated on real data;
219.068's partner is ON-line at 218.9988. Window B: q_max = 0.287, first
end-to-end positive instance of anneal_mod_two_window_relation_of_domination.
Matched-pair windows don't exist at N=5/t≈221 (displacements 0.07–0.36) —
instrument-level confirmation of the doc 32 §6 exponential-family switch.
Archived: computations/mwm/window_instance_136.{py,out}. Next: Jerby-family
instance; interval hardening of the reader.

## 2026-07-04 — (a) exponential-family instance + (b) certified reader (#167)

(a) jerby_instance.py: all five pre-registered verdicts PASS — E–M family
(M=500, J=20) validates at 5.7e−49; Φ* has one on-line zero, displacement 1e−50;
q_max = 3.8e−49; D=L=1, N=0=0 both carriers: FIRST NONTRIVIAL POSITIVE TRANSFER
of the assembled mod-2 window relation. FLAG: doc 32 §7 Jerby transcription at
y=1 reaches only 1.2e−3 → promotion-grade re-read item. (b) certified_reader.py
(python-flint/ARB, scratchpad venv): ALL CERTIFIED — no-zero coverings (C1/C2),
adaptive domination covering (C3, min margin 1.0e−3, 3448 boxes; ARB ζ enclosure
≈33× box half-side ⟹ bisection), interval-Newton #136 pair box (C4: unique
simple zero, the first certified t₂/m₂ entry), domination-failure witness (C5).
Certificate JSON archived. Doc 76 §5 records both. Next: Prop-level
window-certificate interface in Lean to ingest C1–C4 as configuration
hypotheses.

## Cycle 43 (2026-07-04) — THE RELAY TIER: half-law proved, (SURV-EQ) written out, RelayLedger.lean banked (doc 77, task #23)

(i) TWO-LEVEL RELAY RATE (doc 77 §1): the signed walk IS the banked exact
zero motion (DepthUpdate both signs); relay criterion = reverse dichotomy in
the signed coordinate (v₀² < a·cosφ); HALF-LAW proved (one line,
parameter-free): P₁(x) = arccos(x)/π → ½ — measure of a half-circle, no
lattice/envelope/height input. Doc 76's 18–128× "alignment" was the wrong
baseline: the walker persists through the barrier. Null checks
(mc_relay_null.py, pre-registered P-R1..P-R3, archived mwm_xld/): P-R1 PASS
(iid 3-step recross 0.550 brackets measured ζ 0.46–0.56 — relay fully
explained by the signed-walk null); P-R3 PASS to 4 decimals on
iid/envelope (0.3637 vs 0.3632 — arccos formula exact); P-R2 FAIL
informative: frozen-lattice null recrosses at 0.805 ≫ iid 0.550 (rotation
ENHANCES relay; lattice 1-step = 0.5027 = ½ exactly); measured ζ sits on the
IID side ⟹ real mid-walk is phase-mixed, not frozen. CONSEQUENCE: relay rate
is O(1) under every null ⟹ (XLD) sub-criticality must be a CHAIN-tail
statement; named (CHAIN-geo): geometric chain tail from slip growth
(2π(iΔ)² detuning per relay) + rotation_dip — inputs banked, D–H escapes via
pinned increments. (ii) (SURV-EQ) (doc 77 §3): survival channel = two APs of
step 4p displaced ½ (from doc 49 §2 proved lattice); Koksma (BV ≤ 4) ⟹
|window-avg survival − null| ≤ 4D_L; AP regime Erdős–Turán log L/L; coherent
p ≈ ¼,¾ rescued by certified cubic drift on N^{1/3}; expansion error O(L³/N)
harmless below the drift clock. HONEST BOUNDARY recorded: window-averaged
only; the pointwise conditional is (XLD) proper (D–H shares the discrepancy
— its conspiracy is amplitude-sign, not phase-distribution). (iii)
RelayLedger.lean BANKED (umbrella 8637 jobs green, lint passed, axiom-clean
[propext, Classical.choice, Quot.sound]): signedDepth;
exists_last_nonpos_between (discrete first passage w/ last-crossing witness);
run_bounded_of_excursionBound ((EXC-ℓ) ⟹ no off-line run > ℓ — the deep-pair
contradiction shape); exists_upcross_chain + card_upcross_ge_of_spread
(ℓ-separated presence at k+1 levels ⟹ ≥ k+1 upcrossings);
spread_lt_of_upcross_budget (budget R ⟹ no (R+1)-fold spread — consumption
point for (CR)×(XLD)); survivesFrom_iff_forall_signedDepth_pos (old ledger =
off-line at every prefix). (EXC-ℓ)/budget are explicit Prop inputs, nothing
silent. Next: (CHAIN-geo) derivation; (T2) per-instance bridge from Rouché
presence to signedDepth > 0; relay-delay field for the next census.

## Cycle 44 (2026-07-05) — CHAIN LINK 5 UNCONDITIONAL: the EM carrier machine-checked (doc 78, EMCarrier.lean, task #25)

Doc 75 table item 5 worked to its unconditional floor. NEW MODULE
EMCarrier.lean (umbrella 8638 jobs green, lint passed, axiom-clean
[propext, Classical.choice, Quot.sound]): the Euler–Maclaurin representation
ζ(s) = emCarrier N s − s·emTail N s on {re s > 0} \ {1}, every N ≥ 1, with
EXACT remainder ‖s·emTail‖ ≤ ‖s‖·N^(−σ)/σ (telescope, no asymptotics).
Proof route: per-interval closed forms (emTerm_key — one zeta tail term
exactly, pure cpow algebra); integral form for the two norm bounds (sharp
telescope + crude M-test); telescoped finite identity + σ>1 anchor against
mathlib's zeta_eq_tsum_one_div_nat_cpow (limits via HasSum.tendsto_sum_nat,
rpow decay); Weierstrass M-test differentiability of the tail on the strip;
punctured-half-plane connectivity from four convex pieces; identity theorem
(AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq at anchor 2). WIRED
CONSEQUENCES: zeta_ne_zero_of_em_domination (unconditional per-point
zero-free certificate from finite data); afeAccurateOn_of_emCarrier_close
(ZetaCarrier's (AFE) interface discharged: EM bound + finite-vs-finite
closeness); completed_domination_of_em (the exact hdom premise of
anneal_seam_L_transport / anneal_deck_transport). THE RELOCATION: link 5's
entire classical R–S debt is now (EM-CLOSE) — ‖emCarrier M − gN N‖ ≤ δ on
windows, a comparison of two FINITE Dirichlet expressions with no ζ in it
(stationary-phase/Gauss-sum territory, the doc 49 lattice again). Cost:
EM needs N ~ t² vs matched √(t/2π) — a bridge, not a replacement; the
2^k-tower arithmetic stays native to gN. D–H filter respected: the EM rep
holds for D–H too; discrimination stays at (XLD)+budget. Doc 75 addendum
appended. Opens: (EM-CLOSE) as finite theorem target; the certificate
instrument (interval-arithmetic evaluator → first end-to-end machine-checked
zero-free windows + one full seam-transport instance with zero unformalized
inputs); reusable strip scaffold (M-test + connectivity + identity theorem)
for any Dirichlet-type representation the lane needs.

## Cycle 45 (2026-07-05) — review of the codex Lean batch (task #26)

Scope: all 20 entries of lean_updates_codex.md, read at source. Verdict:
CORRECT. No cheap hypotheses found — spot checks: the margin geometry of
`not_riemannHypothesis_of_sphere_domination_center_margin` (Re z ≥ Re s₀ − r >
1/2 via abs_re_le_norm, sound); `pinned_zero_re_eq_half`'s fixed-point algebra
(1 − conj ρ₀ = ρ₀ ⟺ re = 1/2, sound); the Jensen slope arithmetic in
`xi_circleAverage_slope_eq_order` (two evaluations of the banked single-zero
formula, division legal since log r₁ < log r₂); the ε-splitting in
`anneal_deck_transport_of_emCarrier_close` (ε₁ + δ matches AFEAccurateOn
through `afeAccurateOn_of_emCarrier_close` exactly). RelayLedger.lean and
EMCarrier.lean carry no foreign changes beyond the two documented EM
transports. Verification: RHTower 8638 jobs green; formal lint passed; all 23
new/changed endpoints print axioms [propext, Classical.choice, Quot.sound].

Two headline results the batch banks (now fed back into docs):
1. `rh_iff_forall_circleAverage_slope_exp_eq_one` — RH ⟺ two-circle modulus
   slopes at right-half ξ zeros have trivial 2^k exponentials, all k: an
   RH-equivalent in |ξ| alone, welded to the germ and slit-plane gates.
2. `xi_rung_of_finite_side_of_domination` — chain links 3–4 composed:
   domination + seam congruence + finite-side rung ⟹ ξ rung, every k.

Feedback appended: doc 75 Addendum 2 (spine = EM-CLOSE ⟹ domination ⟹ rung
transfer; three named unformalized inputs), doc 78 §7 (EM one-call
transports), 3-formalized card dated entry. Cleanup: banned-word docstrings
fixed in DipKillsWiring.lean + WeldEnvelope.lean (comment-only; rebuild green).

Opens: the composed spine makes the seam congruence hL at 2^(k+1) the single
seam-side object every rung waits on — exactly doc 76-seam-lift-blindness's
target; and the modulus-slope RH surface suggests a numeric instrument (two
circle averages of log|ξ| per zero) that the EM certificate evaluator could
feed directly.

## 2026-07-05 — #135/#138/#139 SPUR-R route driven to verdict (doc 79)

Goal: resolve #139/#138/#135 + blockers as Lean or proven dead-end, no partial results.
Verdict: the DISC/SPUR-R reader is a non-load-bearing, DOMINATED instrument — retired.
- §1 machine-checked: #130 counting spine (enclosed_count_eq_of_close, anneal_deck/seam
  transport_of_emCarrier_close, completed_domination_of_em, xi_rung_of_finite_side_of_domination,
  anneal_mod_two_window_relation_of_domination) all axiom-clean [propext,Classical.choice,
  Quot.sound]; transitive-import ISLAND, zero dependence on any of 23 Spur* modules
  (checked full import closure). Counting unconditional modulo (EM-CLOSE).
- §2 rigorous: Rouché needs DOMINATION (size) only; SPUR-R needs carrier zero-geometry
  (F1)-(F3), measured-only. Dominated.
- §3 verified: winding formula + two-cluster no-go sound (winding_check.py); target Z_c=2
  robust over d=6..60 × six (a,b), never >2 (smono_check.py). Sound, not false. Lean form
  honest-complete (AMPReaderInput hypothesis-typed).
- #135/#138/#139 → completed (retired). #130's blocked-by-#135 edge cleared.
- Open residue isolated as standalone (S-mono) entire-function conjecture (doc 79 §4);
  NOT a #130 blocker. Siblings #142(LEG)/#143(Lean)/#147(B⁗) are the same superseded
  cluster (left for codex/user; codex is on the live chain not Spur).
Forward: #130's whole load is now (XLD)₂ (doc 76-xld §3) — size/phase arithmetic on one
added Dirichlet term, not zero-geometry.

## Cycle 46 (2026-07-05) — the seam congruence exhausted (task #27, /goal)

Target: doc 76-seam-lift-blindness's hL at 2^(k+1), ground to its structural
floor and formalized. Module: SeamCongruence.lean (banked; umbrella 8640 jobs
green, lint passed, 14 endpoints axiom-clean; seam_iff_rung is pure [propext]).

The finding that closes the topic's shape: hL is NOT an independent object.
`seam_iff_rung` / `anneal_seam_iff_rung_of_domination`: under the window
identities + D-transport, hL at 2^(k+1) ⟺ the rung congruence at 2^k — both
directions. Doc 76 §1's blindness upgraded from "no boundary transport
exists" to "the seam datum IS the rung in on-line coordinates". Tower limit
(`seam_tower_iff_offline_eq/_zero`): all levels at once ⟺ N₁ = N₂; with an
on-line finite side ⟺ window RH. The seam's real content = a 2D→1D change
of coordinates.

The discharge instrument (the 1D coordinates cashed): ξ real on the line +
IVT (`exists_interleaved_zeros`, no argument principle) + the peeling + the
Rouché-substitute count ⟹ the squeeze s ≤ L₁ ≤ D₁ ≤ s:
`window_online_of_sign_data` (L₁ = D₁, N₁ = 0), `xi_online_of_sign_data`
(every window zero on-line), `hL_exact_of_sign_data` (hL as EQUALITY, all
levels at once), `window_simple_of_sign_data` + `xi_simple_online_of_sign_data`
(every window zero simple — the tight squeeze pins each multiplicity to 1),
endpoints `xi_window_online_of_domination_sign_certificate` and the EM weld
`xi_window_online_of_em_sign_certificate` (domination from doc 78's finite
EM data — every hypothesis a finite computable inequality).

D–H filter: identity holds verbatim for D–H; the instrument refuses to fire
where D–H's off-line pairs eat the count (sign count < total) — no false
proof derivable. Doc 79 written; the universal hL re-localizes with a proof
onto the exceptional-window census = (CR)×(XLD), doc 77's territory.

Opens: (1) run the E–M window instance through the weld — first end-to-end
machine-checked window-RH certificate (reader has C1–C4; needs a 2-entry
sign table); (2) #24 (CHAIN-geo) re-statable in 1D: bound the density of
sign-deficient windows — the mollified machinery of docs 55–70 prices this
in mean square.

## 2026-07-05 (cont.) — broadened goal: grinding open tasks to Lean; (S-mono) core started

Stop-hook rejected the "superseded/retired" status-verdict as partial: must prove/refute the
MATH. Did:
- Refutation search (smono_refute.py): 3096 configs, 6 carrier shapes incl. F2-VIOLATING
  non-monotone gaps, 12 τ, 11 d — worst Z_c=2, ZERO spurious pairs. (S-mono) NOT refuted;
  robust even without (F2). Two-cluster separation is the only obstruction ⟹ single-range
  one-sidedness alone suffices. Must PROVE.
- Banked Lean (axiom-clean): CothInfra.lean (coth/csch/φ, not in mathlib; monotonicity +
  coth>1) and SpurLattice.lean (field strict-antitone on pole-free gaps ⟹ unique gap
  equilibrium; swap-terms>1). This is the step-(b) engine of the lattice (S-mono).
- Wired both into umbrella; index regenerated.
Open-task scope now = {#130 (=RH₂, frontier), #135/#138/#139/#142/#143/#147 (SPUR-R cluster,
closable)}. Grinding the closable cluster to full Lean; #130's core (XLD) is the RH frontier.

## Cycle 47 (2026-07-05) — Route C /goal opened: the (EQD) attack, priced (task #28)

Doc 80 written: Route C standing map (C-1..C-9 with Lean anchors; open core =
C-5 (TAIL-6)/(EQD)) + the Fourier-majorant framework + pre-registered
P-EQ1..5 + census run (census_eqd.py, mixed_twin_probe.py, archived in
computations/mwm_eqd/).

The framework: double Beurling-Selberg (bandlimited majorant in the value
axis AND in the t axis) makes the transfer error EXACTLY the near-collision
census |log(A/B)| ≤ δ — the far regime contributes zero. The bandwidth-budget
principle (doc 80 §3(iv)): worst-case-gap Fourier = the degree budget,
method-independently; only actual-gap arithmetic can beat moments.

Verdicts (all pre-registered, all bind): P-EQ1/2/3/5 PASS — B1's census is
twin-smooth pairs, measured 1.3e−6 in range, EXACTLY ZERO at the working
δ₁ = 100/T below 3e6; B2 rough spectrum harmless (≤ 6.3e−8). **P-EQ4 FAILS,
obstruction named**: the mixed set SP = smooth×prime has density 0.09 at
3.3e10 with weighted twin census 2.65/octave — O(1), five orders over
budget; and the harvest check shows B1-Fourier composed into the assembly
(3.9e−2) does NOT beat the 2-block optimum (3.3e−2 reproduced; 1.5e−2 at
doc 74's finer setup): union loss eats the Chernoff gain.

Net: the two instrument classes are ONE two-sided wall (degree budget =
collision census), now measured from both sides. Certified floor ~1.5e−2 vs
budget 2–4e−3. Route C's finite-height meeting is blocked at instrument-class
grade; the spine above 10^21 stands. Remaining unexhausted before the
terminal refutation record: (EFF-E) certification of the residual block, and
the odd-parity counter (doc 72 §9.3 — the only BUDGET-side knob untouched).
Positive salvage: B1 at near-model grade via the twin-smooth census — real,
formalizable (Bessel-J mini-theory + bandlimited majorants to be created in
Lean; neither is in mathlib).

Next (force order): (1) doc 81 — the wall statement made precise (the
refutation-grade theorem shape with the census as certificate); (2) the
odd-parity budget-side pass; (3) Lean: the bandlimited-transfer skeleton.

## 2026-07-05 (cont.2) — lattice (S-mono) derivative stack complete in Lean
SpurLattice.lean now 239 lines, all axiom-clean, lint-green:
- rcsch_hasDerivAt (csch'=-coth·csch), rcsch_sq_hasDerivAt ((csch²)'=-2φ),
  spurEnergy_hasDerivAt (W'=-¼Σφ). With cothField_hasDerivAt (field'=-2W) this gives
  field''=½Σφ — the full derivative infrastructure of the electrostatic lattice.
Ingredients for lattice (S-mono) now all banked: field monotone + unique/existent gap
equilibrium, s-march (equilibrium_lt_of_field_lt), field'=-2W, W'=-¼Σφ, rphi_strictAntiOn.
Remaining = the assembly: W-monotonicity along equilibria via the doc-29(c) disjoint-
interval domination (near-ahead φ(s/2) dominates paired behind-ahead differences bounded by
φ((δ-s)/2) < φ(s/2), which is rphi_strictAntiOn at s/2<(δ-s)/2). Next cycle.

## Cycle 48 (2026-07-05) — parity counter banked; A-audit adjudicated (task #28 cont.)

- ParityCounting.lean BANKED (first-compile clean, axiom-clean, lint green):
  `selected_dips_count_le`(+`_of_disjoint`, `selected_sliver_budget`) — dip
  counting through a selection predicate against floor-free measure; with
  the (K1) sign reading as selector this removes the 4/(1−β) thickness
  factor from the budget: ε₀*/4.05 → ε₀*. Budget now 2–3.9e−3 vs stack
  1.5e−2 (short 3.8–7.7, down from 5–15).
- Doc 81 §6(b) A-audit RESOLVED same cycle (§6(c)): the Gabcke-C₀ shortcut
  (A → ¾logT, tail trivial) is CLOSED — doc 43 §2's two catching mechanisms
  pin λ₀ at the valley-registration depth of the deep boundary η = 1/4,
  which is N^{−1/2} = (T/2π)^{−1/4}: the same χ-modulus scale as E(T). A is
  structural at ¼logT-grade. Both "R–S validity" and "deep-boundary
  registration" are one scale; no remainder sharpening moves A.
- Umbrella note: RHTower.lean currently broken by a PARALLEL-SESSION name
  clash (SpurLattice.spurEnergy vs SpurCPI.spurEnergy — both theirs, logged
  in logs/parallel-session-notes.md); my modules gated independently.
- Route C terminal shape after this cycle: C-5's fate = bounded arithmetic
  (ε₀* write-out + allocation vs the 3.8× gap), no longer open-ended
  analysis. Next: the harvest arithmetic; then the Lean program for the
  winning branch; then C-6 formalization + the k ≥ 2 story for the full
  /goal verdict.

## Cycle 49 (2026-07-05) — the harvest arithmetic executed (task #28 cont.)

Doc 81 §7: every lever priced. Split-2 drops (C′ = 16); parity removes
thickness; H_iso = 4 at sketch grade (c_deck = 1/8); joint-deg-4 bypass
REFUTED (L⁴ triangle, 2.7e−2); dip-layer 12 unaudited. Ledger: stack
1.5e−2 (walled); budget 3.9e−3 certified / 7.8e−3 with H_iso sketch;
ceiling 6.25e−2 ABOVE the stack ⟹ the wall alone cannot refute the
meeting, and the proof branch is one factor ~2 away. C-5's fate = ONE
elementary write-out: the dip-layer per-cell cap (doc 56 §4 re-run, sharp
carrier + parity counter): 3·n_max ≤ 6 closes the meeting; 12 leaves it
1.92× short with the class exhausted. Next: dip-layer write-out, H_iso
write-out, then Lean for both.

## Cycle 50 (2026-07-05) — ROUTE C-DIRECT REFUTED: the registration gap (task #28 TERMINAL)

Executing doc 81 §7's "one page" did not yield a constants verdict — it
yielded the located lie. Reconstructing the sharp-carrier count from doc 56
§2's dip lemma exposed that the sharp carrier's masses are κ² ~ logN-grade
(un-mollified), so shallow pairs over typical envelopes dip only to ~c²
(doc 43 §2's central-dip formula): doc 72 §4's counter is NOT
registration-complete at λ₀ ≪ 1. Registration forces c ≤ e^{−A/2} ⟹ budget
∝ e^{−A/2} vs polynomially-walled stack A^{−4}: min_A stack/budget ≈ 13
certified (≥ 3 with all sketches), growing with T — fails at EVERY height.
The mollifier doc 72 discarded was the registration device. Verdict doc 82;
5-failed card route-c-direct-registration-gap.md; doc 80 §8 terminal
pointer. All escapes priced (certification walled docs 80–81; A-audit
closed; budget ceiling ≥ 3; partial registration = Route B + cascade;
envelope worst-case). Survivors: C-1..C-4 Lean links, ParityCounting (now a
Route B asset), wall instruments, B1 certificate, seam/EM machinery.
NEW DESIGN GATE for the branch: the REGISTRATION CRITERION — does a carrier
register its own shallow creation? Sharp: no. Mollified: yes.
Exponential-AFE (doc 32 §6 / doc 76 §5): UNTESTED — the live heir; test it
next. Tasks: #28 CLOSED (refutation branch, all details); #20 (EQD) CLOSED
(adjudicated docs 80–81); #11 CLOSED (superseded by the verdict).

## 2026-07-05 (cont.3) — SPUR-R Lean grind (user: "finish it"): s-march + dW/ds core
SpurLattice.lean now 21 thm (CothInfra 9), all axiom-clean, lint-green. Added this cycle:
- swap_field_gt (swap ahead→behind pole raises field by >2) + equilibrium_gt_of_field_gt
  (⟹ equilibrium moves right = s-march s_{i+1}<s_i), the doc-29 step-(b) mechanism;
- cothField_secondDeriv (field''=½Σφ);
- rphi_pair_gt (m-th paired difference φ((s+mδ)/2)>φ((δ-s+mδ)/2)) + rphi_paired_sum_gt
  (Σ paired > 0 = the UNCONDITIONAL half of dW/ds<0; gives W-monotonicity outright in the
  M≥N no-overhang range).
Remaining for constant-δ lattice (S-mono): φ exponential tail bound (φ(u)≤Ce^{-2u}, u≥1) for
the outer N>M far-behind surplus, + dW/ds<0 assembly + chain to W(t*_{i+1})>W(t*_i). Next.

## Cycle 51 (2026-07-05) — the registration criterion built + formalized (/goal)

Registration.lean BANKED (6 endpoints axiom-clean, lint green, module build
8575): the pair-dip law both sides (‖Φ(½+it)‖ ≥ η²‖H‖ everywhere, = at the
foot — exact, carrier-agnostic), RegistersAt / RegistrationComplete
predicates, registration from envelope upper bounds, and the REGISTRATION
GAP AS A THEOREM (one band pair over a lower-bounded envelope refutes
completeness below η²M) — doc 82 §1's unsound link, machine-checked in
general form. Doc 83: the criterion sorts the lane's carriers — mollified
REGISTERS (κ² = O(1)), sharp FAILS (doc 82), exp-AFE = two-horn dichotomy:
value-normalization says fail, but its e^{−ωt} displacement may CONFINE its
pair population below the band (registration by vacuity) — the criterion
re-types the heir's question into a zero-confinement census (doc 76 §5
instance machinery, next). Umbrella import appended (pending parallel
session's Spur clash fix).

## 2026-07-05 (cont.4) — MILESTONE: lattice (S-mono) proven (no-overhang range)
latticeEnergyS_strictAntiOn (axiom-clean): W(s) strictly decreasing in s for 1≤N≤M ⟹ (S-mono)
S_{i+1}>S_i unconditional in the M≥N range. Chain: latticeEnergyS_hasDerivAt (dW/ds exact) →
latticeEnergyS_deriv_neg (dW/ds<0) → strictAntiOn via strictAntiOn_of_deriv_neg. Session total
39 decls / 487 lines new coth/csch+lattice theory, all axiom-clean, lint-green. Remaining for
FULL lattice (S-mono): outer N>M range = φ exponential-tail bound vs cubic near term. Then
(F)-fields, Lemma R, capstone, #147.

## 2026-07-05 (cont.5) — outer-range: φ exponential tail bound banked
CothInfra.lean: sinh_ge_quarter_exp (sinh u ≥ eᵘ/4, u≥1), cosh_le_exp (cosh u ≤ eᵘ),
rphi_le_exp (φ(u) = cosh u/sinh³u ≤ 64 e^{-2u}, u≥1) — all axiom-clean. This is the
far-behind overhang control for the outer (N>M) lattice (S-mono).
Remaining outer-range pieces (next cycles): (i) near cubic LOWER bound φ(x) ≥ c/x³ for
0<x≤1 (via sinh x ≤ x cosh x ⟹ csch x ≥ 1/(x cosh x), coth x ≥ 1/x); (ii) geometric tail
sum of the overhang Σ_{m≥M} φ((δ-s+mδ)/2) ≤ 64 e^{-(δ-s)} e^{-Mδ}/(1-e^{-δ}) [SPLIT at
mδ~1 since rphi_le_exp needs arg≥1 and δ may be small]; (iii) assembly: near surplus
φ(s/2)-φ((δ-s)/2) > overhang ⟹ dW/ds<0 in outer range ⟹ latticeEnergyS_strictAntiOn
extends to N>M. Then (F)-fields χ1/χ2, Lemma R, capstone, #147.

## 2026-07-05 (cont.6) — outer-range: near cubic lower bound banked
CothInfra.lean: cosh_one_lt_two, sinh_le_mul_cosh (sinh x ≤ x cosh x via monotoneOn_of_deriv_nonneg),
rphi_ge_cubic (φ(x) ≥ 1/(4x³) for 0<x≤1) — all axiom-clean. BOTH outer-range bounds now in hand:
rphi_le_exp (φ(u)≤64e^{-2u}, u≥1, far overhang) + rphi_ge_cubic (near cubic). Session ~48 thm/590
lines. Remaining outer-range: geometric tail sum Σ_{m≥M}64e^{-(δ-s+mδ)} (δ-split at mδ~1) +
assembly (near surplus φ(s/2)-φ((δ-s)/2) via cubic > overhang via geom tail ⟹ dW/ds<0 for N>M).
Then (F)-fields, Lemma R, capstone, #147.

## 2026-07-05 (cont.7) — outer-range: geometric overhang bound banked
CothInfra.lean: rphi_geom_tail_le (Σ_{n<K} φ(a+nδ) ≤ 64 e^{-2a}/(1-e^{-2δ}), a≥1, δ>0) —
axiom-clean, via rphi_le_exp per-term + telescoping geom_sum_mul. ALL THREE outer-range
φ-ingredients now banked: rphi_ge_cubic (near cubic lower), rphi_le_exp (far per-term),
rphi_geom_tail_le (far overhang geometric). Session ~49 axiom-clean thm.
Remaining: final outer-range assembly — dW/ds<0 for N>M by (near cubic surplus >
geometric overhang), handling the arg≥1 δ-split (only far terms mδ≳1 use rphi_le_exp;
near terms use rphi_ge_cubic + rphi_paired_sum_gt). Then latticeEnergyS_strictAntiOn extends
to N>M ⟹ full constant-δ lattice (S-mono). Then (F)-fields, Lemma R, capstone, #147.

## 2026-07-05 (cont.8) — outer-range REDUCED to a scalar inequality
SpurLattice.lean (axiom-clean): latticeEnergyS_deriv_neg_outer (dW/ds<0 for N>M given
overhang < paired surplus, via range/Ico split) + latticeEnergyS_deriv_neg_outer_of_near
(sharper: given overhang < NEAR MARGIN φ(s/2)-φ((δ-s)/2), since paired surplus ≥ its m=0 term
via Finset.single_le_sum + rphi_pair_gt). So the FULL outer range now reduces to ONE scalar
inequality hnear, dischargeable by rphi_geom_tail_le (overhang ≤ geom) + rphi_ge_cubic (near
≥ cubic). Session ~51 axiom-clean thm. Remaining: prove hnear under explicit s-smallness
(cubic>geom+δ-split) ⟹ unconditional outer strictAntiOn ⟹ full constant-δ lattice (S-mono);
then (F)-fields, Lemma R, capstone, #147.

## 2026-07-05 (cont.9) — outer range CLOSED modulo one scalar inequality
SpurLattice.lean (axiom-clean): overhang_le_geom (Ico-sum reindex + rphi_geom_tail_le ⟹
overhang ≤ 64e^{-(δ-s+Mδ)}/(1-e^{-δ}), closed form) + latticeEnergyS_deriv_neg_outer_scalar
(composes overhang_le_geom + rphi_ge_cubic (2/s³) + rphi_le_exp ⟹ dW/ds<0 for N>M given the
single scalar `64e^{-(δ-s+Mδ)}/(1-e^{-δ}) + 64e^{-(δ-s)} < 2/s³`, NO sums). So BOTH ranges of
constant-δ lattice dW/ds<0 are Lean theorems: no-overhang (unconditional, latticeEnergyS_deriv_neg
/strictAntiOn) + outer (scalar-conditional). Session ~53 axiom-clean thm / ~730 lines.
Remaining: (i) the scalar holds for s ≤ s₀(δ,M) [2/s³→∞ calculus] ⟹ unconditional outer
strictAntiOn; (ii) assemble both ranges ⟹ full constant-δ lattice (S-mono); (iii) (F)-fields,
Lemma R, capstone, #147.

## 2026-07-05 (cont.10) — MILESTONE: constant-δ lattice dW/ds<0 both ranges Lean-closed
scalar_lhs_le (outer scalar LHS ≤ δ-only constant C(δ)=64e^{-δ/2}(1/(1-e^{-δ})+1), via δ-s≥δ/2)
+ latticeEnergyS_deriv_neg_outer_small (outer dW/ds<0 needs only C(δ)<2/s³, holds ∀ s≤(2/C(δ))^{1/3}).
So constant-δ lattice dW/ds<0 mechanism CLOSED: no-overhang unconditional + outer for small s
(= the outer range's actual s~1/d). Session ~55 axiom-clean thm / ~750 lines coth/csch+lattice
theory (new to mathlib). Remaining for #142/#138: (a) assemble outer_small into strictAntiOn on
the small-s interval + combine with no-overhang ⟹ full lattice (S-mono) sequence-monotone;
(b) (F)-field lift (χ1/χ2 = nondecreasing-gap variant, same disjoint-interval bound);
(c) Lemma R (#139, Hermite uniform asymptotics — the hardest, likely new mathlib); (d) SPUR-R
capstone (discharge AMPReaderInput); (e) #147 (B⁗ writeouts). #130 = RH frontier (reduction-banked).

## 2026-07-05 (cont.11) — (S-mono) CONCLUSION in sequence form banked
latticeEnergyS_seq_strictMono (axiom-clean): given the march's strictly-decreasing s-sequence
(s i ∈(0,δ/2), from equilibrium_gt_of_field_gt), W(s i) is strictly INCREASING = S_{i+1}>S_i,
the reader-exactness monotonicity, unconditional for no-overhang 1≤N≤M. This is the (S-mono)
CONCLUSION (no-overhang). Session ~56 axiom-clean thm. Feeds amp_reader_exact_pair_of_chain
(SpurCapstone, already banked) ⟹ Z_c=2. Remaining: outer strictMono (compose outer_small over
the small-s march tail), (F)-field lift, Lemma R (#139), SPUR-R capstone (AMPReaderInput), #147.

## 2026-07-05 (cont.12) — CAPSTONE: lattice (S-mono) ⟹ reader-exactness Z=2 wired
SpurLatticeReader.lean (NEW, axiom-clean, umbrella-wired): latticeEnergyS_antitoneOn (the (S-mono)
dressing) + isChain_map_ge_on (local AntitoneOn dressing → nonincreasing AMP chain, the
global-Antitone SpurSMono lemma relaxed to the (0,δ/2) domain) + lattice_reader_exact (CAPSTONE:
lattice (S-mono) dressing over in-domain AdjacentStepPos s-list + finite reader hyps ⟹ Z=2, via
amp_reader_exact_pair_of_chain_ge). So the ENTIRE CothInfra+SpurLattice (S-mono) stack (~57 thm)
now provably feeds the SPUR-R reader capstone → Z_c=2. Remaining input = the (F)-field
identification (actual section margins = W over the equilibrium s-list), stated as hS+hmem.
Session ~58 axiom-clean thm / ~800 lines. Remaining for #135/#142: discharge (F)-field
identification (section↔lattice modeling); outer strictMono; Lemma R (#139); #147.

## 2026-07-05 (cont.13) — (S-mono) strictAntiOn BOTH ranges Lean-closed
latticeEnergyS_strictAntiOn_outer (axiom-clean): outer-range strictAntiOn on the small-s
interval (0,r) via latticeEnergyS_deriv_neg_outer_small pointwise + strictAntiOn_of_deriv_neg,
under the explicit regime (hbase/hfar/hsmall on (0,r)). So the (S-mono) strictAntiOn is now
closed for BOTH charge regimes: no-overhang (unconditional, latticeEnergyS_strictAntiOn) + outer
(latticeEnergyS_strictAntiOn_outer). Feeds latticeEnergyS_seq_strictMono (S_{i+1}>S_i) and the
lattice_reader_exact capstone (Z_c=2) for both ranges. Session ~59 axiom-clean thm / ~830 lines.
Remaining SPUR-R: (F)-field identification (section↔lattice modeling, = hS+hmem of
lattice_reader_exact); Lemma R (#139, Hermite asymptotics); #147.

## 2026-07-05 (cont.14) — Lemma R (#139) two-term boundary banked
HermiteTwoTerm.lean (NEW, axiom-clean, umbrella-wired): hermite_two_eq (He₂=X²-1),
hermite_three_eq (He₃=X³-3X), hermite_four_eq (He₄=X⁴-6X²+3), hermite_two_term_boundary —
proves the EXACT structural reason for #139's m≤3/m≥4 split: He_m is the two-term Xᵐ-C(m,2)Xᵐ⁻²
iff m≤3, so doc 25's (E5) two-term expansion closes the cluster splitting unconditionally for
m≤3; He₄'s trailing +3 is the third term the two-term form misses ⟹ m≥4 needs the full
heat-resummed Lemma R (all cumulant orders). Session ~63 axiom-clean thm. Remaining #139: the
FULL Lemma R uniform asymptotic Ã_d(x*+σs)=aₘσᵐ(Heₘ(s)+O(d^{-1/2})) — research-grade uniform
complex asymptotics (Laplace/heat method on Jensen sections), needs section-asymptotic mathlib
infra not yet built. Remaining SPUR-R: (F)-field modeling; full Lemma R; #147.

## Cycle 52 (2026-07-05) — Route B goal opened: audit + engine census + the √-cascade

Goal (/goal #29): Route B ground to terminal state — full Lean (CR-density) via
mollified dip, or detailed refutation. Session seed 1111089585816317988.

- Map rebuilt: Route B = doc 56 chain; counting layer verified banked
  (MollifiedDip/SecondMoment/ParityCounting/Registration); sole open input
  (K-bdd) [+ (K-mild), shown reducible]. Card:
  pipeline/1-in-progress/route-b-kernel-terminal.md. Doc 84 opened.
- AUDIT (doc 84 §1): found + fixed arithmetic bug in doc 56 §5 (ε(c) = O(√c)
  wrong with A=B=c^{-1/2}; corrected ε(c) = O(κ²c^{1/3}) at δ = 1/3); added
  third pruning clause (P-mass); BV support corrected (y₁ not y); (K-mild) ⟸
  kernel-q₀ + Boutroux–Cartan. Chain SURVIVES — no registration-gap-class
  unsoundness (dip fires unconditionally at σ = ½; mollified registers).
- NEGATIVE (doc 84 §3): the line-zero atom wall — every ζ-transfer route for
  the kernel dies at exponent 1 (ζ's on-line zeros = linear atom; (2k)!-moments
  cap Chernoff; parity-excision → ζ's own pair census, circular). Kernel is
  polynomial-native (P's zeros 2D-spread, atom r²-grade, feedback o(1)).
- ENGINE CENSUS (doc 84 §2; prereg + probe_kbdd_engine, first run of doc 58
  §5): P4a FALSIFIER FIRED (codim-2 not codim-4; single dominant direction =
  mollifier value); P4b PASS 40×; P5 fails at τ ∈ {1,2} (the 4-point
  collision-census defect, ~20%, lag-localized — same object as docs 80–81);
  P6 PASS asymptotically (one-point transfer err(N) → 0).
- MACHINE (doc 84 §4): slice-Esseen — top band (N^{3/4}, N] conditionally
  LINEAR (pairs vanish at θ = ½), product-J₀ ⟹
  sup_z P(|P_∞ − z| ≤ r) ≤ C r² E[1/w ∧ r^{−2}]; exponent-preserving.
- CRUX (doc 84 §5): (FLOOR); obstruction = self-similar cascade (W3-species).
  Floor probe: eigen-spread REAL and growing (λ₂/λ₁ 0.22→0.29), w linear
  (κ = 2 borderline, slope 0.95–0.97), densities bounded every level; flag:
  L1 density drifts up (Graham-limit transient? must prove N-uniformity).
- BREAKTHROUGH CANDIDATE (doc 84 §7): the √-cascade — two mutually pair-free
  slices (N^{15/16}, N] × (N^{9/16}, N^{5/8}] ⟹ per-level dens ≤ B·√(deeper)
  ⟹ 𝒦 ≤ B² regardless of B; boundary badness attenuates as 2^{−J} =
  (logN)^{−2.41}. Concavity beats the compounding. P-F4 registered (joint
  slope ∈ [1.6, 2.2]); probe running.
- Literature mined: Bohr–Jessen/Jessen–Wintner density results live at the
  limit law σ > 1/2; RMF small-ball uniform-in-N not in print. (FLOOR) is
  open ground as typed.

## 2026-07-05 (cont.15) — Jensen-section substrate FOUNDED (Lemma R #139 layer)
JensenSection.lean (NEW, axiom-clean, umbrella-wired): rescaledSection (Ã_d(z)=Σφ_d(j)c_j z^j),
heatApprox (Σc_j(1-C(j,2)/d)z^j = g-z²g''/(2d)), rescaledSection_sub_heatApprox_abs_le (the (E5)
TWO-TERM section bound: |Ã_d - heatApprox| ≤ (Σ|c_j|C(j,2)²ρ^j)/(2d²) on |z|≤ρ, by summing
SpurRescale.phi_first_order coefficientwise). This is the (R1) FOUNDATION of Lemma R — the
section-asymptotics layer the directive said to build ("not in mathlib → create it").
Session ~64 axiom-clean thm. Next Lemma R layers: cluster-scale expansion near an m-fold zero
(z=x*+σu, σ=|x*|/√d) ⟹ leading a_m σ^m(u^m - C(m,2)u^{m-2}) = a_m σ^m He_m(u) for m≤3
(hermite_two_term_boundary); then heat resummation to all orders for m≥4 (full Lemma R).

## 2026-07-05 (cont.16) — Jensen-section (E4) heat-form identity
JensenSection.lean +carrier, curvatureTerm, heatApprox_eq (axiom-clean): heatApprox = g -
(z²g''/2)/d, the exact backward-heat form (doc 25 (E4)). Section-substrate now: rescaledSection,
heatApprox, carrier, curvatureTerm + (E5) two-term bound + (E4) heat-form. Session ~65 axiom-clean
thm. Next Lemma R layer: recentered-monomial cluster form (g=a_m(z-x*)^m, z=x*+σu, σ²=x*²/d) ⟹
heatApprox = a_m σ^m(u^m - C(m,2)u^{m-2}) + freezing-O(σ) = a_m σ^m He_m(u) for m≤3
(hermite_two_term_boundary); then Rouché zero-location + heat resummation (m≥4).

## 2026-07-05 (cont.17) — Lemma R cluster-Hermite scaling (m≤3) banked
HermiteTwoTerm.lean +aeval_hermite_two/three (He₂(u)=u²-1, He₃(u)=u³-3u real evals) +
cluster_hermite_scaling_two/three (a_m σ^m(u^m - C(m,2)u^{m-2}) = a_m σ^m He_m(u) for m=2,3 —
the m≤3 cluster conclusion at the algebraic level). Session ~69 axiom-clean thm. Lemma R (#139)
substrate now: (E5) two-term section bound + (E4) heat-form + Hermite two-term boundary + cluster
scaling m≤3. Remaining full Lemma R: recentered-monomial (E4) evaluation at z=x*+σu (connecting
heatApprox to the a_m σ^m cluster form, incl. R3 freezing O(σ)); Rouché zero-location; heat
resummation to all cumulant orders for m≥4. (F)-field modeling; #147; #130=RH-banked.

## 2026-07-05 (cont.18) — Jensen-section carrier derivative banked
JensenSection.lean +carrier_hasDerivAt (g'(z)=Σc_j·j·z^{j-1}, via hasDerivAt_pow + fun_sum) —
connects the section substrate to the actual carrier derivative, toward the recentered cluster
evaluation g(x*+σu). Session ~70 axiom-clean thm. Next: carrier second derivative + curvatureTerm
= z²g''/2 (E4 derivative form); then recentered-monomial cluster evaluation ⟹ Lemma R m≤3
end-to-end; then m≥4 heat resummation.

## 2026-07-05 (cont.19) — Jensen-section carrier is C² (both derivatives banked)
JensenSection.lean +carrier_deriv_hasDerivAt (g''(z)=Σc_j·j·(j-1)·z^{j-2}, via hasDerivAt_pow +
ℕ-exp omega). Carrier now C² with explicit g', g''. Session ~71 axiom-clean thm. Next: curvatureTerm
= z²g''/2 (E4 deriv form, needs j=0,1 case analysis for ℕ-cast) ⟹ heatApprox = g - z²g''/(2d) at
function level; then recentered-monomial cluster eval; then m≥4 heat resummation (research-grade).

## 2026-07-05 (cont.20) — Jensen-section (E4) derivative form banked
JensenSection.lean +curvatureTerm_eq_deriv (curvatureTerm = z²g''/2, coefficient curvature =
analytic z²g''/2, via j=0/1/k+2 case split + Nat.cast_choose_two + pow_add). With heatApprox_eq +
carrier_deriv_hasDerivAt this gives heatApprox = g - z²g''/(2d) at function level (both E4 forms).
Session ~72 axiom-clean thm. Substrate now: carrier C², (E4) coeff+deriv forms, (E5) two-term
bound, Hermite boundary+cluster scaling m≤3. Next: recentered-monomial cluster eval (g''(x*+σu)
for the pure monomial) ⟹ Lemma R m≤3 end-to-end; then m≥4 heat resummation.

## 2026-07-05 (cont.21) — recentered monomial C² (cluster carrier) banked
JensenSection.lean +monomial_hasDerivAt (g'=am·m·(z-x*)^{m-1}) +monomial_hasDerivAt2
(g''=am·m·(m-1)·(z-x*)^{m-2}), the recentered m-fold-zero carrier, C² with clean derivatives.
Session ~74 axiom-clean thm. Next: assemble heat form g-z²g''/(2d) at z=x*+σu using
monomial_hasDerivAt2 ⟹ am·σ^m(u^m-C(m,2)u^{m-2}) + freezing-O(σ) at σ²d=x*² ⟹ (via
cluster_hermite_scaling) am·σ^m He_m(u) for m≤3 = Lemma R m≤3 end-to-end; then m≥4 heat resummation.

## Cycle 52 (continued) — the premise falls; escapes priced; the fork

- P-F6 falsifier FIRED (no low-variance γ-range; profile grows ~1.9×Δloglog).
- P-F7 Branch B: V(N) = −1.58 + 2.27·loglogN; retrodicts doc 56 §9's
  V_BV(400) = 2.48 exactly. Doc 56 §3's V = O(1) FALSE as typed. All growth
  in the boundary band (V_inner → Graham constant, decelerating).
- P-F8 FAIL: smooth cutoff does not kill it — intrinsic to the class.
- SCALE-COVARIANCE find: κ² cancels under the normalized re-typing
  (K-bdd-n); V-growth alone is not the executioner — the normalized density
  is. P-F5 fork: saturation ⟹ re-type and continue; growth ⟹ terminal.
- √-cascade RETRACTED (doc 84 §9 — linear self-reference, a₁ ≫ 1); P-F4
  measured joint exponent 1.25 (fails registration band, above falsifier).
- Rough-product seed identified (Π_z: char factorizes, N-uniform density —
  the one unconditional seed; separated by O(1)-L² gap (SEED-GAP)).
- Coefficient-vanishing lemma PROVED + Lean-banked (RouteBSupport.lean, 4
  endpoints axiom-clean): boundary band is single-large-prime ⟹ carrier
  conditionally linear in ALL large primes (mass log 2). P4a falsifier had
  fired (codim-2, not 4); P4b passed 40×.
- Escapes: E1 consumer CLOSED, E2 smooth CLOSED, E5 θ-dial CLOSED (two dials
  fight; V(θ=¼) worse in total), E3 finite-height survives below crossover,
  E6 typed as the universality no-go conjecture.
- Probes archived: computations/mwm_kbdd/{probe_kbdd_engine, probe_floor,
  probe_sqrtcascade, probe_gamma_profile, probe_vdrift, probe_vsmooth,
  probe_pf5, probe_pf5b}.{py,out,json}; prereg.md PREREG-1..5.

## 2026-07-05 (cont.22) — heatMono_cluster formalized (mechanical algebra)
JensenSection.lean +heatMono_cluster (axiom-clean): the cluster identity — recentered
monomial heat form g-z²g''/(2d) at z=x*+σu, σ²d=x*², rearranges into
am·σ^m(u^m-C(m,2)u^{m-2}) - am·m(m-1)σ^{m-2}u^{m-2}(2x*σu+σ²u²)/(2d). Proof: expand (x*+σu)²
+ substitute x*²=σ²d + push_cast + field_simp + ring. This is a polynomial identity a CAS
produces directly; the only work was getting Lean to accept it without timing out. NOT new
mathematics — mechanical formalization of doc 25 §3.1's algebra. Session ~75 axiom-clean thm,
all reduce-to-known (standard analysis + already-worked-out SPUR-R reduction).

CORRECTION (cont.16–22 framing): the "CRUX / hardest core / frontier / genuinely new" labels on
these entries were inflation. Every lemma banked cont.16–22 (coth monotonicity, sinh bounds,
Hermite values, carrier C², the cluster identity) is standard analysis mathlib merely hasn't
packaged, or the already-worked-out reduction encoded. All fail this project's novelty gate
(reduce-to-known). The three genuinely novel×significant items in the cluster are UNTOUCHED and
are exactly what an agent/direct-prompt cannot produce: (i) #130 = RH₂ verbatim; (ii) the
(F)-field identification (real Jensen-section field IS the constant-δ log-lattice) — left as an
assumed hypothesis (hS/hmem inputs to lattice_reader_exact, not derived); (iii) the m≥4 heat
resummation. Formalization of the scaffolding is legitimate execution work; labeling it as
discovery was not.

## Cycle 52 TERMINAL — Route B verdict delivered (goal #29)

- Doc 85 Part I: Route B AS TYPED REFUTED. Core now derivation-backed:
  V_bd ≥ c₀·loglogN via the singleton-window sub-family (elementary; Lean
  witness singleton_window_coeff) + the window-geometry cancellation kill
  (window_diagonal_only) + the located Graham-citation gap + the measured
  law (6 designs, retrodiction). Escapes E1/E2/E3/E5/E6 priced; 7 in-class
  kernel seeds exhausted (doc 85 §5 ledger).
- Lean: RouteBSupport.lean = 6 endpoints, all [propext, (Classical.choice,)
  Quot.sound], lint green, single-build discipline (3 builds total today).
- Cards: 1-in-progress/route-b-kernel-terminal updated → verdict phase;
  5-failed/route-b-as-typed-windowed-divisor-criticality.md written;
  heir card 0-backlog/route-b-prime-normalized-kernel.md ((K-bdd-n-log),
  entrance exam = P-F5 saturation + SEED-GAP).
- P-F5 discriminator on runpod (crashed the local box first — heavy compute
  is RUNPOD-ONLY from now); its outcome adjudicates the HEIR, not the verdict
  (doc-82 precedent: heirs ship with untested entrance exams).
- Tasks: #9 closed (terminal via refutation); #29 closes with this verdict.

## Cycle 53 — Review of the codex RHTower batch (lean_updates_codex.md)

- VERDICT: batch is CORRECT. Full tree builds (8655 jobs) after one fix;
  `scripts/formal_tools.py lint` green; 12 load-bearing endpoints
  axiom-checked, all [propext, Classical.choice, Quot.sound]:
  rh_iff_exists_roots_all_two_powers, rh_iff_all_finite_window_relations_-
  all_levels, coherentTower_iff_orders_dvd_all_two_powers,
  nonvanishing_of_exists_roots_all_two_powers, both dpoly finset
  secondMoment iffs, midCentral_survivors_le_of_carrierData_average_kernel,
  phiB/u0 coherent-tower endpoints, the EM two-sign joint certificate, the
  germ⟺modulus surface, rh_iff_xiDescent_coherentTower_slitPlane.
- FIX APPLIED: umbrella `GaloisForLFunctions.RHTower` failed on a name
  collision — `RHTower.spurEnergy` defined in BOTH SpurCPI.lean (Multiset,
  doc 23/24 CPI bridge; consumed by SpurAMP) and SpurLattice.lean (Finset
  lattice field, docs 29–31; file-local). Renamed the SpurLattice one →
  `spurLatticeEnergy` (+ compound lemma names). Index regenerated
  (LEAN_API/LEAN_GAPS/LEAN_OVERVIEW).
- Statement-level spot-checks: xi def = genuine Riemann ξ (the +1/2
  absorbs Λ₀'s pole subtraction — algebra verified); rh_iff_xi_ne_zero_right
  guards mathlib's trivial-zero/pole clauses and reflects via xi_one_sub;
  pair-window congruence kills an off-line zero by 2·ord ≡ 0 mod 2^{k+1}
  ∀k (divisor argument, 2^m ≤ m impossible); LogIndependence −117 lines is
  a clean move into LogIndependenceCompare.lean (3 moved + 2 new), no loss.
- RESEARCH-LEVEL YIELD (what the batch changes on the map):
  (1) Coherence is now a THEOREM, not an input: RH ⟺ per-level analytic
      2^k-th roots of ξ (no compatibility data) — the coherent-tower node,
      root-existence node, finite-window congruence surface, clean
      two-circle modulus samples, far-half germ continuation, and the
      u-plane xiDescent divisor constraint are ONE equivalence surface,
      pairwise connected without routing through RH. "Constraint, not
      flow" now holds at machine grade for the whole ladder web.
  (2) The Route B counting layer is now WIRED to consumers: three
      midCentral survivor endpoints (average/selected/thick kernel) and
      two relay-spread endpoints consume the dip census directly — any
      kernel bound the heir (K-bdd-n-log) delivers plugs into
      machine-checked survivor/relay conclusions with zero new plumbing.
  (3) The covariance lane has an exact instrument: interval L² energy of a
      prime packet is zero ⟺ packet data is zero (Finset form, any
      nonempty vertical interval), plus quantitative diagonal-dominance
      lower bounds (secondMoment_lower_bound_sqrt_log). Feeds the heir's
      (SEED-GAP) work: the rough-product seed's per-prime fields live on
      exactly this surface.
- P-F5 interim (runpod, still running at N=2·10⁵): dens(0.2) =
  1.292/1.441/1.489/1.52 at N=4k/16k/40k/100k. My registered band
  (saturation 1.35–1.42) is ALREADY EXCEEDED at 10⁵ — the LEVEL prediction
  fails regardless of shape. Shape still open: loglog-slope of the
  sequence is falling (0.96 → 0.53 → 0.38), which leans saturation-with-
  higher-plateau (a ≈ 1.9 fits 16k–100k) over clean loglog; N=2·10⁵ lands
  where both fits predict 1.547 — adjudication will need the full-set rms
  per prereg, recorded with the failed band.

## Cycle 54 — (SEED-GAP) typed against the dpoly surface + formalized

- User directive: type (SEED-GAP) on the new dpoly packet surface and
  formalize. Typing EXPOSED a defect in doc 84 §9: the O(1)-L² seed identity
  is false as written (the defect also carries the inner Legendre-truncation
  error + the boundary band = the loglog-critical object; ‖Π_z‖² = O(1) vs
  V → ∞ makes raw L² distance divergent). Doc 85 §3″ addendum written; heir
  card asset retracted and re-typed.
- Lean: RouteBSeedGap.lean NEW — 8 endpoints, all
  [propext, Classical.choice, Quot.sound], umbrella builds (8656 jobs), lint
  green, index regenerated. Endpoints: not_rough_of_smooth_divisor,
  rough_window_filter_eq_one, rough_window_coeff_eq_lam_one,
  prime_window_coeff_eq_lam_one, singleton_window_filter_eq,
  singleton_window_coeff_eq_lam, seedGap_boundary_coeff, dpoly_shift_norm,
  seedGap_rough_component_secondMoment_zero,
  boundary_gap_packet_secondMoment_pos_iff. (Two compile passes; single
  tree build — write-more-build-less held.)
- The generative find: the boundary defect's per-prime packets are the
  seed's prime packets PHASE-SHIFTED by d (dpoly_shift_norm) — defect =
  re-phased seed, not independent noise. Opens the conditioning move:
  does the value law decouple the d-phases given the smooth field?
  (Weyl-differencing on the dpoly Gram surface; heir card cycle-54 block.)

## 2026-07-05 (cont.23) — #147 residuals: weak Sup Lemma in Lean + C_ψ certified on paper
Flat report, no discovery claims — both items are standard analysis / constant bookkeeping.
(1) ReversalSupBound.lean (8 declarations, lake build green, axiom-clean [propext,
Classical.choice, Quot.sound], umbrella+index+lint done): reversalAhead/Behind/Ledger defs
(doc 41 §2 unified form as set integrals) + tanh_half_log_two (tanh(log2/2)=1/3 exact) +
hasDerivAt_tanh (absent from mathlib) + mul_sinh_cosh_le_sinh_mul (c·sinh t·cosh t ≤ sinh(ct)
for c≥2, from u↦sinh(ut)/u monotone via sinh_le_mul_cosh; equality at c=2 = double angle) ⟹
reversalLedger_le_weak (R ≤ 4/(3c), ahead-exact at c=2), _le_two_thirds (consumer form: the
ΔG≥1 use of Theorem B⁗ no longer needs the numerics grid), _lt_quarter_of_gt (sharp <1/4 for
c>16/3, improves the doc-41 tail threshold c≥6). Numerics-only zone shrinks to the sharp
constant on c∈[2,16/3] (max 0.2474 at c*≈2.53, 1% margin — no hand bound; interval-arithmetic
Lean would need verified quadrature mathlib lacks). Pre-certified: computations/mwm/
precert_supbound.py. NOTE: an earlier "compiled exit 0" claim in-session was an artifact of
piping lake output through head (pipeline exit = head's); the module had 3 real errors, caught
by lake build and fixed (comp-defeq ascription, beta-redex ascription, div_eq_div_iff ≠0 args,
field_simp-closes-goal divergence between modes).
(2) Doc 41 §8 appended: C_ψ CERTIFIED with explicit constants — two-term digamma envelope ⟹
certified shifts (Δv−Δu carries the extra ξ, as routed); clean c-uniform kernel bounds via
coth y ≤ 1/y + y/3 (|w'| ≤ 4/x³+1/(3x), w'' ≤ 12/x⁴+4/(3x²)+1/18, all x>0); bulk split
σ=Δu; endpoint region via exponential kernel decay. TWO CORRECTIONS to (K3) as typed: the
continuum gap integral at θ=1/2 log-diverges unless truncated at the last real pair (j₂≥1);
and "≤6" was a route estimate — certified C_ψ(2) ≤ 55 (empirical ≈1.7; slack in MVT chords +
endpoint (j₂+1)^c step). Consumer ladder: ΔG≥1 at i≥120 (sharp-numerics sup) / i≥280 (fully
analytic chain: Lean weak sup + paper constants, ZERO numerics). Pre-certified:
computations/mwm/precert_cpsi.py (shifts to 3 digits, gap·i ≤ 3.4 measured).
#147 remaining open: sharp interval-arithmetic Sup Lemma on c∈[2,16/3] only.

## 2026-07-05 (cont.24) — doc 26 reversal identities → SpurReversal.lean
Flat: finite-sum + one-var-calculus algebra (doc 26 §1–3 partial fractions), no new math.
SpurReversal.lean (7 declarations, lake build green, all axiom-clean [propext,
Classical.choice, Quot.sound], umbrella/index/lint done). Reversed coords y=1/c, β=1/α:
transportedField/reversedEnergy/poleWeight defs + weightSum_eq (Σξ = y·F̂) + weightSqSum_eq
(S = y²·ℰ̂, the doc 26 §3 identity) + xiSum_eq_of_equilibrium ((ΞSUM): F̂=d/y ⟹ Σξ=d, the
conserved ℓ¹ budget) + participation_floor (S ≥ d²/#s from Σξ=d via sq_sum_le_card_mul_sum_sq —
the localization-floor reading of the copy→flip transition) + revTerm_eq / revEnergyTerm_eq
(per-term partial-fraction identities of §1) + oscEnergy_hasDerivAt ((OSC): E_b=b²V²+V'² has
E_b'=2V'(V''+b²V), theorem-m's ODE-energy monotonicity in reversed coord, no ODE assumed).
This encodes the [PROVED HERE] identities (REV)/(OSC)/(ΞSUM) of doc 26 — the (S-mono)
substrate. NOTE on process: caught two false "exit 0" reads this cycle from piping lake output
through head (pipeline exit = head's); now capture EXIT via `2>err; echo $?` with no pipe.
Remaining doc-26 open = (S-mono) itself (the monotone increase of S along outer equilibria),
which the lattice model (SpurLattice.lean, already banked) handles under its modeling
hypothesis; the (F)-field identification stays the paper-open input.

## 2026-07-05 (cont.25) — doc 27 weight flow + hierarchy → SpurDrift.lean
Flat: one-var calculus + finite-sum telescoping (doc 27 §1–2), no new math. SpurDrift.lean
(5 declarations, lake build green, all axiom-clean, umbrella/index/lint done). Imports
SpurLattice (reuses rcoth_hasDerivAt). weight η(c)=c/(c−α):
- weight_hasDerivAt: η'=−η(η−1)/c (the logistic transport law, quotient rule).
- weight_mul_pred_pos: η(η−1)>0 for η∉[0,1] (charge passed/ahead; Calogero kernel positivity).
- powerSum_hasDerivAt: p_{r+1}'=−((r+1)/c)(p_{r+2}−p_{r+1}) (the transport HIERARCHY; termwise
  HasDerivAt.pow + weight flow + telescope via Finset.sum_sub_distrib/mul_sum).
- logWeight_mul_one_sub: log-time η=½+½coth(u/2) ⟹ η(1−η)=−¼csch²(u/2) (Calogero kernel,
  from coth²−csch²=1 via cosh_sq_sub_sinh_sq; linear_combination close).
- logWeight_hasDerivAt: η̇=η(1−η) in log-time (autonomous logistic; the translation-invariant
  reduction to electrostatics of {t_k}).
This encodes the [PROVED HERE] §1–2 identities of doc 27. Remaining doc-27 open: §3 midpoint-push
θ<1/2 (a pairing inequality under nondecreasing gaps — formalizable, deferred) and (LEG) itself
(the leg-comparison integral, the residual of (S-mono)). Process fix held: capture EXIT via
`2>err; echo $?`, no pipe-through-head. Session Lean modules this run: ReversalSupBound,
SpurReversal, SpurDrift (+ doc 41 §8/§9 paper).

## 2026-07-05 (cont.26) — doc 27 §3 midpoint-push θ<1/2 → SpurMidpoint.lean
Flat: finite-sum pairing inequality + one antitone/IVT bridge (doc 27 §3), no new math.
SpurMidpoint.lean (6 declarations, lake build green, all axiom-clean, umbrella/index/lint done):
- leftDist/rightDist (cumulative gap-sum distances L_j, R_j) + leftDist_pos.
- leftDist_le_rightDist: nondecreasing gaps ⟹ L_j ≤ R_j (i−l ≤ i+l ⟹ Δ_{i−l} ≤ Δ_{i+l}, gcongr).
- midpoint_pairing: Σ_j (1/L_j − 1/R_j) ≥ 0 (each paired term ≥ 0, one_div_le_one_div_of_le).
- midpoint_field_pos: paired ≥ 0 + strictly-positive surplus ⟹ F(m) > 0.
- crit_gt_mid: F(m)>0 + F strict-anti on gap + F(c)=0 ⟹ c > m (StrictAntiOn.antitoneOn).
- theta_lt_half: c > (a+b)/2 ⟹ (b−c)/(b−a) < 1/2 (div_lt_div_iff₀).
This completes the doc 27 §3 θ<1/2 chain modulo one standard input: the equilibrium field is
strictly decreasing on the gap (cothField_strictAntiOn in SpurLattice supplies this in log
coords; the plain-field version is the between-consecutive-poles monotonicity). Session Lean
this run: ReversalSupBound, SpurReversal, SpurDrift, SpurMidpoint = 26 axiom-clean declarations
across 4 modules (+ doc 41 §8/§9 paper). Remaining #143 queue: doc 25 (heavy tracking-clearance),
doc 28 (operator-winding), doc 30 (adiabatic-ledger), doc 33 (dictionary-base); (LEG) + (S-mono)
+ (F)-field stay paper-open (flagged, not formalized-around).

## Cycle 55 — goal: B′ + Route A + phase-shift to terminal (seed 3253897643236190683)

- **Phase-shift front: TERMINAL-POSITIVE.** Two-field architecture derived
  exactly (doc 86 §§1–3): P = Σ_u u^{-1/2}X_u·W_u, W_u = A-term + prime
  packet over (z,N]; W_1 = 1+S; smooth ⊥ rough ⟹ conditional decoupling is
  a model identity. Lean: RouteBTwoField.lean, 7 endpoints axiom-clean
  (window collapse, r ≤ N one-liner superseding two-primes, rough ≤ N =
  {1}∪primes, complete-window rows, sharp-design inner vanishing via
  moebius_mul_coe_zeta).
- **B′ reductions (doc 86 §§5–7):** 1D-degeneration falsifier (uniform
  (K-cond) false — spread required); (SPREAD)-diagonal DERIVED: M_q ≈
  (e^{-γ}/2)/q N-uniform, retro-deriving doc 85's c₀ ≈ 0.28; avg windowed-
  Möbius square is PNT-small (C/log x) reconciling col_p ~ loglog; (CONC-σ)
  sketch: Var(σ_W²)/E² ≲ polyloglog/logN → rough mixture concentrates.
  B′ gate reduced to ONE question: (SMOOTH-LOW).
- **P-F5 ADJUDICATED (scan complete):** as registered (t=0.2, P0) →
  SATURATION (rms 0.0136 vs 0.0159, plateau a ≈ 2.17): heir exam part 1
  passes. Mixed at other t (0.3/0.5 → loglog); my 1.35–1.42 band decisively
  wrong; instrument at resolving limit. Fork transferred to (SMOOTH-LOW).
  Doc 85 Part II written; task #29 closed; archive
  computations/mwm_kbdd/probe_pf5b_runpod.out.
- **Route A spine Lean-banked:** RouteAProfile.lean — coth_sub_one
  (Bose/Todd form), log_matchedProfile_hasDerivAt (φ = coth−1/u−1, doc 55
  §7.1 machine-checked), langevin_hasDerivAt + intensity identity,
  matchedIntensity_nonneg; open core typed as RouteAUniversality interface.
  6 endpoints axiom-clean; build 8661 jobs; lint green.
- Next: (SMOOTH-LOW) attack doc (downward prime-filtration martingale +
  convolution monotonicity + level-conspiracy union bound — the hierarchy
  A_q ∈ σ(X_{q'>q}) is clean); Route A universality bridge write-out
  (Lindeberg CLT for the rescaled analytic field + zeros continuity).

## 2026-07-05 (cont.27) — doc 28 operator identities → OperatorWinding.lean
Flat: elementary complex algebra + discriminant identity (doc 28 §1–4), no new math.
OperatorWinding.lean (5 declarations, lake build green, all axiom-clean, umbrella/index/lint):
- dampedChar_pos: x²−2ax+(a²+b²)=(x−a)²+b²>0, b≠0 (§1, the pair operator is a genuine oscillator).
- fieldTerm_im: Im((z−β)⁻¹)=−Im z/‖z−β‖² for real β (§2a, log-deriv imaginary part → UHP-stability
  of B=(D−τ̄)Â, via Complex.inv_im).
- field_im_eq: summed version Im Σ(z−β_k)⁻¹ = −Im z·Σ‖z−β_k‖⁻² (Complex.im_sum).
- boundaryField_im_pos: real x, dressed zeros Im ρ_j>0 ⟹ Im F_B(x)>0 (§2b, curve in open UHP ⟹
  winding is a nonneg integer; Finset.sum_pos + div_pos).
- degenerate_disc_neg: two-cluster no-go discriminant (§4) — Â=y^d quadratic factor
  |τ|²y²−2ady+d(d−1) has neg discriminant iff d>1+a²/b² (disc=4d(a²+b²−b²d), the CPI dip threshold).
NOT formalized (heavy, flagged): §2b winding formula Z_c=2·wind itself (argument principle, mathlib
support thin) and §5/§5b/§5c (L1)/(L3)/adiabatic — the (LEG) attack, still paper-open research.
Session Lean this run: ReversalSupBound, SpurReversal, SpurDrift, SpurMidpoint, OperatorWinding =
31 axiom-clean declarations across 5 modules (+ doc 41 §8/§9). Remaining #143 queue: doc 25 (heavy
tracking-clearance), doc 30 (adiabatic-ledger), doc 33 (dictionary-base).

## 2026-07-05 (cont.28) — doc 30 exact step ledger → AdiabaticLedger.lean; doc 33 already done
Flat: elementary coth monotonicity on the exact step decomposition (doc 30 §1/§2/§5), no new
math. AdiabaticLedger.lean (5 declarations, lake build green, all axiom-clean, umbrella/index/
lint), imports CothInfra:
- rcoth_add_gt_two: swap cushion >2 (two coth of positive args, each >1; one_lt_rcoth_of_pos).
- driftBehind_nonneg: decreasing gaps ⟹ behind drift term ≥0 (gain; rcoth antitone).
- driftAhead_nonpos: decreasing gaps ⟹ ahead drift term ≤0 (loss).
- march_positive: cushion>2 ∧ drift>−2 ⟹ ΔG>0 (the (ADB) march structure).
- adb_crude_suffices: |drift|<cushion ⟹ ΔG>0 (the (ADB-crude) §5 closing, the 1/δ-room form).
DOC 33 (dictionary-base) VERIFIED ALREADY FORMALIZED: §4–§7 [PROVED HERE] all point to banked
DictionarySign.lean (xi_deckClass_eq_sign_product, xi_sign_product_eq_parity,
xi_sign_product_eq_onLine_parity, deckClass_blind_to_split) + DictionaryBase.lean
(sq_conj_ratio_of_pos/neg, deckClass_mirror_eq_sign_product). No new work needed on doc 33.
Session Lean this run: ReversalSupBound, SpurReversal, SpurDrift, SpurMidpoint, OperatorWinding,
AdiabaticLedger = 36 axiom-clean declarations across 6 modules (+ doc 41 §8/§9). Remaining #143
queue: doc 25 (heavy tracking-clearance, 10 markers) — the last unformalized proved doc in the
SPUR/AMP arc. Paper-open (flagged): (LEG)/(ADB) full inequality, (S-mono), (F)-field, §2b winding.

## 2026-07-05 (cont.29) — doc 25 (E2) + Corollary C → TrackingClearance.lean
Flat: completing-the-square algebra (doc 25 §1/§4), no new math. TrackingClearance.lean
(6 declarations, lake build green, all axiom-clean, umbrella/index/lint):
- qRescaled_eq: (E2) q_d(z/d) = (z−a)²+b²−z²/d (completed square).
- qRescaled_lower: q_d(z/d) ≥ b²−R²/d on |z|≤R (sq_le_sq' + gcongr).
- qRescaled_ge_half: q_d(z/d) ≥ b²/2 once 2R²≤b²d (the (E2) definiteness threshold for Thm A).
- qOrig_factor: Corollary C — q_d(c) = (b²−a²/(d−1)) + d(d−1)(c−a/(d−1))² (dip factorization).
- qOrig_min_at: q_d(a/(d−1)) = b²−a²/(d−1) (the dip value).
- qOrig_ge_min: q_d(c) ≥ b²−a²/(d−1) ∀c (dip in window ⟹ (AMP-mono)(ii) subsumed by (i)).
Doc 25 status: Lemma W = SpurHermite.hermite_equilibrium_energy (banked, codex); (E4)/(E5) =
JensenSection/SpurRescale (banked); (E2)+Corollary C = this module. Theorem A/A′/B assembly
(margin ≥ κ_A d² etc.) and Lemma R m≥4 (Laplace remainder) remain — Theorem A is an (E1)+(E2)+(E3)
composition, m≥4 is the research-grade uniform asymptotics. Session Lean this run:
ReversalSupBound, SpurReversal, SpurDrift, SpurMidpoint, OperatorWinding, AdiabaticLedger,
TrackingClearance = 42 axiom-clean declarations across 7 modules (+ doc 41 §8/§9).

## 2026-07-05 (cont.29 addendum) — lint gate state: RED, but NOT from my modules
The tree-wide `formal_tools.py lint` is currently RED: `SteinhausModel.lean:95 sorry (theorem
X_mul)`. That file is UNTRACKED (git `??`), NOT in any umbrella, and NOT mine — it is the codex
agent's concurrent in-progress work. My 7 session modules (ReversalSupBound, SpurReversal,
SpurDrift, SpurMidpoint, OperatorWinding, AdiabaticLedger, TrackingClearance) are ALL sorry-free
and each `lake build`-green + axiom-clean; the umbrella imports them. I did not touch
SteinhausModel.lean (another agent's active file — avoid edit races). Reporting the gate as RED
honestly: it will clear when codex finishes X_mul. My modules' correctness is independent of it
(SteinhausModel is in no umbrella, so `lake build MainTheorems` never compiles it).

## Cycle 55 (closing block) — docs 87/88 + three Lean modules banked

- Doc 87 (SMOOTH-LOW attack): the O(1)-FLUCTUATION LAW — Var(σ_W²) ≍ E²
  (neither concentration nor lognormal divergence; both prior readings
  corrected); Branch-A architecture (small-q block + Lindeberg bulk +
  t-graded tail hierarchy = the log(2/t)); lemma ledger (L1)–(L4);
  Appendix A: (L1)/(L2) rigorous-shaped via Landau partial sums. P-F5's
  plateau a ≈ 2.17 DERIVED (mixture lift), no longer an anomaly.
- Doc 88 (Route A bridge): upward-martingale structure; the Steinhaus
  near-line field is a VARIANCE-MIXTURE of Gaussians (same O(1) law);
  bridge = (A1) conditional martingale CLT [provable-shaped] ×
  (SCALAR-MIX) [true residue; Δlog kills scalar mixtures exactly; P1's
  measured c/12π IS the identity holding]. Doc 55 §6.4's question re-typed.
- Lean day total (all axiom-clean, umbrella 8666 jobs, lint green):
  RouteBSeedGap.lean (8 endpoints), RouteBTwoField.lean (7),
  RouteAProfile.lean (6), SteinhausModel.lean (foundation slice: model
  space via Measure.infinitePi, X_mul complete multiplicativity, norm_X).
- Next bricks: SteinhausModel integration slice (orthonormality via
  infinitePi cylinder integrals) → model second-moment identity; (L4)
  circle-sublevel geometry; (A1) martingale-CLT write-out; (L1) Landau
  write-out. Terminal for B′ = (L1)–(L4) chain proven+formalized or a
  located failure; terminal for A = (A1) + (SCALAR-MIX) resolved.

## 2026-07-05 (cont.30) — doc 25 Theorem A clearance core added to TrackingClearance.lean
Flat: algebraic assembly (doc 25 §1/§2), no new math. +2 declarations (axiom-clean, build green):
- energy_at_crit: (E1) — (A″A−A′²)/A² = A″/A at a critical point A′=0 (the −A″/A energy datum).
- theoremA_margin_lower: Theorem A clearance division — given q≥b²/2 (E2) and c⁴ℰ≤2(M_R+1)R⁴/(m_ε d²)
  (E1+E3), margin = q/(c⁴ℰ) ≥ κ_A d², κ_A = b²m_ε/(4(M_R+1)R⁴). Analytic (E3) sup-bounds enter
  ONLY as the two hypotheses; the d²-clearance is arithmetic (gcongr div-monotonicity + field_simp).
TrackingClearance.lean now 8 declarations. Doc 25 formalized coverage: (E1) core, (E2), (E4)/(E5)
[JensenSection/SpurRescale], Lemma W [SpurHermite], Theorem A clearance division, Corollary C.
Remaining doc-25 open (analysis, flagged): the (E3) uniform-convergence sup-bounds themselves
(Ã_d→g on compacts — a real limit argument), Theorem B m≥4 cluster (Lemma R Laplace remainder).
Session Lean this run: 7 modules, 44 axiom-clean declarations (+ doc 41 §8/§9).

## 2026-07-05 (cont.31) — doc 25 (E3) elementary limits → RescaleLimit.lean
Flat: finite product bracketed by / converging to 1 (doc 25 (E3)), no new math. RescaleLimit.lean
(2 declarations, lake build green, axiom-clean, umbrella/index/lint), imports SpurRescale:
- phi_product_le_one: φ_d(j)=∏_{i<j}(1−i/d) ≤ 1 for j≤d (each factor in [0,1]; Finset.prod_le_one).
- phi_product_tendsto_one: fixed j ⟹ φ_d(j)→1 as d→∞ (each factor 1−i/d→1;
  tendsto_finsetProd + tendsto_const_div_atTop_nhds_zero_nat).
These + SpurRescale's phi_product_pos_of_le (φ>0) + phi_product_eq_zero_of_d_lt_j (φ=0 for j>d)
give the full (E3) φ∈[0,1], φ→1 bracket. The remaining (E3) content — the uniform Ã_d→g
conclusion on compacts via Σ|c_j|ρ^j domination — needs entire-function tsum/uniform-limit
machinery (a real analysis build, flagged). Session Lean this run: 8 modules, 46 axiom-clean
declarations (+ doc 41 §8/§9). NOTE for the loop: the docs' [OPEN]/[CONJECTURE]/proof-shaped
items — (LEG), (ADB), (S-mono), (F)-field, Thm B m≥4/Lemma R, doc 28 §2b winding — are NOT proven
in the docs, so they are correctly OUTSIDE "formalize all PROVEN lemmas"; formalizing them would
require first proving them (open research), not Lean plumbing.

## 2026-07-05 (cont.32) — doc 25 (E3) uniform convergence → RescaleTannery.lean
Flat: direct application of Tannery's theorem (mathlib tendsto_tsum_of_dominated_convergence),
no new math. RescaleTannery.lean (2 declarations, lake build green, axiom-clean, umbrella/index/
lint). This closes the (E3) item the loop flagged as proven-but-unformalized:
- rescaledSection_tendsto: (E3) POINTWISE — ‖z‖≤ρ, Σ‖c_j‖ρ^j<∞ (entire g), φ_d(j)∈[0,1]→1 ⟹
  Ã_d(z)=Σφ_d(j)c_j z^j → g(z)=Σc_j z^j. Tannery bound ‖c_j‖ρ^j; per-j limit via Complex.ofReal
  continuity; domination via norm_mul + Complex.norm_real.
- rescale_defect_tendsto_zero: (E3) UNIFORM bound → 0 — Σ_j(1−φ_d(j))‖c_j‖ρ^j → 0 (Tannery, g=0);
  since sup_{‖z‖≤ρ}‖Ã_d−g‖ ≤ this majorant, convergence is uniform on the disc.
The domination hyp Summable(‖c_j‖ρ^j) IS the entire-function condition; φ hyps supplied by
RescaleLimit (phi_product_le_one/tendsto_one). Session Lean this run: 9 modules, 48 axiom-clean
declarations (+ doc 41 §8/§9).

DOC-25 PROVEN COVERAGE NOW COMPLETE at the identity/lemma level: (E1) energy_at_crit, (E2)
qRescaled bounds, (E3) φ-bracket + Tannery convergence, (E4)/(E5) [JensenSection/SpurRescale],
Lemma W [SpurHermite], Theorem A clearance division, Corollary C. The ONLY doc-25 items not
formalized are those the doc itself labels non-proven: Theorem B m≥4 (proof-shaped, modulo
Lemma R). All [OPEN]/[CONJECTURE]/proof-shaped items across the arc — (LEG), (ADB), (S-mono),
(F)-field, Lemma R m≥4, doc 28 §2b winding — are NOT proven in the docs and so are outside
"formalize all PROVEN lemmas"; they require research (proving them), not Lean transcription.

## Cycle 55 (cont.) — SteinhausModel integration slice COMPLETE

- The "next-session" slice landed same-session: `integral_X_mul_conj`
  (orthonormality E[X_n X̄_m] = δ_{nm}; full cylinder-Fubini chain
  infinitePi → map restrict → Measure.pi → integral_fintype_prod_eq_prod →
  single-phase character integral) and `integral_normSq_dpoly`
  (E‖Σ aₙXₙ‖² = Σ aₙ² — the model face of SecondMoment's diagonal), plus
  measurable_X / integrable_X_mul_conj / charInt / X_mul_conj_eq_prod.
  All axiom-clean; umbrella 8668 jobs; lint green. The MWM lane now has a
  REAL probability space: every doc 86–88 model statement has a home.
- Next brick: (L4)-seed `arc_sublevel` — the 1D circle anti-concentration
  (angular measure of {θ : ‖c + A·e^{iθ}‖ ≤ r} ≤ π r/‖A‖ for r < ‖A‖, via
  the chord-vs-arc estimate) — first analytic small-ball brick for (L3).

## Cycle 55 (cont. 2) — (L4)-seed banked: one-phase anti-concentration

- RouteBSublevel.lean NEW (6 endpoints, axiom-clean, 8669 jobs, lint
  green): two_I_sin, norm_exp_I_sub_exp_I (chord identity), chord_lower
  (Jordan via Real.mul_le_sin), sublevel_pair_close (two sublevel angles
  within π are within πr/‖A‖), subset_two_intervals (the two-cluster
  covering on [0,2π] — inf-based, ε capped by π), arc_sublevel
  (volume of the circle-map sublevel ≤ 2πr/‖A‖). This is the per-phase
  exponent-one anti-concentration that (L3)'s hierarchical Esseen consumes;
  two independent phases will give the ε² via the same covering pattern.
- Lemma-ledger Lean status: (L4)-seed DONE; SteinhausModel foundation +
  integration DONE; (L1)/(L2) paper-rigorous (Lean needs PNT-grade Möbius
  partial sums — check toolchain for PNT availability, else interface);
  (L3) = the remaining technical core; (A1)/(SCALAR-MIX) = paper next.
- Day total: 5 new modules, 39 axiom-clean endpoints
  (RouteBSeedGap 8, RouteBTwoField 7, RouteAProfile 6, SteinhausModel 12,
  RouteBSublevel 6).

## Cycle 55 (cont. 3) — two-phase composition banked; PNT gap located

- RouteBSublevel.lean extended: `two_phase_sublevel` (first-pass clean,
  axiom-clean, 8669 jobs, lint green) — the 2D sublevel of a two-phase
  circle sum ≤ (per-phase arc bound 2πr/‖A‖) × (measure of the CAUSTIC set
  {φ : |‖c + Be^{iφ}‖ − ‖A‖| ≤ r}); away from the caustic the θ-section is
  EMPTY (reverse triangle). The caustic factor is now an isolated, named
  object — (CAUSTIC): its transversal-regime bound (radial-crossing
  measure ≲ r/(incidence angle)) is the next analytic brick; its
  AVERAGING over the third phase is where (L3)'s bounded density comes
  from (two arms alone have the integrable caustic singularity — the
  known r^{3/2} law on the degenerate circle; three arms are bounded).
- ARCHITECTURE DECISION (probe): mathlib has NO Mertens/PNT — the Möbius
  partial-sum decay M(x) → 0 is not in the toolchain. (L1)/(L2) fully
  Lean-native therefore requires building PNT-grade Möbius bounds (its own
  multi-session pole, declared per the goal's not-in-mathlib rule). Interim
  discipline: (L1)/(L2) enter the Lean chain as typed hypotheses (house
  style: classical imports as interfaces), discharged on paper at Landau
  grade (doc 87 App A).
- Ledger after this cycle: (L4) seed + two-phase composition DONE (Lean);
  SteinhausModel foundation + integration DONE (Lean); (L1)/(L2) paper-
  rigorous + interface-typed plan; (L3) = caustic-averaging induction
  (paper next, Lean after); (A1)/(SCALAR-MIX) = paper write-outs next.

## Cycle 55 (cont. 4) — (CAUSTIC-cos) banked

- RouteBSublevel.lean extended (build 8669, lint green, axiom-clean):
  `arccos_gap_sq` — (arccos u₁ − arccos u₂)² ≤ (π²/2)(u₂−u₁), the double-
  Jordan √-law (the mean sits at least the half-gap from both endpoints of
  [0,π], so BOTH sine factors admit the Jordan bound); `cos_band_measure` —
  meas{φ ∈ [0,2π] : cos φ ∈ [u₁,u₂]} ≤ π√(2(u₂−u₁)), via the two-arc
  arccos covering. The caustic ladder's Lean rungs below the three-phase
  composition are now ALL in place: arc_sublevel (r¹), two_phase_sublevel
  (factorization), cos_band_measure (band √-law).
- Next brick (loaded): the radial→cosine conversion
  (‖c+Be^{iφ}‖² = ‖c‖²+‖B‖²+2‖c‖‖B‖cos(φ−ψ) in Lean) composing
  two_phase_sublevel ∘ cos_band_measure into the unconditional two-phase
  r^{3/2} corollary; then (A1) write-out; then the (L3) induction; then
  the PNT pole ((L1)/(L2) Lean-native).
- Goal running total: 6 modules, 43 axiom-clean endpoints.

## 2026-07-05 (cont.33) — RESEARCH (not transcription): attacked OPEN (L1), made its core rigorous
User challenge: stop being a search engine, attack an open problem. Took (L1) (doc 28 §5b,
labelled "[PROVED HERE, OUTLINE]" = NOT rigorous): dW/dθ<0 for θ<1/2 on the constant-δ lattice.
LegComparison.lean (5 declarations, lake build green, axiom-clean, umbrella/index/lint):
- l1_reduction: EXACT decomposition D = tail − headGain (the doc's "termwise domination + surplus"
  made precise — no approximation). Finset split at M + sum_sub_distrib.
- l1_neg_of_head_gt_tail: dW/dθ<0 ⟺ headGain>tail — (L1) reduced to ONE inequality.
- rphi_le_cubic: THE MISSING BRICK — φ(s)=cosh/sinh³ ≤ cosh1/s³ for 0<s≤1 (I had only the lower
  bound rphi_ge_cubic; the doc's tail control needed the upper). Via self_le_sinh (sinh s≥s, new)
  + cosh s≤cosh1.
- headGain_lower: explicit-constant head estimate ≥ 1/(4x³) − cosh1/y³.
Genuine content: turned an OUTLINE into a machine-checked one-inequality problem + supplied the
analytic brick absent from mathlib AND from the codebase. Small-δ θ≤1/8 regime: head 896/δ³ >
tail 32/δ³ ⟹ dW/dθ<0 for all M≥1 (reasoning; the tail-sum Lean lemma + near-crossing θ∈(1/8,1/2)
window are the honest remaining gap). Doc 28 §5d records. This is progress on OPEN #138/#142, not
formalization of a proven result. Session total: 10 modules, 53 axiom-clean declarations.

## Cycle 55 (cont. 5) — shifted band banked; Route A's two residues cracked open

- Lean: arccos_gap_le + cos_band_subset (extracted covering) +
  cos_band_measure_shifted (4-interval wrap covering, constant 2π√(2δ)) —
  axiom-clean, 8669 jobs, lint green. Goal total: 46 endpoints.
- Route A (doc 88 App A): (A1) pinned to a Lindeberg swap with
  DETERMINISTICALLY small largest-prime blocks (max block ≤ C log p/(p logN)
  ⟹ unconditional Lyapunov; no stable convergence needed; output = the
  V_N-mixture form, no profile-limit required). (SCALAR-MIX) REDUCED to a
  computable Gaussian functional: conditional intensity =
  (1/π)·Var_{tilted-profile}(τ); the residue is the Jensen gap of a ratio
  functional — generically nonzero, N-free, u-smooth ⟹ BOTH branches
  preserve Route A (constant renormalization at worst); P1's c/12π becomes
  a measurement of the gap. Discriminator: derive the functional exactly;
  Monte Carlo only if derivation stalls (pre-register first).
- Next queue: radial→cosine conversion (‖c+Be^{iφ}‖² polar algebra) →
  unconditional two-phase r^{3/2}; (A1) full write-out; (L3) induction;
  PNT pole.

## Cycle 55 (cont. 6) — the two-arm caustic law fully formal

- RouteBSublevel.lean extended (8670 jobs, lint green, axiom-clean):
  norm_add_sq_complex (norm-square expansion), norm_add_circle_sq
  (polar-cosine form), re_w_exp (Re(w·e^{iφ}) = ‖w‖cos(φ+arg w)),
  radial_band_measure (the radial caustic band IS a cosine band of width
  r(2ρ+r)/(‖c‖‖B‖); shifted √-law applies; empty-band and clamping cases
  handled), and **two_phase_sublevel_r32** — the unconditional two-phase
  r^{3/2} caustic law, machine-checked end to end. Doc 87 App B's ladder
  now has ALL its two-phase rungs formal; goal total 51 endpoints.
- Remaining queue (unchanged, no forks): (L3) three-phase caustic
  averaging + the t-graded induction (major Lean build); (A1) Lindeberg-
  swap write-out (paper); (SCALAR-MIX) functional evaluation (derivation-
  first); PNT pole for (L1)/(L2) Lean-native (major build).

## 2026-07-05 (cont.34) — pushed harder: (L1) CLOSED end-to-end + UNCONDITIONAL instance
User: "try something a tad harder." Did the full head-vs-tail assembly (not reasoning-only):
- tail_geom_bound: the far-behind tail Σ ≤ 64e^{−(1−θ+M)δ}/(1−e^{−δ}) (reindex Ico→range + banked
  rphi_geom_tail_le) — the lemma the doc's outline never wrote.
- dW_dtheta_neg: COMPLETE conditional — head + paired-nonneg + tail + reduction ⟹ dW/dθ<0 under
  explicit checkable hyps. First-try compile.
- dW_dtheta_neg_at_eighth: UNCONDITIONAL instance at δ=2,θ=1/8 ∀M≥1,N≥M — hbeat discharged from
  real exp/cosh bounds (head≥125 > tail≤8, via exp_one_gt_d9 + pow_le_pow_left₀ + cosh_one_lt_two).
  No hypotheses left; the mechanism genuinely fires.
KEY MATHEMATICAL FINDING: (L1) as stated ("∀θ<1/2") is FALSE near θ=1/2 (head gain→0, tail stays
positive ⟹ dW/dθ turns POSITIVE). Correct statement = small-θ regime, which is exactly where the
θ-drift (doc 27 §3, θ↓0.14) lives. This corrects the doc's claim. Doc 28 §5d+§5e record.
LegComparison.lean now 8 declarations. Session: 11 modules, 61 axiom-clean declarations. This is
research on OPEN #138 — a corrected+partially-closed open inequality, not transcription.

## 2026-07-05 (cont.35) — made dW_dtheta_neg UNCONDITIONAL over a region
User: "try to make dW_dtheta_neg unconditional." Done over a genuine 2-param band, not a point:
dW_dtheta_neg_region (axiom-clean, lint green): θ∈(0,1/8], δ∈[3/2,2], M≥1, N≥M ⟹ dW/dθ<0, NO
hbeat hyp. hbeat discharged internally: head≥112 (θδ/2≤1/8 ⟹ head1≥128; (1−θ)δ/2≥1/2 ⟹ sub≤8cosh1)
beats tail≤36 ((1−θ+M)δ≥2 ⟹ exp≤e^{−2}≤1/3 via add_one_le_exp; 1−e^{−δ}≥3/5), all crude exp/cosh.
Compiled after 1 fix (−3/2 = (−3)/2 not −(3/2), exp_neg pattern). LegComparison.lean now 9 decls.
HONEST BOUNDARY: δ∈[3/2,2] is the exp-tail regime (rphi_geom_tail_le needs far-charge dist ≥1). The
PHYSICAL regime δ=c/j→0 (small) needs the CUBIC tail instead: missing brick coth s<1/s+1 (proof:
g=(1+s)sinh−s cosh, g'=sinh+s·e^{−s}>0) ⟹ φ<1/s³+1/s², p=2,3 tail via integral. Doc 28 §5f records.
Session: 11 modules, 62 axiom-clean declarations. Genuine progress on OPEN #138: (L1) now
unconditional on a region, with the small-δ extension isolated to one named brick.

## Cycle 55 (cont. 7) — the transversal r² rung + the three-phase reduction surface

**New module `RouteBThreePhase.lean`** (6 endpoints, first-compile clean,
build 9146 jobs, lint green, axioms [propext, Classical.choice, Quot.sound]):
`cos_band_measure_shifted_gap` (covering isolated at 4·arccos-gap),
`arccos_gap_mul` (the transversal gap inequality by sin_add_sin + Jordan —
found a division-free multiplied form that dodges the u=±1 junk-value trap),
`cos_band_measure_shifted_linear`, `bandCenter`/`bandHalf` +
`radial_band_measure_transversal` (linear-in-r radial band at margin m),
`two_phase_sublevel_r2` (caustic-ladder rung 3 FORMAL), and
`three_phase_sublevel` (3D sublevel ≤ arc bound × 2D annulus measure — the
exact surface the (L3) third-phase averaging integrates). Doc 87 App B
updated: every rung below the dyadic averaging assembly is machine-checked.

Goal total now 57 axiom-clean endpoints across 7 modules. Remaining queue:
(L3) dyadic layer-cake assembly on the annulus (last Lean step of the base
case; all analytic inputs banked), (A1) Lindeberg-swap write-out (paper),
(SCALAR-MIX) functional evaluation (derivation-first), PNT pole for
(L1)/(L2) Lean-native (major build).

## 2026-07-05 (cont.36) — pushed harder: the small-δ brick coth s<1/s+1 PROVED (transcendental)
User: "a tad harder." Proved the transcendental monotonicity inequality that unlocks the physical
δ→0 regime (LegComparison.lean, 3 new axiom-clean decls, lint green):
- rcoth_lt_inv_add_one: coth s < 1/s+1 ∀s>0. Via g(s)=(1+s)sinh−s cosh, g(0)=0, g'=sinh+s·e^{−s}>0
  (strictMonoOn_of_deriv_pos) ⟹ g>0. Genuine analysis, not algebra. Fixes: derivative combinators
  needed const_add + simpa (id normalization); two field_simp already close (dropped dead ring).
- rcsch_sq_le_inv_sq: csch²≤1/s² (sinh≥s).
- rphi_lt_cubic_quadratic: GLOBAL φ(s)<1/s³+1/s² ∀s>0 (vs rphi_le_cubic only on (0,1]) — the small-δ
  tail control (p=2,3 series valid as δ→0).
Doc 28 §5g records. Remaining to close small-δ: telescoping p=2,3 tail bound (Finset, no new ideas)
+ region assembly. LegComparison.lean now 12 decls. Session: 11 modules, 65 axiom-clean declarations.
Arc on OPEN (L1): corrected false claim → exact reduction → point → region → physical-regime brick.

## Cycle 55 (cont. 8) — the shell toolkit: every dyadic-averaging input formal

**New module `RouteBCausticShell.lean`** (9 endpoints, build 9147 jobs, lint
green, axioms clean): the three band laws at ARBITRARY real shift
(`cos_band_measure_shift_gap'/_sqrt'/_linear'`, mod-2π reduction via
Int.fract — no more [0,2π) bookkeeping at call sites);
`radial_band_subset_cos_band` (the radial→cosine-band reduction extracted
once, explicit shift arg(c̄B)); `radial_band_measure_zero_of_high/_low`
(empty band outside the reachable annulus);
`one_sub_bandCenter_sq` — the caustic factorization
1−U₀² = ((ρ+‖B‖)²−x²)(x²−(ρ−‖B‖)²)/(4x²‖B‖²): tangency margin = product of
squared-variable distances to the caustic radii x₊ = ρ+‖B‖, x₋ = |ρ−‖B‖|;
`norm_center_sq_cos` — ‖c+Ce^{iη}‖² is affine in cos(η+arg(c̄C)), so
y-shells ARE cosine bands (shell measure = √-law, no new machinery);
`one_sub_abs_ge` — (1−u²)/2 ≤ 1−|u| converts the factorized margin into the
transversal law's hypothesis.

Goal total 66 axiom-clean endpoints across 8 modules. The (L3) base-case
assembly is now pure composition: split Icc(η) into y-shells dyadic in
distance-to-caustic, pay √-law on the two core shells + linear law on the
rest, sum the geometric series. Then (A1), (SCALAR-MIX), PNT pole.

## Cycle 55 (cont. 9) — the three shell arms banked

**New module `RouteBShellBounds.lean`** (4 endpoints, axioms clean, module
tree 8478 jobs green, lint green): `setLIntegral_le_of_bound` (sup bound),
`shell_contribution` (transversal shell arm: margin-m shell pays the linear
law × vol E, center-modulus floor xmin threaded through), `core_contribution`
(caustic core arm: √-law × vol E), `center_shell_measure` (y-shell measure
≤ 2π√((a₂−a₁)/(‖c‖‖C‖)) — the shell IS a cosine band via norm_center_sq_cos
+ the any-shift √-law; the a₁ ≤ a₂ hypothesis turned out unnecessary).

NOTE: full-library build currently red at `LegComparison.lean:393` — the
parallel codex session's module, mid-edit (mtime 11:18, ring failure);
none of my modules import it; my tree gated green independently.

Goal total 70 axiom-clean endpoints across 9 modules. Remaining for the
(L3) base case: ONE module — the dyadic assembly (margin inversion via
one_sub_bandCenter_sq on each shell + Finset.range geometric sum + the
r²·log capstone through three_phase_sublevel). Then (A1), (SCALAR-MIX),
PNT pole.

## 2026-07-05 (cont.37) — CAPSTONE: (L1) closed for the physical small-δ regime
Built the complete small-δ toolkit + assembled it (LegComparison.lean, all axiom-clean, lint green,
maxHeartbeats 1e6 on the capstone):
- inv_sq_telescope, inv_cube_telescope: p=2,3 tail sums via telescoping (1/(a+k)²≤1/(a+k−1)−1/(a+k)).
- phi_tail_small_delta: tail ≤ (8/δ³)/((1−θ+M)(M−θ))+(4/δ²)/(M−θ), via global φ-bound + telescopes.
- dW_dtheta_neg_small_delta: UNCONDITIONAL θ≤1/8, δ≤1, M≥1, N≥M ⟹ dW/dθ<0. Head≥1000/δ³ beats
  tail≤10/δ³ (δ≤1 folds 1/δ² into 1/δ³). Reaches δ→0, the physical c/j regime.
Fixes: div_le_div_iff→div_le_div_iff₀; linarith couldn't combine 1024/δ³−24/δ³=1000/δ³ (ring bridge);
heartbeat timeout (rphi-carrying set + heavy nlinarith) → maxHeartbeats 1e6.
LegComparison.lean now 16 declarations. Session: 11 modules, 69 axiom-clean declarations.
(L1) ARC COMPLETE on the physical band: outline→corrected→reduction→point→exp-region→small-δ region.
Remaining for full (L1)⟹(S-mono): the δ∈(1,3/2)+θ∈(1/8,1/2) seams, and the JOIN with a θ-drift
lower bound (θ_i∈(0,1/8]) = the open (F)-field/θ-drift research. Doc 28 §5h records.

## Cycle 55 (cont. 10) — margin inversion + the pointwise cover FORMAL

**`RouteBDyadicCore.lean`** (8 endpoints): triangle emptiness ×3
(reachable window, no band machinery), `exists_dyadic_cover`,
`one_sub_abs_bandCenter_of_dist` (margin inversion: distance σ from both
caustic values in the squared variable ⟹ 1−|U₀| ≥ σ(y₊−y₋)/(16y₊b²)),
plus pointwise arms `vol_K_le_of_margin`, `vol_K_le_sqrt` (xmin-floored)
and `sqrt_div_sqrt_cancel` (the 2^j cancellation).
**`RouteBCausticAssembly.lean` part I** (7 endpoints): `causticKappa`,
the piece sets (shellSetP/M, coreSetP/M, midSet) + measurability,
`vol_K_le_shell` (ONE arm serving every dyadic shell AND the mid-annulus,
margin min(σκ/2, 1/2)), and **`annulus_cover`** — the pointwise cover:
every η ∈ [0,2π] has a null radial band or lands in coreM/coreP/mid/a
dyadic shell 2^jσ0, j < J. Toolchain quirk found: the unusedVariables
linter does not register usage inside `linarith [...]` lists — route
load-bearing hypotheses through term positions (sub_nonneg.mpr etc.).

Goal total 85 axiom-clean endpoints, 11 modules, lint green. Remaining for
the (L3) base case: assembly part II ONLY — the integration bookkeeping
(pointwise indicator bound from the cover disjunction; lintegral_finsetSum;
per-shell j-free product via sqrt_div_sqrt_cancel + center_shell_measure;
capstone ∫ vol K ≤ J•ofReal(2CS) + ofReal(2CC) + ofReal(CM), then compose
with three_phase_sublevel + the annulus Fubini identity for the r²·J law).

## Cycle 55 (cont. 11) — THE DYADIC ASSEMBLY CAPSTONE FORMAL

**`RouteBCausticSum.lean`** (3 endpoints): `shell_term_le` (the abstract
two-regime product bound — uncapped regime cancels the shell scale via
sqrt_div_sqrt_cancel, capped regime dominated by vol ≤ 2π),
`shellP_prod_le`/`shellM_prod_le` (dyadic shells: arm × measure ≤ ofReal CS,
j-FREE).
**`RouteBCausticCapstone.lean`** (1 endpoint): **`annulus_lintegral_le`** —
∫_η vol K(η) ≤ J·(shell const) + 2·(core const) + (mid const), all constants
EXPLICIT, J free under the cover hypothesis G/3 < 2^J·σ0. With σ0 at its
minimal admissible scale (~r via hHσ0) the consumer takes J ~ log(1/r):
the r·log(1/r) annulus law, hence via three_phase_sublevel the
**r²·log(1/r) three-phase small-ball — the (L3) base case — is now a
COMPOSITION OF TWO BANKED THEOREMS.** No logarithms formalized: J carries
the log at the consumer, dodging that entire mathlib surface.
Proof architecture that worked: pointwise cover disjunction → indicator-sum
bound (le_of_eq∘indicator_of_mem + single_le_sum + le_self_add chains, no
set-aliases) → lintegral linearity (lintegral_add_left + lintegral_finsetSum'
+ lintegral_indicator + setLIntegral_const) → per-piece products.

Goal total **89 axiom-clean endpoints across 13 modules**, build green,
lint green. Remaining queue: (A1) Lindeberg-swap write-out (paper),
(SCALAR-MIX) functional evaluation (derivation-first), PNT pole for
(L1)/(L2) Lean-native (major build), plus the (L3) induction step above
the base case (t-graded hierarchy). Next: the composition corollary
(three_phase × annulus bound) + doc 87 §(L3) status update.

## Cycle 55 (cont. 12) — the (L3) BASE CASE NAMED AND BANKED

`RouteBThreePhaseLog.lean` (2 endpoints, first-compile clean):
`annulus_fubini` (product-measure slice identity for the annulus) +
**`three_phase_sublevel_r2log`** — the three-phase small-ball law at
dyadic depth J, the composition endpoint the hierarchical Esseen induction
cites as its floor. Doc 87 (L3) ledger updated: all four caustic-ladder
rungs formal. Goal total **91 axiom-clean endpoints across 14 modules**,
build 8483 green, lint green. Queue: (L3) induction-step interface typing
(next), (A1) write-out, (SCALAR-MIX) derivation, PNT pole.

## Cycle 55 (cont. 13) — the hierarchy interface typed

`RouteBHierarchy.lean` (3 endpoints, axioms clean, lint green, build 8485):
`BlockSmallBall a s bound` — the block-conditional anti-concentration
predicate on the Steinhaus model (uniform in the conditioning value w),
plus `.mono` (rate monotonicity) and `.of_le` (radius transfer). This is
the exact shape of the (L3) induction hypothesis; its three-phase floor is
three_phase_sublevel_r2log. The (L3) STEP = proving BlockSmallBall for a
block from BlockSmallBall of its three largest sub-blocks via the banked
cover/arm pattern (conditional Fubini on steinhausMeasure = infinitePi —
cylinder independence already formal in SteinhausModel).

Goal total 94 axiom-clean endpoints, 15 modules. Queue: (L3) step
execution, (A1) write-out, (SCALAR-MIX) derivation, PNT pole.

## Cycle 55 (cont. 14) — (L3) STEP EXECUTION PLAN (pinned pre-compaction)

Target: BlockSmallBall a s bound for a block s, from three sub-sums, via
the banked cover/arm pattern. Brick list, in order:
1. `block_split_fubini` — steinhausMeasure small-ball of w + Σ_s as an
   iterated integral over the top three frequencies n₁,n₂,n₃ ∈ s (largest
   |a n|): condition on the rest; slice measure = 3-phase sublevel with
   A := a n₁, B := a n₂, C := a n₃, c := w + (rest). Mechanism:
   Measure.infinitePi restrict/marginal on three coordinates — use
   SteinhausModel's Measure.infinitePi_map_restrict cylinder chain
   (already banked for the orthonormality proofs); the phase 2π·ω(n)
   rescales Icc 0 1 → Icc 0 2π with a Jacobian 2π per coordinate.
2. `block_smallball_of_three` — feed three_phase_sublevel_r2log into the
   slice; hypotheses: |a n₂| < |a n₁| strict (generic position), r-window,
   σ0/J admissibility. Output: BlockSmallBall with bound(t) =
   (2π t/|a n₁|)·(J·CS + 2CC + CM)/(2π)³-normalized.
3. The graded ladder: apply 2 at each dyadic block level; the t-graded
   log = per-level J. Assemble (K-bdd-n-log) shape of doc 84/86.
Watchpoints: coordinate-rescale bookkeeping (2π factors), the strictness
hypothesis |a n₂| < |a n₁| fails for equal coefficients — perturb by
splitting ties across levels (doc 87 §4 note).
(A1)/(SCALAR-MIX)/PNT pole unchanged behind this.

### cont. 14 amendment — block_split_fubini mechanism LOCATED (API verified)

Mathlib has NO infinitePi product-split; the correct route (names verified
in .lake source, Mathlib/Probability/ProductMeasure.lean):
1. The small-ball set depends on finitely many coordinates (block s finite)
   → reduce steinhausMeasure to the FINITE pi over s via
   `infinitePi_map_restrict` (line 374; same lemma SteinhausModel already
   uses for orthonormality — pattern banked).
2. Split the finite pi over s into (three distinguished primes) × (rest):
   `MeasurableEquiv.piEquivPiSubtypeProd` + the finite-pi
   `measurePreserving_piEquivPiSubtypeProd` (exists for Measure.pi ✓).
3. `Measure.prod_apply` → the (θ₁,θ₂,θ₃)-slice is the 3-phase sublevel
   after one rescale lemma: Measure.map (2π·) (volume.restrict Icc01)
   = (2π)⁻¹ • volume.restrict (Icc 0 2π) — then three_phase_sublevel_r2log
   applies with A,B,C := the three coefficients, c := w + conditioned rest
   (each prime term IS a single phase: X p ω = e^{2πiω(p)} for p prime —
   needs the small lemma X_prime from factorization_self).
Blocks in doc-86 architecture are prime-supported (rough support = {1} ∪
primes) so no cross-coordinate leakage: slices are exactly independent.

## Cycle 55 (cont. 15) — X_prime banked; rescale lemma next

`RouteBBlockSplit.lean` started: `X_prime` PROVEN (prime-index character
is one bare phase, via Prime.primeFactors + factorization_self). The
rescale lemma map_two_pi_smul (map (2π·) (volume.restrict Icc01) =
(2π)⁻¹ • volume.restrict (Icc 0 2π)) was drafted and REMOVED (no direct
mathlib name found in-context; do NOT re-derive the statement — proof
route: Measure.map_mul_left_volume (a•-scaling of Lebesgue) composed with
image-restrict for the embedding x ↦ 2πx, image of Icc01 = Icc 0 2π;
probe Real.volume_image_mul_left / MeasurableEmbedding.map_restrict
first). Then block_split_fubini per the cont. 14 amendment. Build 8486
green, lint green, 95 endpoints/16 modules.

## cont.38 (2026-07-05) — goal items 1+2: window settled both ways + the equilibrium join

Goal: (1) δ∈(1,3/2) seam + θ∈(1/8,1/2) window via the paired k≥1 sum; (2) the join
(proven θ-drift bound ⟹ no window hypothesis). Both now machine-checked (lattice register).

- Pre-certified everything first (scratchpad precert_legwindow.py, mpmath 40 dps): bricks 0
  failures / 5500 random trials; assemblies A,B zero violations / 5850 grid points; the D≥0
  set = exactly the near-crossing sliver; equilibrium scan: D<0 at EVERY equilibrium, A>1 at
  all but one near-balanced point.
- **LegWindow.lean** (11 decls, axiom-clean): rphi_hasDerivAt (φ′ = −(2csch²+3csch⁴)),
  rphi_pair_gain (MVT pair gain), rcoth_pair_le, rphi_pair_tail, csch_sq_sum_ge (coth
  telescope), rphi_tail_le (csch²/2 telescope), dW_dtheta_neg_seam ((1−2θ)Mδ²>1),
  dW_dtheta_neg_window (3(1−2θ)δ·Δcoth>1, survives δ→0), l1_fails_near_crossing (the
  DISPROOF: continuity at θ=1/2 exhibits dW/dθ>0 below 1/2 at δ=1,M=1,N=2). Doc 28 §5i.
- **LegEquilibrium.lean** (3 decls, axiom-clean): lattice_constraint_hasDerivAt (g′=2δW),
  equilibrium_theta_gap (equilibrium + θ≥1/8 ⟹ Nδ/78 ≤ 1/2−θ), and the capstone
  dW_dtheta_neg_at_equilibrium (δ≤1, Nδ>30, equilibrium ⟹ dW/dθ<0, NO θ hypothesis —
  the constraint forces θ<1/8). Doc 28 §5j. This is the join, item 2, lattice form.
- Name dedup: rcsch/rcoth/rcsch_sq derivative bricks already in SpurLattice — reused.
- NEW STANDING ORDER (Michael): Lean comments are mathematics, not diary — no doc/task/date/
  process references; a Lean project stands for itself. Written into formal/CLAUDE.md +
  formal/AGENTS.md; LegWindow/LegEquilibrium written clean; sweep of earlier session modules
  next.
- Next object (opened, not closed): field_theta_gap on nondecreasing-gap configurations —
  quantitative midpoint-push (doc 27 §3 pairing) + varying-step csch² telescopes = the
  general-gap join; then the §5b adiabatic comparison for general-gap (L1).

## Cycle 55 (cont. 16) — rescale lemma PROVEN

`map_two_pi_smul` banked first-compile (Measure.restrict_map +
Real.map_volume_mul_left + restrict_smul; preimage of Icc by 2π· via
nlinarith). RouteBBlockSplit.lean now holds both split inputs (X_prime +
rescale). 96 endpoints/16 modules, build+lint green. NEXT:
block_split_fubini itself — reduce the BlockSmallBall event to the finite
pi over the block s (infinitePi_map_restrict), split three distinguished
primes off via piEquivPiSubtypeProd (finite-pi measurePreserving version),
Measure.prod_apply, rescale each of the three coordinates by
map_two_pi_smul, land on three_phase_sublevel_r2log. Then
block_smallball_of_three, then the graded ladder. Behind: (A1),
(SCALAR-MIX), PNT pole.

## Cycle 55 (cont. 17) — the center-UNIFORM one-phase law

`one_phase_smallball_uniform` PROVEN (RouteBBlockSplit.lean): for
2s ≤ ‖D‖, vol{η : ‖c' + De^{iη}‖ ≤ s} ≤ 8πs/‖D‖ for EVERY center c' —
empty below reach (triangle), radial √-law above (‖c'‖ ≥ ‖D‖/2 kills the
1/√‖c'‖ singularity). DESIGN FINDING recorded: three_phase_sublevel_r2log's
constants carry 1/√‖c‖ in the conditioned value, so block_smallball needs
FOUR distinguished primes — the fourth phase averages the singularity, and
one_phase_smallball_uniform is exactly its distribution input (min-split
∫min(M, K/√dist) with a free split parameter, same style as J). Next
bricks: G2 = the min-split averaging lemma; G3 = block_split_fubini (the
infinitePi reduction). 97 endpoints, build+lint green.

## Cycle 55 (cont. 18) — G2 PROVEN: the fourth-phase averaging lemma

`inv_sqrt_average` banked (RouteBBlockSplit.lean, axiom-clean, lint green):
any integrand dominated by min(M, K/√‖c'+De^{iη}‖) integrates over the
circle to ≤ M·(8πs*/‖D‖) + (K/√s*)·2π, free split height s* (2s* ≤ ‖D‖) —
the singular region pays M against one_phase_smallball_uniform, the bulk
pays the capped singularity. Consumer picks s* ~ (K‖D‖/M)^{2/3}-optimal or
anything sufficient. The 1/√‖c‖ singularity of the three-phase constants
is now integrable BY BANKED LEMMA. 98 endpoints.
REMAINING for the (L3) step: G3 block_split_fubini (the infinitePi
4-coordinate reduction: infinitePi_map_restrict + piEquivPiSubtypeProd +
prod_apply + map_two_pi_smul ×4 — all names verified) + the assembly
block_smallball_of_four (three_phase_sublevel_r2log's c-dependent bound
fed through inv_sqrt_average with M := (2π)³ trivial cap). Then the graded
ladder; then (A1), (SCALAR-MIX), PNT pole.

## Cycle 55 (cont. 19) — H1: the four-phase Fubini identity PROVEN

`four_phase_fubini` banked FIRST-COMPILE (RouteBFourPhase.lean): the 4D
sublevel measure of a four-phase circle sum EQUALS the circle integral of
3D sublevel measures at the moving center w + De^{iη}. G3 was re-factored:
the mathematically-real content lives on the 4-torus (this brick + H2);
the infinitePi plumbing reduces the Steinhaus block event to it separately.
NEXT = H2 `four_phase_sublevel_uniform`: pointwise
μ³(slice η) ≤ min(ofReal (2π)³, 3-phase-bound(w+De^{iη})) where the
3-phase bound decomposes as ofReal(K/√‖c‖ + K') (K collects the CS/CC
c-singular parts, K' the c-free parts incl. J•-term folded via nsmul→real);
then min(a, x+y) ≤ min(a,x)+y, lintegral_add_right, and inv_sqrt_average.
CARE: the J•-term is ENNReal-nsmul — convert J • ofReal X = ofReal (J·X)
(nsmul_eq_mul + ofReal_natCast-mul) before the real decomposition.
99 endpoints, build+lint green. Behind: infinitePi plumbing, graded
ladder, (A1), (SCALAR-MIX), PNT pole.

## Cycle 55 (cont. 20) — H2 PROVEN: the center-UNIFORM four-phase law

**`four_phase_sublevel_uniform`** banked (RouteBFourPhaseUniform.lean,
axioms clean, build 8488): the 4D sublevel measure of a four-phase circle
sum at ANY center w is ≤ (2π)³·(8πs*/‖D‖) + (arc·K/√s*)·2π + (arc·K')·2π,
all constants explicit — the 1/√‖c‖ singularity of the three-phase
constants is AVERAGED OUT by the fourth phase (inv_sqrt_average' — the
conditional variant dodging the c=0 junk value — + ENNReal truncated-sub
decomposition + the √-split identities e₁/e₂). With it the analytic
engine of the (L3) induction step is COMPLETE: uniform-in-conditioning
anti-concentration at r²·J for any four dominant phases. 101 endpoints,
18 modules.
NOTE: tree lint currently red at LegLatticeStep.lean:455 (active sorry) —
the parallel codex session's NEW file, not in my import tree; their fix
to land. My modules all gate green.
REMAINING: the infinitePi plumbing (Steinhaus block event → 4-torus, per
cont. 14 amendment), the graded ladder, (A1), (SCALAR-MIX), PNT pole.

## Cycle 55 (cont. 21) — the block marginal PROVEN

`block_marginal` banked (near-first-compile; one deprecation rename): the
Steinhaus small-ball event of a prime-supported block sum EQUALS the
finite product of uniform phases over the block (X_prime + sum_attach +
infinitePi_map_restrict + map_apply). 102 endpoints. The plumbing chain
now: finite-pi 4-vs-rest split (piEquivPiSubtypeProd + prod_apply) +
4-fold rescale (map_two_pi_smul) → four_phase_sublevel_uniform →
BlockSmallBall. Then the graded ladder, (A1), (SCALAR-MIX), PNT pole.
(Tree lint still red at codex's LegLatticeStep.lean:455 sorry — theirs.)

## Cycle 55 (cont. 22) — lmarginal route pinned + lintegral rescale banked

ROUTE REVISION (better than cont. 14's equiv plan): the finite-pi
4-vs-rest split runs on mathlib's lmarginal machinery (VERIFIED API:
lintegral_eq_lmarginal_univ, lmarginal_union disjoint-split,
lmarginal_insert single-coordinate peel) — NO subtype-prod equivs, NO
Fin-4 enumeration. Chain: (pi ↥s)(E') = lmarginal_univ 1_E' =
lmarginal_{univ\F}(lmarginal_F 1_E'); unfold lmarginal_F by 4×
lmarginal_insert into iterated single integrals over uniform01; rescale
each by `lintegral_two_pi_rescale` (BANKED this cont., 103 endpoints);
convert the iterated Icc(0,2π)⁴ integral to the 4D product measure
(iterated Measure.prod_apply adapter, to bank next) and cite
four_phase_sublevel_uniform; the outer lmarginal is over a probability
measure so the uniform bound passes through (lmarginal_const-mono).
Then BlockSmallBall for prime blocks = the (L3) STEP. Behind: graded
ladder, (A1), (SCALAR-MIX), PNT pole. (Codex's LegLatticeStep sorry
still red on tree lint — theirs.)

## cont.39 — (LEG) both legs formalized

Constant-lattice leg: `LegLatticeStep.lattice_step_energy_increase` (axiom-clean) — one
lattice step between consecutive equilibria strictly raises Calogero energy on the small-δ
band (θ ≤ 1/8, δ ≤ 1, δm² ≥ 4). Two MVTs (constraint + energy), drift bracket
(32/39)δθ′² ≤ θ−θ′ ≤ (3/7)θ, gain ≥ 1/δ vs loss ≤ 1/(4δ). Recorded doc 28 §5k.

General-gap leg: `LegAdiabatic.lean` (axiom-clean) — the exact §1 ledger identity
`adiabatic_ledger` (advance-by-δ keeps ahead-distance s invariant, crosses one pole, ΔG =
two swap extras + one coth-increment per spectator), the cushion `swap_cushion_gt_two`,
per-term MVT drift bounds `behind/ahead_drift_abs_le` ((δ/2)csch²), and the closing
`adiabatic_march_pos` = (ADB-crude) ⟹ ΔG > 0. Recorded doc 30 §6.

Residual = the field-class instantiation: verify (ADB-crude) `Σ(δ/2)csch² < cushion` for the
concrete section gap sequences (|Δδ|=O(δ²), one-sided, s<δ/2), LHS O(log/δ) vs cushion ~2i/δ.
That is #170 (field_theta_gap).

## cont.40 — adiabatic ledger CORRECTION: pole-crude tight, rank form clears

Attacked own §5 (ADB-crude) as false: the pole-pairing no-signs bound Σ(δ/2)csch²(c_m/2) <
cushion FAILS for s ≳ δ/4 even on the constant lattice (mpmath: δ=0.1,s=δ/2 → LHS 94 vs
cushion 53). Full-δ increments hide the telescoping cancellation. Fix = rank pairing
(LegAdiabatic.lean, axiom-clean): adiabatic_ledger_rank (increments = gap DIFFERENCES, 0 on
constant lattice), far_cushion_gt_two (>2 unconditional), behind_gain_nonneg/ahead_loss_nonpos,
rank_march_pos (net drift ≥ 0 ⟹ ΔG > 2). Constant lattice immediate. Real (ADB) = SIGNED
Σgains ≥ Σlosses, not no-signs TV bound. Recorded doc 30 §7. Residual #170 = net-drift
nonnegativity for concrete section gaps (k-wise gain/loss pairing under δ-convexity).

## cont.41 — (ADB) net drift discharged: coth-free, closed on one-sided-far

Reduced rank_march_pos's hADB to elementary coth-free per-rank distance inequalities
(LegAdiabatic.lean, axiom-clean): rcoth_pair_ge (MVT far-endpoint lower bound),
rank_pair_domination (gain ≥ loss from signs + midpoint-push oldB≤newA + convexity width),
net_drift_nonneg (sum: R≤L outer half), section_march_pos capstone (per-rank conds ⟹ ΔG>2).
The transcendental (ADB) is GONE — only distance inequalities remain.

Verified (mpmath, δ=1/j, s=δ_{i+1}/2): all per-rank conditions hold for i=d−3,d−5,d−8 (R=1,3,6)
→ section_march_pos fires; bulk (R≳10) DIST fails ~rank 5 (behind cumulative overtakes 2s). So
(ADB)/s-march CLOSED on one-sided-far carriers (the SPUR-R target, doc 25/30§3); bulk residual =
coth-free csch²-tail smallness of the far paired ranks vs near behind gains. Recorded doc 30 §8.

## Cycle 55 (cont. 23) — the iterated prod_apply adapter BANKED; peel mechanics all verified

ROUTE re-cut cleaner than cont. 22: the four-phase product bound feeds the
Steinhaus block via a fubini CHAIN, not raw prod_apply juggling. Banked this
cont. (all axiom-clean [propext, Classical.choice, Quot.sound], tree lint green
— codex LegLatticeStep sorry resolved):

- RouteBProdFubini.lean (4 endpoints): three_phase_fubini, two_phase_fubini,
  one_phase_fubini (mirror four_phase_fubini at arities 3/2/1, peel one circle
  coord at fixed center), and four_phase_prod_eq_nested — the "iterated
  prod_apply adapter" cont. 22 flagged: prod4(Icc^4 cap sublevel) EQUALS the
  4-fold nested setLIntegral over Icc(0,2pi) of the sublevel indicator. Proof:
  rw four_phase_fubini; simp_rw [three/two/one_phase_fubini] (telescopes clean).
- RouteBBlockStep.lean (1 endpoint so far): four_phase_nested_uniform — the
  center-uniform four-phase bound in the exact nested-integral form the peel
  produces. One line: le_trans (four_phase_prod_eq_nested).symm
  (four_phase_sublevel_uniform).

Umbrella updated (RouteBProdFubini imported); index regenerated.

VERIFIED (scratchpad, not yet in-tree) peel mechanics — ALL compile:
- sum_phase_update4: the block-center split. Sum over s.attach of a(p)e(update^4)
  = 4 fresh phases + rest-sum(y) = conditioned center V. Via a `peel` helper
  (phase-transform commutes with Function.update + Finset.sum_update_of_mem, ×4).
- single-coordinate rescale (lintegral_two_pi_rescale + exp cast).
- indicator conversion (simp only [Set.indicator_apply, Set.mem_setOf_eq]).

GOTCHA: chained Finset sdiff a \ {x} \ {y} MUST be ((a \ {x}) \ {y}) — bare
chaining is a PARSE error. Nested membership via nested Finset.mem_sdiff.mpr.

REMAINING for the (L3) STEP (block_smallball_of_four_dominant):
1. bank sum_phase_update4 into RouteBBlockStep.
2. INNER peel: lmarginal {q1..q4} 1_{E'} y = (lmarginal_insert ×4) →
   sum_phase_update4 rewrite → rescale ×4 → indicator conv →
   four_phase_nested_uniform ⟹ ≤ ofReal(2π)⁻¹^4·four_phase_RHS uniform in y.
3. OUTER wrap: lmarginal_union split univ=(univ\F)∪F; lmarginal_mono + lmarginal
   of const over probability pi = const.
4. block_marginal closes steinhausMeasure. bound(t) window-restricted, not ∀t.
Then graded ladder; (A1); (SCALAR-MIX); PNT pole.

## cont.42 — bulk (ADB) closed by the summed csch²-box inequality

Reasoned first (anti-theatre): far-rank per-rank domination FAILS for the physical c = 2 gaps
(exact scaling criterion φ(1+α) ≥ φ(1−α), φ(x) = x^{c+1}+x^{1−c}−2x; c = 1 neutral, c = 2
deficit −2α⁵/(1−α²)); the pre-registered "net < 0 at mid-carrier" prediction was then REFUTED
(+4.65 measured) — the miss located the true mechanism: midpoint-push near-rank asymmetry
(surplus 64/(9c) on O(1) ranks) absorbs the O(1) paired deficit (0.235 at c = 2). Banked
`net_drift_nonneg_csch` + `bulk_march_pos` (LegAdiabatic.lean, axiom-clean; umbrella + lint
green): (ADB) from ONE summed box inequality (htail), no per-rank condition. (htail)
pre-certified on δ_j = c/j, c ∈ [1,3], θ ∈ [0.15, 0.5], worst margin +0.33; equilibrium
θ* ∈ [0.29, 0.38]. Doc 30 §9 records it and corrects §8's closing sentence. Open next: Lean
instantiation of (htail) on the c/j class; the inner-half "march horizon" (predicted breakdown
at log((d−i)/i) ~ 32/9) as a new object.
