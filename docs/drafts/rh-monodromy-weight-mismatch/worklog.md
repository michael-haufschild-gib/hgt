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
