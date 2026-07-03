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
