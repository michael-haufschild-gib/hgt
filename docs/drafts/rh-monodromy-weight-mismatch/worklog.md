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
