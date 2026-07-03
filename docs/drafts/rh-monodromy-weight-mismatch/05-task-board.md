# MWM task board — wave 2 (after Arc A + R1–R3)

State on entry (2026-07-03): Arc A fully formalized and gated; campaign R1–R3 closed
(findings in `worklog.md`); mechanisms after audit: M1 primary, M2 downgraded, M3 only as
FE ∧ positivity. Sequencing rule: **C2 first** (it gates the novelty inventory), then
paper-math (C1) and cheap compute (R3b/R5) interleaved; Arc B after checks #3/#7/#8.
Entropy discipline per research-rules §4 at every open choice.

## C-arc — mechanism (the theory spine)

**C2 — Bagchi verified reading (check #1). GATING, do first.**
Fetch and read the actual statements: Bagchi 1981 thesis ("The statistical behaviour and
universality properties of the Riemann zeta-function...") and the Math. Z. (~1982) paper.
Answer: (a) is strong recurrence sup-norm-on-compacts of the open strip? (b) does his proof
pass through zero-counting/Rouché+density (if so, is the mod-2^k coarsening implicit)?
(c) any follow-up stating a coarse/topological-invariant version? Outcomes: implicit →
novelty item 2 (00-approach §10) downgrades to "grading + formalization of known"; absent →
item 2 stands. Deliverable: check-note appended to worklog.md + §8/§10 updated in place.
Method exception: positioning literature lookup, sanctioned.

**C0 — bundled checks #2/#3/#4/#5/#7/#8 (one verified-reading session).**
- #8 first (fresh data wants it): known theorems on D–H off-line zero density (Davenport–
  Heilbronn 1936 original; Balanzario–Sánchez-Ortiz numerics; positive-proportion results for
  linear combinations, Bombieri–Hejhal adjacent). Compare with measured T/21.
- #3 Hamburger exact hypotheses (bounds Arc B's search space).
- #2 random Euler product a.s. convergence/nonvanishing σ > 1/2 (fixes 00-approach §4.3).
- #5 any literature on multiplicity parity of hypothetical off-line zeros (expect none —
  confirms the ladder's novelty-candidate status).
- #7 Bohr almost-periodicity ⟺ zero-free statements (perimeter of §4.3).
- #4 DRH/partial-Euler on the critical line (Conrad; Kurokawa school).
Deliverable: one check-note; every §8 [CHECK] item resolved to verified/refuted-with-citation.

**C1 — the Reduction, rigorous paper proof.**
Theorem: fix σ₀ > ½, H > 0, k ≥ 1; if the defect set {T : w_k(T) ≠ 0} is relatively dense
once nonempty, then lim sup N(σ₀,T)/T > 0; with Ingham ⟹ w_k ≡ 0 ⟹ (box-shrinking)
2^k ∣ ord at every zero right of σ₀. Full care: boundary zeros (a.e. boxes / interior
winding), the box-shrinking localization, quantifier order over (σ₀, k). Write as
`06-reduction.md` in this directory (paper note, LEDGER-candidate register with explicit
hypotheses). Lean version later as its own card (Ingham as named hypothesis — NOT an axiom).
Depends on: nothing (C2 only repositions the writeup's claims).

**C3 — explicit formula as index formula (M1 made precise).**
(a) w_k as ∮ ξ'/ξ mod 2^k, connect to S(T)-type quantities mod 2^k; (b) inventory
parity-sensitive test-function families (ledger says linear probes are β-blind — the absence
is the opening); (c) transpose the `index_formula_split` + resonance-pinning pattern: state
M1 as a conditional theorem ("defect term's spectral content vs the {j log p} side ⟹
recurrence"), isolate its hypothesis as the new open core. Depends on C1.

## Arc B — parity in FE ∧ positivity (open math; after C0's #3/#7/#8)

**B1 — FE-grafting hunt (attack-as-false).** Start from DMV positive systems; ask whether an
FE can be grafted; if "Beurling + FE" is provably thin (Hamburger-type), the emptiness proof
IS a parity theorem for that class and direct progress on realization problem #85. Either
exit terminalizes (pipeline card when the statement stabilizes).

**B2 — L1-lemma attempts.** FE ∧ positive-log ⟹ divisibility/pairing structure on the
divergence-strip divisor: paper attempts, each failure names the missing Euler feature.
Wild-analogy slot (scripts/rng) when plateaued.

**B3 — real-structure equivariance (small Lean).** Conjugation-symmetric cycles carry even
winding; level-1 obstruction lives on classes separating ρ from ρ̄. Needs `xi_conj`
(probe `completedRiemannZeta₀` conjugation lemma in mathlib; if absent, derive from
Hurwitz-zeta layer or state on abstract f with f(s̄) = conj f(s)). Extends RHTower.

## R-campaign — wave 2 (all parallel-batched on the pod, minutes each; results →
`computations/` here, per standing order)

**R3b — FE-minimum replication, window 2.** Same k-scan over t ∈ [150, 200) (contains the
banked-adjacent defects at ~167, ~177). Pre-register: minimum again at the FE fiber; floor
count = the window's D–H zero count (2); linear plateau scaling replicates.

**R3c — pinning order + exponent refinement.** Bands σ₀ ∈ {0.5025, 0.505, 0.51} × fine k;
track WHICH zeros exit the band last as k → κ (pinning order vs height/initial σ); refine
the width coefficient. Deliverable: defect-velocity per zero — the family's "spectral gap"
profile.

**R5 — NEW: the Euler-approach profile (the opened question).** Extend the pencil to complex
c: walk c from the D–H point (1−iκ)/2 toward c = 1 (pure L(s,χ) — Euler product, GRH-clean
in range). Measure the off-line defect count along the path (window t ≤ 200, band σ₀ = 0.51).
Pre-register: count decreases to 0 at c = 1; the SHAPE near c = 1 (linear vanishing vs
threshold) is the observable — "the Euler cut as the second, deeper minimizer." Any pinned
defect that survives to near c = 1 would be a major anomaly (early-fail sensor for the family
picture). Engine: f_pencil generalized to complex c (small edit).

**R4 — (unchanged, optional)** three-way extreme-statistics comparison; run only on momentum.

## Bookkeeping / publication track

**P1 — mailbox post to the parent lab** after C2 + C1: the RH_{2^k} ladder + tower Lean bank
+ the FE-minimizer measurement (ledger-aligned: B7 shape + proof_shape's "fake families
producing unsanctioned linking"). Flag the Bagchi verdict honestly; don't oversell.

**P2 — fold RHTower into the publication surface** (formalization-paper.md section or a
standalone short note "A machine-checked multiplicity-parity ladder for RH") — decide AFTER
C2's novelty verdict. Card gate 3 → 4 rides on this.

**A3 — (deferred until C1 fixes the invariant)** formalize the cocycle w_k (argument-principle
mod 2^k); check the atlas's formalized Schur–Cohn winding=inertia bridge for reuse before
writing new Lean (audit F5).

## Default order

C2 → C0 → R3b + R5 (parallel with C1 writing) → C1 → C3 → B1/B2 → R3c → P1 → P2.
At each session start: `scripts/rng seed`; if two consecutive sessions only re-derive,
force a wild-analogy collision on B2 (research-rules §4).

---

## Wave-2 status (2026-07-03, second half of day)

DONE: **C2** (delegated verified reading, spot-checked — Bagchi confirmed, mechanism =
full-magnitude count, coarsening ABSENT-FROM-LITERATURE; §8/§9/§10 of 00-approach updated,
`checks/c2-bagchi-note.md`); **C1** (`06-reduction.md` — (D) × (R_k) ⟹ RHLadder k, cluster-sum
subtlety handled, level-1 corollary isolated); **R3b** (window-2 replication exact, coeff 4.0);
**R5** (profile 4 → 29 → 0; Euler point exact minimizer, no anomaly; linear flux n ≈ 120(1−u)
near u = 1). C0 delegated, in flight. Results: `computations/R3b-R5-RESULTS.md`, worklog.

NEW (opened by wave 2):
**R5b — near-Euler mobility scan.** u ∈ [0.90, 1.0] step 0.005, σ₀ = 0.51, t ≤ 200.
Pre-register: the linear law n ≈ 120·(1−u) persists at fine resolution (no staircase
clustering, i.e. wall-crossings u* roughly uniformly spread); n(0.995) ∈ {0,1,2}; n(1) = 0.
Deliverable: per-zero wall-crossing estimates u* (mobility distribution) → cross with R3c.
**C4 = [CHECK #9] — where density proofs consume the Euler product.** Verified reading of
Carlson/Ingham-style density proofs (mollifier coefficients? mean-value inputs?) + the precise
structural reason D–H evades them (it must: measured T/21). Feeds §4 of 06-reduction.md.

## Wave-2 status, second update (2026-07-03 evening)

DONE since last block: **C0** (all six checks verdicted, `checks/c0-checks-note.md`; #5 ABSENT
⟹ §10.1 ladder novelty VERIFIED-ABSENT — with C2, both gating novelty items survived; my added
caveat: Lamzouri–Lee's near-line asymptotic needs G(T)→∞, fixed-strip linear rests on the
unfetched Bombieri–Hejhal pointer); **(R_k) weakened** to conditional positive UPPER density
(Bagchi's own limsup register — user-relayed GPT nuance, verified verbatim, 06-reduction.md
amended, proof adapted); **R5b** (linear flux to u≈0.955, then collapse + defect-free EULER
MOAT u∈[0.98,1]; mobility ranking banked). New: **R5c** (moat scaling in T, #106, pre-register
first). Remaining default order: **C3 → B1/B2 (+B3 small) → R3c/R5c → P1 → P2**; C4 (#105)
delegatable alongside C3. Hooks for C3/P-track: DRH's √2^{ν(ρ)} factor = literature's one
multiplicity-sensitive Euler-product law (on-line central) — cite as adjacent, distinguish
off-line ladder; 237/237 simplicity is publishable new data (no counterpart).

## Wave-2 status, third update (2026-07-03 night)

**C3 DONE** (`07-index-formula.md`): M1 is now a theorem with one isolated hypothesis —
Rouché-transfer + (H_k) ⟹ (R_k); (D) + (H_k ∀k) ⟹ RH. **C4 delegated** (#105, in flight:
density-proof Euler-input + Bombieri–Hejhal exact statement + Speiser + Levinson–Montgomery).
**R6 launched** (#107, pre-registered in 07 §5.1): return-set measurement at the certified
defect box [0.53,1.2]×[166,168], τ ∈ [0,400] step 0.1, 120-pt boundary proxy, winding
certification for candidates. R6 discriminates "defects recur because data returns
(M1/(H))" vs "defects recur for a weaker reason" — either verdict reshapes M1. Remaining:
B1/B2/B3 (B3 next: xi_conj mathlib probe), R3c/R5c, P1 (after C4), P2.

## Wave-2 status, fourth update (2026-07-03 night) — R6 verdict

**R6 DONE, registered prediction REFUTED** (`computations/R6-RESULTS.md`, 07 §6): zero
sub-margin boundary-data returns over τ ∈ (1,400] (deepest 24× margin) while defects recur
≈ 19× there. Defect recurrence ⇏ data recurrence — (H)'s causal reading dead in the family;
C3's theorem stands as mathematics. **M1 primary open core re-cut to (P_k) population-forcing**
(one coarse defect ⟹ linear off-line count; (P_k) + (D) needs NO recurrence input). C4's
Bombieri–Hejhal reading now directly feeds the (P_k) statement. B3 scoped: zeta-layer conj
lemmas absent, ingredients (Gamma_conj/cpow_conj/tsum_star/exp_conj) verified present;
missing piece = reflection analyticity lemma. Queue: C4-integrate → B1/B2 (informed by
(P_k)) → B3 → R3c/R5c → P1 → P2.

## Wave-2 status, fifth update — C4 integrated

**C4 DONE** (spot-checked): #9 = mollifier Möbius coefficients (single load-bearing Euler
step; Tao notes fetched); Ivić anchors the D–H division-of-labor; CORRECTION — off-line ≫T
in fixed strips is UNCONDITIONAL (Voronin/LNP), BH is the conditional 100%-on-line converse;
Speiser + LM verified exactly (LM blunt below log T ⟹ companion cocycle must be box-level).
B3 in progress (all names probed: DifferentiableAt.conj_conj, Gamma_conj, cpow_conj,
tsum_star, zeta_eq_tsum_one_div_nat_cpow, DifferentiableOn.analyticAt). Queue after B3:
B1/B2 (target: (P_k) seed⟹population for combination-of-one) → R3c/R5c → P1 → P2.

## Wave-2 status, sixth update — B3 banked

**B3 DONE**: `RHTower/Reflection.lean` — xi_conj + generic order-equivariance (conj, 1−s)
+ the two pairings, axiom-clean, full gate green. The 07 §3 symmetry slack is now
machine-checked infrastructure. Remaining queue: B1/B2 (primary target re-cut to (P_k):
seed ⟹ population for a combination-of-one; Hamburger gap + Ivić anchor as start points)
→ R3c/R5c (pre-register first) → P1 (mailbox: ladder + Reduction + two-minimizer/moat
measurements + R6 negative) → P2 (publication surface; both novelty gates verified-absent).

## Wave-2b compute pre-registrations (2026-07-03, before launch)

**R3c (window 1, t∈[2,102), k∈[0.27,0.30] step 0.0025, bands σ₀∈{0.5025,0.505,0.51}).**
Pre-register: (a) plateau stays linear at coeff ≈ 4 down to σ₀−½ = 0.0025 (predicted width
≈ 0.01, i.e. ~4 grid points); (b) pinning order (which boxes stay defective longest as
k→κ) is STABLE across bands; (c) open comparison: does the k-pinning order correlate with
R5b's Euler-resistance ranking? Correlation ⟹ one mobility spectrum under both constraints;
anti-correlation ⟹ the two constraints grade zeros differently. Either is a finding.

**R5c (moat scaling; already registered in R3b-R5-RESULTS.md).** Windows t ≤ 500 (u∈[0.94,1],
step 0.0025·... = 24 steps) and t ≤ 1000 (u∈[0.96,1], 16 steps), σ₀ = 0.51. Pre-register:
moat persists (n = 0 at u = 1 AND on a final u-interval); width shrinks with T (candidate
1−u*_max ~ c/log T ⟹ widths ≈ 0.020 (T=500), 0.017 (T=1000) if c calibrated at T=200 width
0.025... treat the log-law as the hypothesis under test, not assumed).

**R6-loc (NEW — local return measurement; the (H-loc) probe).** Circle of radius 0.05,
48 points, centered at the banked certified D–H zero 0.808517182456637386 + 85.6993484853775922i;
τ ∈ [0, 400] step 0.05; margin = sampled min |f| on the circle. Pre-register: CONTRAST with
R6 — local sub-margin returns DO occur (∃ τ > 0.5 with d(τ) < margin), at gap scale
comparable to tens; rationale: the circle data is ≈ finitely many Taylor coefficients
(f, f′ dominate at this radius), so returns are a finite-dimensional value-recurrence event
(Bohr–Jessen/Voronin-denseness genre), unlike R6's 120-point box sup-norm. Kill criterion:
min_τ d/margin > 3 over the whole range ⟹ NO recurrence mechanism at any scale supports
the family population; the (P) population route then stands alone as M1's re-cut.

## P1 retired (2026-07-03)

The parent-lab mailbox is not in use (single-agent context; only the q62/Böttcher agent runs
in parallel, and it coordinates through the pipeline, not the mailbox). P1 dropped; its
content lives in worklog.md + the lane docs. P2 (publication surface) remains the outward
channel.

## R6-loc-b pre-registration (2026-07-03, before launch)

Radius scan at the deepest R6-loc near-return (τ ≈ 91.0, mapping the banked zero t≈85.7 onto
the defect zero t≈176.7): r ∈ {0.02, 0.05, 0.08, 0.12, 0.15}, τ ∈ [90.5, 91.5] step 0.02,
48 pts. Pre-register: ratio min_τ d(τ,r)/m(r) DECREASES with r (d ≈ jet-difference-dominated,
m ≈ r·|f′|); [CONJECTURE, prior ≈ 0.5] some r ≤ 0.15 achieves a strict sub-margin return —
a certified local Rouché transfer between two actual zeros (first non-counterfactual
instance). Kill clause: ratio > 1.5 at every r ⟹ the near-miss is intrinsic (the two jets
genuinely differ at all scales) — local transfer then needs the symmetry slack (07 §3).
Job size: 5 × 51 × 48 ≈ 12k evals — seconds.

## Wave-2b close (2026-07-03 night)

DONE: quantified Reduction (06 §6: open core → T^{θ(σ₀)} recurrence, graded burden);
`no_polynomial_surgery` Lean-banked (dichotomy fragment); C5 verified (FE = load-bearing
axiom; Hilberdink–Lapidus testbed lead); R3c (anti-correlated FE/Euler mobility spectra;
two-population asymmetry, only the banked zero pinned both sides); R5c (moat persists,
shrinks faster than 1/log T; partial at T=1000 — job was oversized, killed, salvaged);
**R6-loc/b/c: certified local Rouché transfer between two actual zeros (r=0.15, τ=91.005,
hardened ratio 0.639) — first non-counterfactual instance of M1; R6's negative was a
contour-size artifact.** Pod idle. NEXT: R7 transfer graph (#108, chunked!), B1' =
Hilberdink–Lapidus FE-class reading (delegatable), B2 collision, P2.

## R7 chunk-1 pre-registration (2026-07-03, before launch)

Localized zeros (r7c0.out, winding-certified ±0.01): ρ₁ = (0.8065, 85.695), ρ₂ = (0.6555,
114.164), ρ₃ = (0.5693, 166.477), ρ₄ = (0.7202, 176.695). Discovered candidate law from
R6-loc depths vs Δβ: **d_min(ρᵢ→ρⱼ) ≈ (1.1–1.3)·|βᵢ−βⱼ|**, hence sub-margin transfer ⟺
r ≳ |Δβ| (vertical shifts cannot move β; margin ≈ |f′|·r; jet distance ≈ |f′|·Δβ).
Pre-register for all 6 pairs, radii {0.8, 1.0, 1.2, 1.5}×|Δβ| (capped to keep disc right of
σ = 0.52), τ = Δt ± 0.5 step 0.05: (i) sub-margin appears iff r ≳ 1.05·|Δβ| (±15%);
(ii) min ratio ≈ Δβ/r within ±25% at every pair; (iii) hence the transfer graph at radius r
is the β-proximity graph. Failure of (i)/(ii) at any pair kills the law (then jets differ
through more than β). Job ≈ 24k evals — minutes.

## Wave-3 status (2026-07-03, theory-first tick)

DONE: **09** (family (H-loc) THEOREM modulo [CHECK]-marked joint-universality imports +
the principal wall located: (H-loc for ζ) ⟺ principal-direction self-approximation at a
vanishing target; opened the blind cone + primitivity grading); **no_polynomial_surgery_zeta**
(Lean, axiom-clean, gate green; mathlib has NO Rouché — noted for A3); **R7 chunk 0** (four
zeros winding-localized ±0.01) + the **β-proximity law** discovered (d_min ≈ 1.1·|Δβ|;
sub-margin ⟺ r ≳ Δβ; matches R6-loc ratios to ~10%); chunk 1 (six-pair law test,
pre-registered) running. 00-approach §10 inventory updated (items 6–8).
QUEUE: R7c1 verdict → C6 = verify the joint-universality import (delegatable verified
reading: exact positive-lower-density joint universality statement + Hurwitz strong
universality) → B2 collision on the blind cone → P2.

---

## Wave-4 (2026-07-03, seed 382100489098707208) — R8 pre-registration + the blind-cone attack

**R8 chunk 0 (local, seconds) — direct jets at the four centers.** Measure f′(ρᵢ) by central
difference (h = 1e-8, dps 30) at the chunk-0 centers. PRE-REGISTERED PREDICTIONS:
(i) |f′(ρ₂)| differs from the {ρ₁, ρ₄} values by ≥ 30% (jet-class hypothesis, direct);
(ii) |f′(ρ₃)| lands nearer the {ρ₁, ρ₄} class than its naive margin/r proxy 0.42 suggested
(since ρ₃ demonstrably transfers at r = 0.18). Falsifier: if |f′| values are all within 15%,
the jet-proximity law's second term is NOT carried by |f′| and the R7 refinement is wrong.

**R8 chunk A (pod, ≤ 10 min) — census extension t ∈ [200, 320).** engine6 localize
0.52 200 320 1.0, dt = ds = 0.02, dps 20. PRE-REGISTERED: new off-line zeros exist in the
window (D–H off-line density is positive); each new zero's (β, |f′|) either joins an existing
jet class or founds a new one — discreteness vs continuum is the question the census answers.
Chunks B [320, 420) and C [420, 500) follow only after A's verdict.

**Theory task (this tick's center): answer 09 §3.1 — the universality-blind cone.** Target:
the dichotomy (multi-support steerable / single-line RH-grade), representation-independence
across moduli, and the exact carrier of the wall in Hurwitz coordinates. Output: new doc
10-blind-cone.md + Lean witness pair (log-relation dependence + transcendental-shift
independence) in RHTower/LogIndependence.lean.
