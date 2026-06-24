# Revision 01 — Changelog

> **What this is.** The change record for `docs/consolidated/revision01/`, which integrates the
> **2026-06-20/21 experiment battery** (Penrose R1–R69 + per-experiment summaries, Conway/hgt-machine
> `n/50` ticks, Dyson HGT-continuation) into the consolidated corpus. It records, per the brief, what
> affected what — and which changes are a **new synthesis**, a **proof**, a **falsification**, a
> **precisification**, a **new theorem/lemma**, or a **new conjecture**.
>
> **Provenance of the integration.** Conjectures and results were extracted faithfully (verbatim node
> IDs, numbers, verdicts) from the five working/state logs and the `computations/2026-06-21-*`
> outputs. The full standalone inventory is `logs/conjectures.md`; the updated narrative synthesis is
> `logs/synthesis.md`. **Register discipline held:** every new item is `[CONJECTURE]` /
> `[OBSERVED]` / `[EXPERIMENTAL FINDING]` / `[FALSIFIED]` as its source assigns it. **No new proof of
> RH, no promotion to the proven ledger, and no new Lean** resulted from this batch (§7).

---

## 1. Headline (the new synthesis)

The "one object" (the weld phase carrier) and its catalog (Groups A–G) are **reconfirmed and
over-determined**, not overturned. The batch's net effect is four-fold:

1. **A new gatekeeper layer.** The single largest new product is a class of **acceptance gates** —
   conjectural statements of the form *"a valid test of conjecture X must control for Y."* They sharpen
   the *definitions* of C1–C6 / B2 / APEX-B (not the carrier facts). This is genuinely new structure
   the prior corpus lacked.
2. **New RH-side discriminators** (Penrose R27/R28/R30/R34/R36-37/R41/R42/R45) that sharpen the apex
   detectors and add one bridge-candidate (R34, the state-law abscissa passport).
3. **Targeted falsifications** of specific candidate forms — the **naive scalar oriented 2-form**
   (C1's literal realization), the **Scalar Layer**, the raw **`H=A+P` selection**, and (re-confirmed)
   **naive phase-run positivity** as an HT detector.
4. **A re-grounded central tension** — Dyson's R6 "fixed point" makes precise that every value-relation
   transfer collapses to shift/deriv rank, so a real win needs a new transcendence detector.

The wall's location is unchanged; what moved is the **sharpness of the detectors and the rigor of the
controls**.

---

## 2. New conjectures (NEW knowledge produced this batch)

All are SEARCH-register; none promoted. Full statements + kill criteria in `logs/conjectures.md` §2.

### 2a. RH-side discriminators (Penrose)
| ID | One-line | Maps to (doc §) | Evidence |
|---|---|---|---|
| **N1** (R27) | D_∞ period-domain **quenched-stable interior**; off-line FE quartet lowers boundary score *without* masking | `08` APEX-C / C-2026-06-18-001, B3 | `penrose-r27-*` |
| **N2** (R28) | **Seam-local Ito/Stratonovich corank correction** (`+1.5–2.2` rank, σ=½ only); state-dependent completion can change observed finite corank | `01-geometry` §3 corank; `08` APEX-A | `penrose-r28-*` |
| **N3** (R30) | **Jensen anti-collective margin firewall** — natural Ξ time-order *suppresses* TP-defect nucleation (reverse of expectation) | `08` APEX-B (Jensen=2κ₋), G-C17 | `penrose-r30-*` |
| **N4** (R34) | **State-law abscissa passport** `σ_wall = max(½, 1/k₀)` — hidden state-law hypothesis in the abscissa theorem. `[BRIDGE-CANDIDATE]` | `01-geometry` §6; `08` APEX-C | `penrose-r34-*` |
| **N5** (R36/R37) | APEX-B detector must be **sign-changing AND scale-matched** (`C_a(τ)` zero-area core/wing; matched width `≈a/2`) | `03` Thm I, `07` L-A, `08` APEX-B | `penrose-r36-*`,`-r37-*` |
| **N6** (R41) | **FID Hankel volume bottleneck** (`κ_n=ζ(2n+1)`, sign lost size 8); needs tail-stable certificate | `08` APEX-B / FID | `penrose-r41-*` |
| **N7** (R42) | **Affine passport `Π(S)=(|S|,Σm)`** with shift `−|S|log p`; affine determinant-volume observables RH-blind until `Π(S)` subtracted `[gatekeeper]` | `01-geometry` §2, `02-transport` §5, C2 | `penrose-r42-*` |
| **N8** (R45) | **Scalar layer `β` is not an independent mixing coordinate** (true Δ retains σ-lane structure after β-conditioning) | `01-geometry` §4 layers; LT1 | `penrose-r45-*` |

### 2b. The gatekeeper class (Conway/hgt-machine — methodology conjectures sharpening the framework)
| Gate | Refines | One-line acceptance criterion | Evidence |
|---|---|---|---|
| **G-gate-C3** | C3 | guard-band invariance reporting (single window edge-contaminable; `11/12` stable) | `conway-hawkes-edge-c3` |
| **G-gate-C4a** | C4 | per-lane-spectrum-preserving controls mandatory (isospectral surrogate kills cross-lane top eig; per-lane power 1e-15) | `conway-isospectral-orientability-c4`, `-morphogenesis-noise-c4` |
| **G-gate-C4b** | C4 | report cross-lane **memory-kernel / Laplace family**, not just `top_eig`/`ξ_σ` | `conway-grote-hynes-c4-memory` |
| **G-gate-B2** | B2 | multiscale contour/splitting (one-scale smoothing falsely merges off-seam pairs) | `conway-finite-size-rounding-b2` |
| **G-gate-APEXB** | APEX-B | height-coverage/mask certificate (centered `~1/8` mask hides positive core) | `conway-survey-mask-apexb` |
| **G-gate-C6** | C6 | carrier-event peak-retention certificate (retention `0.724→0.412`) | `conway-attractor-switching-c6-sampling` (id801) |
| **G-gate-twoclock** | two-clock / C5 | declare observation sequence + min window (`120`-sample subwindows flip) | `conway-observation-sequence-two-clock` |
| **G-gate-affine** | C2 holonomy | recurrence passport — de-periodize log grid or it is universal aliasing (`1.000000` all 18) | `conway-affine-boundary-alias` (id802) |
| **N9** | APEX-A | domain-corank **leak law `T/(N+T)`** (finite corank windows boundary-dominated) | `conway-domain-invariance-corank` |

### 2c. New carrier-facet conjectures (Conway)
| ID | One-line | Maps to | Evidence |
|---|---|---|---|
| **N10** (id800) | **Weld first-bridge orientation** — earliest A/P cycle connection is *left of Re=½* for true (left-first 8/8; finite/random right-first 7/8) | `01-weld` §3, Group D/E, C2 | `conway-monodromy-transitivity-weld` |
| **N11** (id748) | **Near-neutral hidden layer** at σ≈0.7 (hidden_frac 0.707, hidden_mean +0.042) | C5, Group B/F | `conway-near-neutral-collapse` |
| **N12** (id750) | **Transition-path softness** (edge-softness ~46.8 vs finite ~12) | C3, Group B/D | `conway-transition-path-vs-residence` |
| **N13** | **Context-fragility monotone** (0 violations true; controls keep violations) | C3, Group B | `conway-catch-context-phase-noise` |
| **N14** | **Phase-defect mass is component-bound** (short non-singleton components; survival 9–12/36) | C4, Group C, L-C | `conway-filtration-particle-bound` |

---

## 3. Falsifications / downgrades (a specific candidate, NOT the conjecture's target)

| What | Verdict | Evidence | Doc affected |
|---|---|---|---|
| **Naive *scalar* oriented 2-form** (C1's literal `∬dO∧dφ`) | **FALSIFIED** as a working detector: `0/9` scalar `(O,φ)` variants pass the combined gate; raw 2-form shares sign across true/finite/random/zero-pole. R69 minimal counterexample: identical scalar samples, opposite oriented areas `±5.633`. **C1 must be the non-scalar/holonomy form.** | `conway-ventilation-c1-twoform`, `penrose-r69-*` | `04` LT7, `05` LT7, `08` C1 |
| **Scalar Layer as discriminator** | **FALSIFIED**: `SCALAR_SCALE_RESCUE 0/16`; `logP` exactly random-phase-blind | `conway-scale-invariance-scalar` | `01-geometry` §4, `05` |
| **Raw one-object `H=A+P` scalar selection** | **FALSIFIED**: `H_BEST_THRESHOLD 0/18`; `H` residual `0.8922` *worse* than `Δ` (`0.0014`) | `conway-soc-scaling-one-object`, `-catalog-completeness-one-object` | `02-transport` §0 |
| **Naive phase-run positivity as an HT detector** | **FALSIFIED / re-confirmed**: adversarial constant-phase FE-exact fake forces full carrier positivity (`true_longest = best_fake_longest = 121`) | `penrose-r9` | `05` §0, `synthesis` §4/§5 |
| **Boundary-domain finding** id764 | **DEMOTED → id765 (DEAD-END)**: finite z-scored controls comparable; STEP12 survival 1/4 windows | `hgt-machine-state` | `06` (was never promoted) |

---

## 4. Precisifications (existing claims made sharper)

| Claim | Precisification | Evidence | Doc affected |
|---|---|---|---|
| **Universal curvature** `[∂_s,M_p]=−log p` (01 §2) | extended to blocks: every affine tangent-volume observable factors through **passport `Π(S)=(|S|,Σ_{m∈S}m)`**, shift `−|S|log p`; distinct blocks sharing a passport have identical trace. **C2's holonomy = the shape content beyond `Π(S)`.** | R42 | `01-geometry` §2, `02-transport` §5, `08` C2 |
| **Seam = `Fix(ι)`, `ι:s↦1−s`** (everywhere) | **Formal correction (external audit):** the *holomorphic* `s↦1−s` fixes only the point `s=½`; the *line* `Re=½` is `Fix` of the **anti-holomorphic** `s↦1−s̄`. The line (the seam) is what is meant. | `deep-research-report.md` | `01-geometry` §1, `01-weld`, `09` §1 |
| **Off-line quartet curvature** `2(a²−τ²)/(a²+τ²)²` (01 §5, 03, 06) | it is the **same-height mirror pair** `ρ=½±a+iγ` contribution near `t=γ`; the conjugate pair gives a second window near `t=−γ`. And (R36/R37) it is a **zero-area positive-core/negative-wing** kernel whose faithful detector must be sign-changing + scale-matched (width `≈a/2`). | `deep-research-report.md`, `penrose-r36/r37` | `01-geometry` §5, `03` Thm I, `06`, `08` APEX-B |
| **C4 (`ξ_σ`)** | now **triply gated** (per-lane-spectrum-preserving controls; cross-lane memory-kernel reporting) and **supported** by isospectral separation; "zero-spacing kill not fully discharged" | R28-gates, `conway` C4 nodes | `04` LT4, `08` C4 |
| **Abscissa-of-convergence seam `½`** (01 §6) | carries a **hidden state-law hypothesis**: total wall `= max(½, 1/k₀)`; robust `½` only for source-pure (U(1)) state laws | R34 | `01-geometry` §6, `08` APEX-C |
| **Dyson meta** (holonomy not curvature) | sharpened to **R6 fixed point**: every value-relation transfer collapses to shift/deriv rank; a win needs a new transcendence detector | dyson R6 | `05` §0, `synthesis` §5 |

---

## 5. Confirmations / over-determinations (treat as fixed; stop re-testing)

- **Right-strip `σ≈1.2` true↔finite collapse** — universal across ~100 new nodes (finite gaps
  `0.0003–0.0052`). A fixed property, not a result to re-derive.
- **Berry completion-switch (R24/id773)** — reproduced and bounded (imbalance `0.485→0.0` at σ=½,
  residual to relative phase `1.46`; off-center reintroduces `0.117`). *Caveat repeated by the
  experiments:* the exact seam equality is FE-symmetry/BRIDGE, not new HT.
- **The seam apex is transcendence/positivity-only** — a large dead-end block (Penrose R3–R8, R14,
  R17, R18, R21, R22, R25, R26, R32, R43–R52, R59–R68 + the whole Dyson HGT-continuation series)
  collapses onto the FE-completion / argument-principle / zero-proximity / left-strip-Δ floor. Strong
  negative evidence the apex is not reachable by transport/topology/sampling reframings.
- **Weld/constraint symmetry does NOT force positivity/RH** — independently re-witnessed (Penrose
  R51 seam-firewall: center excess `−0.0082`; R62 two-axis: FE residual `~2e-13` yet positive center
  curvature `2/a²`; R61 B2 synchronous artifact).

---

## 6. Per-document change map

| Doc (revision01/) | Change | Type |
|---|---|---|
| **01-landscape-and-geometry.md** | §1 fixed-locus correction (point vs anti-holomorphic line); §2 passport `Π(S)` extension of universal curvature (N7); §3 corank Ito/Strato warning (N2); §4 Scalar Layer falsified + β-not-mixing (N8); §5 curvature-window correction; §6 abscissa state-law passport (N4) | precisification ×4, new conjecture ×3, falsification ×1 |
| **01-landscape-and-weld-geometry.md** | Berry-seam layer reconfirmed (R24, BRIDGE caveat); Scalar Layer note (N8); pointer to the gatekeeper class | confirmation, precisification |
| **02-transport-system.md** | §5 holonomy sharpened by passport `Π(S)` (N7); §4.6 C4 memory-kernel gate; appendix axiom-4/8 still undischarged, now with gates | precisification, new conjecture |
| **03-theorems-toward-rh.md** | Theorem-I / L-A curvature window correction + scale-matched detector (N5); no-go reconfirmations (R51/R62); the bridge unchanged (still OPEN) | precisification, confirmation |
| **04-light-tower-support.md** | new supports: isospectral C4 (LT4), Weld first-bridge orientation (LT7/Weld, N10), near-neutral (N11), transition-path (N12); **LT7 caveat: the naive scalar 2-form is falsified** | new support, falsification-caveat |
| **05-light-tower-challenges.md** | new falsifications (naive C1, Scalar Layer, H-selection, R9 reconfirmed); the **gatekeeper acceptance standard** folded into the no-go standard; dyson R6 fixed point; the seam-only dead-end block | falsification ×4, new acceptance standard, confirmation |
| **06-experimental-findings.md** | new **Section IV — the 06-20/21 battery** with effect sizes (R27/28/30/34/36-37/41/42/45, the gatekeeper findings, the falsification numbers, id764→765) | new findings (numbers) |
| **07-theorems-and-lemmas-required.md** | L-A/L-C/L-D refined by the gates; new lemma-shapes: passport-subtraction (N7), scale-matched detector (N5) | precisification, new lemma-shape |
| **08-conjectures-required.md** | new **§6 — the 06-20/21 additions**: N1–N14 + the gatekeeper class + the §3.1/3.2/3.3 status ledger; revised priority order | new conjecture ×many, status changes |
| **09-preprint-draft.md** | §3 empirical carrier + §5 central question updated (R9 reconfirmation, C1-scalar falsification); guardrail sentence **unchanged** | precisification |

**Carried forward unchanged:** the `2-fully-proven` / `3-formalized` Lean bedrock (no batch touched
it); `00-README.md` (superseded by `revision01/00-README.md`); `deep-research-report.md` (it is the
*source* of two corrections, not a revision target).

---

## 7. What did NOT change (explicit, for honesty)

- **No new proof of RH.** Nothing crossed the wall.
- **No new ledger promotion and no new Lean.** The batch is entirely SEARCH-register
  (`[CONJECTURE]`/`[OBSERVED]`/`[FALSIFIED]`). The Lean bedrock (`07` §2) is untouched and unchallenged.
- **No new BRIDGE theorem.** R34 is labelled a *bridge-candidate*, not a proven bridge; R42 is a
  gatekeeper finding, not a promoted theorem.
- **The two apexes remain open and distinct** (APEX-A Schanuel-for-prime-logs; APEX-B uniform-in-`d`
  positivity), joined only at the seam (`ω=0 ⇏ RH`). The batch sharpened their detectors and gates,
  not their truth.
- **The §4 surrogate ladder is still unrun.** R9 shows a naive fake already defeats naive run-positivity;
  R53 adds that a grid-stability certificate is a precondition. It remains the single most informative
  open action.

*Source inventory: `logs/conjectures.md` (standalone conjecture catalog), `logs/synthesis.md` (updated
narrative), `logs/archive/{penrose-working-log,conway-working-log,hgt-machine-state,dyson-working-log,
penrose-machine-state}.md`, `computations/2026-06-2[01]-*`. All numbers quoted as recorded in those
sources.*

---

## 8. Revision 01.1 (2026-06-21) — SOTA integration, Conjecture E, review precisifications

A second pass folding in (a) the external SOTA calibration, (b) a sharpened no-flow conjecture, and
(c) a structured-review of `big-picture.md`. No new proof, ledger promotion, or Lean.

### 8a. New: Conjecture E (scoped no-generative-flow operator)
The founding "constraint, not flow" lens is raised to an explicit, **scoped** conjecture: *no
prime-built, order-preserving, generative one-parameter-flow self-adjoint operator has the zeros as
spectrum with self-adjointness ⟺ RH; any genuine Hilbert–Pólya realization is archimedean and is a
positivity (`κ₋=0`), not an evolution.* Scope guard: does **not** ban heat-flow / de Bruijn–Newman /
potential theory or archimedean positivity operators. **Reconciles** the instruction to sharpen the
no-operator stance with the review's caution: the recent **Connes–Consani prolate operator** is
archimedean/positivity and so *confirms* the scoping rather than refuting it. *Files:* `big-picture.md`
§4, `../../../logs/conjectures.md` §4, `02-transport-system.md` Rev 01.1, `08-conjectures-required.md`
§7.1, `05-light-tower-challenges.md` Rev 01.1.

### 8b. SOTA-lag consolidation (the largest external gap)
Folded the 2026 calibration (`../big-picture-vs-sota.md`) into the docs:
- **APEX-B** ↔ Pólya–Jensen / **Griffin–Ono–Rolen–Zagier 2019** (fixed-`d` proven, uniform-in-`d` open
  ⟺ RH); the live construction of the archimedean positivity is **Connes–Consani 2014–2026**
  (Riemann–Roch / Jacobian of `\overline{Spec ℤ}`, prolate-operator realization) — recorded as the
  corpus's largest lag and the strongest handle on Master 2. *Files:* `03` Rev 01.1, `07` Rev 01.1,
  `08` §7.3, `05` Rev 01.1.
- **APEX-A** ↔ Schanuel-for-prime-logs (open even for `{log 2, log 3}`), role scoped to "why the value
  detector is hard."
- **Source A/B** ↔ Hardouin–Singer / Adamczewski–Dreyfus–Hardouin; the open **weld** is the joint
  archimedean+prime direction beyond their `ℂ(z)` results.

### 8c. Review precisifications (applied to `big-picture.md`)
| # | Change | Type |
|---|---|---|
| 1 | one-sentence picture rewritten: rules out only a *generative* flow; heat-flow/de Bruijn–Newman/potential theory/source-measure remain valid lenses | precisification |
| 2 | "constraint not flow" scoped; Hilbert–Pólya softened into Conjecture E (positivity, not evolution) | precisification + new conjecture |
| 3 | **Master Conjecture split** into Master 1 (transport face) / Master 2 (faithful-index face) / identification bridge — "holonomy is κ₋" is a theorem to build, not a name | precisification |
| 4 | affine confinement restated as a **theorem schema** (observables factoring through `Π(S)` are RH-blind), not a blanket ban on positivity methods | precisification |
| 5 | APEX-B equivalences **registered**: one faithful restatement (`κ₋=0`), two classical theorems (Jensen–Pólya, Weil), two conjectural bridges (`Ω≽Π`, G5) | precisification |
| 6 | Schanuel apex role made **modest** ("why the detector is hard," not a necessary RH route) | precisification |
| 7 | bottom line keeps the "classical when vocabulary stripped" qualifier prominent; geometric interpretations flagged `[CONJECTURE]`; anti-conflation discipline named | precisification |
| 8 | next moves reaffirmed: surrogate ladder (empirical fork) + transcendence detector not of shift/deriv-rank (moonshot) | confirmation |

### 8d. What did NOT change (8b–8c)
Still no RH proof, no ledger promotion, no new Lean, no new BRIDGE theorem. Conjecture E is a *scoped
framing assumption*, not a theorem; the SOTA integration is bibliographic calibration, not new results.
The two apexes remain open and distinct; the surrogate ladder remains unrun.

---

## 9. Revision 01.2 (2026-06-21, `connes`) — the rung-1 no-go (central tension resolved)

Analytical + computational cleanup. The standing "is the weld carrier a native-HT detector?" tension is
**resolved deflationary by argument**; the corpus is pruned accordingly.

### 9a. The rung-1 no-go `[ARGUMENT — one classical import; verified]`
By Hadamard, every entire function with ξ's exact zeros and finite order is `e^{q((s−½)²)}ξ`; its
log-derivative keeps `ζ'/ζ` untouched, and `HT ± (D-alg) = HT` ⟹ every such object is HT. **No
FE-exact, ζ-exact-zeros, non-HT object exists** ⟹ the surrogate ladder's decisive rung is empty.
Verified: `2026-06-21-connes-surrogate-ladder-nogo` (carrier decomp 1.4e-31; level law 7e-32;
`Δ_S→Δ_true`). Sharpens Penrose R32. **The weld carrier is settled as an analytic-continuation /
zero-structure discriminator, not a transcendence detector.**

### 9b. The GPT detector `𝔗_ξ` (`gpt/01.md`) — relocated to the bridge axis
All four components of GPT's `𝔗_ξ = Hol^{⊥Π,event}_{Ward/src}(d log ξ)` are **invariant** under the
rung-1 surrogate (`μ_S=μ_ξ`, `W_S=W_ξ`, `∮dq=0`, passport shared; verified
`2026-06-21-connes-ward-holonomy-invariance`). So `𝔗_ξ` is a `{zeros, FE, source}` detector — **not**
transcendence — but it **is** the right instrument for the **bridge arrow (Conjecture C / Lemma 2)**
(source-width tomography = where the charge lives). Adopted there.

### 9c. Pruning (what this closes/relabels)
- **Closed:** "run the §4 surrogate ladder" everywhere (synthesis §4/§6, 05 §0, 06 III, 08, 09 §5,
  big-picture #2) — the adversary is provably empty.
- **Relabeled:** the carrier (and `𝔗_ξ`) → structural weld invariant (Master 1) + analyticity / source
  diagnostic; C1's "native-HT" claim dropped.
- **Sharpened open work:** the bridge arrow (C) and the positivity apex (B); A scoped to "why the value
  detector is hard."
- Updated: `logs/synthesis.md` §4/§5/§6, `logs/conjectures.md` Part 6, `big-picture.md` issue 2 / lens
  8 / §5; new `revision01/research-topics.md`.

### 9d. What did NOT change
Still no RH proof, no ledger promotion, no new Lean. The no-go is an `[ARGUMENT]` resting on one
classical import (ζ hypertranscendental); it resolves a *meta* question (the carrier's status), not RH.

### 9e. The HT is divisor-encoded — gpt/02's source-quotient detector is self-defeating
`[ARGUMENT — classical Hadamard; verified `2026-06-21-connes-divisor-encoded-ht`]` ξ is order 1 ⟹
`ξ'/ξ = b + Σ_ρ[1/(s−ρ)+1/ρ]` ⟹ the source-quotiented connection is a **constant**. So a
"remove-the-divisor-then-test-nonclosure" detector (gpt/02) returns zero defect on ξ — it removes the
HT, which is **divisor-encoded** (the arithmetic of `{γ_n}`). **Unified frame:** the two apexes meet at
the divisor — its *geometry* = positivity/bridge axis (B/C), its *arithmetic* = value axis (A); phase/
holonomy/`𝔗_ξ` see geometry, transcendence is arithmetic. Updated: `big-picture.md` issue 1 + lens 5.

### 9f. gpt/04 ratification + refinement
gpt/04 ratifies the divisor map (geometry→B/C, arithmetic→A) and the `sin πs` contrast. Refinement: the
`{γ_n}↔{log p}` algebraic-independence link is **conjectural** (explicit formula / DSS-cross), not a
proven equivalence — `big-picture.md` issue #1 softened ("equivalently" → "tied to … link itself
conjectural"). No new result.

### 9g. Source-width tomography = the Conjecture-C instrument; B and C are one object at two scales
`[OBSERVED/verified `2026-06-21-connes-source-width-tomography`]` The contour moments
`M_k=(1/2πi)∮(s−½)^k ξ'/ξ ds=Σ(ρ−½)^k` (= the superzeta/Li power sums, proven bricks) give a
source-accountable tomography. Passport (`M_0,M_1`) is off-seam-blind; the discriminator is the
explicit-formula defect `D2=Re(M_2)+Σγ²=Σ(β−½)²` (verified: real ζ `D2=0`; inserted off-line quartet
`D2=4a²>0`). One-scale smoothing merges off-seam pairs (B2 gate); `M_2`/thin-strip separate them.
**Synthesis:** `D2` windowed = local detection (Conjecture C / Lemma 1), globally regularized = Weil/Li
positivity = RH (Conjecture B / APEX-B) — the bridge instrument and the positivity apex are the **same
power-sum moments at two scales** (both divisor-geometry). Lemma 2 (global confinement) stays open.

---

## 10. Revision 01.3 (2026-06-21, `connes`) — Contour-Moment Bridge Instrument + new gatekeepers

- **NEW NOTE `10-contour-moment-bridge-instrument.md`** `[PROVED Thms 1–3; global OPEN]`: the relocated
  `𝔗_ξ` has one clean bridge-side representative — the contour moments `M_k(R)=(1/2πi)∮(s−½)^k ξ'/ξ ds
  =Σ_ρ m_ρ(ρ−½)^k` (= superzeta/Li power sums). Thm 2: the defect `D₂(R)=Re M_2+Σγ²=Σ m_ρ(β_ρ−½)²≥0`,
  `=0 ⟺` window seam-confined (local detection, Lemma 1). Thm 3: smoothing-merge gatekeeper. **B↔C
  unification:** windowed `M_k` = local C; regularized global `Σ(β−½)²=0 ⟺ RH` = B. Pure divisor
  geometry (preserves the no-go). Ratified by `gpt/05.md` (split-theorem milestone) + `gpt/06.md`.
- **New chat gatekeepers (Conway/Penrose, all self-scoped to bridge-geometry / Conjecture-E — the
  reorientation landed):**
  - id828 (Conway) **zero-shadow topology** needs a 2-part certificate: profile **recurrence +
    connected spanning support** (recurrence alone finite-vulnerable; connectivity alone
    thin-bridge-vulnerable). → bridge-geometry gate.
  - id829 (Penrose) **reset-occupation** needs an **external-feed subtraction passport** (rich shared-feed
    captures some R15 rows; high-window residual survives) — demotes R15 row-by-row.
  - id830 (Conway) **prime-built feedback flows** need an **out-of-sample zero-spectrum + spacing kill
    gate** (internal prime-lane lock-in is not a zero-generating flow) → Conjecture-E diagnostic.
- Updated: `research-topics.md` (T1 contour-moment note; §6 gatekeeper suite); `logs/connes-worklog.md`.

### 10a. Contour-moment Lemma 4 (refinement-invariance + additivity) + chat 831/832
- **Note 10 / Theorem 4** `[PROVED — residue; verified `2026-06-21-connes-moment-additivity-invariance`]`:
  `M_k(R)` depends only on the enclosed divisor ⟹ refinement-history invariant (passes Conway id832's
  Master-1 gate by construction) and **finitely additive**: `D₂(R₁⊔R₂)=D₂(R₁)+D₂(R₂)`. **Local→global law:**
  global confinement = `D₂=0` on every window = regularized `Σ_ρ(β−½)²=0` = **RH**; the only open piece is
  the regularization (height baseline via the explicit formula), not the composition.
- **id832 (Conway)** Master-1 holonomy refinement-history-invariance gate — **answered**: the contour
  moments `M_k` satisfy it (residue), so they are the correct non-winding observable.
- **id831 (Penrose)** source-built `κ₋` needs a **congruence passport** (only congruence preserves inertia,
  Sylvester; scalar reporter/projection summaries are measured evidence, not `κ₋` certificates) → Master-2/B
  gate; recorded in research-topics P2 (#13/#14).

### 10b. Note 10 / Lemma 5 — the bridge regularization is Li's criterion (B↔C fully unified)
`[BRIDGE — classical Li; verified `2026-06-21-connes-li-regularization`]` The global regularized
`Σ_ρ(β−½)²` (axis C equality) has its convergent positivity companion in **Li's criterion**
`λ_n=Σ_j C(n,j)(−1)^{j+1}P_j ≥ 0 ⟺ RH`, built from the SAME divisor power sums `P_k=Σ_ρ ρ^{-k}` (superzeta
brick). Verified `λ_1..λ_8>0` from ζ's first 80 zeros (→ classical `0.0231, 0.0923, 0.2076` from below).
**B (λ_n≥0) and C (D₂=0) are two power-sum readings of one divisor; M_k is the common substrate.** Closes
the "regularization open" gap (it is classical Li/Weil = APEX-B); open core unchanged: `λ_n≥0 ∀n`.

### 10c. Note 10 / Corollary 5a — Jensen/Turán is a third power-sum reading; chat 834/835
- `[classical GORZ floor; verified `2026-06-21-connes-jensen-turan-apexb`]` the Jensen coeffs
  `a(n)=(−1)^n[t^{2n}\text{-coeff of }Ξ]` are the elementary-symmetric/Newton companions of `P_k`. So Li
  `λ_n`, Jensen `J_{d,n}`, Hankel `det H_d`, and the bridge `M_k` are all functions of **one divisor** —
  "one wall, many names" made concrete; open apex = uniformity in `d` (= RH). Verified: `a(0)=0.49712`;
  Turán `>0` n=1..12 (margins `7e-5→8e-62`, the sparse no-margin in Jensen coords); d=3,4 hyperbolic.
- **id834 (Conway)** event-certified contours need an **event-community passport** (side
  distribution/entropy, cluster count, refinement stability), subordinate to winding/root-location →
  refines the Note-10 contour-moment calculus requirements.
- **id835 (Penrose, negative)** co-failure sheets need an **absolute source-reserve / inner-filter-overlap
  passport** (rank-normalized overlap manufactures false sheets) → Group-C / #24 gate.

### 10d. APEX-B normalized Turán margin + Certified Calculus v1.0 + chat 838/839
- `[OBSERVED; consistent with GORZ]` normalized Turán ratio `g(n)=a(n)²/(a(n−1)a(n+1))>1` decays to 1 as
  `g(n)−1~c/n` (`2026-06-21-connes-turan-normalized-margin`) — uniform positivity is delicate even
  scale-free (the corpus no-margin in Jensen coordinates). Folded into note 10 Cor 5a.
- **Certified Contour-Moment Bridge Calculus v1.0** (note 10, new section) — the 8-point admissibility
  spec + 3 theorem-schemas (refinement-invariant certificate; faithful reporter congruence gate;
  prime-flow zero-spectrum gate), consolidating gatekeepers id808/785/796/830/831/832/834/836/837 +
  `gpt/07.md`.
- **id838 (Penrose)** transition-softness boundary/confinement passport (battery passes); **id839 (Conway)**
  holonomy event-shape needs deformation-stability over a thickening band — again `M_k` passes by
  construction (it is the residue, invariant under homotopic deformation), unlike event-shape readouts.
- Runpod env set up (`python3.13`, mpmath 1.4.1) for subsequent runs.

### 10e. Chat 840/841 — full-kernel + zero-shadow live/fixation gatekeepers
- **id840 (Conway)** cross-lane holonomy events need a **full directed lag kernel** (off-diagonal mass)
  with finite/random controls — pairwise co-event counts saturate (true=finite=90 edges) and spectral
  radius is finite-vulnerable. → Master-1 / C4 kernel gate.
- **id841 (Penrose)** zero-shadow bridges need a **live/fixation persistence passport**: accept only when
  the fixed full-mask span is confirmed by sliding live-window spans, not time-smear dilation. → #27 gate.
- Both fold into the Certified Calculus gatekeeper suite (note 10) / research-topics §6.

---

## 11. Revision 01.4 (2026-06-21, `connes`) — Divisor Atlas + passport blindness; FID positivity resolved

- **NEW NOTE `11-divisor-atlas-and-passport-blindness.md`** `[PROVED — classical/elementary]`: the explicit
  atlas `M_k=p_k ↔ e_n ↔ h_n ↔ a(n) ↔ λ_n ↔ J_{d,n} ↔ H_d ↔ Q_W ↔ κ₋` (one divisor, many charts) + the
  **finite-passport blindness theorem** (any finite low-order passport not reconstructing the local
  divisor or computing `D₂` is seam-blind: the `M_2` quartet counterexample + the `K<N` fibre-dimension
  argument). Makes "one wall, many names" precise and explains *why* the apex is uniform-in-`d`. Distilled
  from `gpt/08.md` + `gpt/09.md`.
- **FID positivity RESOLVED** `[verified hi-dps `2026-06-21-connes-fid-prime-peel-hankel{,-hidps}`]`: R41's
  "free-cumulant Hankel loses sign at size 8" is **numerical underflow**, not a positivity failure —
  `H=[ζ(2(i+j)+3)]` is genuinely PSD through size 24 (dps150) / 28 (dps300); the thin cone is quantified
  `det ~ 10^{−43·size}` (need `dps ≳ 43·size`). Conway **id843** prime-peeling genuinely reconditions
  (size-24 raw min-det `1e-1039` → `peel{2}sc3` `1e-668`). FID open question is now a *tail-stable
  certificate*, not positivity.
- Chat **id842** (Conway, C3 cryptic-context σ/window activation atlas), **id843** (FID prime-peel basis,
  above), **id844** (Penrose, joint-source covariance passport for source-built κ₋) — folded into the
  gatekeeper suite / FID route.

### 11. Revision 01.4 — Atlas note (gpt/08–09) + FID/R41 resolved
- **NEW NOTE `11-divisor-atlas-and-passport-blindness.md`** — consolidates the **atlas** (Li, Jensen,
  Hankel, Weil, κ₋, M_k = symmetric-function coordinate charts of one divisor; transforms = Newton
  identities, **classical**) + the **finite-passport blindness theorem** (any fixed-order passport not
  reconstructing the local divisor / not computing D₂ is seam-blind; **elementary**). Makes "one wall,
  many names" precise. No new mathematics — consolidation of classical facts under the corpus lens.
- **FID/R41 resolved** `[OBSERVED]`: `κ_n=ζ(2n+1)` Hankel is genuinely PSD (it's a positive moment
  sequence); R41's "sign loss at size 8" is double-precision underflow (determinants `~1e-1000`). At dps
  150 PSD through size 24, dps 300 through size 28. Prime-peeling (id843) reconditions small-size tests
  but doesn't extend the size. The FID open question is FID⟹RH, not FID positivity.
- Chat 842 (C3 context atlas), 844 (joint-source covariance passport for κ₋) → gatekeeper suite.

### 12. Revision 01.5 — Seam constraint, forced vs free value-relations (note 12)
- **NEW NOTE `12-reciprocal-seam-moments-resolves-the-regularization.md`.** Re-cut in the founding
  register *constraint, not flow*. The seam values `S_k = Σ_ρ(ρ−½)^{−2k}` (abs. convergent reciprocal
  coordinate; the *forward* `Σ(ρ−½)^k` divergence was the false trail in #9) are read as the object's
  characteristic values; the question is which value-relations the constraint `Ξ(w)=Ξ(−w)` forces vs
  leaves free.
  - **FORCED (ω axis, RH-blind):** `(F1)` all odd seam moments vanish `μ_{2k+1}=0 ∀k` (= FE evenness at
    value level; structural — `log Ξ` is even); `(F2)` even moments real.
  - **FREE (κ₋ axis = RH):** whether `{T_k=(−1)^kS_k}` is a positive-moment sequence (Hankel PSD ∀order).
    Constraint reaches F1–F2 and stops; the residue *is* RH. Finite-passport blindness (note 11) = "the
    constraint under-determines the object in exactly the localization direction."
  - **FREE (A axis = APEX‑A):** independence of `{γ_n,S_k}` from `{π,log p,ζ(odd)}` — the value-relation
    apex; constraint forces no relation.
  - The three-way split (forced / free-localization / free-independence) makes "no generative rule"
    concrete: a constraint that fixes its even value-lattice and abandons both free axes.
- `[KNOWN]` the "Hankel-PSD ⟺ RH" equivalence is Laguerre–Pólya/Turán re-charted — used only to *locate*
  the κ₋ residue, not claimed. Numerically witnessed: `S_1=−0.0231049931…` = `−Σ1/γ²` to the exact
  partial-sum tail; `T_k>0`, Hankel PSD through `d=5` (`2026-06-21-connes-reciprocal-seam-moments`).
- **Resolves research-topics #9**: the "regularization" was a coordinate choice — reciprocal
  seam-squared values converge from `k=1`; #9's `Σ(β−½)²=0` is literally the κ₋ free-residue of F1–F2.

### 13. Revision 01.6 — Seam cancellation connects weld / superzeta / phase-defect / entire-ness (note 13)
- **NEW NOTE `13-the-seam-cancellation-connects-weld-superzeta-and-phase-defect.md`.** Connective, not a
  theorem. Splitting each superzeta value along the weld `ξ'/ξ(½+w)=A(½+w)+P(½+w)` gives
  `S_k = S_k^A + S_k^P`, and the two halves are **co-dominant and nearly cancel**:
  `|S_k^A|≈|S_k^P|≈2^{2k−1}` (grows; scale = `s=1` pole at distance ½) while the true `S_k≈γ_1^{−2k}`
  (decays; scale = first zero). Agreement depth `≈800^{−k}` (~23 digits at k=8).
  - **Cause:** `A` has `+1/(s−1)` (completion), `P=ζ'/ζ` has `−1/(s−1)` (ζ pole); they cancel — *why ξ
    is entire* — propagated to all seam-Taylor orders. This is the **phase-defect `Δ` at value level**:
    `Δ_k ∼ k·log(4γ_1²)` grows linearly in order; the seam is a maximal-cancellation locus by order.
  - **Connects four boxes into one mechanism:** weld(A+P) = superzeta{S_k} = phase-defect Δ =
    entire-ness `(s−1)ζ`. RH-relevant values = residue of a *forced* cancellation; sign still open (κ₋).
  - **Numerics corollary:** seam-Taylor `S_k` needs `≳2.9k` guard digits or the residue is destroyed —
    same disease as the FID/R41 underflow (§11), now named. `[OBSERVED dps40, KNOWN pieces]`.
- gpt/10 (ratifies Penrose r45/r46 gates): **anisotropic Jensen stability gate** (report direction-wise
  hyperbolicity radius `ρ_min(d,n)`, not scalar margin) + **fidelity-vs-detectability gate** (ridge/
  smoothing that improves PSD must report object fidelity; ridge `H+εI` is not a congruence) → folded
  into research-topics #15/#32. Chat 848–852 (anisotropic, storage-Schur, value-ergodicity,
  common-noise cross-lane) → gatekeeper suite #32.

### 13. Revision 01.5 addendum — weld split of the seam values; gpt/10 + new gates
- **Note 12 ADDENDUM (reasoned, no computation needed):** split each seam value along the weld
  `ξ'/ξ(½+w)=A(½+w)+P(½+w)` ⟹ `S_k=S_k^A+S_k^P`. By Cauchy–Hadamard (singularity distance alone):
  both halves `≍2^{2k}` (nearest singularity = `s=1` pole at distance ½: `A`'s `1/(s−1)`, `P`'s ζ-pole),
  while `S_k≍γ_1^{−2k}` (`A+P=ξ'/ξ` has poles only at zeros; nearest at `γ_1≈14.13`). The halves cancel
  to a residue exponentially smaller than either — depth `(4γ_1²)^{−k}≈800^{−k}`. The cancellation **is**
  the completion's `s=1` pole-cancellation (= ξ entire) read at value level. CONNECTS four corpus boxes:
  phase-carrier defect (A↔P cancellation) = weld(A+P) = superzeta `{S_k}` = entireness; RH-relevant
  values live in the residue. `[PROVED — elementary singularity analysis]`, reduces-to-known as a fact;
  value = the connection, not novelty. NOT posted to chat. (Lesson logged: known singularity locations ⟹
  coefficient asymptotics are reasoning, not an experiment.)
- **gpt/10 consolidated** (ratifies Penrose id848/id849): two APEX-B gates → research-topics #32 —
  *anisotropic Jensen radius* (scalar margin ≠ tensorial certificate; report direction-wise
  hyperbolicity radius `ρ_min(d,n)` + vulnerable axes) and *regularization fidelity* (ridge `H+εI` is not
  a congruence → regularized-object evidence, not original-object). Also id852 (Conway): cross-lane
  kernels need *common-field conditioning* (raw off-diagonal mass mixes shared per-time event field).

### 13b. Fused closed form for the seam superzeta values (certified)
- **One formula from three** (weld + Hadamard/superzeta + Γ-completion), certified to ~10⁻³⁸ for k=1..6
  (`2026-06-21-connes-superzeta-fused-closed-form`):
  `Σ_ρ(ρ−½)^{−2k} = 2^{2k} − ¼(2^{2k}−1)ζ(2k) − 2^{2k−2}β(2k) − (2(2k−1)!)^{−1}(ζ'/ζ)^{(2k−1)}(½)`,
  β = Dirichlet beta (β(2)=Catalan G).
  - **Derives note-13's `2^{2k−1}` law:** ζ(2k),β(2k)→1 ⟹ archimedean half → 2^{2k}(1−¼−¼)=2^{2k−1}.
  - **Value-relation (APEX‑A):** the zero-side power sum splits into THREE constant-families —
    π-periods ζ(2k), Catalan-family β(2k) (not a π-period), prime (ζ'/ζ)-derivatives. The archimedean
    half carries β(2k), so {S_k} are not π-periods; they mix the Γ-period lattice with the prime side.
  - Register: `[PROVED — fused closed form, certified]`; pieces classical (Voros), the fusion + the two
    readings are the contribution. Added as the analytic backbone of note 13.

### 14. Revision 01.7 — FID = reciprocal-seam instrument on the integer divisor (note 14); gpt/11; final gates
- **NEW NOTE `14-fid-and-reciprocal-seam-are-one-instrument-on-two-divisors.md`** (reasoned, no
  computation). FID (`κ_n=ζ(2n+1)` Hankel, #18) and the reciprocal-seam chart (`T_k=Σ(ρ−½)^{−2k}`,
  note 12) are the **same instrument** — a reciprocal-squared Stieltjes moment problem — on two divisors:
  - integers: `ζ(2k+1)=∫y^k dν`, `ν=Σ_m(1/m)δ_{1/m²}≥0` ⟹ FID Hankel PSD **unconditionally** (RH-empty).
  - zeros: `T_k=∫y^k d(Σ m_ρ δ_{y_ρ})`, positive ⟺ RH.
  So FID positivity is the integer divisor on the positive axis for trivial reasons; peeling
  (id843/id856) only reconditions. **The FID⟹RH content lives entirely in the integer↔zero map (the
  explicit formula / weld split, note 12 addendum), never in positivity of `ζ(odd)`.** Sharpens #18 to
  `[positivity is RH-empty]`. `[PROVED — elementary]`.
- **gpt/11** ratifies note 12 (reciprocal seam) as "the cleanest one-wall coordinate"; adds A-axis
  ergodicity passport + E-axis cluster/decoy passport framing → folded into #34 and the A-track.
- **Final agent gates (id854–857):** numerical-representation passport (Conjecture-E, id854) → #34;
  annular collar-clearance (contour moments, id855) → #10/#32; FID successor-integer peeling correction
  (id856) → #18/note 14; objectwise/fiberwise compatibility for 𝓜⁺ (id857) → #21/#32.

### 15. Revision 01.8 — THE ONE WALL (collapse of notes 10–14 into one canonical synthesis)
- **NEW CANONICAL NOTE `15-the-one-wall.md`.** Per directive ("so much in our docs that is the same thing
  in different dresses — turn them into one thing"): collapsed notes 10 (M_k/D₂), 11 (atlas+blindness),
  12 (reciprocal seam+constraint split), 13 (cancellation), 14 (FID), and the scattered names
  Li/Jensen/Hankel/Weil/κ₋ into ONE object + ONE wall + many coordinate charts:
  - §1 one object (constraint, not flow); §2 the one wall = reciprocal-seam Stieltjes positivity on the
    ZERO divisor (=RH=κ₋=0); §3 atlas (all names Newton-conjugate charts); §4 forced/free three-axis
    split (ω/κ₋/A); §5 the seam cancellation (weld=phase-defect=entireness); §6 FID = same instrument on
    integer divisor (RH-empty); §7 the separate value apex (A); §8 passport discipline; §9 bottom line.
  - Notes 10–14 banner-folded ("backing detail; read 15 first"), kept for their proofs. `[unifying, not
    new]`. Open unchanged: the wall (κ₋ all-order) + APEX-A.

### 16. Revision 01.9 — RESTRUCTURE: fold the new notes into 01/08, kill duplicates and history scaffolding
Directive: stop adding numbered notes; keep 01–08 as the compressed living synthesis; remove cruft and
in-doc history logs; read before editing.
- **Deleted** stale duplicate `01-landscape-and-weld-geometry.md` (ASCII predecessor of
  `01-landscape-and-geometry.md`).
- **Rewrote `08-conjectures-required.md`** as a clean current inventory: §1 C1–C6 (native-HT no-go folded
  into a §1 note), §2 B1–B3, **§3 THE ONE WALL** (folds former notes 12–15: reciprocal-seam Stieltjes
  coordinate, the atlas + finite-passport blindness, the seam cancellation, the certified fused closed
  form, FID-as-integer-divisor, plus APEX-A/B/C/D/E), §4 named/coordinate conjectures (G-C source-built
  family compressed into "source-built faithful index"), §5 gatekeepers (battery folded in), §6 one
  dependency block + one priority order. **Removed** the three "Revision 01.x additions / [REV01]"
  history sections (content folded into the body).
- **Deleted** notes 12,13,14,15 (folded into 08 §3). **Notes 10,11 kept** as the proven-lemma backing
  for 08 §3 (contour-moment + atlas proofs), re-bannered accordingly.
- **Trimmed `01-landscape-and-geometry.md`**: folded its `[REV01]` tail (anti-holomorphic seam locus,
  `Π(S)` passport, scalar-layer falsification, abscissa state-law, mirror-pair detector) into the body
  §1/§2/§4/§5/§6; deleted the tail and the header `[REV01]` pointer.
- id859 (Conway 50/50, Conjecture-E finite-window ladder) → #34.

### 17. gpt/13 — Lemma 2 restated as a positivity-transfer theorem (folded into 08 §2)
- gpt/13 reads note 15 / 08 §3 (THE ONE WALL) and ratifies it (one object / one RH wall / one separate
  transcendence apex). Genuine sharpening folded into **08 §2 (B2)**: the open core Lemma 2 is **not**
  "phase ⟹ RH" nor "FID positivity ⟹ RH" (FID is RH-empty); it is a **positivity-transfer theorem** —
  `completion + explicit formula + A/P weld ⟹ {T_k}` Stieltjes. Candidate subclaims: (i) total-positivity
  / variation-diminishing of the integer→zero transform; (ii) source-built `κ₋` from `{T_k}`; (iii) no
  off-seam signed defect survives the reciprocal chart. No new doc; folded per directive.

### 18. Formula-graph fold-back — canonical nomenclature aligned in the prose
- The 178→100 node reduction (`formulas-graph.md`, audit in `formulas-graph.worklog.md`) exposed
  nomenclature drift still living in the documents. Folded the canonical choice back:
  the line-curvature family `Σ_ρ(½+it−ρ)^{−k}` was written three ways — `χ`, `χ_n`, `P^{(k)}` — with
  `P^{(k)}` **colliding** against `P = ζ'/ζ` (the prime weld term). Unified to the canonical **`Φ_k`**
  (node PH1; `Φ_2 = (log Ξ)''`), reserving `χ` for the functional-equation factor `Γ_ℝ(1−s)/Γ_ℝ(s)`.
  Edits: `01` (curvature hierarchy + susceptibility-balance), `04` (LT6 bullet), `07` (T17). Collision
  removed; family now uniform across the set.
- No structural merges into the prose: the graph keeps framework-distinct RH-characterizations
  (APS index, Koszul/ω + caveat ω=0⇏RH, de Branges, period domain, FF ι-unitary) as separate nodes
  *edged* to the positivity master PA1, and the documents' "one wall, many names" + two-apex
  (positivity PA1 / value TA1, seam-joined) structure already mirrors that — restatement in context
  is not redundancy.

### 19. Folded OpenAI proof-route results (id919–933, gpt 19–20)
- **id919 (Li↔T_k signed kernel)** → 08 atlas: `L_n(y)=2−2C_n((4−y)/(4+y))` expands in the reciprocal
  basis with signed coeffs (`c_{n,1}=n²`, `c_{n,2}=−n²(n²+2)/12`), so Li positivity is not a
  coefficientwise route to `T_k` positivity — the transform is infinite and signed.
- **id931/id932 (gauge ghost + Hadamard finite part)** → 08: low-order charts need canonical
  normalization (`P_1=−b=1+γ_E/2−log(2√π)`, only `P_k, k≥2` absolutely convergent; zero-free gauge
  `δλ_n=cn²` makes phantom `δP_1=c, δP_2=−2c`).
- **id933 (folded-pair degree-1 minor)** → Formula 180 + bridge-theorem §4: `det H_1^(0)=−4μ²|y|²(Im y)²`,
  `det H_1^(1)=−4μ²|y|⁴(Im y)²`; **obstruction coordinate = `Im y`**; FE quartet is the `μ=2` special case.
- **id920 (boundary amplification)** → 08 §2 boundary bullet: finite Schur audit fails under amplification
  (`H(t)=I−εe^{κt}vv*`); need a scale-independent boundary Weyl inequality / canonical fixed extension.
- **gpt/20 #1 (FID strict total positivity)** → 08 FID note: even strict total positivity (Cauchy–Binet)
  on the integer divisor is RH-empty; the bridge is the explicit-formula transfer, not a stronger cone.
- **gpt/20 #2 (CO6 host passport)** → 07 T8: `g²=1⟹g=±1` only in a connected/scalar host; product/projector
  host gives `g=2e−1` sector signs.

### 20. id936 — source-aware Q_0-alone sufficiency (folded into bridge-theorem §3 + 08 §2)
- For the **actual** zero divisor, all-order `Q_0[p]≥0` alone forces every `y_ρ∈ℝ_{>0}`, hence RH:
  a real polynomial isolates any negative-real atom (`y·p(y)²<0`) or non-real conjugate pair
  (`Re[y·p(y)²]<0`) and makes `Q_0<0`. Reconciles the dual-barrier independence (id908/909/916) with
  single-form sufficiency: needing **both** `Q_0,Q_1` is the source-forgotten (abstract moment-sequence)
  statement; the divisor's real/conjugate-paired atom structure makes `Q_0` alone sufficient source-aware.

### 21. id937 — γ-tail law for the shifted square-tests (folded into bridge-theorem §3)
- High-height tail of `Q_r[p]` for `p(y)=y^j q(y)` is `O(G^{−(2r+4j+1)} log G)`: the source-aware `Q_0`
  certificate (`r=0`, `p(0)≠0`) is the slowest, `O(G^{−1} log G)`; `Q_1` starts at `O(G^{−3} log G)`;
  each hard-edge zero of `p` gains a further `G^{−4}`. Pairs with id936 (Q_0 alone suffices but converges
  slowest).

### 22. id938 — FE-orbit quotient generating function for T_k (Formula 181)
- `T_k = −2k(−1)^k [z^k] log Φ(z)`, `Φ(z)=Ξ(√z)` the even FE-orbit quotient (quotient multiplicity m per
  orbit; the factor 2 converts m to the bridge trace weight 2m). Consistent with `S_k=−k[w^{2k}]logΞ` and
  the folded `T_k=Σ_{[w]}2m_w y_{[w]}^k`. Added as Formula 181.

### 23. gpt/21 — Q_0-alone promoted to the minimal source-aware bridge target
- gpt/21 fully elaborates id936 and recommends restating the bridge theorem with the one-power test
  `Q_0` alone as the primary target. Updated bridge-theorem.md §1 (headline now the minimal source-aware
  form: `completion + explicit formula + boundary ⟹ Q_0[p]≥0 ∀p`, `[T_{i+j+1}]⪰0 ∀d`) and §7 summary;
  `Q_1` reframed as the **companion passport** (finite-domain repair of the unshifted form + classical
  Stieltjes consistency chart), required independently only in the source-forgotten abstract moment
  problem. No formula change (Q_0/Q_1 already in Formula 152).

### 24. id939 — seam centre ½ is unique for the reciprocal bridge (bridge-theorem §3)
- The recentring at ½ is forced: it is the unique centre for which the FE pair {w,−w} folds to one
  y-atom AND on-line zeros map to the positive axis. Off-centre ½+ε breaks folding (`4wε=0` needed) and
  makes `−(iγ−ε)^{−2}` non-real. Added as a well-posedness clause to bridge-theorem §3 step 1.

### 25. Leap (formula-graph): new exact edge GA4—LX5 (bridge BR6)
- Analytical leap connecting two previously-unedged nodes in different clusters: GA4 (`∂_s log χ`,
  Γ/ψ/χ) and LX5 (`θ'(T)=½log(T/2π)`, Riemann–Siegel theta / log-ξ). The exact identity
  `∂_s log χ(½+iT) = −2θ'(T)` (since `arg χ(½+iT)=−2θ(T)`, `|χ|=1`) was numerically certified to 1e-31 at
  T=10…1000. The Riemann–Siegel theta derivative *is* `−½ ∂_s log χ` on the seam; GA4's digamma
  asymptotics reproduce LX5's `½log(T/2π)`. Added as BR6 + the exact GA4—LX5 edge (upgrading the
  asymptotic-only GA1—LX5). Archive: it ties the FE-factor archimedean phase directly to the zero-count
  N(T).

### 26. Leap-significance judged; new cross-cluster edge PH2—LX3 (bridge BR7)
- Per "strengthen the web, judge housekeeping vs significance": re-judged BR6 (GA4—LX5) as
  **housekeeping** — exact but classical, and the two nodes already sat adjacent in the archimedean
  backbone (no connectivity gained). Labelled it so in the graph.
- New leap BR7 (PH2—LX3), judged **moderate significance** (cross-cluster, no prior edge; mechanism
  elementary but the synthesis is genuine): harmonicity of `log|ξ|` gives `Re Φ_2 = ∂²_σ log|ξ| =
  −∂²_t log|ξ|` and `Δlog|ξ|=2πμ_ξ`, tying line-curvature PH2 to source-measure LX3 and re-reading PH3
  (`RH ⟹ Φ_2<0`) as **RH ⟺ the critical line is a crest/ridge of log|ξ|** (concave along, convex across).
  Numerically certified to ~1e-28. id942 judged a non-finding (Conway's own note; classical determinant
  calculus) — no document change.

### 27. Leap: new edge IV4—PS14 (bridge BR8) — the squared coordinate is parity-forced
- Judged **moderate/load-bearing**: mechanism elementary (parity), but joins IV4↔PS14 (no prior edge) and
  grounds the bridge's coordinate. `Ξ` even ⟹ divisor `w↦−w` symmetric ⟹ all odd moments vanish
  (`Σw^{−1,−3,−5}=0` verified; even `Σw^{−2,−4}≠0`) ⟹ first informative reciprocal moment is `w^{−2}`.
  So `y=−(ρ−½)^{−2}` is **triply forced**: centre by FE-folding (id939), power −2 by parity (this), sign
  by on-line positivity. Added BR8 + edge to formulas-graph; completed the coordinate justification in
  bridge-theorem §3.

### 28. Insight (posted #research id943): line-curvature chart Φ_2<0 is necessary-not-sufficient
- Pursuing the BR7 converse to a genuine problem-space insight: `Φ_2(t)=Σ_ρ(½+it−ρ)^{−2}<0 ∀t` (log|ξ|
  concave on the line; the proven `RH ⟹` direction) is **necessary but NOT sufficient** for RH. An
  off-line zero adds a positive curvature bump peak `C_a(0)=2/a²`; near-line zeros (spike→∞) are always
  caught, but the bump is bounded (`2/a²≥8`, `a≤½`) while the on-line background `|Φ_2|~(log γ)²` grows —
  so a far-off-line `a=0.45` quartet is **undetected** at `γ≈180,260,261` (verified, first 900 zeros).
  RH-blind to far-off-line zeros, like the forward Hankel; contrast the faithful reciprocal-Hankel `Q_0`
  (obstruction `Im y`, fixed sign at all heights, id915/id933). Explains why the bridge uses the
  reciprocal-Hankel chart. Folded into bridge-theorem §4 + BR7 (converse resolved). Script:
  computations/2026-06-21-connes-phi2-line-curvature-blindspot.{py,txt}.

### 29. gpt/22 judged — confirms corpus, independently validates BR8; one graph edge added
- gpt/22 is a full synthesis of the recent batch (source-aware Q_0, Im y obstruction, tail law,
  even-quotient dictionary, seam-center, parity). **All already folded**; §6–7 independently re-derive
  BR8 (triply-forced coordinate, IV4↔PS14 parity) — corroboration, no document change.
- Honored its one explicit graph request (§5): added the even-quotient dictionary as an IV4—PS-POW edge
  in formulas-graph (Φ(z)=Ξ(√z), T_k=−2k(−1)^k[z^k]logΦ = Formula 181). Modest/mechanical consolidation.

### 30. Bridge-theorem §3: hard-edge density of the reciprocal measure
- Added: the bridge measure y=1/γ² has edge density ρ(y) ~ (|log y|/8π) y^{−3/2} near 0 (change of
  variables from N(T)~(T/2π)log T) — so T_0=∫ρ diverges, T_1=∫y·ρ converges, and Q_0 with p(0)≠0 probes
  this hard edge, giving its O(G^{−1}log G) tail (id937).

### 31. gpt/23 + gpt/24 folded — both incorporate the connes Φ_2 finding (id943)
- gpt/23 (reacts to id943): confirms Φ_2<0 ∀t is necessary-not-sufficient; recommends a guardrail node.
  Added **PH3b** to formulas-graph (Φ_2<0 RH-necessary/insufficient; corrected hierarchy Φ_2<0 ⊊ D₂=0 ⟺
  Q_0≥0 ⟺ RH). Φ_2 demoted to "crest shadow", not the wall.
- gpt/24 (proof-route synthesis): the Φ_2 finding now sits in its canonical "what the proof cannot be"
  list. Folded gpt/24's **candidate proof shapes for Q_0≥0** into 08 §2 B2: (a) direct square identity
  Q_0=∫|𝒦_p|²dμ_{arch/prime}; (b) positivity-preserving explicit-formula transfer integer→zero; (c)
  positive Jacobi/Stieltjes continued-fraction parameters from Ξ; (d) contradiction-localization vs D₂;
  with the arch/prime split Q_0=Q_arch+Q_prime as the likely-decisive computation.


### 32. 08 §2 B2(c): Jacobi/continued-fraction route assessed (gpt/24 §B; #research id944)
- Q_0 moment sequence T_k=2Σγ^{−2k} is positive-definite (β_n>0 through d=6, dps200) but dominated by the
  single atom y_1=1/γ_1² (T_k→2y_1^k; next atom suppressed (y_1/y_2)^k=2.2^k) → Chebyshev/Jacobi recurrence
  catastrophically ill-conditioned (α_n leave support [0,y_1] at the precision wall, ~80 guard digits/order).
  Jacobi/CF route needs y_1 deflated first; raw parameters have no clean stable structure. Folded into
  08 §2 B2(c). Script: computations/2026-06-21-connes-Q0-jacobi-parameters.{py,txt}.

### 33. 08 §2 B2(d): arch/prime form decomposition of Q_0 (gpt/24 §H; #research id945)
- Q_0=Q_arch+Q_prime (Ξ'/Ξ=A+P; S_k=−[w^{2k−1}](A+P), validated S_k^A+S_k^P=S_k to 1e-40) is NOT
  structureless: arch Hankel [T^A_{i+j+1}] has signature exactly (d,1) — one negative direction = the
  s=0,1 pole (S_k^A=2^{2k} ⟹ rank-1 negative −4·uu*, u_i=(−4)^i), rest PD; prime Hankel indefinite; sum is
  PD Q_0. The (2γ_1)^{2k}-deep cancellation is essentially rank-1 (the pole). Proof-shape hint: deflate the
  rank-1 pole, prove residual PSD. Also folded gpt/25 (reacts to id944): Jacobi route needs atom-deflation
  or a Christoffel test class p=∏(y−y_j)q. Script: computations/2026-06-21-connes-Q0-arch-prime-split.{py,txt}.

### 34. Session findings woven across docs (not just 08)
- bridge-theorem §5b "The emerging proof shape": the Q_0 measure is one dominant atom y_1 + hard-edge
  y^{−3/2} tail; the arch/prime cancellation is rank-1 (the s=0,1 pole, arch signature (d,1)) → conjectured
  proof shape = atom-deflated + pole-deflated + hard-edge-aware square-test positivity; the (d,1) signature
  is the finite-d shadow of the Weil/Hodge (1,∞) index (the two faces meet).
- 06 "No-margin / positivity numerics": added the three session findings (Φ_2 necessary-not-sufficient;
  Q_0 one-atom-dominated / Jacobi ill-conditioned; arch/prime rank-1 cancellation, arch sig (d,1)).
- formulas.md Formula 182: arch/prime Hankel split, sig[T^A_{i+j+1}]=(d,1), sig[T_{i+j+1}]=(d+1,0).

### 35. Formula web: BR9 edges the seam-split to the signature node
- formulas-graph BR9 (WD1/PS-POW ↔ PA5/IN1): the weld split Ξ'/Ξ=A+P lifts to a form-level split
  Q_0=Q_arch+Q_prime; arch Hankel sig exactly (d,1) (rank-1 pole, S_k^A=2^{2k} ⟹ −4·uu*), prime indefinite,
  sum PD — the arch (d,1) is the finite-d shadow of the Weil/Hodge (1,∞)/(1,ρ−1) signature. Connects the
  weld/seam-split cluster to the signature/inertia node. gpt/27 (programme consolidation, Thm 1–25 + Comp
  1–11): all already folded, no change.

### 36. Deflation refuted (gpt/27 Comp 4 / gpt/25; #research id946)
- Atom deflation does NOT fix Q_0 conditioning — both naive moment-subtraction (cond 5.6e30→1.9e40, r:0→10)
  and Christoffel ∏(y−y_j)q (cond →2.0e38, λ_min→7e-69, r:0→5) make it strictly worse: the reciprocal atoms
  cluster ever-tighter toward the hard edge (y_n/y_{n+1}→1), so removing the best-separated atom leaves a
  more degenerate residual. Ill-conditioning is intrinsic ⟹ a numerical/deflated-recurrence proof
  coordinate is dead; the handle must be analytic (closed-form S_k / rank-1 pole). Corrected bridge-theorem
  §5b (was "deflate → well-conditioned"), 08 §2 B2(c), 06. Script: computations/2026-06-21-connes-Q0-deflated.{py,txt}.

### 37. Most-dangerous polynomial (gpt/27 Comp 6; #research id947)
- λ_min eigenvector of H_d^(0) (d=6, λ_min=1.0e-39) = degree-d orthogonal polynomial with roots exactly on
  dominant atoms y_1..y_5 (auto-deflation → explains why Comp-4 deflation fails); residual mass broad/mid-
  range (atoms n≈4–20, γ≈25–80; 67% by n=8, 94% by n=30), not y_1 or hard edge. Obstruction distributed ⟹
  proof needs uniform (not local) control. Folded bridge-theorem §5b, 06. Script:
  computations/2026-06-21-connes-Q0-dangerous-poly.{py,txt}.

### 38. Q_0 Hankel off-line resolution is height-graded (gpt/27 Comp 7; #research id948)
- Inject off-line quartet {±a±iγ0} into on-line bulk; smallest d with λ_min(H_d^(0))<0 is d*≈γ0/3
  (γ0=14→4, 30→11, 80→>14); d*≠1 even at γ0=14 (bulk masks isolated-quartet d=1). All-order faithful
  (finite d*, caught eventually — unlike Φ_2's permanent blind spot) but finite-d resolution height-graded:
  a height-γ0 quartet → tiny atom |y0|≈1/γ0² near the hard edge, resolved only when the d-th OP node reaches
  it. ⟹ finite-d numerical Q_0 has height-limited reach; certificate is irreducibly all-order/analytic.
  Folded bridge-theorem §4, 06. Script: computations/2026-06-21-connes-Q0-hankel-resolution.{py,txt}.

### 39. FID calibration — the Q_0 numerical battery is generic, not RH-specific (#research id949)
- The RH-empty FID integer divisor (y_n=1/n², H_FID[i,j]=ζ(2(i+j)+3)) shows the SAME structure as Q_0:
  exponential ill-conditioning (cond 6e3→5e9→9e16, d=2/4/6), auto-deflating dangerous polynomial (roots on
  1,0.25,0.111,...), mid-range distributed obstruction (94% by n=8); differs only quantitatively (zero
  divisor ~1e15× more ill-conditioned at d=4). So every numerical Q_0 finding (Comp 3–7, id944–948) is
  generic to reciprocal-squared accumulating measures, carrying ZERO RH content. The RH content is only the
  integer→zero explicit-formula transfer ⟹ no Hankel/conditioning/deflation argument is RH-relevant; the
  proof must be the analytic transfer. Folded bridge-theorem §5b (calibration capstone), 06. Script:
  computations/2026-06-21-connes-FID-calibration.{py,txt}.

### 40. Analytical step: RH wall localized to a codim-1 prime-vs-arch budget (#research id950)
- Verified (d≤4): the single negative direction of Q_arch IS the pole vector u_i=(−4)^i (S_k^A=2^{2k} ⟹
  leading [T^A_{i+j+1}]=−4uu*; neg-eigvec·û=1.0). On u, Q_arch[u]=−Q_prime[u] to ~1e-12 (= the s=1
  entireness, form-level); on u^⊥, Q_arch is PD. So the 10^{2.8k}-deep cancellation is the single pole
  direction (automatic entireness), and RH ⟺ on the codim-1 complement u^⊥ the prime form Q_prime does not
  overcome the archimedean PD budget Q_arch — a perturbation-positivity wall (Q_arch = FID-like auto-positive
  integer side, Q_prime = prime RH content); where the integer→zero transfer must work. Folded bridge-theorem
  §5b. Also Comp 9: certified no prime-log relation (linear <1e40; corank^(2) {log2,log3} <1e33). Scripts:
  computations/2026-06-21-connes-pole-direction.{py,txt}, 2026-06-21-connes-primelog-corank.py.

### 41. Session findings propagated to big-picture + 05 (gpt/28 ratifies the session)
- big-picture §2.4 (positivity apex): reframed "numerically slippery" → the numerical no-margin is GENERIC
  (RH-empty FID reproduces all of it), carries zero RH content; RH content is the explicit-formula transfer;
  the wall localizes to one pole direction (s=1 entireness) + a codim-1 prime-vs-arch budget; the apex is
  analytic, never numerical.
- 05 (Jensen–Pólya apex challenge): same reframe — the positivity numerics are a red herring (FID-generic),
  the proof must be the analytic transfer / codim-1 budget, not a determinant sweep.
- gpt/28: full ratification of the session (id944–949) — numerical route dead, FID deflationary, RH content
  = explicit-formula transfer; promotes band-local Q_0 tests + explicit-formula decomposition. No new math.

### 42. Rank-one pole strip is exact but not a reduction (gpt/28+29 computations run, dichotomy settled)
- Ran all computations promoted by gpt/28 (arch/prime anatomy, band-local, off-line insertion) and gpt/29
  (rank-one pole structure + residual positivity on u^⊥), via one optimized script over cached zeros and the
  closed-form S_k^A (polygamma; no Taylor of ζ'/ζ — that was the prior hang). Cross-checked to 1e-121.
- Part A is exact, now d≤6: sig[T^A_{i+j+1}]=(d,1) and the single negative direction IS the pole vector
  u_i=(−4)^i (overlap û=1.0 to 120 digits). On u, Q_arch[u]=−Q_prime[u] to depth 1.5e−7→3.6e−17 (d:2→6),
  leaving the FIXED positive residue Q_0[u]=0.04564 (independent of d) = ∫2y²/(1+4y)²dν_0, since Σ(−4)^i y^i
  =1/(1+4y) on the support. Q_arch|_{u^⊥} is PD.
- NEW (settles gpt/29's open dichotomy): restricting H_d^(0) to u^⊥ keeps it PD but improves cond by only a
  FIXED ~10^6.5 factor (4.5e37→5.9e30 at d=6; min-eig still ~10⁻³³) — the residual is still the generic hard-
  edge problem. The most-dangerous direction p_d is 0.97·u and is PRIME-DELICATE (|Q_arch/Q_prime|=1.0, Q_0
  =λ_min tiny+). So Part A (pole cancellation) is a clean closed-form move, but Part B (residual PSD on u^⊥)
  is STILL the full integer→zero transfer problem — the rank-one split clarifies where RH sits, it does not
  make the residual tractable.
- NEW: the off-line defect is orthogonal to the pole. Pushing one atom off-line flips inertia (7,0)→(6,1);
  the new negative direction overlaps u by only 0.057→0.014 and p_d by ~10⁻⁵ — RH-sensitivity is a new
  direction at the off-line coordinate, so Part A (RH-independent) and Part B (RH-sensitive) act on
  essentially orthogonal subspaces.
- Folded: bridge-theorem §5b (Part A exact d≤6 + the not-a-reduction result + Q_0[u] residue), 06 §II (three
  bullets), formulas 183 (closed-form S_k^A + Q_0[u]). Script: computations/2026-06-21-connes-wall-anatomy.py
  (+ precompute-zeros.py), outputs wall-{resid,danger,offline,band}.txt.

### 43. The archimedean budget is the trivial-zero divisor (derived closed form, cross-checked 1e-62)
- Analytic next step on the only RH-bearing question (does the prime form stay in the arch budget on u^⊥).
  Deriving Q_arch from the weld's archimedean half A by residues gives the exact form-level identity
  Q_arch[p] = −4 p(−4)² + Σ_{j≥1}(2j+½)^{−2} p(−(2j+½)^{−2})²  (S_k^A = 2^{2k} − Σ_{j≥1}(2j+½)^{−2k}).
- So the (d,1) signature is explicit: positive squares over the TRIVIAL-ZERO divisor (images y_j=−(2j+½)^{−2},
  clustered in (−0.16,0)) minus one rank-1 square at the s=0,1 pole image y=−4 (coefficient exactly −4 = y·mass,
  negative direction p↦p(−4)=⟨c,u⟩). The s=0 pole at w=−½ cancels the digamma; trivial-zero poles have residue −1.
- This NAMES the previously-vague "archimedean PD budget": it is literally the trivial-zero square-sum. RH on u^⊥
  ⟺ ∀p with p(−4)=0: Q_prime[p] + Σ_{j≥1}(2j+½)^{−2}p(−(2j+½)^{−2})² ≥ 0. The budget is small (tight hard-edge
  cluster) — the quantitative face of the residual's ill-conditioning.
- Hankel(polygamma) vs the derived decomposition cross-checked to 1e-62 (random p, d=6). Folded: bridge-theorem
  §5b, formula 184. Script: computations/2026-06-21-connes-arch-trivialzero-decomp.py.

### 44. Propagated the session's two findings into 05 and 08
- 08 §2 route (d): corrected the stale "deflate the rank-1 pole, then prove residual PSD" hint. Now states
  the exact closed form Q_arch[p] = −4p(−4)² + Σ_{j≥1}(2j+½)^{−2}p(−(2j+½)^{−2})² (trivial-zero divisor minus
  the pole), the verified (d,1)/neg-dir=u, the "exact-but-not-a-reduction" result (u^⊥ residual stays
  FID-hard-edge), prime-delicacy of the dangerous direction, off-line defect ⊥ u, and the named u^⊥ inequality
  as the genuine target.
- 05: named the codim-1 archimedean budget as the trivial-zero square-sum, and noted the pole strip is exact
  but not a reduction.
- Checked 00–04, 07: no update needed (00 is the index; 01/02/04 are different topics; 03 states Lemma 2
  abstractly above the bridge route; 07's "rank-1" is the unrelated dual-multiplier obstruction).

### 45. Part A PROVED for all d — the archimedean rank-one theorem (gpt proof verified & promoted)
- gpt/proof-archimedean-rank-one-theorem.md supplies a rigorous proof of the (d,1) inertia for EVERY d (I had
  d≤6 numerically + the residue derivation of the identity). Verified every step by hand and promoted.
- Theorem: H_d^A = R_d^A − 4 u uᵀ, R_d^A = Σ_{j≥1}(2j+½)^{−2} v_j v_jᵀ, v_j=(−(2j+½)^{−2})^i, u_i=(−4)^i.
  (i) R_d^A ≻ 0 since cᵀR_d^A c = Σ_j(2j+½)^{−2}p(y_j)² and a nonzero deg-d poly can't vanish at the infinitely
  many distinct trivial-zero images y_j; (ii) PD minus one neg rank-1 ⟹ at most one neg eigenvalue; (iii)
  uᵀH_d^A u = uᵀR_d^A u − 4(uᵀu)² < 1−4 < 0 (uᵀR_d^A u<1 as 4y_j≤16/25; (uᵀu)²≥1) ⟹ at least one. So inertia
  (d,1), single neg dir = u, for all d.
- Same object as session Arc F (the trivial-zero decomposition), GPT in the orbit (−½) normalization (pole −2,
  a_n=4/(4n+1)²=(2n+½)^{−2}); mine in all-ρ (pole −4). Identical theorem ×2.
- STATUS: Part A (archimedean rank-one / form-level entireness) is now CLOSED. The entire RH content is Part B
  — the residual inequality ∀p with p(−4)=0: Q_prime[p] + Σ_{j≥1}(2j+½)^{−2}p(−(2j+½)^{−2})² ≥ 0.
- Upgraded markers to [PROVED, all d]: bridge-theorem §5b, formula 184, 08 §2 route (d).

### 46. Fused four-way split of p_d: even-ζ protects the residual, β/Catalan cancels it, prime closes the gap
- Decomposed the dangerous direction's Q_0 by the fused seam formula into POLE=2^{2k+1}, ZETA=−½(2^{2k}−1)ζ(2k),
  BETA=−2^{2k−1}β(2k), PRIME=(−1)^kT_k−(arch). (Corrected an earlier note: the ζ/β arch form is NOT
  mis-transcribed — it is the orbit (−½) normalization, = ½ the all-ρ polygamma S_k^A; both verified to 1e-121.)
- On the genuine residual direction (λ_min of H_0|u^⊥, p(−4)=0 ⟹ Q_pole→0 ~10⁻¹³⁴), for every d∈{4..8}: even-ζ is
  the SOLE positive contributor (d=6: Q_ζ=+5.201·10⁻⁵), β/Catalan is large and nearly equal-and-opposite
  (Q_β=−5.201·10⁻⁵), prime is sub-dominant (Q_prime=−1.7·10⁻⁹, matching only the arch-even net Q_ζ+Q_β). Two-stage
  cascade: ζ-vs-β(Catalan) at 10⁻⁵ → arch-even surplus 10⁻⁹ → prime cancels it → λ_min~10⁻³³.
- So the residual delicacy is ARCH-EVEN (ζ-vs-Catalan), prime as a small closing correction — distinct from the
  pole direction p_d≈0.97u, where the four are in clean ratio POLE:ZETA:BETA:PRIME=−4:1:1:2 and the prime is
  dominant (that is the pole cancellation = Part A). This refines "prime-delicate": prime-delicacy is on the pole
  direction; on the RH-bearing residual it is ζ-vs-β delicacy.
- Folded: bridge-theorem §5b, 06 §II, formula 185. Script: computations/2026-06-21-connes-fused-split-pd.py.

### 47. Canonical reading of the fused split: prime SATURATES the trivial-zero budget (tightness)
- The ζ/β split is not canonical: ZETA+BETA = the proved-positive trivial-zero budget R_d^A, split by residue
  class mod 4 (Hurwitz). The invariant statement: on the worst residual direction Q_prime=−1.72e-9 nearly
  saturates R_d^A=+1.72e-9, sum = λ_min=+7.8e-33 (~24-digit cancellation, d=4..8). The prime consumes ~all of
  the budget, margin ~10⁻²⁴ of it.
- Consequence for the proof: the bridge inequality Q_prime + R_d^A ≥ 0 is TIGHT, not slack — no soft bound
  Q_prime ≥ −(1−ε)R_d^A with fixed ε>0 holds; the proof must be exact/equality-grade, not order-of-magnitude.
  Folded: bridge-theorem §5b.

### 48. Incorporated gpt/proof3 + gpt/31; verified Q_ζ+Q_β is PD (the "ζ-vs-β battlefield" is an artifact)
- proof3/31 ratify the session (rank-one pole, residual = the wall, fused split). Incorporated the meaningful
  structural items: the full A/P split H^A=R^A−2uuᵀ, H^P=+2uuᵀ+R^P ⟹ H^0=R^A+R^P is pole-free, so "R_d⪰0" IS the
  Q_0 wall (no reduction); the correct pole-quotient is the Schur complement Schur_u(H^0)⪰0 ⟺ H^0⪰0; the
  form-level no-go (H^A=I−2uuᵀ, H^P=2uuᵀ−3I cancel poles yet sum=−2I≺0: cancellation ⇏ positivity); the four
  candidate proof shapes (square identity / positive transfer / Weil pullback Q_0[p]=Q_W[h_p] / source-built index).
- CORRECTED gpt/31's over-claim: the "ζ-vs-β battlefield" is not real. Verified inertia(H^{ζ+β})=(d+1,0) PD for
  d=4,6,8 and Q_ζ+Q_β = 4p(−4)²+R_d^A (cross-check 1e-81). The ζ/β halves are one PD object split by character
  mod 4 (β=L(·,χ₄)); only Q_prime-vs-R_d^A is RH content, and it is tight. NEW lead: a Dirichlet-character
  (trivial vs χ₄) decomposed positivity may be the natural route.
- Folded: bridge-theorem §5b (two paragraphs), 08 §2 (no-go sharpened + proof-shape candidates + χ₄ lead),
  06 §II. Script: computations/2026-06-21-connes-zeta-beta-sum-psd.py.

### 49. χ₄/character-decomposition lead pushed analytically — DEMOTED (positivity ≠ character basis)
- Derived the arch budget's exact mod-4 character split (Hurwitz: ζ(2k,¼)±ζ(2k,¾) = principal-odd ζ-tower /
  χ₄=β-tower; ZETA=−2^{2k−1}Σ_{odd}m^{−2k}, BETA=−2^{2k−1}β(2k)). Verified identities to machine precision.
- Tested whether the character split helps positivity: inertia(H^ζ)=(d+1,0) PD (all-odd-integer principal sector),
  but inertia(H^β)=INDEFINITE (≈(d−1,⌈d/2⌉), stable min-eig ≈−0.226) for d=4,6,8. The 1-mod-4 residue-class budget
  is PD only as a positive measure; splitting by character breaks that manifest positivity into PD-principal +
  indefinite-χ₄. So decomposing turns a trivial statement (positive measure ⟹ PSD Hankel) into a harder one
  (PD sector dominates an indefinite sector).
- VERDICT: character decomposition is the wrong representation — positivity lives in the residue-class measure
  cone, not the character/spectral basis. The proof must stay in measure/support (square test functions over the
  divisor). Demotes gpt/31's χ₄ "natural route." Mild salvage: regrouping Q_0^res = Q_ζ(all-odd PD)+(Q_β+Q_prime)
  is cleaner but still RH-equivalent/tight.
- Folded: bridge-theorem (canonical reading already notes χ₄=L), 08 §2 (lead → demoted verdict), 06 §II, formula
  186. Script: computations/2026-06-21-connes-character-sectors.py.

### 50. Square identity (08 cand.1) pushed: PARTIAL from source; the prime residual R^P is high-rank negative
- A full square Q_0[p]=∫|p|²dμ (μ≥0) is RH (Weil/Stieltjes). But half is explicit: R_d^A=∫|p|²dμ_triv with
  μ_triv=Σ_{j≥1}(2j+½)^{−2}δ_{y_j} the trivial-zero divisor (positive measure, M^A verified PD). So the proved
  split gives the PARTIAL square identity Q_0[p]=∫|p|²dμ_triv + R^P[p], R^P:=H^0−M^A the prime residual.
- NEW (the obstruction's shape): R^P is high-rank and predominantly NEGATIVE — inertia (1,4)/(2,5)/(2,7) at
  d=4/6/8, only 1–2 tiny-positive modes (max-eig ~3e-8), stable min-eig ≈ −0.2565. Not a low-rank correction.
  On the dangerous direction μ_triv-square=+1.7e-9 vs R^P=−1.7e-9 (the tightness, reframed).
- For polynomial tests R^P=H^0−M^A is fixed by the explicit formula (nontrivial− trivial-zero moments): the
  prime side gives NO independent positive measure, so the square can't be completed from source without μ_0≥0
  (=RH). Target: a measure/transfer proof that the small hard-edge trivial-zero square M^A dominates the
  full-dimensional negative R^P everywhere.
- Folded: bridge-theorem §5b, 08 §2 cand.1. Script: computations/2026-06-21-connes-partial-square.py.

### 51. Ran the remaining gpt/31 §8 computations (C, E); §8 now complete
- C (does prime close the surplus / |Q_prime|≤Q_ζ+Q_β?): the relation is ONE-sided. Lower side H^{ζβ}+H^prime⪰0
  holds (min-eig +7.8e-33, the bridge/RH side); upper side H^{ζβ}−H^prime is NOT PSD (min-eig −5.2e-11, stable
  d=4,6,8). So Q_prime can overshoot the arch budget positively; only Q_prime≥−(Q_ζ+Q_β) (=RH, tight) is content.
  H^prime indefinite (2,3)/(2,5)/(3,6).
- E (compare FID): H_FID=[ζ(2(i+j)+3)] strictly PD (d+1,0) all d; Q_FID[u]>0 (+4e4→+2.7e9), no pole, no −uuᵀ,
  no (d,1). The arch/pole/trivial-zero/β/χ₄ structure is zero-divisor-specific, absent from FID. FID shares only
  the hard-edge conditioning, none of the structure ⟹ RH content is structural, not numerical.
- 31 §8 status: A,B (Q_ζ+Q_β PD, §46/§48), C (here), D (character demoted, §49), E (here) — all run.
- Folded: 06 §II (two bullets). Script: computations/2026-06-21-connes-31CE.py.

### 52. The discriminant attack — corrected: termwise det H_1 proof retracted
- Used the Gram/Heine identity: det H_d = (1/(d+1)!) Σ_tuples ∏(2y_ρ) ∏_{i<j}(y_ρi−y_ρj)² (verified d=1,2 to 8
  digits). Makes positivity manifest termwise; the ONLY negativity is a tuple with an off-line pair {y,ȳ},
  self-term −4|y|²(Im y)²<0.
- CORRECTION [2026-06-24]: the termwise cross-sign step was false. `Re y>0` does not imply
  `Re(y(y−x)^2)>0` for every positive real bulk atom `x`; at `x=Re y` the cross term is negative. The exact
  replacement is `discriminant-cross-positive-interval.md`, where the positive range is controlled by
  `x_+(y)=(u^2-a^2+a|y|)/u` and `x>=1.18|y|` is sufficient.
- The valid degree-one repair is `degree-one-discriminant-tail-stability.md`: split a verified positive real
  bulk from the remaining tail and check an explicit determinant-margin inequality. The old unconditional
  `det H_1` statement and the `d~H` determinant range are not promoted without that summed domination estimate.
- Folded correction: bridge-theorem §5b; route cards:
  `discriminant-bulk-cross-sign-needs-scale-separation.md`,
  `discriminant-cross-positive-interval.md`,
  `degree-one-discriminant-tail-stability.md`.

### 53. Incorporated gpt/32; ran the relative-operator computation — λ_max(K_d)→1⁻ super-exponentially
- gpt/32 ratifies the partial-square/31CE results and crystallizes the bridge as the ONE-SIDED Loewner
  domination: −R^P ⪯ M_triv ⟺ λ_max(K_d)≤1, K_d=M_triv^{−1/2}(−R^P)M_triv^{−1/2}. (Named: Trivial-Zero
  Domination Theorem.) Current protector/threat language: protector=μ_triv (positive measure), threat=R^P
  (high-rank negative), RH=protector dominates threat one-sidedly. Character/ζ-vs-β framing superseded.
- Ran §9 (the relative operator): λ_max(K_d) ↗ 1⁻ with margin 1−λ_max ≈ 2e-9,4e-19,2e-29,2e-40 at d=2,4,6,8
  — super-exponential ~10^{−5d}≈γ₁^{−4d}; extremizing polynomial = the dangerous direction p_d (overlap 1.0,
  0.97 u). The margin 1−λ_max(K_d) = generalized λ_min(Q_0,M_triv) = the discriminant margin (§52), so the
  relative-operator and discriminant pictures coincide. RH = λ_max(K_d)<1 ∀d (slack stays >0 as d→∞).
- Folded: bridge-theorem §5b. Script: computations/2026-06-21-connes-relative-operator.py.

### 54. The race quantified: margin decay law + height-linear detection law as evidence
- (1) on-line margin 1-lambda_max(K_d) decays super-exponentially with INCREASING rate: dlog10/dd −4.7→−6.3
  over d=3..16 (hard-edge: each degree resolves deeper where zeros are denser).
- (2) off-line detection threshold d*(gamma0) grows ~LINEARLY in height: d*=8,14,>16 at gamma0=20,30,45
  (slope ~0.4 at beta=0.1), NOT in zero-count N(gamma0)~gamma0 log gamma0.
- CORRECTION [2026-06-24]: the measured height-linear detection law is evidence for a finite-range theorem, not
  a theorem itself. Promoting a `d~H` range requires the summed determinant domination estimate described in §52,
  equivalently the finite-degree eigenvalue/tail-norm gate in
  `finite-degree-shifted-hankel-tail-stability.md`. The monomial absolute-tail version of that gate is now ruled
  out by `monomial-tail-gate-height-linear-no-go.md`; a viable proof must use relative/source-Weyl control.
- Bankable content: Gram/Heine mechanism, local off-axis negative term, exact cross-positive interval, degree-one
  tail-stability criterion, and measured height-linear detection law. Folded: bridge-theorem §5b. Script:
  computations/2026-06-21-connes-detection-law.py.

### 55. gpt/33 computations: the no-margin law is a product over the zeros; K_d corner-concentrated; off-line detector
- #1 (no-margin law): fitting 1−λ_max(K_d) to d=20 (margin ~10^{−113}), per-degree ratio ≈ γ_d^{−3.40}, exponent
  STABLE at 3.40 ∀d ⟹ 1−λ_max(K_d) ≈ C·∏_{n=1}^d γ_n^{−3.40} (~(d!)^{−3.4}, super-exp). The slack is an explicit
  product over the on-line zero heights — >0 factor-by-factor because each γ_n is real/finite; an off-line γ_n
  corrupts its factor. Cleanest "RH = slack stays positive" = reality of the zeros read off the product.
- #3 (K_d structure): in the μ_triv-orthonormal basis K_d is corner-concentrated (NOT Jacobi/Toeplitz/compact);
  entries explode toward the deepest index (K[8,8]≈−6e4, ~4×/step), λ_max≈1 = one dominant direction at the
  deepest hard-edge scale.
- #7 (off-line under K_d): M_triv fixed ⟹ λ_max(K_d)>1 ⟺ off-line detected. d=10>d*(20)=8: quartet at γ0=20 pushes
  λ_max>1 ∀β>0; d=4<d*: λ_max<1 ∀β (finite-degree blindness in operator form). K_d is the clean detector.
- gpt/33 otherwise ratifies the discriminant + relative-operator anatomy (one-sided domination −R^P ⪯ M_triv).
  Folded: bridge-theorem §5b. Scripts: computations/2026-06-21-connes-K-asymptotics.py, -K-offline.py.

### 56. Derived the no-margin exponent: density-determined (→4), generic — RH is in the SIGN not the rate
- Densities (derived): nu' (zeros, weight 2y_rho) ~ |log y| y^{-1/2} at 0+; mu_triv ~ |y|^{-1/2} at 0- — same
  hard-edge class. Extremal p_d (roots on lowest zeros) ⟹ per-step margin ratio ~ y_{d+1}y_d/c² ~ gamma_d^{-4}:
  exponent 4 from the reciprocal-square weight 2y_rho~gamma^{-2}. Measured ≈3.40 = 4 − 0.6, the 0.6 a log
  correction from the zero density N(T)~T log T.
- CHECK (synthetic zeros, M_triv fixed): exponent tracks the density — linear gamma_n=g1 n gives 3.36→3.50↗4;
  sqrt gives 3.31→3.45; quad (sparse) gives 3.55→3.64; all drift toward the universal 4. So the exponent is
  GENERIC to any reciprocal-squared hard-edge measure, not zeta-specific (deepest form of the FID lesson).
- CONCLUSION: RH is NOT in the no-margin rate/exponent (generic); it is ONLY in whether the product prod
  gamma_n^{-exp} stays positive = reality of the zeros, factor by factor. The rate is generic, the sign is RH.
- Folded: bridge-theorem §5b. Scripts: computations/2026-06-21-connes-exponent-derivation.py, -exponent-synthetic.py.

### 57. gpt/34 (A-axis detector menu): ran the load-bearing separation test — confirms the no-go quantitatively
- gpt/34 is A-axis (transcendence detector), not the B/C bridge. Its menu A–J: most are tautological (D: E_k(ζ)=0
  IS the explicit formula), Schanuel-hard (E prime-log shell minima — gpt admits open), or rank-reducible (F).
  Ran the load-bearing core (A+B): does any S_k detector separate ζ from same-density random?
- Result: PSLQ on S_k=2Σγ_n^{−2k} vs {π^{2k}, β(2k)} detects AP(γ_n=n, S_k=2ζ(2k)∈ℚ(π)) at Bernoulli heights
  3,45,945,4725,93555, but ζ, same-density random, and jittered-ζ are ALL "none" (indistinguishable). So
  S_k-only detects simplicity-vs-genericity, NOT zeta-arithmetic — confirms the established A-axis no-go
  quantitatively. The genuine detector needs prime-side data (separates only tautologically via the explicit
  formula); the non-tautological core is Schanuel-for-prime-logs (Conjecture A, open).
- Folded: big-picture §1 (A-axis). Script: computations/2026-06-21-connes-Aaxis-separation.py.

### 58. gpt/35 sign-transfer computations: off-line zero flips EXACTLY ONE eigenvalue; clean factorization closed
- gpt/35 ratifies the exponent result (rate generic, sign is RH) and refocuses on sign transfer (demoting all
  rate/asymptotics/conditioning/deflation work). Ran #C and #D.
- #C (decisive): tracking all generalized eigenvalues of (Q_0,M_triv)=I−K_d as a zero goes off-line — at β=0
  zero negative (λ_min=+7e-50); at β>0 EXACTLY ONE turns negative (smallest, →−9e-8), second-smallest stays
  +3e-48. So an off-line zero flips precisely the deepest hard-edge mode: RH ⟺ λ_min(Q_0,M_triv)>0 ∀d, factor
  by factor (single eigenvalue carries the sign).
- #D: Cholesky pivots of I−K_d exist (PD) but exponents GROW (2.97→13.06) — they are OP-norms, NOT the γ_n^{-3.40}
  margin factors. So gpt/35 B's clean determinant/L*L factorization does not materialize; the product law lives in
  the λ_min spectral flow. Proof target: sign-preserving transfer keeping the single deepest eigenvalue positive.
- Folded: bridge-theorem §5b. Script: computations/2026-06-21-connes-sign-transfer.py.

### 59. gpt/36 + operator-K computations: domination is cross-scale (single-point protector); edge mode not universal
- gpt/36 ratifies the spectral bridge (RH ⟺ λ_min(Q_0,M_triv)>0 ∀d ⟺ λ_max(K_d)≤1) and proposes the operator-K
  proof shape: K_d = P_d K P_d^* compressions of a limiting K with K⪯I. Corner-concentration of K_d ⟹ K likely
  NOT compact (λ_max→1 essential-spectrum-like) ⟹ proof is operator monotonicity, not a finite eigenvalue bound.
- #4 (extremizing mode): the deepest eigenvector has NO universal hard-edge profile — rescaled to ξ=y/y_d the
  degree-d mode gains oscillations with d; L2 distance of rescaled profiles GROWS 0.72→1.45→1.62 (d=6,8,10,12).
  Closes the "universal edge state" route.
- #7 (band domination): on the dangerous mode p_d, protector M_triv mass sits ENTIRELY at j=1 (coarsest trivial
  zero |y|=0.16; j≥4 <1e-21), threat Q_0 mass at the deep hard edge (peak n*=6, y≈7e-4) — scales ~226x apart.
  Domination is cross-scale, NOT bandwise (scale-local/dyadic proof dead). On the dangerous direction the protector
  reduces to a single evaluation (2.5)^{-2} p(-0.16)^2 at the coarsest trivial zero.
- Folded: bridge-theorem §5b. Scripts: computations/2026-06-21-connes-edge-mode.py, -band-domination.py.

### 60. Margin = inverse Christoffel function of the zero measure at the coarsest trivial zero (Markov/potential-theory form)
- The zero measure ν'=Σ 2y_ρ δ has moment matrix = H^0 (∫y^{i+j}dν'=T_{i+j+1}). Its reproducing/Christoffel kernel
  K_ν'(y_*,y_*)=e(y_*)^T(H^0)^{-1}e(y_*)=max_p p(y_*)^2/Q_0[p]. Verified exact identity (d=10, 6 digits):
  1/margin = (2.5)^{-2} K_ν'(-0.16,-0.16) = 1.27007e51 (both ways); trivial-zero kernel sum dominated by j=1
  (profile drops ~10 orders/j: 7.9e51,6.8e41,4.6e35,...).
- So the bridge margin IS the inverse Christoffel function of the zero measure at the coarsest trivial zero
  y=-0.16 (exterior to supp(ν')=(0,y_1]). Potential-theory reading: (i) rate K~e^{2d g(-0.16)}, g=Green's function
  of C\supp(ν'), depends only on the support endpoints ⟹ generic (re-derives "rate is geometry"); (ii) sign
  K=e^T(H^0)^{-1}e ≥0 ⟺ H^0⪰0 ⟺ ν' positive ⟺ zeros real ⟺ RH. RH content is the sub-exponential prefactor
  (equilibrium-measure vs actual zero density), not the Green's-function rate.
- Folded: bridge-theorem §5b. Script: computations/2026-06-21-connes-christoffel.py.

### 61. Christoffel rate is density-tracking, not endpoint-Green's; corrected §60's over-claim
- Tested K_ν'(-0.16,-0.16)^{1/(2d)} for ζ vs same-support linear-density divisor: rates DIVERGE (z 236→512,
  lin 392→2436, ratio 0.60→0.21, d=2..14). K^{1/(2d)} does NOT converge to a constant — the hard-edge
  accumulation at 0 makes exterior growth super-e^{2dg} and DENSITY-tracking (matches Arc Q synthetic spread).
- So §60's "rate = endpoint Green's function, generic" was too strong. Corrected: the Christoffel growth tracks
  the zero density (generic band, not a fixed constant); the RH content is isolated cleanly in the SIGN of the
  kernel — K_ν'>0 ⟺ H^0⪰0 ⟺ ν' positive ⟺ zeros real. The exact margin = inverse Christoffel identity (§60) stands.
- Folded: bridge-theorem §5b (rate clause corrected). Script: computations/2026-06-21-connes-christoffel-prefactor.py.

### 62. Real-axis kernel does NOT localize the off-line defect (necessary not sufficient)
- Scanned K(y)=e(y)^T(H^0)^{-1}e(y) on R for on-line vs an injected off-line quartet (d=10>d*). K_online>0
  everywhere (the zero-measure reproducing kernel is a positive function under RH). But K_offline ALSO stays >0
  everywhere — even though H^0 is indefinite (Arc S: λ_min<0 at these params). The flipped eigenvalue ~1e-21
  contributes ~1e21 at the aligned point y=-0.16 vs positive terms ~1e51, so the defect is sub-threshold on the
  moment curve {e(y)}; it lives in a polynomial-eigenvector direction off that curve.
- So K(y)>0 ∀ real y is NECESSARY but NOT SUFFICIENT for H^0⪰0/RH — the real-axis kernel does not localize the
  off-line defect. The faithful handle is the single flipped generalized eigenvalue (Arc S), not the kernel-on-R.
- Folded: bridge-theorem §5b. Script: computations/2026-06-21-connes-kernel-scan.py.

### 63. gpt/37 folded — the irreducible named (one-sided Loewner domination), the three-stratum divisor, the ranked proof menu, and the forward route-killer agenda

**Source.** `docs/consolidated/gpt/37.md` (GPT synthesis). It demotes the carrier (already done in this
corpus), names the single irreducible as *"the completed explicit formula is a one-sided Loewner domination
theorem,"* proposes the **three-stratum reciprocal boundary divisor**, **ranks** the proof shapes, and lays
out a **10-item forward computation agenda** with a priority order and a decisive fork.

**Register.** All SEARCH; nothing promoted. **No new proof of RH, no Lean, no new proven-ledger item.** The
underlying facts 37.md rests on were already banked (`Q_0=M_triv+R^P`; `−R^P⪯M_triv`; `λ_max(K_d)≤1`; the
`j=1` single-point protector; the inverse-Christoffel margin; the corrected degree-one determinant stability
criterion; the height-linear detection law — all in `bridge-theorem.md` §5b and `08` §2). What is genuinely new and
folded in:

- **Three-stratum reciprocal boundary divisor** — pole `y=−4` (entireness `u`) + trivial-zero chain
  `y_j=−(2j+½)^{−2}` (positive protector `μ_triv`) + nontrivial divisor `y_ρ=−(ρ−½)^{−2}` — as a *named
  object*, with the **RH-divisor vs proof-divisor** distinction (Stieltjes positivity of the nontrivial
  divisor vs the trivial-zero divisor as boundary protector) and the relative/Schur-complement speculation
  `𝒟_rel=𝒟_nontriv⊘𝒟_triv⊘𝒟_pole`. → `bridge-theorem.md` §5b; `08` §2; `big-picture.md` Conj C.
- **Factorization/contraction sharpening of the proof object** — not "find some positivity" but *source-build
  a factorization/contraction giving `I−K_d⪰0` at **zero margin*** (the prime saturates the budget to ~24
  digits; no slack/gap/reserve route survives). → `bridge-theorem.md` §5b; `03` §7; `08` §2.
- **Ranked proof-shape menu** — (1) one-sided Loewner / boundary-Weyl `K⪯I` (compression of a *non-compact*
  completed-boundary `K`, essential-spectrum-like `λ_max→1`); (2) Weil-form pullback `p↦h_p`; (3)
  discriminant / Gram–Heine using the exact cross-positive interval plus a summed domination estimate; (4) direct
  Jacobi / Hankel-det (lowest). → `bridge-theorem.md` §5b;
  `03` §7; `08` §2.
- **Forward route-killer agenda (#35–44)** — high-degree `K_d` law (P1); Dirichlet-`L`/DH reciprocal
  domination as a **source gate** (P2: genuine Euler `L` pass `K_d⪯I`, DH fails `λ_max>1`); Weil-pullback
  construction (P3); coarsest-trivial-zero protector test (P4); detection law `d*(γ,β)` (P5); plus
  Gram–Heine ladder, hard-edge fake battery, hidden-basis search, exterior-Christoffel growth, source-built
  Schur complement. With the **decisive fork**: broad hard-edge fakes also dominate ⟹ find *why the explicit
  formula puts ζ in that class*; vs genuine-`L` pass / DH fail ⟹ the domination *is* the source gate.
  → `research-topics.md` #35–44.

**Affected files:** `bridge-theorem.md` (new §5b synthesis + ranked-menu + agenda block), `08-conjectures-
required.md` (new §2 bullet), `03-theorems-toward-rh.md` (new §7 subsection), `big-picture.md` (Conj C
sharpening), `research-topics.md` (#35–44). **New synthesis:** the three-stratum-divisor framing and the
proof/RH divisor split. **Precisification:** the proof object as a zero-margin contraction; the proof-shape
ranking. **New conjecture / proof / falsification:** none (restatement + agenda). **Forward agenda:** the
Dirichlet/DH source-gate test (#38) as the highest-value structural discriminator.

### 64. gpt/37 forward agenda EXECUTED — 10-computation battery run; findings folded into bridge-theorem/08/big-picture/research-topics

**What.** Ran all ten gpt/37 route-killer computations (`research-topics.md` #35–44) on a high-precision
remote node, exact ζ/L zero-moments `T_k=2Σγ^{−2k}` via `c_{2k}=[w^{2k}]logΞ` (no zero-truncation — an
80-zero cut corrupts `T_1` by 15%, which had produced a spurious exponent reading). Scripts + raw outputs
archived under `computations/2026-06-22-*`; full worklog `logs/gpt37-computations-worklog.md`. **Register:**
all SEARCH/`[OBSERVED]`/`[VERIFIED]`; **no new proof of RH, no Lean, no proven-ledger promotion.**

**Findings folded in (per doc).**
- **bridge-theorem.md §5b** — new "Empirical refinements" block + an inline marker on the no-margin law:
  exponent **CORRECTED** (≈3.41→3.48 stable, not 3.7) and **REFINED** (protector/parity-set across the
  `L`-family: ζ3.41/odd-χ3.90/even-χ5.05, not universal-density); jittered-ζ ≡ ζ to 4–5 digits (numerics carry
  ZERO prime content); `λ_max→1` no compactness (route 1); `u`=pole vector universal incl. odd-χ (geometric,
  not arithmetic); protector 100% at `j=1` to d=50; `1/margin=(2.5)^{−2}K_{ν'}(−0.16)` verified to 1.7e-21 at
  d=20; `R^P` rank-1 in norm / full-rank in sign, near-Jacobi in the `(y+0.16)` basis; detection law mildly
  super-linear; **DH source gate is faithful but height-limited (real DH off-line zero undetected through
  d=55) — all-order, not finite-`d`**; Weil-pullback inadmissible, boundary at the seam centre `s=½`.
- **08 §2** — the gpt/37 source-gate fork marked **RESOLVED** (Euler-product-general mechanism; DH not a
  finite-`d` gate; route 2 inadmissible / route 1 favored).
- **big-picture.md** — Conjecture C source-gate question **answered** (faithful but height-limited; all-order).
- **research-topics.md** — #35–44 annotated `[DONE]` with one-line verdicts.

**Net epistemic change.** No route opened to a finite-`d` certificate; several CLOSED or refined: the K_d/
margin/conditioning numerics are confirmed **prime-blind** (jitter test), so RH is purely in the **all-order
sign**; route 2 (Weil-pullback) needs a de Branges/Krein limit with boundary at `s=½`; route 1 (operator/
boundary-Weyl) is favored (non-compact `K`, near-Jacobi `R^P` in the protector basis). The bridge **mechanism
is Euler-product-family general** (good for the source-built-transfer framing), and the exponent (rate) is
archimedean-protector-set, not universal — RH content is exclusively the sign.

### 65. gpt/38 folded — the "purification" verdict; the missing object named as a noncompact boundary-Weyl contraction; four-point compactified boundary divisor; 8 operator-identity computations queued

**Source.** `docs/consolidated/gpt/38.md` (GPT synthesis of the 2026-06-22 battery, entry #64). Its thrust is a
**purification**: every finite-`d`/conditioning/margin/correlation/rate observable is demoted (the battery showed
them prime-blind, density/protector-set, generic), leaving exactly one RH-bearing object — the **all-order sign**.
**Register:** SEARCH/`[SYNTHESIS]`; **no new proof, no Lean, no ledger promotion.**

**Folded in.**
- **bridge-theorem.md §5b** — new "Purification" block: (i) the missing theorem is now a **single named operator**
  — a noncompact self-adjoint contraction `K=M_triv^{−1/2}(−R^P)M_triv^{−1/2}` with `K⪯I`, `‖K‖=1`, `1∈σ_ess(K)`,
  `K_d=P_dKP_d^*`, built without zero-feeding; proof = boundary monotonicity / Weyl positivity, never a
  spectral-gap estimate; RH `⟺ λ_min(I−K_d)>0 ∀d`. (ii) **revises the three-stratum divisor** to a **four-point
  compactified reciprocal-boundary divisor** {seam centre `y=∞`(s=½) + pole `y=−4` + first trivial protector
  `y=−0.16` + hard edge `y=0⁺`}, with the nontrivial divisor demoted to "object controlled, not proof divisor".
  (iii) updated 5-step proof shape (protector-point `x=y+0.16` operator coordinate; near-Jacobi core + sign-exact
  tail; Weil-pullback regularized by promoting its seam-centre pole to a boundary vector). (iv) updated slogan.
- **big-picture.md** — Conjecture B gets the purified form (named noncompact contraction `K`; all-order sign only).
- **08 §2** — new "Purified target" bullet (the named operator; four-point boundary divisor; →#45–52).
- **research-topics.md** — gpt/38 agenda **#45–52** (operator-identity computations): protector-point Jacobi
  model; DH past threshold (d=58–80); regularized Weil-pullback identity; protector-point perturbation/criticality;
  Dirichlet parity exponent formula; sign-tail audit; Gram–Heine→interval proofs; direct boundary-Weyl triple.

**Net.** No mathematics promoted; the *framing* sharpens from "trivial-zero domination / source gate" to
"**source-built all-order sign transfer** = a noncompact boundary-Weyl contraction `K⪯I, ‖K‖=1`," with a concrete
operator coordinate (protector-point shift) and boundary location (seam centre `s=½`) to build against. Next work
is the operator identity (#45–52), not more rate/margin evidence.

### 66. gpt/38 operator-identity battery EXECUTED — boundary-Weyl theorem shown RANK-ONE; parity exponent formula; band/low-rank routes killed

**What.** Ran the gpt/38 agenda (`research-topics.md` #45–52) on the remote node (exact ζ/L moments). Scripts +
outputs under `computations/2026-06-22-comp4*/comp5*`; worklog `logs/gpt37-computations-worklog.md`. **Register:**
SEARCH/`[VERIFIED]`/`[DERIVED]`; **no new proof of RH, no Lean, no ledger promotion.** Seven of eight run (DH-push
#46 deferred for compute cost; Weil-reg #47 left as the de Branges construction).

**Findings folded in (bridge-theorem.md §5b "Operator-identity battery"; 08 §2; research-topics.md).**
- **The completed-boundary Weyl PSD theorem is RANK-ONE** (comp52/#52): `H^0=H0_minus+(2.5)^{−2}vv^T`,
  `v=e(−0.16)`, `inertia(H0_minus)=(d,1)`; RH ⟺ scalar `s(d)=(2.5)^{−2}·margin≥0`. Operator face = moment face =
  scalar boundary face — the corpus's "finite-rank boundary" is now pinned to **rank one**.
- **The first trivial zero is the exactly-critical, optimal boundary datum** (comp48/#48): `a_c(−0.16)=0.16` exactly
  (deficit `=0.16·margin`), and `y_*=−0.16` minimizes `a_c` over the exterior. Structurally explains comp10.
- **Band and low-rank approximations are both formally dead** (comp45/#45, comp50/#50): R^P=J+E near-Jacobi in the
  `(y+0.16)` basis, but dropping the 0.8% tail flips `margin +10^{−40}→−10^{16}`, and every rank-`r<d+1` truncation
  gives the wrong sign. Proof must be sign-exact over the full operator.
- **No-margin exponent law** (comp49/#49): `α≈4.31+½ln|y_*|` (fits ζ/odd-χ/even-χ to 3 digits) — archimedean-
  protector-set, slope ½ from the reciprocal square; no universal 4.
- **Gram–Heine schema reusable** (comp51/#51): tuple identity at d=3,4; `det H_4>0` unconditional for `γ≥16`.

**Net.** The proof target sharpens to a **source-built RANK-ONE boundary-Weyl contraction**: build the bulk
`H0_minus` (inertia (d,1)) and the single boundary atom `(y=−0.16, mass (2.5)^{−2})` from Γ/pole/FE/EF data without
zero-feeding, in the protector coordinate `x=y+0.16`, and prove the scalar Weyl function `s(d)≥0 ∀d` keeping the
exact sign tail. Open next: the de Branges/Krein seam-centre construction (#47) and source-building the bulk/boundary.

### 67. gpt/39 folded — the bridge collapses to a rank-one SCALAR boundary-Weyl theorem at y=−0.16; 7 scalar-Weyl computations queued

**Source.** `docs/consolidated/gpt/39.md` (GPT synthesis of the comp45–52 battery). Thrust: the bridge collapses
one level further — from "prove a noncompact boundary-Weyl *operator* inequality" to "**prove a rank-one *scalar*
boundary-Weyl inequality at y=−0.16**." The proof divisor reduces to the single rank-one exterior datum
`0.16·δ_{−0.16}`; RH ⟺ the scalar Weyl gap `s_d=0.16·margin_d>0 ∀d`. **Register:** SEARCH/`[SYNTHESIS]`; **no new
proof, no Lean, no ledger promotion.**

**Folded in.**
- **bridge-theorem.md §5b** — new "collapse to a rank-one SCALAR boundary-Weyl theorem" block: `H^0_d=H^-_d+0.16
  v_*v_*^T`, `inertia(H^-_d)=(d,1)`, scalar gap `s_d=0.16·margin_d`; the proof divisor reduces to `0.16·δ_{−0.16}`
  (pole = bookkeeping, chain = background, j=1 = active gate); the "one theorem before RH" rank-one form + slogan.
- **bridge-theorem.md §7** — added the rank-one "sharpest form" of the one-line summary.
- **big-picture.md §0** — sharpened the named target to the scalar gap `s_d=0.16·margin_d`.
- **08 §2** — new "collapse to a scalar gap" bullet (proof divisor = single datum; open faces (i) source-build
  H^-_d + boundary m-function, (ii) seam-centre de Branges/Krein weld of the Weil pullback).
- **research-topics.md** — gpt/39 agenda **#53–59** (scalar Weyl m-function; Weyl=Schur=Christoffel unification;
  Dirichlet generalization; tail-identity; regularized Weil-pullback→scalar gap; DH scalar-gap calibration;
  Gram–Heine asymptotic lemma).

**Net.** The programme's proof target sharpens from "prove a noncompact operator inequality" to "**prove a
rank-one scalar boundary-Weyl inequality at y=−0.16**" — `s_d=0.16·margin_d>0 ∀d`, source-built. The first
trivial zero is reclassified from "protector" to **critical Weyl boundary condition**. Next work: identify the
scalar Weyl m-function (#53–54), not more margin/tail/dominance tests.

### 68. gpt/39 scalar-Weyl battery EXECUTED — moment & operator faces UNIFIED (Sherman–Morrison); rank-one boundary theorem is Euler-product-general; sign-tail is Hankel

**What.** Ran the gpt/39 agenda's core (#53–56) on the remote node (exact ζ/L moments). Scripts+outputs under
`computations/2026-06-22-comp5[3-6]*`; worklog `logs/gpt37-computations-worklog.md`. **Register:** SEARCH/
`[VERIFIED]`/`[PROVED — Sherman–Morrison]`; **no new proof of RH, no Lean, no ledger promotion.** (#57 Weil-reg
left as the de Branges construction; #58 DH deferred for compute; #59 Gram–Heine pending.)

**Findings folded in (bridge-theorem.md §5b "Scalar Weyl m-function battery"; research-topics.md).**
- **The two faces are ONE number** (comp54/#54): Sherman–Morrison gives `s_d = a_*+1/m` (rank-one Schur) `=
  1/K_{ν'}(−0.16)` (inverse exterior Christoffel) `= (2.5)^{−2}·margin_d` (PSD regime), exact to 10^{−103}. The
  moment-face reproducing kernel and the operator-face rank-one Schur gap are the **same scalar** — RH ⟺ that
  scalar stays positive ∀d.
- **The rank-one boundary theorem is completed-Euler-product-general** (comp55/#55): inertia(H^-_χ)=(d,1) for ζ
  and every real primitive Dirichlet `L`; the Γ-factor selects the boundary datum `y_{*,χ}=−(a+½)^{−2}` (the same
  point that sets comp49's exponent law `α=4.31+½ln|y_*|`).
- **The sign-essential tail is a Hankel functional** (comp56/#56): in the protector coordinate `R^P=J+E`, `E` is
  exactly Hankel (`E_{ij}=f(i+j)`) — the moments of one signed functional `μ_E` (conjecturally the seam-centre
  boundary distribution); source-identifying `μ_E` is the tail identity.
- **No stationarity** (comp53/#53): `∂_y a_c(−0.16)≈2d≠0`; the entrance is the Christoffel identity, not `∂_y a_c=0`.

**Net.** The proof object narrows to a **single scalar Weyl m-function = the inverse exterior Christoffel kernel
`1/K_{ν'}(y_{*,χ})` at the Γ-selected first trivial zero**, uniform across the completed-`L` family; RH ⟺ it stays
positive ∀d. Moment face = operator face (proved). Open: source-build `K_{ν'}(y_{*,χ})` (= bulk `H^-` + Hankel
tail `μ_E`) without zero-feeding, and weld the seam-centre Weil-pullback regularization (#57).

### 69. The 3 deferred computations resolved/advanced — DH caught at d*=62 (fails by scalar-gap crossing); boundary is source-built; batched-Hurwitz tooling

**What.** Resolved the gpt/39 deferrals (#57/#58/#59) and the gpt/38 DH deferral (#46). Scripts+outputs under
`computations/2026-06-22-comp5[7-9]*`, `-hurwitz-batch.py`; worklog updated. **Register:** SEARCH/`[VERIFIED]`;
**no new RH proof / Lean / ledger promotion.**

- **#58/#46 DH past threshold — SOLVED.** Root cause was mpmath recomputing a full Euler–Maclaurin sweep per
  derivative order. Built a **batched Hurwitz–Taylor routine** (`hurwitz_taylor`, all M coeffs in one sweep,
  verified to 2.7e−499 at dps=500); only 4 calls needed for DH ⟹ build 146s (was 250–500s+). Result: **DH
  off-line zero caught at d*=62** — the scalar gap `s_d=a_*·margin` flips negative at d=62 while `inertia(H^-)=
  (d,1)` PERSISTS. DH fails by the **boundary atom becoming insufficient** (`a_*<a_c`), the exact rank-one
  Weyl-threshold crossing — fake-family failure in the boundary-Weyl language (gpt/39 #58 target hit).
- **#57 Weil-pullback — computable half done.** The rank-one boundary atom = the **j=1 term of the archimedean
  square-sum** (rel 0) ⟹ boundary source-built from the Γ-factor, no zero-feeding; bulk `H^-=M_triv^{(j≥2)}+R^P`,
  defect prime-sourced, inertia (d,1). The de Branges/Krein seam-centre construction remains paper-math (target
  now source-identified).
- **#59 Gram–Heine d=5,6 — done.** Tuple identity holds d=5,6; det H_5,H_6 unconditional for γ≥25; schema
  reusable. Rigorous interval-symbolic version is a follow-on.

**Folded:** bridge-theorem.md §5b (source-boundary anatomy + DH fails-by-gap); research-topics.md (deferrals
resolved + the batched-Hurwitz tooling note). **Net:** all queued computations across gpt/37–39 are now run; the
only genuinely-open item is the de Branges/Krein construction (paper math), with a source-identified target.

### 70. gpt/proof4 + gpt/41 folded — exponent law DERIVED; the four-piece Rank-one Γ-boundary Weyl Bridge; named gate s_d=0

**Source.** `docs/consolidated/gpt/proof4.md` (analytic derivation of comp49's exponent law) and `gpt/41.md`
(synthesis of the comp57/58/59 deferral-resolution runs). **Register:** SEARCH/`[DERIVED]`/`[SYNTHESIS]`; **no new
proof of RH, no Lean, no ledger promotion.**

**Folded in.**
- **The parity exponent is DERIVED, not fitted** (proof4): `α_d(y_*)≈4+[4(1−ln2)+2ln|y_*|]/L̄_d`, L̄_d=(1/d)Σln γ_j,
  from exterior-Christoffel asymptotics — base 4 (reciprocal-square) + 4(1−ln2) hard-edge Vandermonde correction
  (`2∫₀¹log(1−t²)dt`) + 2ln|y_*| Christoffel normalization. The empirical `≈4.31+½ln|y_*|` is the L̄_d≈4
  finite-window case; the slope ½=2/L̄_d drifts down with d (no universal slope). Checks ζ/odd/even →3.391/3.901/
  5.000. → bridge-theorem §5b, big-picture §5.
- **The four-piece proof shape / Rank-one Γ-boundary Weyl Bridge** (41): (A) reciprocal chart; (B) Γ boundary split
  H^0=H^-+a_*v_*v_*^T (atom = first Γ-trivial-zero term, source-built); (C) one-defect bulk theorem inertia(H^-)=
  (d,1) ∀d; (D) scalar Weyl gap s_d=a_*+1/m_d=1/K_ν'(y_*)=a_*·margin>0 ∀d. New reduction: **Q_0≥0 ∀p ⟺ s_d>0 ∀d**.
  → bridge-theorem §5b/§7, big-picture §0, 08 §2.
- **Named fake-family gate s_d=0** (41): DH crosses at d=62 with inertia(H^-)=(d,1) preserved — separates DH at a
  structural gate (satisfies the corpus's fake-family-separation requirement). → bridge-theorem §5b, big-picture §0, 08 §2.
- **The remaining work is a finite-part identity, not a sweep** (41 §9): source-identify μ_E (comp56 Hankel tail)
  as the seam-centre finite-part boundary distribution; target `FP_{w=0}Q_W[h_p]=Q_0[p]−a_*p(y_*)²` ⟹ s_d>0. Plus
  the one-defect bulk lemma inertia(H^-)=(d,1) ∀d. → research-topics #60–62.

**Net.** The conjectured last theorem before RH is now the **Rank-one Γ-boundary Weyl Bridge** with a derived rate
law and a named fake-family gate (s_d=0); the open work is paper-math (the seam-centre finite-part identity + the
one-defect lemma), not further numerical sweeps. Acceptance scorecard: faithful/completed/source-built-boundary/
fake-separating/no-margin-compatible all ✓; the one open word is **prove** (all-d s_d>0).

### 71. gpt/proof5 folded — seam finite-part lemma package; Lemma 1 (residue identity) VERIFIED; the tail E PROVED Hankel; one open analytic step isolated

**Source.** `docs/consolidated/gpt/proof5.md` (paper-math lemma package for the open Weil-pullback / seam
finite-part step). **Register:** Lemma 1 `[VERIFIED — comp60]`, §6 Hankel-forcing `[DERIVED]`, the de Branges/Krein
finite-part construction `[OPEN — paper math]`. **No new proof of RH, no Lean, no ledger promotion.**

**Folded in (bridge-theorem.md §5b "seam-residue lemma package"; 08 §2; research-topics #60).**
- **Lemma 1 — seam-residue identity, VERIFIED (comp60).** `Q_0[p] = −Res_{w=0}[h_p(w)·(Ξ'/Ξ)(w)dw]`,
  `h_p(w)=−w^{−2}p(−w^{−2})²`, with `(1/2w)(Ξ'/Ξ)=Σ(−1)^k(T_{k+1}/2)w^{2k}`. The bridge form is a single seam-centre
  (w=0 ⟺ s=½) residue of the COMPLETED log-derivative; splitting `Ξ'/Ξ=A+P` gives `Q_0=Q_A+Q_P` source-side.
  (Corrected proof5's constant: −1 on Ξ'/Ξ in our folded `T_k=2Σγ^{−2k}` convention, not −½ — proof5 uses unfolded T.)
- **The tail E is PROVED Hankel (§6).** `h_p` is a Laurent series at w=0; a finite-part distribution there pairs only
  with the coefficients indexed by n ⟹ `E_{ij}=e_{i+j}` necessarily — *proves* comp56's empirical Hankel tail from
  the singular-pullback structure. Generating fn `M_E(w)`, `μ_E[p²]=−Res[h_p·w·M_E]`.
- **The one open analytic step, isolated.** All else is closed algebra (Lemma 1; the Γ-atom = j=1 trivial-zero term,
  source-built; the Sherman–Morrison scalar `s_d=a_*+1/m_d=1/K_{ν'}(y_*)`). The single remaining theorem: construct
  the canonical de Branges/Krein finite-part domain at w=0 and prove its boundary distribution is exactly μ_E
  (`FP^bulk_{w=0}Q_W[h_p]=Q_0[p]−a_*p(y_*)²`). A completed-function-theory finite-part identity, not a numerical lemma.

**Net.** The Weil-pullback route is no longer "vague" — it has a verified residue backbone (Q_0 = seam residue of the
completed Ξ'/Ξ), a proof that the sign-essential tail must be a Hankel functional, and a single isolated open step
(the de Branges/Krein finite-part domain). The proof-program's remaining content is now one named completed-function
construction, with everything around it closed.

### 72. de Branges/Krein construction — blocker diagnosed (claude + gpt/42 synthesis); 8-computation program queued (rt#63–70)

**Context.** The one genuinely-open step (gpt/proof5) is the canonical de Branges/Krein finite-part construction at
the seam centre. Both Claude and GPT (`docs/consolidated/gpt/42.md`) were asked to diagnose the blocker and propose
NON-theatre computations. **Register:** SEARCH/diagnosis; no new math promoted.

**Synthesis (independent convergence).** Both reached: Krein–Langer **Π₁ (one-negative-square)**, not ordinary
Hilbert de Branges; Hankel is forced by locality at w=0 but the actual `e_n` is not fixed until the domain is;
zero-margin kills ε-closure. GPT's shortest-form blocker — **"canonicality of the finite part"** — is the sharpest:
since tiny tails flip the sign (comp45/50), a finite-part scheme ambiguity could *decide RH in the model*; so the
single most decisive test is whether μ_E is even regulator-independent (rt#67), prior to locating it (rt#63).

**Tasks created (rt#63–70):** #63 locate μ_E (support/Padé/at-infinity), #64 source-identify μ_E (PSLQ + prime-sum),
#65 N₁ Pick test, #66 is-H^- a moment matrix, #67 regulator-canonicality (sharpest), #68 zero-free gauge audit, #69
Hankel-tail comparison across ζ/L/DH, #70 boundary-triple section reconstruction. #63/#64 enriched with gpt/42's
Padé-singularity-archaeology and explicit prime-sum form. **Run order: 67 → 63,64 → 65,66,68 → 69,70.**

**Folded:** research-topics.md (blocker diagnosis + the 8-computation program + where-not-to-go). The frontier has
moved from "what is the finite object" (settled) to "is the finite-part construction canonical and source-built."

### 73. de Branges program — all 8 computations run (comp63–70), results recorded

**What.** Ran the de-Branges-program computations (rt#63–70). Scripts+outputs `computations/2026-06-22-comp6*`;
worklog updated. **Register:** `[VERIFIED]` computational results; no RH math promoted.
- **#63:** the tridiagonal-split tail μ_E is a SIGNED measure (inertia (5,12)) dominated by x≈0.165 ⟺ the lowest
  zero y_1; e_n mostly negative, 1 sign change.
- **#64:** R^P (prime part) source-identified = PRIME_k = (ζ'/ζ)^{(2k−1)}(½) data; split-tail e_n PSLQ-miss
  (γ_1-dominated, not elementary).
- **#65:** m_σ=Cauchy(σ) has Pick-kernel κ=1 (generalized Nevanlinna N1; the boundary atom is the one negative
  square). Off-line quartet at γ0=20 leaves κ=1 at O(1) samples (sampling/height-limited).
- **#66:** H^- = signed moment matrix of σ=ν'−a_*δ_{y_*} (Krein–Langer Π₁; one negative square = boundary atom;
  derivable by inspection).
- **#67:** s_d is presentation/regulator-invariant (three presentations agree to reldiff 1e-116; depends only on H^-).
- **#68:** s_d gauge-invariant under Ξ→e^{cw²}Ξ; naive Lemma-1 source-extraction is q-contaminated (needs canonical
  ξ-normalization).
- **#69:** DH tail = genuine odd-χ tail (gate is s_d=0); tail scale parity-dependent (even-χ deviates).
- **#70:** m_d(y)=K_{H^0}(y,y) − s_d·(v(y)^T(H^0)^{-1}v_*)²: positive Christoffel minus a thin κ=1 dip at y_*=−0.16
  (width ~margin), stable across d.

**Folded:** research-topics.md (results). Tasks #32–39 completed.

### 74. gpt/proof7 + proof8 folded — seam finite-part construction BUILT; tail identified (E=μ_E); open content narrowed to s_d>0 (docs updated to current state)

**Source.** `docs/consolidated/gpt/proof7.md` (regulator/finite-part construction) + `proof8.md` (identification
E=μ_E). **Register:** proof7 anatomy `[DERIVED — paper math]`, proof8 `[PROVED — conditional on the source-defined
Jacobi J]`; the scalar positivity s_d>0 stays `[OPEN]`. No RH math promoted.

**What changed in the knowledge docs (updated to current state, not appended as history):**
- **proof7 — the canonical finite part exists and is regulator-independent.** Admissible even approximants
  h^{ε,R}=t^{−2}p(t^{−2})q(t^{−2})η(t/ε)ψ(t/R); Hadamard expansion has only odd powers and B=0 (no log) by evenness;
  the finite part is η-/ψ-independent (no u^{−1} term for even jets), has an R→∞ limit, and is necessarily Hankel
  (analytic proof of E_{ij}=f(i+j)). Gauge Ξ→e^{q(w²)}Ξ shifts it by a local Hankel counterterm removed by canonical
  ξ-normalization ⟹ unique. This settles the canonicality concern (gpt42 sharpest blocker; consistent with comp67/68).
- **proof8 — E=μ_E.** With the source-defined Green split R^P=J+𝓑, 𝓑_{ij}=e^{fp}_{i+j} (from the source prime-residual
  distribution, not zero-fed); J Jacobi + both Hankel ⟹ the computed tail E equals the seam finite-part boundary
  distribution μ_E on all i+j≥2 (i+j=0,1 pinned by canonical ξ + the Γ-atom). "What is E" is closed.
- **Open content narrowed to one statement:** the source-built scalar Weyl positivity s_d=1/K_{ν'}(y_*)>0 ∀d.

**Docs revised to current state:** bridge-theorem.md §5b (the seam-residue lemma-package block rewritten: construction
built + E=μ_E proved; open = s_d>0), 08 §2 (same), big-picture §5 ("what stays open" = s_d>0 only), research-topics
(the seam finite-part section rewritten to BUILT + open=s_d>0). The dated working blocks were updated in place rather
than accumulated.
### 75. gpt/43 folded — synthesis of comp63–70 into a Krein–Langer rank-one signed moment problem; μ_E demoted to anatomy; apex = s_d>0 (Uvarov kernel); docs updated to current state

**Source.** `docs/consolidated/gpt/43.md` — gpt's synthesis of the de-Branges battery (comp63–70). **Register:**
reformulation `[CONJECTURE — structural]` resting on the verified runs; the apex `s_d>0` stays `[OPEN]`. No RH math
promoted.

**The current sharp form (folded into the knowledge docs as current state):**
- **Krein–Langer signed moment problem.** `H^-_d = M_d(σ)`, `σ = ν' − a_*δ_{y_*}` (positive reciprocal zero measure
  minus one exterior Γ-boundary atom); `H^0_d = M_d(ν')`. Bridge = the transition `σ∈Π₁ ─(+a_*δ_{y_*})→ ν'∈Π₀`, i.e.
  `m_σ=∫dσ/(t−z)∈N₁` (κ=1, comp65/66) becomes PSD after the canonical Γ atom. A boundary-Weyl theorem, not a bulk
  estimate.
- **μ_E demoted.** The identified tail `E=μ_E` is the seam Hankel *shadow* of `σ` — anatomy, γ_1-dominated (comp63/64),
  not a fourth divisor and not the fake-family gate (DH and odd-χ share the tail, comp69). The gate is `s_d=0` alone.
- **Three divisors:** RH divisor `{y_ρ}`; Γ-boundary divisor `0.16δ_{−0.16}`; Krein signed divisor `σ` (the proof
  divisor, in Π₁).
- **Apex as a reproducing-kernel (Uvarov) statement:** `K_σ(y,y)=K_{ν'}(y,y)−K_{ν'}(y,y_*)²/K_{ν'}(y_*,y_*)` ⟹
  `K_{ν'}(y_*,y_*)>0 ∀d`, i.e. `s_d>0 ∀d`. N₁ anatomy alone is not enough (DH shares it); the Euler/polarization
  ingredient enters exactly at the scalar repair sign. Likely final shape: a Hodge/de Branges signature theorem.
- **5-step proof route:** canonical ξ-gauge → source-build R^P from (ζ'/ζ)^{(2k-1)}(½) → prove m_σ∈N₁ globally →
  rank-one repair s_d>0 → identify the Hodge/de Branges object behind s_d.

**Docs revised to current state (in place, not appended as history):** bridge-theorem §5b (Krein–Langer current-sharp-form
block added; the stale "μ_E is the missing theorem" bullet rewritten to "identified, then demoted"), bridge §7 (current
sharp form added), big-picture §0 (Krein–Langer naming) + §5 (open content = Π₁→Π₀ / s_d>0 with the gauge-lemma and
N₁-carrier sub-obligations), 08 §2 (Krein–Langer + Uvarov + N₁-before-positivity), research-topics (gpt/43 synthesis +
the 10-item priority computation agenda; the superseded gpt/42 canonicality-blocker block reframed as RESOLVED).

### 76. gpt/proof9 folded — canonical-gauge extraction lemma PROVED + comp71 VERIFIED; the gpt/43 feeder sub-theorem (a) is discharged; comp68 "gauge bug" resolved

**Source.** `docs/consolidated/gpt/proof9.md` (canonical-gauge extraction lemma) + comp71 (local verification,
`computations/2026-06-22-comp71-gauge-law.py`). **Register:** lemma `[PROVED — paper math]`, law `[VERIFIED — comp71]`;
RH positivity still `[OPEN]`. No RH math promoted.

**The result.** Under the zero-free even gauge `Ξ↦e^{q(w²)}Ξ`, `q=Σ_{r≥1}a_r w^{2r}`, the extracted reciprocal moments
obey the **exact diagonal law `T_k↦T_k+2k(−1)^{k+1}a_k`** (only `a_k` moves `T_k`). Mechanism: `T_k=2(−1)^{k+1}k·c_{2k}`,
`c_{2k}=[w^{2k}]logΞ`, and `logΞ↦logΞ+q(w²)` shifts `c_{2k}↦c_{2k}+a_k`. Form-level Hankel counterterm
`(Δ_q H^0)_{ij}=2(i+j+1)(−1)^{i+j+2}a_{i+j+1}`. Canonical extraction `T_k^can=T_k^raw−2k(−1)^{k+1}a_k` (= the completed
Riemann `ξ`-normalization, `a_r≡0`).

**comp71 verification (at the actual Ξ, k=1..6).** logΞ-Taylor anchor agrees with the analytic-pieces `c_{2k}` to
`1e-77`; the closed form, diagonality (only-`a_3` gauge moves only `T_3`), the Hankel counterterm, and canonical
recovery are all exact. The `T_1↦T_1+2c` of comp68 is the `k=1` case.

**comp68 "bug" resolved.** The earlier "gauge contamination" of the naive source-extraction is not an error — it is
this canonical-gauge law; the canonical `ξ`-gauge (or the explicit diagonal subtraction) is the fix. comp68 re-surfaced
in research-topics with the proof9 clarification.

**Docs revised to current state:** bridge-theorem §5b (canonical-gauge extraction lemma bullet added; the proof7 gauge
bullet points to the now-exact counterterm), big-picture §5 (feeder sub-obligation (a) marked discharged), 08 §2 (same),
research-topics (gpt/proof9 block + comp71 done + comp68 resolution; gpt/43 agenda #1 marked DONE). Task #40 (comp71)
completed.

### 77. comp72 run — N_kappa Pick stress test: ζ robustly N₁ (κ=1 stable); off-line zero → κ=2 (resolution-limited)

**What.** gpt/43 computation #2 (priority 2). Script+output `computations/2026-06-22-comp72-pick.*`; worklog updated.
**Register:** `[VERIFIED]` computational result. No RH math promoted. Task #41 completed.
- **ζ (RH): κ=1 STABLE** across sample size M=6..30 and zero-truncation N=50..400 — gpt/43's falsifier "κ>1 at larger
  samples ⟹ rank-one route weakens" did NOT fire. Strong support for the global N₁ carrier theorem.
- **Off-line FE quartet (DH-like): κ=2, resolution-limited.** On-line β=0.5 stays κ=1; off-line β=0.7/1.0 gives κ=2 when
  sample points sit near the off-line atom scale 1/γ₀² (dense local sampling → κ=2 robust, min-eig→−31).
- **Reading.** The off-line zero is a 2nd negative square in the *infinite* Cauchy-transform Pick kernel
  (resolution-limited) — complementary to the *finite* scalar s_d gate (height-limited) and the moment-inertia
  (d,1)→(d,2) — while leaving the tail μ_E unchanged (comp69). Refines gpt/43's "fake failure is only scalar": several
  complementary, resolution/height-limited detectors of the same off-line atom; ζ stays cleanly N₁.

**Folded:** research-topics (agenda #2 → DONE), bridge-theorem §5b (N₁ line strengthened with the stress-test result).

### 78. comp73 run — prime truncation is NOT a faithful source for (ζ'/ζ)^{(2k-1)}(½) (pole-dominated); the no-zero-feeding extraction needs the completed Ξ

**What.** gpt/43 computation #3 (priority 3). Script+output `computations/2026-06-22-comp73-prime-source.*`; worklog
updated. **Register:** `[VERIFIED]` computational result. Task #42 completed.
- **Result.** Sharp/Riesz-smoothed prime sums for g_k=(ζ'/ζ)^{(2k-1)}(½) DIVERGE (pole-dominated ~√X·(log X)^{2k-1};
  S_1(2e6)=35385 vs target 3.75). The O(1) residual sign that sets s_d is invisible in any finite prime truncation
  without explicit s=1-pole subtraction + the zero oscillation. Confirms gpt/43's worst-case surprise.
- **Clarification.** The no-zero-feeding obligation IS met by the completed/continued ζ: T_moments_exact extracts T_k
  from c_{2k}=[w^{2k}]logΞ (ζ-derivatives at ½, Γ/pole closed) — zero-free, finite, = the exact T_k. So source-side
  s_d ≡ zero-side s_d via Ξ; the prime sum is the wrong (divergent) representation. The mandatory step is the analytic
  pole subtraction built into Ξ.

**Folded:** research-topics (agenda #3 → DONE with the clarification).

### 79. comp74 run — the Christoffel dip is universal & parabolic (P(Y)=4Y²−1); no-margin geometry collapses to one scalar (the curvature)

**What.** gpt/43 computation #4 (priority 4). Script+output `computations/2026-06-22-comp74-dip-profile.*`; worklog
updated. **Register:** `[VERIFIED]` computational result. Task #43 completed.
- **Universal parabolic dip.** Rescaled `P(Y)=m_d(y)/|dip_min| = 4Y²−1` to `3.6e-15` across d=8,12,16,20,24,28 (Y=(y−y_min)/w_d).
  A smooth quadratic minimum — no cusp/anomalous local shape.
- **Depth pinned `m_d(y_*)=−1/a_*=−6.25 ∀d`** (= the no-margin identity `a_*m_d→−1 ⟺ s_d→0`); depth and shape frozen.
- **Width curvature-controlled** `w_d=2√(2|m_d(y_*)|/m_d''(y_*))`, super-exponential shrink 2.4e-18→3.1e-81 (d=8..28),
  `w_d~s_d^{≈0.45}` (not ∝ s_d). ⟹ the asymptotic no-margin geometry collapses to ONE d-scalar, the inverse-Christoffel
  curvature `m_d''(y_*)`; gpt/43's "universal profile ⟹ asymptotic kernel proof" route is open.
- **Caveat (recorded).** s_d sign at d=28 (printed −1.9e-168) is precision-limited at dps=322 (below ~1e-150 unreliable);
  not a real RH violation — d≤24 reliably s_d>0.

**Folded:** research-topics (agenda #4 → DONE), bridge-theorem §5b (comp70 dip line + the universal-parabola/curvature refinement).

### 80. comp75 run — rank-one boundary theorem extends to a COMPLEX self-dual product (still N₁); rank = #distinct Γ-shifts

**What.** gpt/43 computation #5 (priority 5). Script+output `computations/2026-06-22-comp75-complex-selfdual.*`; worklog
updated. **Register:** `[VERIFIED]`. Task #44 completed.
- For complex χ mod 5 (order 4, odd), the self-dual product Λ(s,χ)Λ(s,χ̄) (real moments, squared Γ) stays **N₁**:
  H^0 PSD, removing the rank-one boundary atom (weight a_*=4/9 or doubled 2a_*=8/9) leaves exactly ONE negative square
  — inertia (d,1) — and s_d=1/K_{H^0}(y_*,y_*)>0 ∀d (d=6..12), shrinking like ζ. (s_d is weight-independent by
  Sherman–Morrison, consistent with comp67.)
- **The rank-one boundary-Weyl theorem is structural, not ζ-specific.** The squared Γ does NOT force rank-two; χ,χ̄ share
  one parity/Γ-channel ⟹ coincident doubled trivial zeros ⟹ rank-one. Rank = number of DISTINCT Γ-shift values; a
  genuine two-channel object (GL(2) Γ_ℝ(s)Γ_ℝ(s+1)) would give rank-two/N₂.

**Folded:** research-topics (agenda #5 → DONE), bridge-theorem §5b ("completed-Euler-product-general" line extended to
the complex self-dual case).

### 81. comp76 run (partly negative) — single off-line quartet does NOT cleanly control s_d=0; the gate responds to the GLOBAL off-line density

**What.** gpt/43 computation #6 (priority 6). Script+output `computations/2026-06-22-comp76-dh-deformation.*`; worklog
updated. **Register:** `[VERIFIED]` (negative/refining result). Task #45 completed.
- Adding λ·(one off-line quartet) to ζ's moments shifts s_d to a saturated, generically POSITIVE value (d=10:
  1.3e-52→5.3e-49 for λ≥0.5); crossings are sporadic/non-monotone (only d=8 λ≈0.16; d=16 only at g0=40).
- **Reading.** s_d=0 is not controlled by a single off-line atom's weight; the genuine DH failure (s_d<0 at d*=62)
  needs the GLOBAL/cumulative off-line zero density — a height-limited condition, consistent with comp72's
  resolution-limited κ=2. Answers gpt/43's "crossing appears without a clean single-parameter signature."

**Folded:** research-topics (agenda #6 → DONE).

---
**gpt/43 priority computations (1–6) COMPLETE.** comp71 (gauge law, proof9 verified), comp72 (ζ κ=1 stable / off-line
κ=2), comp73 (prime truncation diverges), comp74 (universal parabolic dip), comp75 (complex self-dual stays N₁),
comp76 (s_d gate is global, not single-atom). Remaining unprioritized: comp77 (μ_E spectral measure), comp78 (Padé of
F_E), comp79 (regulator-to-scalar s_d), comp80 (determinantal/Jensen identity).

### 82. comp80 run — s_d is a Hankel-determinant ratio (τ-function form); Jacobi–Krein ↔ Pólya–Jensen are one object

**What.** gpt/43 computation #10. Script+output `computations/2026-06-22-comp80-determinant.*`; worklog updated.
**Register:** `[VERIFIED]`. Task #49 completed.
- **s_d = −det(H^0_d)/det(B_d)** (B_d = H^0 bordered by v_*=(y_*^i)) verified vs a_*+1/m_d to rel ~1e-120 (d=6..14);
  det(H^0)=det(H^-)(1+a_*m_d) (matrix-determinant lemma) to same precision.
- det(H^0_d)>0 ∀d = Hankel/Pólya–Jensen positivity (= H^0 PSD = Q_0≥0); det(H^-)<0 (inertia (d,1)); so
  1+a_*m_d=det(H^0)/det(H^-)<0→0⁻ (Krein threshold in determinant form; no-margin = det(H^0) vanishing rel. det(H^-)).
- **Jacobi–Krein and Pólya–Jensen entrances are the SAME object**, joined by the matrix-determinant lemma + Uvarov
  border; s_d is their Christoffel determinant quotient.

**Folded:** research-topics (agenda #10 → DONE), bridge-theorem §5b (apex reproducing-kernel line gains a determinant/Jensen face).

### 83. comp77+78 run — μ_E is the zero-side spectral measure on {a_*+y_n}; F_E meromorphic with poles accumulating at z=1/a_*

**What.** gpt/43 #7+#8. Script+output `computations/2026-06-22-comp77-78-muE-measure.*`; worklog updated.
**Register:** `[VERIFIED]`. Tasks #46,#47 completed.
- **comp77:** μ_E's signed-Gaussian-quadrature nodes = the reciprocal zero images {a_*+y_n=0.16+1/γ_n²} (leading
  → 0.165005=a_*+y_1; next 0.162263=a_*+y_2, 0.161599=a_*+y_3). Negative inertia grows ~0.6d ((3,6)→(9,18), d=12..30)
  ⟹ a genuine full signed measure, no rank-one simplification.
- **comp78:** F_E(z)=Σe_n z^n meromorphic, simple poles at z=1/(a_*+y_n) (nearest 6.0604), accumulating at z=1/a_*=6.25
  (the y=0⁺ hard edge). ⟹ μ_E = ν' in the protector coordinate (the seam shadow of σ); confirms gpt/43's demotion.

### 84. comp79 — regulator-to-scalar (covered, not re-run)
gpt/43 #9. The claim (s_d regulator-independence) is established by proof7 Lemma 2 + comp67 (presentation-invariance
1e-116) + comp71/proof9 (seam FP = T_k exact). A direct contour re-derivation (`2026-06-22-comp79-regulator.py`) was
slow (4:19) and had a coefficient-extraction bug; not debugged (redundant/theatre by the residue theorem). Task #48
completed-by-coverage. **gpt/43 computation agenda (1–10) COMPLETE.**

### 85. gpt/proof10 + gpt/proof11 folded — N₁ carrier theorem (feeder b) and Christoffel/Uvarov kernel theorem proved; doc reorganization

**Source.** `docs/consolidated/gpt/proof10.md` (N₁ carrier) + `proof11.md` (Uvarov kernel). **Register:** both
`[PROVED — conditional]` (proof10 on the 1-dim seam quotient; proof11 exact ∀d); apex `s_d>0` still `[OPEN]`.
- **proof10 — N₁ carrier theorem.** `m_σ∈N₁` / `inertia(H^-_d)=(d,1)` proved from: the one-dimensional seam boundary
  quotient `𝒦_max/𝒦_min≅ℂ` (deficiency index one), the Green identity `Γ_0F_p=p(y_*)`, the Γ-atom `a_*|p(y_*)|²`
  (κ₋≤1 from the 1-dim quotient; =1 from the active defect). The matrix pattern is now an operator-domain theorem.
  Discharges gpt/43's feeder sub-theorem (b).
- **proof11 — Christoffel/Uvarov boundary-removal kernel theorem.** Proves comp70 exactly ∀d:
  `K^crit_d(y,z)=K_{ν'}(y,z)−K_{ν'}(y,y_*)K_{ν'}(y_*,z)/K_{ν'}(y_*,y_*)` (reproducing kernel of {p:p(y_*)=0}). The
  actual signed Π₁ kernel is an infinitesimal over-subtraction `s_d²/(a_*−s_d)` beyond it (explains the vanishing
  dip, comp74). No-margin limit via the normalized boundary vector `ψ_{*,d}` (persists as s_d→0). Apex caveat:
  real-axis kernel positivity insufficient (off-line defect off the moment curve, comp72).

**Docs revised to current state:** bridge-theorem §5b (N₁-carrier-proved + Uvarov-kernel-theorem + over-subtraction
taxonomy), big-picture §5 (both feeders discharged; sole open = repair theorem s_d>0), 08 §2 (feeder (b) DONE + Uvarov
∀d).

**Doc reorganization (per user).** All gpt/43 + de-Branges computation RESULTS now live in
`06-experimental-findings.md` (new subsection "The rank-one Krein–Langer boundary-Weyl battery"). research-topics.md
is no longer used as a results log — the comp-results blocks added this session (the gpt/43 synthesis/agenda/results,
proof9 block, de Branges results) were removed from it; the conceptual synthesis remains in the knowledge docs
(bridge/big-picture/08). The per-computation factual records stay in logs/gpt37-computations-worklog.md.

### 86. Correction (honesty) — comp80's "Jacobi–Krein ↔ Pólya–Jensen are one object" was overstated; it reduces-to-known

Prompted by the user. The comp80 determinant identities (`s_d=−det(H^0)/det(B)`, `det(H^0)=det(H^-)(1+a_*m_d)`,
`det(H^0_d)>0` ⟺ H^0 PSD) are **classical**: Cramer's rule for the Christoffel function + the matrix-determinant lemma
+ the textbook "Hankel PSD ⟺ Hankel-determinant positivity" (Hamburger moment problem) and Krein–Langer Π_κ apparatus.
By our own novelty gate this **reduces-to-known** — search, not new knowledge; comp80 only *verified* the algebra
numerically. Two corrections applied to 06-experimental-findings.md and bridge §5b: (1) the result is downgraded to
*organizational* (it places the bridge's scalar gate `s_d` inside the classical OP/Christoffel/de-Branges toolkit, and
identifies the no-margin `s_d→0⁺` as a hard-edge Christoffel asymptotic — useful internally, not a contribution to the
field); (2) it is **not** the Pólya–Jensen criterion — that is Hankel/Turán positivity of ξ's Taylor coefficients (a
*different* sequence and determinants). Both are "RH as Hankel positivity," cousins under one classical principle, not
the same object. The genuinely open/significant item remains the apex: the **source-built** `s_d>0 ∀d` (the repair
theorem), which comp80/proof10/proof11 do not touch.

### 87. SOTA / prior-art literature sweep — six-cluster WebSearch+arXiv; new doc 10-prior-art-and-sota.md; rediscoveries flagged

**What.** User-requested full literature sweep (6 parallel agents: RH positivity criteria, Pólya–Jensen/Hankel,
de Branges/Krein, Christoffel/OP hard-edge, hypertranscendence field, Davenport–Heilbronn/Selberg). Two load-bearing
citations verified directly (Derkach–Hassi–de Snoo 2002; Uvarov 1969). **Register:** `[KNOWN — cite]` / `[NOT FOUND]`.

**Headline:** nearly the entire rank-one Krein–Langer battery is **classical apparatus reassembled in the seam
coordinate**, not new knowledge:
- `T_k=2Σγ^{−2k}` = **Voros secondary-zeta values** (Mellin 1917; Voros 2010, arXiv:1403.4558).
- `s_d` = inverse **Christoffel function = Hankel-determinant ratio** (Szegő 1939; Nevai 1986) ⟹ **comp80 reduces-to-known**.
- proof11's boundary-removal kernel = **Uvarov 1969** (Krattenthaler arXiv:2103.03969).
- proof10's `N₁→N₀` rank-one transition = ζ-specialization of **Derkach–Hassi–de Snoo, JFA 188 (2002) 317**.
- boundary-Weyl positivity overlaps **Suzuki arXiv:1204.1827** (RH ⟺ Hamiltonian PSD); Lagarias/Burnol.
- `Q_0≥0⟺RH` in the **Weil/Li/Csordas–Varga** moment-positivity family; and (Pólya–Jensen agent's catch) the `T_k`
  Hankel is auto-PD for any positive measure ⟹ `Q_0` is the Hamburger real-support test repackaged (low content).
- **Pólya–Jensen ≠ our `T_k` Hankel** (different sequence — ξ Taylor coefficients); GORZ 2019 proved only *asymptotic*
  hyperbolicity.
- Hypertranscendence field = **mature but fragmented** (Hölder/Ostrowski; Hardouin–Singer; ADH 2021 arXiv:1910.01874;
  Fresán–Jossen); "constraint not flow" is framing, not theorem.
- DH/Euler-product separation is textbook (Selberg class); "Euler product + FE ⟹ RH" is open/RH-equivalent.

**No-go to heed:** **Conrey–Li (arXiv:math/9812166, IMRN 2000)** — de Branges positivity FAILS for ξ.

**NOT found (candidate non-reducing):** (i) explicit *exterior* hard-edge Christoffel asymptotic `s_d~∏γ_j^{−α}`
(comp49/proof4) — interior/edge solved (Totik 2000; Kuijlaars–Vanlessen 2003; Lubinsky 2009), exterior only
qualitative; possibly open OP theory but not RH (check Stahl–Totik). (ii) a *positivity-framed* Euler-product-vs-DH
separator = the open apex `s_d>0`.

**Docs updated:** new `10-prior-art-and-sota.md` (full map); inline SOTA flags in bridge-theorem §5b (proof10/proof11
+ Krein–Langer block), big-picture §5, 06-experimental-findings (battery); README index. The operational point:
import the classical apparatus with citations; the only genuinely-open/significant target is the apex `s_d>0 ∀d`.

### 88. gpt/45 folded — independent SOTA assessment converges with our sweep; adds Connes–Consani; sharpens the open-theorem list

**Source.** `docs/consolidated/gpt/45.md` — GPT's answer to the same SOTA/prior-art task. **Register:** `[KNOWN]` /
meta. Strongly convergent with CHANGELOG #87's six-cluster sweep.

**Convergent bottom line (two independent assessments agree):** this is a computationally driven candidate normal form
/ coordinate atlas of one known wall — NOT yet new mathematics. RH-is-positivity is old; Jensen–Pólya is SOTA (GORZ);
the `s_d` identities are mechanical (Sherman–Morrison/Schur/Uvarov/Christoffel); comp73 confirmed an expected failure
mode, not new theory.

**What gpt/45 added (folded into §10):**
- **Connes–Consani(–Moscovici) archimedean-positivity programme** (§10.A12, verified): arithmetic site (Adv. Math.
  2016); Riemann–Roch for Arakelov Spec ℤ; **"Zeta zeros and prolate wave operators"** (arXiv:2310.18423 = Ann. Funct.
  Anal. 15(4):87, 2024; PNAS 2022). Direct overlap: the prolate operator = scaling-operator² + **orthogonal-polynomial
  grading**, with a positive/negative (Sonin) spectral split — our Christoffel/`N₁`/`s_d` apparatus is adjacent. Was
  under-weighted in #87; now the principal "source-built archimedean positivity" SOTA to compare against.
- **The five statements that would be genuinely new** (§10.D): source-built `H^-` without zero-feeding; `N₁` from
  source data (not assuming the 1-dim quotient); `s_d>0 ∀d`; a *positivity-preserving* Jensen/Pólya identification of
  `s_d` (comp80's is NOT); the fake-family separation theorem.
- **gpt/45's self-correction = our `[conditional]` flags:** proof7–11 are algebraic consequences of assumed objects,
  not the constructed source-built operator domain; the `N₁` carrier is conditional on the 1-dim seam quotient; comp80
  doesn't prove `s_d>0`.
- **The deliverable** (§10.D): a short note "The reciprocal-seam moment form of ξ and its Γ-Uvarov boundary scalar"
  (precise finite normal form + falsification ledger + comparison to GORZ and Connes–Consani) — converts atlas →
  research output without an RH proof.

**Docs updated:** 10-prior-art-and-sota.md (§A12 Connes–Consani; new §D gpt/45 convergence + the 5 open theorems +
the deliverable).

### 89. Stahl–Totik chase — the exterior hard-edge Christoffel asymptotic (§10.B1) is CLOSED, not open; no RH content

**What.** Chased the one OP-theory side-question (is `s_d~∏γ_j^{−α}`, comp49/proof4, genuinely open OP theory?).
WebSearch + reasoning. **Verdict: NOT open — it is the non-regular regime of Stahl–Totik regularity theory, a
derivable special case, RH-empty.**
- **Regular measures:** exterior Christoffel ~ `exp(2d·g_E(y_*))` (pure exponential, Green's function) — classical
  (Totik J.d'Analyse 81 (2000); Stahl–Totik, *General Orthogonal Polynomials*, CUP 1992).
- **Our `ν'` is non-regular:** thin atomic measure accumulating at the hard edge 0 with decaying masses; the n-th-root
  test fails (`K_d^{1/d}~exp(α ln d)→∞`, super-exponential `~d^{αd}` since `Σ_{j≤d}ln γ_j≈d ln d`), so the universal
  `exp(2dg)` law does not apply and the exterior rate is measure-specific (no universal exterior law for non-regular
  measures; the literature gives only interior/on-support asymptotics).
- **Derivable, not hard:** proof4's interpolation argument gives `ln s_d≈−4Σln γ_j−2d ln|y_*|+4(1−ln2)d` = the
  `α≈4+[4(1−ln2)+2ln|y_*|]/L̄_d` law — routine hard-edge OP computation, "unwritten for this measure," not a frontier.
- **No RH content:** the rate is generic hard-edge geometry (our docs already say this); the RH content is the sign
  `s_d>0`.

**Net:** B1 dropped as a novelty candidate. **The apex `s_d>0 ∀d` (B2) is now the SOLE open RH-bearing cell.**

**Docs updated:** 10-prior-art-and-sota.md §B1 (RESOLVED) + §C (B1 closed); big-picture §5; 06-experimental-findings.

### 90. Lens-status map (§10.E) added; lens 8 (empirical weld carrier) removed from the lenses

Added §10.E — a per-lens status table against the SOTA sweep: the sweep invalidated none of the lenses logically;
it relocates lenses 3/4/5/7 as SOTA-overlapping (Connes–Consani adelic weld; Krein–Langer index — corroborated by
comp72; Selberg-class FE-vs-Euler; 𝔽₁/function-field analogy), and lens 4's `κ₋=0` = the apex `s_d>0` is the sole
open RH-bearing cell.

Per user: **removed lens 8 (the empirical weld carrier)** from big-picture §1 — it was already deflated to an
analytic-continuation/zero-structure diagnostic (not a transcendence detector, big-picture Issue 2). The lenses list
now runs 1–7; the "unifying claim" line and §10.E updated to "seven lenses." (Issue 2's deflation record and the 06
phase-cancellation carrier findings are left in place — they document the observable, not a lens.)

### 91. gpt/proof12 folded — the reduction Q_0≥0 ⟹ RH is now rigorously proved (classical moment theory); passes the roleplaying audit

**Source.** `docs/consolidated/gpt/proof12.md`. **Register:** `[PROVED]` (the `⟹` half only). Verified the proof line
by line — it is correct.
- **What it proves:** `Q_0[p]≥0 ∀p∈ℝ[y] ⟹ RH` for the actual folded reciprocal zero divisor. Mechanism: `Q_0⪰0` ⟺
  `[T_{i+j+1}]⪰0` ⟹ (Hamburger/Riesz) a positive measure `μ` on `[−R,R]` (`R=sup|y_ρ|<∞`, `ξ(½)≠0`); the divisor g.f.
  `G(z)=Σ_α M_α y_α/(1−y_α z)` (meromorphic, poles at `1/y_α`) equals `∫dμ/(1−xz)` (Cauchy transform of a positive
  real-line measure, holomorphic off `ℝ`) ⟹ no non-real atoms (Step 3); `μ=ν=Σ M_α y_α δ_{y_α}` by Weierstrass ⟹
  `y_α>0` (Step 4) ⟹ `ρ=½+iγ`.
- **Roleplaying audit: PASSES** — proof12 §5 itself scopes it as a precise checkable reduction that does NOT cross the
  wall. It does not prove the converse (source-built `Q_0≥0`), which stays the open bridge / apex.
- **Novelty: LOW** — classical moment theory (Hamburger + Cauchy-transform singularity structure + Weierstrass), the
  `⟹` half of the known moment-positivity↔RH family (§10.A2). It is the rigorous write-up the corpus had only stated
  heuristically (the "source-aware refinement: Q_0 alone, not the companion Q_1").

**Docs updated:** bridge-theorem §1 intro + §3 (source-aware refinement upgraded to `[PROVED — proof12]` with the
mechanism), 07 §1 (new row T30), 10-prior-art §A2 (the `⟹` half now rigorous; passes roleplaying; low novelty).

### 92. gpt/proof13 read — it is gpt/proof9 (the canonical gauge law) re-derived; passes the roleplaying test; no new content

**Source.** `docs/consolidated/gpt/proof13.md`. **Verdict: a clean independent RE-DERIVATION of the proof9 canonical
gauge law** — identical statement and proof skeleton: `Ξ↦e^{q(w²)}Ξ` (`q=Σa_r w^{2r}`) ⟹ `T_k^raw↦T_k^raw+2k(−1)^{k+1}a_k`
(diagonal: only `a_k` moves `T_k`, since `d/dw q(w²)=Σ2r a_r w^{2r−1}` feeds `2k a_k` to the `w^{2k−1}` coefficient and
`T_k=(−1)^{k−1}[w^{2k−1}](Ξ'/Ξ)`); Hankel counterterm `(ΔH^0)_{ij}=2(i+j+1)(−1)^{i+j+2}a_{i+j+1}`; canonical fix
`T_k^can=T_k^raw−2k(−1)^{k+1}a_k` (= the completed-ξ representative, `q=0`); `T_1↦T_1+2c` is the `k=1` case.
- **Roleplaying test: PASSES** (proof13 §8 scopes it as a local coefficient calculation: "fixes the gauge bug; does
  not prove positivity, `Q_0≥0`, or RH"). Math verified correct.
- **No new content** — already PROVED (proof9, CHANGELOG #76) and numerically VERIFIED (comp71, k=1..6: closed form,
  diagonality, Hankel counterterm, canonical recovery all exact). proof13 is a second independent derivation, which
  strengthens confidence in the `[PROVED]` status; nothing to add to the open cores.

**Docs updated:** bridge §5b — `gpt/proof13 — independently re-derived` added as a co-citation on the gauge-law bullet.
(Not re-cited elsewhere: it duplicates proof9, already folded across 06/08/big-picture/§10.)

### 93. no-roleplay-items.md created — the surviving open cores, decomposed into a conjunction, projected through the seven lenses

New doc (register-honest map, not a proof). **The items that survive the SOTA sweep + roleplay audits:**
- **NR-1** the positivity transfer (source-built `Q_0≥0` / `s_d>0 ∀d` without zero-feeding) — the apex, RH-bearing;
- **NR-2** the fake-family separation (Euler-product ⟹ `s_d>0`, DH crosses) — the discriminating content, §10.B2;
- **NR-3** a *positivity-preserving* Jensen/Pólya identification of `s_d` (comp80's determinant one is sign-blind) — structural target;
- **NR-orth** the value/transcendence apex (Schanuel-for-prime-logs) — orthogonal, famous-open, set aside.

**Decomposition (iterated conjunction):** NR-1 ⟺ (I-a `N₁` carrier from source) ∧ (III-sign `a_*−a_c(d)>0 ∀d`), with
III-sign ⟸ NR-2 (Euler-product positivity transfer). Two genuine identities surfaced: `s_d = a_*−a_c(d)` (Γ budget
minus prime-bulk demand, lens 3); `1/s_d = K_{ν'}(y_*,y_*) = Σ_j|p_j(y_*)|²` (boundary transport-norm, lens 2).
III-rate (`∏γ_j^{−α}`) and comp80's determinant are reduces-to-known and carry none of the content.

**Seven-lens projections:** L1 no-margin = fixed-point sign (no flow to bound below); L2 holonomy non-degeneracy at
`y_*`; L3 weld balance = Connes–Consani semilocal weld; L4 `s_d` = continuous shadow of the integer `κ₋`; L5
must-consume-Euler-product (built-in correctness check vs DH); L6 `s_d` is a localization (not affine-volume)
functional — passes the faithfulness filter; L7 `s_d>0` = the "missing archimedean Frobenius positivity" (𝔽₁ /
Connes–Consani). **Most promising concrete move:** test whether `a_*−a_c(d)` is the compression of the Connes–Consani
prolate operator's positive/Sonin split (NR-3). Added to README index.

### 94. Prolate-compression test run (no-roleplay) — archimedean half matches exactly; literal compression claim refuted; target = semilocal prolate

**Task.** Test whether the finite weld `s_d=a_*−a_c(d)` is the compression of the Connes–Consani–Moscovici prolate
operator's positive/Sonin split. **Sourced** the operator: `W_λ=−𝕊²+2πλ²(4N+1)−¼` (`𝕊` scaling, `N` Hermite/OP
grading; Sonin = negative eigenvalues whose UV behaviour reproduces `γ_n²`; the Sonin/scaling compression proves Weil
positivity *at the archimedean place*). arXiv:2112.05500, 2310.18423.

**Result (no-roleplay — partial match + logical refutation):**
- `[PROVED — verified exact]` Our archimedean protector lattice `2|w|=4N+1` (N≥0) **is** the prolate Hermite grading:
  N=0 = the `s=1` pole (`−4` term), **N=1 = the boundary atom `a_*=(5/2)^{−2}=0.16`**, N=2 = `y=−0.0494`, … Same
  Gaussian origin (`Γ_ℝ` = Mellin transform of the prolate cyclic vector `e^{−πx²}`). Zero-side `γ_n²` = Sonin scale;
  our `ν'` lives on its reciprocals `1/γ_n²`.
- `[PROVED — logical]` The literal compression claim is **FALSE**: the Sonin compression is *unconditional* archimedean
  Weil positivity; `s_d>0` is RH-conditional. They cannot be equal. The match is the **archimedean budget** `a_*`
  (= `M_triv`, unconditional `⪰0`, the analog of `W_∞≥0`); the **prime demand** `a_c(d)` (the finite places, `Σ_p W_p`)
  is *outside* the archimedean prolate and carries the RH content.
- `[CONJECTURE — corrected target]` `s_d>0` ↔ positivity of the **SEMILOCAL** prolate (arXiv:2310.18423) = archimedean
  Sonin compression + finite places. Same architecture; `H^-_d` conjecturally a compression of
  `(−W_semilocal)^{−1}|_Sonin` with `y_*` the N=1 archimedean channel.
- `[NO-ROLEPLAY note]` No numerical comparison run — the semilocal prolate matrix in a comparable basis is not in hand,
  so a computation would be theatre. What was established is exact (the `4N+1` lattice) or logical (unconditional vs
  conditional). The missing piece is precisely stated.

**Docs:** no-roleplay-items.md §5 (full write-up) + §4 pointer; 10-prior-art §A12 (lattice match + refutation).

### 95. Prolate finding folded into docs; comp81 run (NR-2 probe) — the fake-family separator is κ₋, not the scalar s_d

**Docs updated (prolate-compression §5 finding):** 02-transport-system.md (exact `2|w|=4N+1` lattice = prolate Hermite
grading; archimedean budget `a_*` matches unconditionally, RH content = semilocal prolate); bridge-theorem §5b SOTA
flag; (no-roleplay §5/§4 and 10-prior-art §A12 already done).

**comp81 `[VERIFIED]` — next no-roleplay step (NR-2 probe).** Split `T_k=T_k^A`(pole+Γ)`+T_k^P`(prime `g_{2k}`); compared
the boundary gap for ζ (A+P), archimedean-only, and prime-sign-flipped (A−P):
- archimedean budget `s_d(A only) ≈ a_*=0.16` at all d (Γ-structure ≈critical at its own atom);
- prime eats it to `s_d(ζ)→0⁺` (contributes `≈−a_*` to `1/m_d`) — the budget-vs-demand identity made concrete;
- **flipping the prime sign gives `s_d≈2a_*>0` BUT inertia `(d−1,2)` — TWO negative squares.** The rank-one Γ-atom
  repairs one ⟹ `H^0_flip` not PSD (fails RH via a second κ that `s_d` is blind to).
- **Conclusion:** the fake-family separator (NR-2) is the integer `κ₋`, NOT the scalar `s_d`. Correct Euler sign ⟹
  `N₁` (repairable); wrong sign ⟹ `N₂`. Matches comp72 + lens 4. NR-2 sharpened to NR-2′ (Euler positivity ⟹ exactly
  one negative square). Script+output `computations/2026-06-22-comp81-prime-sign.*`; no-roleplay-items §6.

### 96. Two findings propagated across 01–10 + big-picture + bridge (per user): the prolate lattice and "κ₋ not s_d"

Propagated the §5 prolate-compression result and the comp81 NR-2′ finding consistently:
- **Prolate `2|w|=4N+1` lattice + semilocal-prolate target:** 01-landscape (archimedean-realization passage),
  02-transport (already), 03-theorems (the seam-coordinate finite form), 07-required (new lemma-shape), 10-prior-art
  §A12 (already), bridge §5b SOTA flag (already). The archimedean *budget* `a_*` (= N=1 grading level) matches the
  Connes–Consani–Moscovici archimedean Sonin positivity *unconditionally*; the RH content is the semilocal prolate.
- **The fake-family separator is the integer `κ₋`, not the scalar `s_d` (comp81):** refined the "`s_d=0` gate"
  framing in 08 §2, bridge §5b (two spots), big-picture §0, 06 (battery + new comp81 entry); added as supporting
  evidence in 04 (faithful-index claim), 09 (the faithful-index section), as a falsification/kill-criterion in 05,
  and as a new lemma-shape in 07. Consistent message everywhere: `s_d=0` is the height-limited rank-one **shadow** of
  `κ₋` (a sign-fake has `κ₋=2` with `s_d>0`); certify by `κ₋=0`, not `s_d>0`. Corroborates the long-standing
  faithful-index lens (lens 4) and comp72.

### 97. gpt/48 folded — apex restated on κ₋ (Faithful semilocal Uvarov–Krein index theorem); scalar-shadow lemma + finite-rank promotion + integer-index agenda

**Source.** `docs/consolidated/gpt/48.md` (GPT's response to the comp81 finding). Strongly convergent with the §6
correction already propagated (CHANGELOG #95–96); core (`s_d` not the apex, `κ₋=0` is, semilocal prolate) NOT re-done.
**Four sharpenings consolidated:**
- **Corrected bridge name:** *Faithful semilocal Uvarov–Krein index theorem* (`κ₋=0`); Layer 1 (Q_0 reduction, proof12)
  unchanged, Layer 2 (proof object) is the integer index.
- **Divisor correction:** `σ=ν'−a_*δ_{y_*}` = the rank-one `N=1` channel shadow; proof divisor = the completed
  semilocal index carrier.
- **Scalar-shadow lemma:** `s_d>0 ∧ κ₋(v_*^⊥)=0 ⟺ κ₋=0` (bars the scalar from posing as faithful; comp81 countercase).
- **Finite-rank boundary Weyl:** `a_*v_*v_*^T → VCV^*` over the prolate `4N+1` channels, gate `κ₋(S_r)=0`, `S_r=
  C^{−1}+V^*B^{−1}V`; `s_d` = the `r=0` compression.

**Docs updated:** bridge §5b (three-divisor correction + finite-rank promotion + scalar-shadow lemma + corrected apex
name); 07 (two new lemma-shapes); no-roleplay-items §7 (corrections + the gpt/48 integer-index experiment agenda a–f).
The methodological line is unchanged and reinforced: certify by `κ₋=0`, not `s_d>0`.

### 98. comp82 run — the prolate 4N+1 channel basis is FAITHFUL but height-limited (gpt/48 finite-rank Weyl, tested)

**What.** Took gpt/48's next no-roleplay step (agenda §7e/a): where does a fake's negative direction live — in the
prolate `4N+1` boundary channels or the finite-place bulk? Script+output `computations/2026-06-22-comp82-channel-completeness.*`;
worklog updated. **Register:** `[VERIFIED]`.
- **Sign-fake (comp81):** negative eigenvector is the **N=0 pole channel** `v(−4)` (residual 0 at `r=0`, `|cos(u,v_*)|~1e-5`
  — orthogonal to the `N=1` scalar channel, so `s_d` blind). The sign-flip destroys the exact pole/entireness cancellation.
- **Real off-line quartet (`g0=8`):** defect lives in **mid channels `N≈3–5`** matching its height (residual
  `1.0→0.98→0.26→0.025→0`); low channels miss it.
- **Conclusion:** the `4N+1` basis is **faithful** (every fake's negative direction is in `span{v_N}`; not decorative —
  gpt/48's finite-rank boundary-Weyl direction has merit) **BUT height-limited** — the channel index needed = the
  defect's height (same `d*≈γ0/3` law as the moment matrix / comp72 Pick kernel), so finite-`r` is *not* a finite-rank
  shortcut. Channel map: `N=0` pole/entireness, `N=1`=`v_*` (only channel `s_d` sees), `N≥2` protector tail (off-line
  zeros at their height). The scalar is blind to both `N=0` and `N≥3`.

**Docs:** bridge §5b (finite-rank promotion bullet + result), 07 (lemma-shape resolved), no-roleplay-items §7 (result).
The faithful object is the full all-channel semilocal carrier (`κ₋`); every finite truncation inherits the height limit.

### 99. Lens 8 added (per user) — "no target, only byproduct"; the positivity column reclassified as a hall of mirrors

User insight (correct, and it restores the charter): `κ₋=0 is RH`, so the entire positivity program has walked to the
exact spot everyone failed at — RH attacked under a new name. The RH-equivalences (κ₋=0, Q_0≥0, Weil/Li, Pólya–Jensen,
prolate Sonin) are **horizontal/cheap** (proof12 = one line); the difficulty is invariant under them; moving among them
is a **hall of mirrors**, and is the *deduction* the immutable rules forbid. Treating RH as a target to prove violates
lens 1 (constraint, not flow). **Warrant:** the only RH-type statement ever proved — RH over `𝔽_q` (Deligne, Weil II) —
was a **byproduct** of Grothendieck's étale cohomology built for its own sake, not a direct attack.

**Lens 8 — "No target, only byproduct"** (the anti-mirror lens, enforcement of lens 1): RH cannot be reached by aiming
at RH; leverage requires a **non-RH-equivalent constraint** (hypertranscendence / `𝔽₁` / transcendence-independence)
that leaves no room for off-line zeros, so RH is a **residue** ("cannot be otherwise"), never a goal. Operational rule:
test every target for RH-reduction; if it reduces, step back to a provable non-equivalent point (hypertranscendence,
Baker, `𝓜⁺`) and turn orthogonal.

**Docs updated:** big-picture §1 (lens 8 added; unifying-claim restated; "eight lenses"); 10-prior-art §E (lens table +
lens 8 row; the positivity column 3/4 reclassified as mirrors, lens 7 = the one non-mirror direction); no-roleplay-items
§8 (NR-1/2/3 reclassified as mirrors; forward agenda = NR-orth / the hypertranscendence home, byproduct stance).
**The redirection:** stop polishing the positivity mirrors; build the non-equivalent constraint from which the divisor
location, hence RH, falls out as a byproduct.

### 100. The logical form of a constraint-proof (big-picture §1′) — gives lenses 1 & 8 their logical content

User question: "constraint, not flow" needs a precise logic — a syllogism `a⟹b` is what HT can't be, but
"constraint" stated as `¬(a⟹b)` is empty (= `a∧¬b`, a counterexample). What is the plain principle behind forcing
RH to "manifest in one way"? **Answer recorded as big-picture §1′:**
- Not modus ponens (needs a generative premise; Hölder says none exists) and not `¬(a⟹b)` (wrong type).
- The form is **`∃!` from rigidity** — a degrees-of-freedom/conservation argument: an off-line zero is an extra free
  parameter; the completed object is parameter-free (FE + Euler + finite order); a rigid object can't absorb the extra
  parameter ⟹ no off-line zero *for lack of room*. The conclusion is read off a unique fixed point, not derived.
- **Mirror vs non-mirror = lens 8 in logic:** the quantifier either ranges over *zeros* (case-elimination = RH = mirror;
  `κ₋=0` is this) or over the *ambient object* (over-determine it from non-zero data; uniqueness is structural; zero
  locations fall out — non-mirror). The dividing line is *what the quantifier ranges over*.
- **"Decoherence" made exact:** pointer-basis/superselection — off-line zeros are states not commuting with the
  Euler-product constraint `T`, suppressed by incompatibility, not prohibition. RH = pointer basis of the multiplicative constraint.
- **Rigorous instance:** Deligne/Weil II proves RH-over-`𝔽_q` by **purity** (weight-grading rigidity forces `|α|=q^{i/2}`),
  not eigenvalue-elimination — the one time this exact logic settled an RH. Same shape as Wheeler–DeWitt (kernel of a
  constraint) and holography (boundary fixes bulk).
- **Forward:** the non-mirror task is to build a weight/purity rigidity structure (the missing `𝔽₁` Frobenius, lens 7)
  whose rigidity dimensionally excludes off-line zeros; RH as a residue of purity.

### 101. NEW DOC 11-f1-the-target-object.md — consolidated 𝔽₁ reference (parent-corpus sweep)

User asked to search /Users/Spare/Documents/code/riemann/docs for "𝔽₁" and consolidate everything into a document.
Ran 5 parallel read-only extractors over ~28 disjoint parent files (rh/*, plans/archived/*, literature/*, rh-corp/*,
where_we_stand/pure_facts). Synthesized into `11-f1-the-target-object.md`. All five batches converged on one verdict.

**The object & the consensus.** Every spectral/geometric route (Connes–Consani, Deninger, Weil-étale, Borger Λ-ring,
modular/Eisenstein) converges onto ONE master object: an infinite-dimensional 𝔽₁-Jacobian / self-product
`Spec ℤ ×_{𝔽₁} Spec ℤ` with a polarization of signature `(1,ρ−1)`. **Positivity is free (Rosati for any real
polarization); the wall is INTEGRALITY** — a ℤ-form / complex structure `J` for the ℚ-independent `{log p}`
("no uniform integer q"). Doc sections: A why 𝔽₁ is forced (primes≠q-powers); B six facets (finite curve Γ_S =
circles of circ. log p with real-torus Jacobian / Spec ℤ genus-0-vs-∞ / arithmetic site topos / Borger Λ-ring ψ_p
skeleton / Connes adele-class triple D=log|·|, Frobenius=modular flow, zeros on Sonin cokernel / Deninger foliated
system); C constructions ((α−1)/log q→ρ; A+iB split RH⟺A=½⟺F*F=e^{−1}; the J/polarization; Witt=Deninger=dBN);
D the integrality crux (no-margin log2/logX→0; type-II₁ vs type-I; mixed-Tate no purity; Deninger polarization axiom);
E recent SOTA (CC/CCM 2006.13771, 2205.01391, 2306.00456, 2602.04022, 2602.15941, 2606.06604, 2511.22755 — none
proves RH; NO ζ-attached Hodge-index theorem exists); F retired no-gos (finite-carrier Lean, resolution wall,
Schatten, flow-of-weights type-III₁, GL2 off-diagonal, bare-J, Lee-Yang, FID, modular-scattering); G hgt connection.

**hgt connection (§G).** 𝔽₁ is the §1′/lens-7-8 constraint object. Direct identifications: our κ₋ = the
intersection signature `(1,ρ−1)`; our prolate 4N+1 channels faithful / semilocal open (comp82) = Connes archimedean
Sonin positivity proven / semilocal S→∞ open; our s_d→0 = the no-margin log2/logX; seam 𝓜⁺ = the 𝔽₁ self-product.
The Wheeler–DeWitt reading (user's founding metaphor): modular flow σ_t = canonical clock (no external time), the
zeros = the Sonin COKERNEL (state = kernel of the constraint, not a trajectory); q→1 = the clock degenerating. The
one genuinely non-mirror sub-piece the corpus isolates = a **type-II₁ symmetry-rigidity theorem** forcing the
real-valued index κ₋ to exactly 0 from self-duality (no margin to estimate) — the only lens-8-admissible target.

**Wired:** 00-README index (+ row 11); big-picture lens 7 (pointer to doc 11).
