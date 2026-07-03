# Prior-work audit (parent lab + hgt corpus) — what it changes in 00–03

Audit run 2026-07-03 over `riemann/docs`, `riemann/logs`, hgt docs/computations, before
executing any Arc A / campaign task. Verdict: **Arc A survives unchanged** (no prior Lean or
paper work on the tower/ladder/root equivalences found anywhere in the corpus); **the mechanism
section and half the computation campaign needed re-cutting** against banked results. Findings
F1–F9 with anchors; amendments applied in place to 00/01/03.

## F1 — The D–H apparatus is already banked

- Off-line zero at 18 digits in the ledger: `s ≈ 0.808517182456637386 + 85.6993484853775922i`
  (`riemann/docs/where_we_stand/pure_facts.md` ~line 19–21, FAKE-FAMILY FILTER entry; FE +
  conjugation give the quadruple).
- Exact implementation data: D–H coefficient stream `a_n = Re((1−iκ)χ(n))`, residue pattern
  `[1, κ, −κ, −1, 0]` mod 5; finite non-multiplicativity witness `a_2·a_3 = −κ² ≠ 1 = a_6`
  (`riemann/docs/rh/dh_multiplicativity_fake_gate_20260614.md`).
- **DH-test is a mandatory lab gate** (mailbox `rh_agent_coordination.md` ~16350): every
  proposed lemma must NAME THE STEP THAT FAILS for a D–H-type object.
- MWM passes the DH-test structurally, and the failing step has a name: **the zero-density
  input of the Reduction (§5)**. Defect-recurrence can hold for D–H without contradiction
  because D–H is not covered by Ingham's ζ-density theorem (its off-line zero count need not be
  o(T)); for ζ the same recurrence collides with Ingham. The discriminator enters exactly where
  the family picture says it must. (Whether D–H's off-line density is provably ≫T is check #8 —
  NOT found banked; stays an external literature check.)
- Consequence: campaign R2a re-cut from "find D–H off-line zeros" (done, banked) to "verify the
  banked zero + compute its parity/winding certificate" — a validation-grade step; the
  scientific weight moves to R2b (defect time-series — no tall-range D–H survey found banked)
  and R3.

## F2 — Positivity is NOT the genuineness cut; DMV kills naive M3

hgt door bucket X5 (`docs/drafts/door/bucket-realization-and-fake-family.md`): genuineness is
the **Euler cut (A), not the positivity cut (P)**; the three cuts (E)/(A)/(P) are independent;
fakes live in (E)∧¬(A) and can satisfy Hankel-positivity. **KEY IMPORT (Diamond–Montgomery–
Vorhauer): Beurling systems — positive prime measures, hence Landau-positive logs — with
OFF-line zeros EXIST; off-line zeros are GENERIC in the moduli 𝓟 of positive prime systems.**
- Mechanism M3 as stated ("positivity forces parity/divisibility structure") is **refuted at
  the positivity-alone level** by this banked import (generic zeros carry no divisibility
  structure; residual sliver: DMV multiplicities are not explicitly banked as odd — but
  genericity makes simplicity the default). M3 survives ONLY as the conjunction FE ∧ positivity.
- Arc B re-cut accordingly: B2/L1's hypothesis class must include the FE; B1's hunt starts from
  DMV-type constructions and asks whether an FE can be grafted. The structural neighbor is the
  bucket's **realization problem #85** (does positivity ∧ genericity ∧ FE ⟹ Euler-realized?):
  if realization holds, the FE∧positivity∧¬Euler class is empty and the parity question
  collapses onto the Euler cut. Arc B is now explicitly a probe OF the realization problem
  from the parity side — a sharper, ledger-connected target than the original L1.

## F3 — Banked no-go: ambient Bohr-torus data is projection-blind (downgrades M2)

`pure_facts.md` ~9994–9998 and `proof_shape.md` ~5195–5197 (the lab's own universality-
falsification lane, killed 2026-06): finite prime-frequency models lift to a Bohr torus map
`F : T^k → ℂ`; **planar winding around 0 is NOT a property of the ambient torus flow — it is
linking data with the source zero fiber `F⁻¹(0)`**. Haar equidistribution, ℚ-independence of
`{log p}`, and torus cohomology are projection-blind. Zero-admitting universality via Rouché is
topologically blocked (separating loop ⟹ disconnected complement ⟹ outside Voronin). Also
banked: scalar-renormalized finite Euler packets are winding-trivial (stronger than 00 §4.1's
partial-product observation).
- **M2 downgraded:** "coarse Bohr continuity" cannot be powered by ambient almost-periodicity
  alone — that is precisely the banked projection-blindness. Any surviving M2 must inject
  source data (Euler stream, FE). The proof burden shifts to M1.
- The Reduction (§5) itself is untouched: it compares ζ against its own translates (Rouché
  between translates, no universality target, no separating-loop issue), and the banked kill
  was of the *falsification* direction (constructing off-line zeros), not the exclusion
  direction.
- proof_shape.md ~5197 states the surviving route's need: "describe the zero fiber for finite
  Euler-product models and prove that orbit-linking events are exactly sanctioned source
  collisions, **with fake families producing unsanctioned linking**." Campaign R3 (pencil
  deformation, defect linking events in the fake family) supplies exactly this data — R3 is
  upgraded from lead-generation to ledger-aligned need.

## F4 — Ledger already isolates the faithful invariant class (confirms the cocycle's seat)

`pure_facts.md` ~724–728: linear explicit-formula probes are β-blind; `S(T)` has Selberg-CLT
Gaussian statistics whose universal limit is RH-blind; **faithful detection must be
quadratic/signature OR global winding/index data**, with S(T) as the prime phase in the
argument-principle count.
- Confirms banked what 00 §6(b) conjectured ("expect: no classical parity-sensitive linear
  tests").
- Confirms the skipped S(T)-mod-2 statistics run as theatre (Gaussian limit RH-blind).
- The MWM cocycle w_k sits in the ledger's own faithful class (winding/index column). The lab
  worked the quadratic/signature column extensively (CCM/Weil–Gram, Q_W inertia with D–H
  replays showing negative inertia — `object_x.md` ~454–456; screw-hat PRWC certificates —
  `rh/rebel2_screw_hat_euler_prwc_certificate.md`); the **winding column mod 2^k is unworked**.
  MWM's novelty inventory adjusts: "faithful = winding" is banked; the mod-2^k grading, ladder,
  and recurrence mechanism remain the new axes.

## F5 — A formalized finite avatar of the winding count exists

`pure_facts.md` ~1403–1409: `sigNeg(scForm[P]) = #inside(P) = winding(P)` via the formalized
Schur–Cohn theorem + argument principle; the open gate is pollution-free `convergesToXi` on the
critical contour. The finite winding-count already has a machine-checked component (atlas
lane); mod-2^k reduction of THAT object is a candidate shortcut for the Arc A3 cocycle
formalization later — check the rh-formal-atlas publication before writing new Lean for
argument-principle counts.

## F6 — The "quantized winding charge" framing exists (Avila lens)

`pure_facts.md` ~2500–2506 + `rh/dyson_cocycle_curvature_lens_20260617.md`: Avila's
acceleration (quantized integer via zeros of determinants = winding) identified with the
faithful `κ₋` = Schur–Cohn inertia = argument-principle winding; RH as the d=∞ (∞-torus/Euler)
analogue of Avila's d=1 quantization; two named obstructions — multi-frequency (open even at
d=2) and long-range (not an SL(2) cocycle). The MWM cocycle is this same object family graded
mod 2^k; the two Avila obstructions are constraints any M2-type continuity argument inherits.
Cite; do not re-derive.

## F7 — Two random models, banked dichotomy (re-cuts R4)

`object_x.md` ~256: every statistic of the heights is transverse-blind; ℚ-independence ⟹
Selberg CLT ⟹ the Gaussian-analytic-function model is EXACT for log ζ's marginals, and its
Edelman–Kostlan off-line zero density is strictly positive (~ 1/(π(2σ−1)²)) — Gaussian
universality *spreads* zeros into the strip; **RH lives only in the extreme/zero functional,
discontinuous under Gaussian convergence, carried by the multiplicative cumulants**.
- Corrects 00 §4.3: "the orbit is generic for zero-freeness" is MODEL-DEPENDENT — generic for
  the Haar-random Euler product (a.s. nonvanishing, check #2, part in-house: Bohr–Jessen
  liminf|ζ|=0 used in `logs/rh_proof_quest_einstein.md` E5) but NOT for the marginal-exact
  GAF model. RH = the zero functional follows the Euler-random model, not the GAF model.
- R4 re-cut to a three-way design (deterministic orbit vs Haar-Euler vs GAF surrogate) whose
  only non-banked cell is the extreme-statistic comparison deterministic-vs-Haar-Euler right of
  1/2; marginal agreement with GAF is banked theory — asserting it numerically is theatre.

## F8 — The universality/recurrence lane has in-house history

`logs/rh_proof_quest_einstein.md` E4–E5 (2026-06-15): "RH ⟺ ζ-translates cannot approximate
any f WITH a zero in ½<Re<1 (Voronin non-vanishing = exact boundary)"; effective-universality
falsification attack; Euler product identified as the obstruction, weakest at the seam;
Bohr–Jessen positive density near 0. The lane was pushed in the falsification direction and
died on F3. Check #1 (Bagchi exact statement) remains external, but the in-house articulation
confirms the Reduction's engine is the corpus-known one — the mod-2^k coarsening and the
proof-direction use are the deltas.

## F9 — Winding compute scaffolding exists in hgt

`computations/2026-06-21-conway-STEP12-c2-zero-winding-battery.py` (+ canalization-c2-holonomy
companion): rectangle-contour winding/holonomy battery, numpy finite-prime-model stack, from
the wild-analogy web sessions. R1 adapts the rectangle/winding pattern to mpmath
high-precision Hurwitz-zeta L-combinations; do not rebuild blind, do not reuse the numpy stack
(precision-inadequate for zero certification).

## Net amendment table

| Item | Verdict |
|---|---|
| Arc A (tower/ladder/root Lean) | **unchanged** — no prior work found, anywhere |
| C1 Reduction | unchanged; DH-failing step now named (F1) — DH-test compliant |
| C2 Bagchi check | unchanged (external); in-house context noted (F8) |
| C3 index/parity tests | repositioned: quadratic column banked, winding column open (F4, F5) |
| M1 (weight mismatch) | now carries the main burden (F3) |
| M2 (coarse Bohr) | **downgraded** — must inject source data; ambient a.p. is banked-blind (F3, F6) |
| M3 (positivity) | **refuted as positivity-alone** (DMV, F2); survives only as FE ∧ positivity |
| Arc B | re-cut onto the FE∧positivity intersection; now a parity-side probe of realization problem #85 (F2) |
| R1 | adapt existing battery pattern to mpmath (F9) |
| R2a | re-cut: verify banked zero + parity certificate only (F1) |
| R2b | unchanged — no banked tall-range D–H defect survey found; check #8 external |
| R3 | **upgraded**: supplies the ledger's own stated need (unsanctioned linking data, F3) |
| R4 | re-cut three-way; only the deterministic-vs-Haar-Euler extreme cell is non-banked (F7) |
| S(T) mod 2 run | confirmed theatre (banked CLT blindness, F4) — stays dead |
