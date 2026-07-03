# MWM computation campaign — pre-registered

Purpose: every computation below can produce an **early fail** (kill a mechanism/invariant
before months of theory), a **new lead** (defect dynamics we haven't imagined), or
**encouragement** (the discriminant behaves as the family picture predicts). Per the
anti-theatre rule, each run has a pre-registered prediction written BEFORE execution; a run
whose outcome theory already fixes is banned (exception: R1's engine validation, labelled as
validation, not science). Nothing here can falsify RH_{2^k} for ζ itself (that would need an
off-line zero); the computable falsification surface is the FAMILY (§7 of 00-approach.md) and
the mechanisms M1–M3.

## Environment (verified 2026-07-03)

- Pod: `ssh root@157.157.221.30 -p 28997 -i ~/.ssh/id_ed25519` — 32 cores, 124 GB, load ~0,
  `python3.13` + mpmath 1.4.1 (default `python3` is 3.8 WITHOUT mpmath — always `python3.13`).
  Workdir `/root/mwm`. Filter ssh post-quantum stderr noise. Chunk every run; nohup + poll;
  never block; archive to `computations/mwm/` in this repo.
- Every script self-checks: (a) verify the implemented function's FE numerically at random
  points before trusting zeros; (b) carry a cross-check column (e.g., winding vs direct
  argument variation at doubled precision).
- Engine scaffold: adapt the rectangle-contour winding pattern from
  `computations/2026-06-21-conway-STEP12-c2-zero-winding-battery.py` (+ its canalization
  companion) — pattern only; the numpy finite-model stack is precision-inadequate for zero
  certification, rebuild in mpmath (audit F9).

## The test objects

- **ζ** — positivity ✓ FE ✓ (validation only).
- **Davenport–Heilbronn f_DH** — FE ✓, positivity ✗, off-line zeros BANKED in the parent
  ledger with the witness `s ≈ 0.808517182456637386 + 85.6993484853775922i` (pure_facts,
  audit F1). Implementation: χ = character mod 5 with χ(2) = i;
  f(s) = ((1−iκ)/2)·L(s,χ) + ((1+iκ)/2)·L(s,χ̄), κ = (√(10−2√5) − 2)/(√5 − 1);
  coefficient stream a_n = Re((1−iκ)χ(n)), residue pattern [1, κ, −κ, −1, 0] mod 5 (banked,
  `rh/dh_multiplicativity_fake_gate_20260614.md` — includes the finite non-multiplicativity
  witness a_2·a_3 = −κ² ≠ 1 = a_6);
  L(s,χ) = 5^{−s} Σ_{a=1}^{4} χ(a) ζ(s, a/5) via `mpmath.zeta(s, a/5)` (Hurwitz).
  Script still verifies the FE numerically first (implementation self-check); the banked zero
  is the second engine test point.
- **Pencil** g_c = c·L(s,χ) + (1−c)·L(s,χ̄), c ∈ ℂ arc through the D–H point — the
  deformation family (all members share the Γ-factor ⟹ FE-type symmetry for suitable c).
- Winding engine: w(box) = (1/2πi)∮ g′/g via argument tracking along the rectangle
  boundary (adaptive refinement until consecutive-point phase steps < π/2), g′ by term-wise
  Hurwitz derivative. Integer output with |raw − round| < 10⁻⁶ acceptance.

## Runs

### R1 — engine validation (VALIDATION, not science)
Boxes [−1, 2] × [T, T+5] for T ∈ {10, 50, 100, 500}: winding must equal the known ζ zero
count (`mpmath.zetazero` cross-check). Also unit-test on ξ-values: ξ(0) = ξ(1) = 1/2.
Exit: engine trusted. Failure = bug, fix before anything else.

### R2a — D–H parity certificate (RE-CUT per audit F1: existence is banked, don't re-discover)
**Question:** what winding does the BANKED off-line zero (0.808517…+85.699348…i) carry — and
the other zeros in t ≤ 200 — odd or even?
**Pre-registered prediction:** winding +1 (odd/simple) at the banked zero and at the sweep's
finds. (Simplicity is the generic expectation, so the certificate leans validation-grade; the
run doubles as engine cross-check against an 18-digit ledger value and produces the seed list
for R2b/R3, which carry the scientific weight.)
**Early fail if any defect is even:** parity would behave unexpectedly in the fake family —
re-examine the ladder invariant before Arc B investment.
Method: verify the banked zero (winding on a shrinking box around it, 30→60 dps), then the
sweep (σ ∈ [0.55, 1.2]) × (t-windows of height 2, t ≤ 200) purely as seed-list generation.
Chunks of 25 windows.

### R2b — D–H defect-recurrence statistics (mechanism M2 stress test)
**Question:** is the level-1 defect indicator w₁(T) of f_DH (boxes σ ∈ [σ₀, 1.2],
σ₀ ∈ {0.55, 0.6, 0.7}, height H = 2) recurrent — positive empirical density with structured
(quasi-periodic / bounded-at-sample-scale) gap statistics — over t ≤ 5000 (chunk: 500-tall
blocks)?
**Pre-registered prediction:** positive density and structured gaps (the FE + almost-periodic
ambient forces recurrence even without positivity).
**Reading:** matches → encouragement for the Reduction picture (defects in an FE family DO
recur; ζ's emptiness right of the line is then the Euler-positive rigidity, exactly the
family picture). **Early fail for M2:** defects of vanishing density / a lone non-recurrent
defect — an FE object whose ambient does NOT force recurrence; M2 needs more than
FE-almost-periodicity, name what.
Literature guard (check #8): before interpreting, verify what is proven about the density of
D–H off-line zeros (recalled: positive proportion — verify); if the density is a known
theorem, the DENSITY part of this run is theatre and only the GAP-STRUCTURE statistics
(recurrence geometry, autocorrelation) are the scientific output — restrict claims to those.

### R3 — pencil deformation: defect collisions and ℤ/2 charge dynamics
**Question:** as c walks an arc through the D–H point, how do off-line defects move, pair,
and collide? Do winding-2 (even-defect) members exist at isolated parameter values, and is
total charge mod 2 per region conserved between collisions?
**Pre-registered prediction:** defects move continuously, collisions (winding 2) occur at
isolated c (codim-1), charge mod 2 per tracked region is conserved between collisions.
**Reading:** this is the lead-generation run — the deformation dynamics of ℤ/2 monodromy
charge in an FE family is the family picture's §7(iii) made concrete; any unexpected
behavior (charge non-conservation = zeros entering/leaving through the line or the box
walls; pinned defects that refuse to move; collision loci with structure) is a new object
for the theory. Encouragement: a clean "defects are charged particles, FE is the arena"
phenomenology. **Ledger alignment (audit F3):** proof_shape ~5197 states the surviving
route's need verbatim — describe the zero fiber and show "fake families producing
unsanctioned linking"; R3 is the first systematic collection of exactly that linking data,
so its output is parent-ledger-relevant regardless of which way the phenomenology falls
(mailbox-worthy if it passes the novelty gate).
Method: fix the 3 lowest R2a defects; grid c along [0,1] + small imaginary detours (24
values/chunk), track each defect's box, refine adaptively; log (c, ρ(c), winding).

### R4 (optional, run only if R2/R3 produce momentum) — three-way orbit comparison (RE-CUT per audit F7)
Banked frame (object_x ~256): the GAF model is EXACT for log ζ's marginals yet has positive
off-line zero density; the zero functional is discontinuous under the Gaussian limit. So
marginal comparisons are banked theory (asserting them numerically = theatre). The ONLY
non-banked cell: **extreme statistics, deterministic orbit vs Haar-random Euler ensemble.**
**Question:** at σ = 0.75, is min_{t ∈ window} |ζ_X(σ+it)| (p ≤ X, X ∈ {10³, 10⁴, 10⁵})
distributed as the random-ω ensemble min |∏_{p≤X}(1−ω_p p^{−σ})^{−1}|? (GAF surrogate column
computed only as a reference axis, not as a claim.)
**Pre-registered prediction:** indistinguishable from Haar-Euler (the orbit is generic for
the extreme statistic where it matters). **Lead if not:** a named statistic where arithmetic
beats Euler-genericity — direct input to M1/C4 and to the ledger's multiplicative-cumulant
picture.

## Bookkeeping

- Results → `computations/mwm/rXY-<name>/` (script + raw output + one RESULTS.md per run
  stating: prediction, outcome, verdict line early-fail/lead/encouragement/null).
- Worklog tick per run in `logs/rh-mwm-worklog.md`. Findings that pass the novelty gate →
  chat/mailbox; dead ends → worklog only.
- Any run contradicting its prediction is a FINDING (not a failure): write it up before
  moving on.
