# 57 — What the Bridge Actually Charges creation_rate: the Budget Audit

**Register: SEARCH** (task board item: quantitative-demand audit of (R3)).
Question: does the consumer of `creation_rate` need doc 52 §4's full limit form
ε(c) → 0, or less? Sources read: `MidCentral.lean`, `DipKillsWiring.lean`
(typing), docs 43 §8–9, 47–50, 53–54 (bridge semantics), doc 53 §3 (DEEP-FATE
measurements). Verdict in §4: **three tiers; the limit form is the luxury tier.**

## 1. The formal consumer takes K raw

`MidCentralInput` (MidCentral.lean:71) carries `creation_rate :
(resonantBirths …).length ≤ K` with `K : ℕ` free, and every downstream theorem
(`midCentral_survivors_le`, `…_of_carrierData`) outputs `survivors ≤ K`
verbatim. **No limit, no rate, no ε enters the machine-checked skeleton.** The
ε(c) → 0 typing of (CR-density) was chosen at doc 52 §4 as the natural
classical-shaped statement, not extracted from a consumer budget. The budget
lives one level up, in how (SD-parity)'s window traversal spends the survivor
count. That arithmetic is audited here.

## 2. The traversal geometry: slip bands are BLOCKS of length ≍ N

p(T) = frac √(T/2π) has dp/dT = 1/(4π(N+p)): the RS phase is locally constant
on unit scales. The slip window {d(p) ≤ 0.194} is therefore a union of
contiguous height-blocks of length ≈ 4πN·0.39 ≍ N, alternating with p-central
blocks of length ≍ N. Consequence: a single parity window whose interior spans
a slip block inherits the block's ENTIRE survivor population — expected
(block length)·(measured rate ~10⁻³) ≍ N·10⁻³ objects, each contributing odd
local parity (a survivor pair = one right-half zero). A tall-window traversal
would need the parity of that population: not controllable by any rate bound.
**So the traversal must be local** — isolate a putative odd ζ-zero by a SHORT
self-dominated window — and the load creation_rate carries is per-window
finiteness plus localization, not a global census.

## 3. Two structural facts the audit surfaced [new to the lane's ledger]

**(a) The transport dichotomy prices deep survivors.** If a mid-band survivor
of the exact-FE carrier at height T has depth η with min_{∂D}|g| > E*(T) on
some contour D around its pair (available once η ≫ √(E*·‖H‖⁻¹-scale), i.e.
η ≫ T^{−1/8}·polylog), then Rouché TRANSPORTS the pair to ζ: two off-line
ζ-zeros. [REDUCTION — contrapositive of banked #134/#136-grade transport.]
So: **RH ⟹ survivor depths shrink below the moat scale T^{−1/8}+ as T grows**;
persistent fixed-depth survivors would themselves refute RH per instance. The
census is consistent with onset of shrinkage (max η: 0.178 at T ≤ 1.2·10⁴,
0.133 in [2·10⁴, 3·10⁴)). The bridge should EXPLOIT the dichotomy rather than
fight it: every survivor is either shallow (digs its own moat, self-excluded
from parity windows by MOAT-shallow — doc 43 §6) or deep (per-instance
transport contradiction available). The residual band between the two scales
is exactly what (MID-central) must empty — nothing NEW is charged to
creation_rate by this reading, but the depth cutoff it must control is the
MOVING scale √(E*/‖H‖), not a fixed c.

**(b) The level-shift dodge [CONJECTURE — promotes P-DF3 to load-bearing].**
Survivors are ephemeral in the LEVEL index: doc 53 §3 measured resonant
survivors alive for exactly one entry epoch (on-line at N−1, pair at N,
reabsorbed at N+1). Consecutive-level carriers differ by one term,
|Φ_{N+1} − Φ_N| ≍ 2N^{−1/2} ≈ E(T)-order (the weld/seam constant — marginal,
per-instance checkable). IF (EPH) ephemerality holds as a theorem and
two-level domination holds off the union of the two moat systems, THEN every
height admits an isolating window at one of two adjacent levels: the moat of a
level-N survivor is not a moat of the level-(N±1) carrier at the same height.
**The traversal then never consumes the count K at all** — only ephemerality
plus a per-instance domination margin. Typed:

> **(EPH) [lemma-shape, new]:** every resonant birth of the cascade at level k
> is reabsorbed by level k + C·N^{1/3} (measured clock: ≈ 3.3·N^{1/3}, doc 53
> §3); in particular no height carries survivors of two consecutive matched
> levels. Proof material: the deepen-saturate-die arc = drift rotation out of
> the frozen window (banked `perturbed_rotation_dip` budgets) + the η ≈ k^{−1/4}
> saturation ceiling (doc 53 §4(3)).

## 4. Verdict: the three-tier budget

- **Tier 1 (sufficient; current typing).** ε(c) → 0 as c → 0 — the doc 52 §4
  form. Doc 56 delivers ε(c) = O(√c) conditional on (K-bdd) + (K-mild).
- **Tier 2 (sufficient with one constant made explicit).** A single pair
  (c₀, ε₀) at the slip-budget scale, with ε₀ under the deck-relation margin.
  The missing piece is not analytic but ARITHMETIC: the (SWEEP-margin) budget
  of docs 46 §5/51 §5 has never been written as an explicit inequality
  "K per window ≤ ⌊margin⌋". Until that write-out exists, Tier 2 is
  plausible-but-unpriced. [Next executable: extract the margin constant from
  doc 51 §5's quadrature/hold ratio.]
- **Tier 0 (possibly sufficient; dissolves K).** (EPH) + level-shift dodge
  (§3b): creation_rate degrades to per-window finiteness (automatic — zeros
  are locally finite). Everything then rides on ephemerality and per-instance
  domination — both perturbation-grade, no density theorem at all.

**Effort allocation consequence.** The kernel attack (doc 56 §5) stays primary:
it serves Tiers 1–2 and is the only route that also upgrades doc 55's (AC).
But (EPH) is promoted from "measured support" to a typed lemma target — it is
perturbation mathematics (the lane's home ground, banked walk-tier tools), and
if it lands, the (R3) budget collapses to Tier 0 and (CR-density) exits the
critical path entirely. That is the cheapest conceivable closure of
(MID-central) and nobody had typed it.

## 5. What this opens

1. Write the (SWEEP-margin) budget inequality explicitly (prices Tier 2).
2. Attack (EPH) with the banked walk tier: the reabsorption clock is
   first-passage of the drift-rotated walk from the saturated ceiling — the
   same `drift_dip_excursion` machinery pointed at the level index instead of
   the entry index.
3. The transport dichotomy (§3a) invites a per-instance Lean card: "deep
   survivor ⟹ ζ pair" as a checkable Rouché certificate — the contradiction
   half of the bridge, formalizable against the #136/#140 interval technology.
