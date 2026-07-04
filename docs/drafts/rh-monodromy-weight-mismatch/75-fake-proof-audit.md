# 75 — The Fake-Proof Audit: RH₂ Walked End-to-End, and Where It Lies

**Register: SEARCH** (task #21; the attack-as-false at chain scale,
triggered by the anti-theatre challenge). Method: write the RH₂ proof as if
every sketch were done; mark each link; find the sentence that lies. The
verdict is at §5; it is neither "route sound" nor "route dead".

## 1. The chain, walked

| # | Link | Status |
|---|---|---|
| 1 | RH ⟺ ∀k RHLadder(k) | **Lean** ✓ |
| 2 | RH_{2^k} ⟺ (WR_k): D(W) ≡ L(W) mod 2^{k+1} | elementary ✓ (doc 18) |
| 3 | D-transport under domination (Rouché) | **Lean** ✓ — `seam_transport_ladder`; on the concrete carrier `anneal_deck_transport` (ZetaCarrier.lean), analytic residues typed as `AFEAccurateOn`/`CarrierFloorOn` |
| 4 | **L-transport (seam side)** | **Lean** ✓ (2026-07-04, `SeamSignTransport.lean`) — k=1 seam datum = (K1) sign product; transports under domination at the TWO on-line basepoints alone; capstone `anneal_seam_L_transport` on the concrete `completedGN` (doc 22 §8) |
| 5 | Self-domination replaces ζ-domination (E(T) explicit) | ✓ (doc 43 §1 + doc 71's numeric R–S) |
| 6 | Shallow odd pairs (η ≤ η₀ ~ T^{−1/8}) self-exclude via their own moat | lemma-shape ✓ (doc 43 §2) — but note: self-exclusion means UNREADABLE, not refuted; the RS tower shrinks η₀, it does not kill the band |
| 7 | Very deep pairs (η ≥ η₁ = O(1)) excluded absolutely | ✓-sketch (leading-coefficient first-moment bound; works for D–H too, consistently — D–H's zeros live below η₁) |
| 8 | Walk/kill tier (births die off-resonance) | **Lean = counting shell only**: `MidCentralInput.dip_kills`, `.creation_rate` are hypothesis FIELDS; discharge for the actual carrier = (T1) [execution] + **(T2)-general [simplicity/Rouché counts: hypothesis-typed in general — doc 54 §3 says so]** |
| 9 | Creation density at resonance (p-central budget) | the docs 56–74 arc: asymptotic ✓-sketch (transfer + Selberg); finite-height gap (3e12, 10^21) = (EQD) |
| 10 | Cofinality (C1/C2) | ✓-sketch (docs 59 corr., 70 §3) |
| 11 | **The contradiction step** | **THE LIE IS HERE — §2** |
| 12 | k ≥ 2 rungs ((HANK-fin)) | untouched |

*(Table updated 2026-07-04: links 3–4 upgraded — the carrier is now CONCRETE in Lean
(ZetaCarrier.lean: `gN`/`completedGN`, exact FEs, order equivariances, domination
cancellation) and BOTH window-relation transports are machine-checked on it; link 4's
15-cycle wiring gap is closed, discharging §5's executable (3). The (ID)-assembly of
links 2+3+4 is ALSO banked (`AnnealWindowRelation.lean`: `anneal_mod_two_window_relation`,
N_ξ ≡ N_g mod 2 from level-4 boundary congruences, (ID)s derived not assumed; the hL
mod-4 lift is finite-side-computable, NOT boundary-transportable — `deckClass_blind_to_split`);
§2's (XLD) core and links 8/9/12 are unaffected.)*

## 2. The located lie: density cannot kill a single zero — and the mechanism that could is not banked

A putative odd ζ-pair at FIXED (η, t\*) forces, by Rouché under domination,
a matching carrier pair in EVERY dominated carrier — and the sharp-cutoff
AFE tolerance allows ~δ√n consecutive tower levels g_{n±j} to dominate at
t\*. So the single zero MULTIPLIES: it forces births at ~J ≫ 1 consecutive
levels, all pinned at (η, t\*), all kill-exempt (Rouché keeps them alive).
The intended contradiction: forced presence at J levels vs (kill tier ×
creation budget) allowing presence ≪ J. This CAN kill a single zero — the
architecture is genuinely sound in shape. But walking it exposed three
holes, in increasing severity:

- **(H1)** The level-multiplication accounting (forced births at
  consecutive levels enter the SAME ledger the budget bounds) is my
  reconstruction of docs 47–51; whether the banked cascade ledger actually
  implements cross-level forcing at fixed height must be VERIFIED against
  the walk-tier definitions — if it does not, the density tier is
  currently unconsumed.
- **(H2)** The walk/kill machinery operates at SLIVER depth (c/log N). A
  putative pair at fixed η sits above the sliver for all large N — in the
  MID-BAND η ∈ (sliver, η₁), where the forced structures are L²-deficit
  valleys and the only available statements are per-level DENSITY bounds.
- **(H3) The killer.** Per-level density does not contradict J-fold forced
  presence at a FIXED point: the per-level bad sets can simply align at
  t\*. The contradiction needs a JOINT statement across levels — "the
  deficit cannot persist at one height across J levels" — and that is a
  CROSS-LEVEL DECORRELATION input: the new primes entering between levels
  must scramble the deficit. Nothing in the lane proves it; no density
  technology can. **This is where Euler must act, and it is the same genre
  as (EQD)** — multiplicative-independence/equidistribution across scales.

## 3. The D–H filter, run through the assembled chain

D–H has genuine off-line zeros; its truncations inherit matched pairs by
the same Rouché forcing; the counting shell, the moat geometry, the
first-moment deep exclusion, and the level-multiplication all apply to D–H
verbatim. So the chain MUST discriminate at exactly one place — and it
does, consistently: **the cross-level decorrelation (H3) + the creation
budget are where Euler enters.** For D–H the deficit-persistence at its
actual zeros is REAL (its new "primes" fail to scramble — no Euler
product), and its creation density is floor-inflated by its own zeros.
The filter passes ARCHITECTURALLY — the discriminator is quantitative
(ε vs kill-rate; scrambling vs alignment) — which retroactively makes the
finite-height constants war load-bearing IN PRINCIPLE. But the filter also
sharpens the indictment: since the discriminator is (H3)+budget, and (H3)
is unproven, the chain currently contains NO proven step that fails for
D–H. A chain that would "prove" the same for D–H proves nothing yet.

## 4. What survives, what was theatre

- **Survives as load-bearing:** the ladder/window/dictionary tier (Lean);
  the transfer + collapse (docs 70/72 — the carrier is canonical); the
  creation-density arc INCLUDING the constants war (it is one leg of the
  quantitative discriminator); the thickness counting; the measured
  statistics (restricted-Gaussianity, floor law) — these are the raw
  material for (H3).
- **Was drift:** treating the creation leg as "the single load-bearing
  item" (docs 69–74's framing) while links 4, 8-(T2), 11, 12 sat
  unexamined. The optimizer/Christoffel refinements beyond doc 73 §3 were
  polish on a subordinate constant.
- **Corrected claim for the ledger:** the lane's honest status is a
  REDUCTION MACHINE: RH₂ ⟸ (XLD) cross-level decorrelation in the
  mid-band + seam-transport wiring + (T2)-general + finite-height budget
  ((EQD)) + k≥2 rungs. The first item is the true open core and the only
  one that is not classical-shaped.

## 5. Verdict and the forward move

The route is not theatre in destination — the architecture kills single
zeros in shape, and the D–H filter locates the Euler entry point exactly
where the unproven core sits, which is what a non-vacuous route must do.
The walking order was the failure: fifteen cycles on the best-lit leg. The
named core is now:

> **(XLD):** for the matched truncations g_n, the L²-deficit (equivalently
> mid-band forced-pair) events at a fixed height cannot persist across
> ~δ√n consecutive levels: the primes entering between levels scramble the
> deficit at a rate beating the per-level density. Euler-specific;
> (EQD)-genre; refuted-by-construction for D–H — the first statement in
> the lane with that property.

Next executables, in force order: (1) verify (H1) against the banked
cascade ledger (a reading task, hours); (2) state (XLD) precisely at two
consecutive levels (the n → n+1 update adds ONE term (n+1)^{−s} + mirror —
the minimal scrambling question, concrete and finite); (3) the seam-transport
wiring write-out (link 4, classical-shaped, overdue); (4) only then resume
any constants work.

## Addendum (2026-07-05, task #25): table row 5 upgraded

Row 5 (self-domination with explicit E) is now UNCONDITIONAL at EM grade in
Lean: `EMCarrier.lean` proves ζ = emCarrier N − s·emTail N on
{re > 0} \ {1} with the machine-checked remainder ‖s·emTail‖ ≤ ‖s‖N^(−σ)/σ,
discharges the (AFE) interface, and supplies the seam/deck `hdom` premises.
The R–S-grade residue is relocated into (EM-CLOSE) — a finite-vs-finite
comparison ‖emCarrier M − gN N‖, no ζ in it. Details: doc 78.
