# 78 — Chain Link 5 Unconditional: the Euler–Maclaurin Carrier, Machine-Checked

**Register: LEDGER for §3 (Lean, proven through); SEARCH for §§5–7**
(task #25; doc 75 §1 table item 5 worked to its unconditional floor).

## 1. What item 5 was, and its debt

Link 5 of the RH₂ chain (doc 75 §1): *self-domination replaces ζ-domination
with explicit E(T)* — doc 43 §1's recast removing ζ from the bridge's
arithmetic input via the classical AFE bound |ζ − g_N| ≤ E(T) = O(T^{−1/4}),
made numeric by doc 71 (|R(t)| ≤ 1.463·t^{−1/4} + 0.127·t^{−3/4}, t ≥ 200).
Status before this cycle: architecture banked (`ZetaCarrier.lean` reduced all
deck/seam transport to the (AFE) accuracy + (LOW) floor interfaces), but the
accuracy CONSTANT was classical-cited — Gabcke/Hiary–Patel–Yang-grade
analysis, nowhere near formalizable. The chain's single ζ-input was a
citation.

## 2. The two carriers

The R–S matched length is not the only way to trade ζ for a finite object.

| | matched carrier `gN` | EM carrier `emCarrier` |
|---|---|---|
| length | N = √(t/2π) | any N ≥ 1 (need N ≳ t² for O(1) accuracy on the line) |
| accuracy | O(t^{−1/4}), numeric by citation | **‖s‖·N^(−re s)/re s, THEOREM** |
| structure | exact-FE symmetric (deck/ledger native) | plain sum + one pole term |
| debt | Riemann–Siegel analysis | **zero** |

`emCarrier N s := Σ_{n≤N} n^(−s) + N^(1−s)/(s−1)`. The representation

> ζ(s) = emCarrier N s − s·emTail N s,  ‖s·emTail N s‖ ≤ ‖s‖·N^(−re s)/re s

holds for every N ≥ 1 on the whole punctured half-plane {re s > 0} \ {1} —
elementary (per-interval partial summation + analytic continuation), with the
remainder bound an EXACT telescope, no asymptotics anywhere.

## 3. What is now proven in Lean [LEDGER]

`formal/GaloisForLFunctions/RHTower/EMCarrier.lean` — builds, umbrella 8638
jobs green, lint passed, all capstones axiom-clean
[propext, Classical.choice, Quot.sound]:

- `emTerm_key` — the per-interval identity (one zeta tail term, exactly);
- `emTerm_eq_integral`, `norm_emTerm_le`, `norm_emTerm_le'` — the closed
  form as `∫ (x−m)x^(−s−1)`, sharp telescoping bound, crude M-test bound;
- `norm_emTail_le` — ‖emTail N s‖ ≤ N^(−σ)/σ (exact telescope);
- `finite_em_identity`, `zeta_eq_emCarrier_of_one_lt` — the telescoped
  identity and its σ > 1 anchor against mathlib's zeta series;
- `differentiableOn_emTail` — Weierstrass M-test on the strip;
- `isPreconnected_emStrip` — the punctured half-plane from four convex
  pieces;
- **`zeta_eq_emCarrier_sub`** — the representation on {re > 0} \ {1}
  (identity theorem);
- **`zeta_sub_emCarrier_norm_le`** — the (AFE)-grade accuracy as a theorem;
- **`zeta_ne_zero_of_em_domination`** — unconditional zero-free certificate:
  wherever the finite side beats its own explicit remainder, ζ ≠ 0;
- **`afeAccurateOn_of_emCarrier_close`** — `ZetaCarrier.AFEAccurateOn S N
  (ε₁ + δ)` discharged from the EM bound (ε₁, machine-checked) plus
  `‖emCarrier M − gN N‖ ≤ δ` on S;
- **`completed_domination_of_em`** — the pointwise `hdom` premise of
  `anneal_seam_L_transport` / `anneal_deck_transport`, supplied the same way.

## 4. The wiring, and where the debt now lives

The consumers were already typed: `completed_domination_of_interfaces`
(ZetaCarrier §7) turns (AFE) + (LOW) into the `hdom` hypotheses of the seam
and deck transports. This module discharges the ζ-side of those interfaces
UNCONDITIONALLY. What remains of link 5's classical content is exactly one
named finite object:

> **(EM-CLOSE):** for windows S at height t and M ≳ t²-scale,
> ‖emCarrier M z − gN N z‖ ≤ δ on S — a comparison of two FINITE Dirichlet
> expressions (long plain sum + pole term vs matched symmetrized sum).
> No ζ, no analytic continuation, no unformalizable analysis: the entire
> R–S debt of the chain, relocated into Dirichlet-polynomial territory
> (stationary phase / Gauss sums on finite objects — hgt home ground).

Chain table update (doc 75 §1, row 5): **✓ UNCONDITIONAL at EM grade
(Lean, EMCarrier.lean); R–S grade = (EM-CLOSE) + doc 71's numeric constants,
now a finite-vs-finite statement.** No other row's status changes; the D–H
filter is respected — the EM representation holds for D–H's analogue too, so
this link (correctly) still does not discriminate; discrimination stays at
(XLD)+budget where it belongs.

## 5. What the EM carrier costs and buys

Cost: length. On the line the remainder is ~2|t|·N^(−1/2), so O(1) accuracy
needs N ~ t² — quadratically longer than matched; the ledger/deck arithmetic
(2^k tower, Kummer structure) stays native to `gN`, so the EM carrier is a
BRIDGE, not a replacement.

Buys, immediately usable:
1. **Per-point unconditional certificates.** `zeta_ne_zero_of_em_domination`
   turns any interval-arithmetic evaluation of a finite sum into a
   machine-checked ζ ≠ 0 statement — no external verification imported. The
   first fully-in-Lean zero-free window certificates of the lane are now one
   numeric evaluation away.
2. **`hdom` on demand.** For any window instance (e.g. the #136 certified
   t₂/m₂ run), the seam/deck transport hypotheses can be discharged by
   computing two finite quantities per point — `completed_domination_of_em`
   consumes them directly.
3. **The (AFE) interface is no longer a citation.** Any future consumer of
   `AFEAccurateOn` can route through `afeAccurateOn_of_emCarrier_close`
   and owe only (EM-CLOSE).

## 6. What this opens

1. **(EM-CLOSE) as a theorem target**: the R–S approximation restated as a
   finite-vs-finite inequality is a stationary-phase statement about
   explicit sums — formalizable in principle (Gauss-sum technology, the
   doc 49 §2 lattice again), and PRICEABLE numerically per window today.
2. **Certificate instrument**: wire a small evaluator (interval arithmetic
   on dirichletPoly + pole term) to `zeta_ne_zero_of_em_domination` and
   produce the lane's first end-to-end machine-checked window facts; then
   feed `completed_domination_of_em` to run one FULL seam-transport instance
   with zero unformalized inputs.
3. The connectivity + M-test + identity-theorem scaffold built here is
   reusable for ANY Dirichlet-type representation the lane needs on the
   strip (the mollified/tapered variants of docs 55–70 included).
