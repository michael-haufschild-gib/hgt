# 70 — (SEL-PS) by Transfer: the Riemann–Siegel Block Pins the Designed Carrier's Line Profile to ζ's Own Law

**Register: SEARCH** (task #15). §§1–2 [PROVED HERE (sketch)] on [KNOWN]
imports (Titchmarsh Thm 4.15/R–S; Selberg 1946); §3 closes the (C2) zones;
§4 the defect second moment; §5 the banked Lean bricks. The finding in one
line: **the matched-length designed completion has no independent line
statistics — on Riemann–Siegel blocks its line profile IS ζ's, up to the
taper-difference polynomial and O(t^{−1/4}) — so Selberg's unconditional
CLT polices the designed tower's zero creation.** The "deterministic
partial-sum CLT" (doc 67 §5's not-in-print item) is bypassed, not proven:
no new CLT exists after this document, and none is needed.

## 1. The R–S block and the transfer identity [KNOWN + one design change]

Blocks **B_n := [2πn², 2π(n+1)²)**. On B_n, ⌊√(t/2π)⌋ = n exactly; block
length |B_n| = 2π(2n+1) ≍ √(8πt). Re-anchor the tower per block: the
level-N carrier lives on B_N. The lane's matching T ≍ 2πN² becomes exact —
the R–S block IS the tower epoch, and the epoch is a constraint surface
(t = 2πn²), not a flow clock.

- [KNOWN — Hardy–Littlewood/Riemann–Siegel, Titchmarsh Thm 4.15]: for
  t ∈ B_N, **ζ(½+it) = g_N(½+it) + O(t^{−1/4})** with g_N = S_N + χS̃_N
  the exact-FE symmetric truncation (doc 22's anneal object). The completed
  sharp truncation's line profile equals ζ pointwise on its own block.
- Half-sum corollary (one-sided sum): on the line g_N = S_N + χ·conj(S_N),
  |χ| = 1, so ‖g_N(½+it)‖ = 2|Re(e^{−iθ(t)}S_N(½+it))| ≤ 2‖S_N(½+it)‖,
  hence ‖S_N(½+it)‖ ≥ (‖ζ(½+it)‖ − Ct^{−1/4})/2.
  [Lean: `norm_add_sq_unit_conj_eq`, SelbergTransfer.lean]
- **Attack-as-false record (the trap that forces the blocks).** The
  fixed-cutoff variant — one N′ for a whole U ≍ T window — FAILS: the
  mismatch S_{⌊√(t/2π)⌋} − S_{N′} has mean square Σ_{N′<n≤√2·N′} 1/n =
  ½log 2 = O(1), fatally above the small-ball scale λ₀. Block re-anchoring
  is forced, not optional. Aggregation survives it: each block's small-set
  maps into ONE global ζ-sublevel set (§2), so Selberg is applied once, to
  the full window.
- Block-edge bookkeeping: dip intervals have length ~c/log N ≪ |B_n|;
  straddling losses are O(1) per boundary, ~√T total — negligible against
  the ε₀·U·log N budget.

## 2. (SEL-PS) closed at the line [PROVED HERE (sketch)]

Designed carrier on block B_N: plateau A₀ to N′, taper to N (N′ = N e^{−ℓ}).
Completed: Z_W = F_W + χF̃_W(1−·). The single rewriting that unifies this
document with doc 69 §1:

> **Z_W = A₀·g_N − (Δ + χΔ̃(1−·)), Δ := Σ_{N′<n≤N}(A₀ − A_n)n^{−s}** —

the SAME taper-difference polynomial that carries the (DOM-W) defect now
carries the creation slack. E‖Δ(½+it)‖² ≤ A₀²ℓ (MV; polynomial length
N < |B_N|/12 — block-valid with constant 1+O(1/12)); on the line the
completed Δ-part has norm ≤ 2‖Δ‖.

**Chain.** For t ∈ B_N: ‖Z_W(½+it)‖ ≤ A₀λ₀ ⟹ ‖ζ(½+it)‖ ≤ λ₀ + 2‖Δ‖/A₀
+ Ct^{−1/4} ⟹ t ∈ {‖ζ‖ ≤ 2λ₀ + Ct^{−1/4}} ∪ {‖Δ‖ ≥ A₀λ₀/2}
[Lean: `sublevel_split_subset`]. Union over blocks covering [T, 2T]
[Lean: `blockwise_transfer_measure_le`]:

> meas{t : ‖Z_W‖ ≤ A₀λ₀} ≤ meas{‖ζ(½+it)‖ ≤ 2λ₀ + CT^{−1/4}}
> + Σ_blocks meas{‖Δ‖ ≥ A₀λ₀/2} ≤ (Φ(−z₀) + o(1))·U + 4(ℓ/λ₀²)·U,

the first term by **Selberg 1946 [KNOWN, unconditional]** at
λ₀ = e^{−z₀√(½ log log T)} (fixed z₀; T^{−1/4} ≪ λ₀ forever, factor ~100
already at T = 10¹³). With ℓ = ε₀λ₀², ε₀ = Φ(−z₀): total ≤ 5Φ(−z₀)·U.
The dip/count layer (doc 56 §2 — carrier-agnostic, fires at σ = ½ for
every sliver zero; `MollifiedDip.lean`) converts as-is:

> **K_designed(N) ≤ C′·(Φ(−z₀) + o(1))·U·log N, z₀ FREE — unconditional.**

The doc 65 §3 endgame FIRES: the CLT-grade taper ℓ = Φ(−z₀)e^{−2z₀√(½loglogT)}
is now legitimate, and with it doc 69 §4's onset arithmetic
(log N ≥ log(1/ε₀*) + 2z₀√(½ log log N) ≈ 14, T ~ 10¹³).

Write-out flags (constants, not structure): (i) the dip lemma applied to
Z_W picks up χ′-terms ~ log T·|poly| in the derivative masses — same L²
class, constants into C′; (ii) `plateau_split` (banked, abstract) still
serves the one-sided F_W version; the Z_W version above consumes only the
Δ-decomposition and the sublevel split.

## 3. Off the line: the (C2) zones close [PROVED HERE (sketch) + one CHECK]

For the horizontal-edge union (doc 59 §2), σ-grid across width w, threshold
E* = T^{−1/4} (so −log E* = ¼ log T):

- **Zone M (σ − ½ ≥ 3 log log N/log N):** |χ(σ+it)| = (t/2π)^{½−σ} damps
  the mirror below (log N)^{−2}·(mirror sup-norm growth) — pointwise
  S(σ+it) = ζ(σ+it) + O((log N)^{−2}) and likewise g. Defect moments
  transfer. E(defect_ζ(σ))² ≤ C·log log T on the zone [KNOWN-shaped:
  Selberg's method; uniformity across σ − ½ ∈ [3loglog/log, (log T)^{−θ}]
  is the one **[CHECK]**: Tsang 1984 / the near-line expansions
  (arXiv:2101.00632, 2301.01925) — if the exact range is not in print, the
  classical method runs with room, since the demand (any O(loglog) bound)
  sits far below the true variance asymptotics]. Chebyshev at ¼ log T:
  per-point meas ≤ 16·loglog/log²·U; union over w·log T points ≤
  16w·loglog/log T·U = o(U).
- **Zone N (0 ≤ σ − ½ < 3 log log N/log N):** O(log log) grid points only;
  (C1) per point (loglog/log each): union ≤ C(log log)²/log → o(1). No new
  input.
- Consequence: **(C2) horizontal-edge threading closes** with second-moment
  transfer + (C1); doc 59 §2 route 3's demand O((loglog)²) is met at
  strength O(loglog). The strata-match audit (doc 59 §2 route 1) is no
  longer load-bearing — it survives as an optimization.

## 4. The defect second moment at the line [the task's opening move, now a corollary]

E_t[((−log‖S_{N′}(½+it)‖)⁺)²] ≤ C·log log T, by three ranges of
a := (−log‖S‖)⁺ via the layer-cake ∫ defect² = 2∫ a·meas{defect > a} da:

1. a ≤ A₀-grade: half-sum transfer (§1) + Selberg's second moment
   (E(log⁻|ζ|)² = ¼ loglog T·(1+o(1))) — the main term.
2. a ∈ [·, ⅛ log T]: transfer + Selberg's fourth moment:
   meas{‖ζ‖ ≤ e^{−a}} ≤ C(loglog)²/a⁴·U — the integral converges to
   O((loglog)²/A₀²·…) = lower order.
3. a > ⅛ log T (transfer dead: e^{−a} below the R–S error): per unit box,
   S has ≤ C log N zeros (Jensen from ‖S‖ ≪ N^{1/2}); Boutroux–Cartan on
   the Blaschke factor + Borel–Carathéodory on the zero-free factor give
   meas{‖S‖ ≤ e^{−a}} ≤ 4e·exp(−(a − C₂log N)/(C₁log N)): the tail
   integral is o(1) beyond a = C log N·loglog N.

All ranges sum to O(log log T). This is the doc 59 §2 route 3 object at
the line, delivered at strength loglog (demand was (loglog)²).

## 5. Lean pass [banked — SelbergTransfer.lean, axiom-clean]

- `norm_add_sq_unit_conj_eq` — the half-sum identity ‖S + v²·conj S‖ =
  2·|Re(conj v·S)| for ‖v‖ = 1 (the algebraic heart of §1).
- `sublevel_split_subset` — {‖Z‖ ≤ A₀λ} ⊆ {‖g‖ ≤ 2λ} ∪ {‖τ‖ ≥ A₀λ} under
  the pointwise identity Z = A₀•g + τ (§2's split).
- `sublevel_transfer_subset` — {‖g‖ ≤ 2λ} ∩ B ⊆ {‖ζ‖ ≤ 2λ + ε} under
  per-block proximity ‖g − ζ‖ ≤ ε on B (§1's transfer).
- `blockwise_transfer_measure_le` — μ(⋃_j (E_j ∩ B_j)) ≤ μ(F) +
  Σ'_j μ(G_j ∩ B_j) from per-block inclusions E_j ∩ B_j ⊆ F ∪ (G_j ∩ B_j)
  (§2's aggregation: re-anchored small-sets, one global Selberg set).

## 6. Status: the load-bearing residue is EFFECTIVITY, not existence

(SEL-PS): **CLOSED as a transfer** — line at full CLT grade (§2), off-line
at second-moment grade (§3), all known consumers fed. What remains for the
onset number (doc 69 §4's T ~ 10¹³):

- (i) an effective Berry–Esseen-grade rate for Selberg's CLT at fixed
  z₀ ≈ 3 [CHECK: rates (loglog T)^{−1/2} exist in the modern literature];
  at loglog T = 3.4 the correction is O(1)-grade, so the finite-T constant
  genuinely decides the onset;
- (ii) the explicit R–S error constant [CHECK: Gabcke's thesis];
- (iii) MV block constants and C′ under the χ′-terms (§2 flag).

Bracket arithmetic (labelled illustration, first-pass constants): a 10×
effectivity slack in λ₀ costs +4.6 in log N — onset moves 10¹³ → ~10^{18}.
The claim that survives any reasonable effectivization: **the designed
tower's onset is bounded by e^{~45}-grade heights, against (TIGHT)-only
e^{~650}** — and the 10¹³/verified-range meeting is the target of the
promotion pass, not its assumption. Force order: effectivization pass →
(C2)/§3 write-out → (MOAT-W)/(DEEP-W) transplants → k ≥ 2 rungs.

## 7. What this opens

1. **The designed tower has no free line statistics.** Everything the
   designer controls is the taper; the plateau's law is ζ's own. The
   constraint side of ζ (its unconditional value-distribution law) polices
   the zero creation of the very carrier built to read ζ's zeros —
   self-policing, and legitimately non-circular (Selberg 1946 needs no
   zero hypothesis). Constraint-not-flow at the value-distribution level.
2. **The R–S block = tower epoch identification** is a native object:
   t = 2πn² as the lane's clock-surface. Worth a card: deck/window
   bookkeeping in block coordinates; prediction — any future census sees
   re-anchoring artifacts concentrate at block edges 2πn².
3. The two-tails card (doc 65 §5(3)) sharpens: domination is the right
   tail and creation the left tail of ONE law (ζ's own lognormal),
   transported by ONE identity, with ONE polynomial Δ carrying both
   defects. The design problem is now literally: place a taper between
   the two tails of ζ's value distribution.
4. z₀-optimization: K and taper feasibility are both monotone in z₀; with
   effective constants the design point z₀* = argmin(onset) subject to
   Φ(−z₀) ≤ ε₀* is one page of arithmetic — the first fully numeric design
   triple (z₀*, ℓ*, N₀*).
