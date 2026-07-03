# 22 — The Anneal Reduction: Window Parity Transfers to Finite Truncations

**Register: SEARCH** (calibration archived: `computations/ANNEAL-RESULTS.md`;
Spira/Jerby citations delegate-sourced — spot-check before promotion). Task #134.

## 1. The comparison object

g_N(s) = Σ_{n≤N} n^{−s} + χ(s) Σ_{n≤N} n^{s−1}, N = ⌊√(T/2π)⌋ (the analytic object
behind the Riemann–Siegel main sum). Since χ(s)χ(1−s) = 1, it satisfies the EXACT
functional equation g_N(1−s) = χ(1−s) g_N(s) — one line. So g_N carries the full
FE×reality structure: a real carrier on the critical line exists (Γ-dressing as for
ξ), the window identity (ID) applies to it verbatim, and its window invariants
D_g, L_g, N_g are defined exactly as ζ's. **The truncation lives on the same
carrier-layer as ξ; only the Euler depth differs.** (Doc 19's layering again: FE
builds the carrier — and it builds it for every truncation level.)

## 2. The reduction [theorem-shaped; wiring gap named]

If ‖ξ_c − g_c‖ < ‖g_c‖ on the boundary charts of a window W (deck domination, with
ξ_c, g_c the matched completed objects), the banked machinery transports the deck
class at every level: D_ξ ≡ D_g (mod 2^{k+1}). Given also the seam-side transport
(the L-invariant under domination on slit-adjacent charts — the one unproven wiring
piece, same shape as #131's dictionary), (ID) on both carriers yields

> **N_ξ(W) ≡ N_g(W) (mod 2^k): ζ's window parity equals the truncation's window
> parity on dominated windows.**

The bridge identity (WR_1) then reduces, window by dominated window, to a FINITE
question: **do the off-line zeros of the exact-FE symmetric truncation occur in even
local counts?**

## 3. Calibration (pre-registered; ANNEAL-RESULTS.md)

7/7 rng-drawn line-centered windows (r = 0.20, T up to ≈ 2800) are dominated —
q = max|ζ−g_N|/|g_N| between 0.02 and 0.75; the sole r = 0.35 failure sits at a
truncation zero 0.003 from the circle (the predicted exceptional mechanism, movable
by nudging r). At accessible heights the reduction's premise is the ROBUST regime,
not the exception.

## 4. The finite question inherits the whole program

[Delegate-sourced] Spira 1967 observed, and Jerby 2024 codifies, that RS-length
truncations DO have off-line zeros numerically ("Spira's RH for sections" — on-line
confinement at length [t/2] — is an open conjecture). Our target is the mod-2
WEAKENING: not absence of off-line zeros of g_N, only local evenness — the same
weakening the square class performs on RH itself, one level down the ladder.

Convergence of the dispatch's three coordinates, and the sharpest constructive
output: apply the DISC jet reader (doc 20) to the truncation's OWN carrier. Its jets
are closed-form finite exponential sums, so:

> **(DISC-fin) [CONJECTURE, the fully finite bridge target]** For dominated windows,
> (WR_1) follows from: the recentered degree-d jet sections (n = 0) of the completed
> symmetric truncation have positive discriminant. A sign inequality for EXPLICIT
> finite exponential-sum expressions — Euler structure in the coefficients, FE in
> the realness, window in the recentering.

Consistency check at accessible heights: where RH is verified and domination is
measured, transport already FORCES N_g even in those windows — so (DISC-fin) is
true there; its content is a direct finite proof that survives past verified
heights.

## 5. Verdict on #134

(ANNEAL) is alive and calibrated: zero-free comparisons are dead (doc 19 §4b), the
exact-FE truncation is the right comparison, domination is the robust regime at
r = 0.20, and the reduction converts the bridge identity on dominated windows into
finite exponential-sum parity — attackable by the DISC reader. Open pieces, carded:
the seam-transport lemma (with #131), and (DISC-fin) itself. Next: run the DISC jet
reader on g_N's carrier in a dominated window containing an off-line g_N zero pair —
the first fully finite window-relation instance.
