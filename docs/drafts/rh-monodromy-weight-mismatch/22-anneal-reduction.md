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

## 6. Status refresh + carrier layer machine-checked (2026-07-04)

§2's "one unproven wiring piece" and §5's open items are OVERTAKEN by later rounds; this
section records where each landed, so the doc reads current.

- **Seam transport: PROVED and BANKED.** Doc 32 §1 proves the transport lemma (segment
  homotopy + deck-class deformation invariance, no argument principle);
  `SeamTransport.lean` machine-checks it (`seam_transport`, `seam_transport_ladder`) at
  every level 2^k.
- **Domination premise: unconditional on the right family.** Doc 32 §§6–8 (#144 CLOSED at
  SEARCH grade): the HL truncation g_N of §1–§3 is superseded as the *theorem-track*
  comparison object by the SYMMETRIZED exponential-AFE family Φ* := ½(Φ_F(s)+Φ_F(1−s))
  (Jerby arXiv:1910.05754 as Φ_F), where (DOM) holds unconditionally via Cartan/(LOW-BC).
  §3's g_N calibration remains valid as measurement; (DISC-fin) instances ran as
  #136/#140.
- **The carrier layer (§1) is now Lean:** `AnnealCarrier.lean` (task #143 queue), all
  axiom-clean:
  - `chiSymmetrize_one_sub` — §1's "one line": χ(s)χ(1−s)=1 ⟹ g = h + χ·h(1−·)
    satisfies the exact asymmetric FE (g_N is the instance).
  - `symmetrize_one_sub` / `symmetrize_eq_self` / `symmetrize_xi` — (SYM): exact even FE
    for ½(Φ(s)+Φ(1−s)); ξ a fixed point.
  - `norm_sub_symmetrize_le(_of_mem)` — (SYM-err): accuracy preserved on FE-closed sets
    (doc 32 §7's one-liner, checked).
  - `symmetrize_differentiable`, `symmetrize_conj`,
    `symmetrize_orderAt_one_sub`, `symmetrize_orderAt_conj` — the full FE×reality
    equivariance package for the symmetrized carrier: the finite-side analogues of
    `xi_orderAt_one_sub`/`xi_orderAt_conj`, i.e. exactly what instantiates the window
    identity (ID) of `WindowRelation.lean` on the truncation — §1's "same carrier-layer"
    claim as theorems.
  - `symmetrize_domination` — doc 32 §6's (DOM) assembly: (AFE-exp) error ε + (LOW-BC)
    lower bound ε < ‖Φ*‖ ⟹ the strict domination `seam_transport` consumes. The two
    analytic estimates stay as explicit hypotheses (instrument-grade inputs).
- **Chain now machine-checked end to end** (analytic inputs as hypotheses):
  (AFE-exp) + (LOW-BC) → `symmetrize_domination` → `seam_transport_ladder` → deck-class
  transport at level 2^k → (ID) on both carriers (`WindowRelation`, fed by the
  equivariance package) → window parity transfers to the finite side.
- **What stays open here:** nothing doc-22-local. The live consumers are #130 (the bridge
  identity itself — does the FINITE side's parity hold?) and the eventual
  exponential-family instance run (doc 32 §8). Next generative object: a Lean-level
  `Prop` interface packaging (AFE-exp)/(LOW-BC) for the Jerby family, so an instance run
  can discharge `symmetrize_domination`'s hypotheses numerically per window.

## 7. The carrier made CONCRETE and unconditional in Lean (2026-07-04, after doc 72 §4)

Doc 72's collapse ("the parity carrier IS g_N, the doc 22 object") upgraded the target:
not the abstract symmetrization layer (§6) but THE objects. Banked as
`ZetaCarrier.lean` (24 declarations, all axiom-clean, lint green):

**Hypotheses discharged — now proofs from mathlib:**
- The abstract `hχ` (χ(s)χ(1−s)=1) → PROVED for the actual `zetaChi = Γ_ℝ(1−s)/Γ_ℝ(s)`,
  unconditionally on the open critical strip (`zetaChi_mul_one_sub_of_mem_strip`);
  validated against ζ's own FE (`zeta_eq_zetaChi_mul`, from
  `riemannZeta_def_of_ne_zero` + `completedRiemannZeta_one_sub`).
- The abstract approximant → the actual `dirichletPoly` (entire, Schwarz-real, proved).
- `gN := chiSymmetrize zetaChi (dirichletPoly N)`: exact FE (`gN_one_sub`), reality
  (`gN_conj`), strip analyticity, and FE order-pairing (`gN_orderAt_one_sub`) —
  §1's "same carrier-layer" sentence, concrete, no hypotheses on the strip.
- `completedGN := s(s−1)/2·Γ_ℝ·gN`: the exact EVEN functional equation on the strip
  (`completedGN_one_sub`) — the full ξ-shape at finite Euler depth — plus reality and
  order equivariance (`completedGN_orderAt_one_sub`), i.e. the (ID) inputs.
- `analyticOrderAt_one_sub`: the order-equivariance engine strengthened to
  hypothesis-FREE (entirety dropped) — now applies to meromorphic carriers.
- Doc 32 §5's cancellation → `completed_domination_iff`: completed-level domination
  ⟺ raw ‖ζ−g_N‖<‖g_N‖. The archimedean bookkeeping is REMOVED from the premise.

**What remains, exactly:** two named Prop interfaces per window —
`AFEAccurateOn` (the R–S/HL error bound; explicit constants exist, doc 71 §1) and
`CarrierFloorOn` (the (LOW) floor; per doc 72 §4 boundary threading just avoids
ζ-zero neighborhoods). The capstone `anneal_deck_transport` shows these two are the
ONLY analytic content: given them on a strip window's charts, every level-2^k deck
reading of ξ equals the completed truncation's. Discharge routes, in order of reach:
(i) per-window certified interval arithmetic (numerical instances, #136/#140-style —
turns single windows into machine-checked parity transfers); (ii) the Gabcke/HL
explicit remainder as a formalized theorem (classical-shaped, months-grade — kills
`AFEAccurateOn` for all large T at once); (iii) Cartan/(LOW-BC) via mathlib's NEW
`JensenFormula.lean` (spotted this round — the enabling brick for formalizing the
doc 32 §7 minimum-modulus argument, killing `CarrierFloorOn` off exceptional discs).
Next generative object: (i) on the #136 window — the first end-to-end machine-checked
window-parity transfer on the actual ζ.
