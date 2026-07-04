# 69 — (DOM-W) in Threading Form + the Constants Pass: ε₀* ≈ 1/512, and the Onset Finding

**Register: SEARCH** (task #14). §1–§2 [PROVED-sketch]; §3 first-pass
constants (promotion pass will tighten); §4 is an honest catch that
re-promotes the CLT refinement for the finite range — recorded with the same
prominence as the wins.

## 1. (DOM-W) — domination without new AFE machinery [PROVED-sketch]

Reference the SHARP Hardy–Littlewood AFE (E_HL = O(t^{−1/4}) at matched
lengths; classical). With Z_W the designed symmetrized completion (weights
w_n: plateau to N′, taper of log-length ℓ), the defect
D_W := ζ_normalized − Z_W decomposes as

> D_W = (taper-difference pair) + E_HL,  taper-difference = Σ (1_{n≤N} − w_n)n^{−s} + χ-mirror,

a Dirichlet polynomial supported on the taper range with
E|taper-diff(½+it)|² = Σ_{taper}(1−w_n)²/n ≤ ℓ (MV, exact). The bridge only
ever needs domination on CHOSEN window boundaries (self-domination is
per-window; placement is co-countable), so the consumable form is threading:

1. **Defect smallness off a dial-set:** meas{|D_W| > √(ℓ/ε₁)} ≤ ε₁·U
   (Chebyshev + MV; E_HL is lower order).
2. **Carrier largeness off a dial-set:** meas{|Z_W| ≤ τ} ≤ U·(½ log log N +
   C)/log(1/τ) — (TIGHT) applied to Z_W itself (leading coefficient 1 on the
   line-real form; the convexity-tangent floor is carrier-generic). At
   τ = √(ℓ/ε₁) with ℓ = ε₀λ₀²: log(1/τ) ≈ (½ log log N)/ε₀ ⟹ measure
   ≤ (1 + o(1))·ε₀·U.
3. **Verdict:** off an (ε₁ + ε₀)-fraction of heights, ∂W threads with
   |D_W| < τ < |Z_W| — domination holds on a placement-dense window family.
   Horizontal edges ride the (C2) strata-match exactly as for the sharp
   carrier. Pointwise-superpolynomial smoothed AFEs (Iwaniec–Kowalski
   Thm 5.3-class weights) remain the luxury upgrade [CHECK cite at
   promotion]; the threading form needs none of it.

## 2. The no-tension check, now quantitative

Creation suppression wants ℓ small (ℓ = ε₀λ₀²); domination wants ℓ small
(τ = √(ℓ/ε₁) below the carrier scale); the SAME (TIGHT) lemma prices both
threading clauses. The only opposing pressure on ℓ is the trivial one — the
taper must contain integers (N·ℓ ≥ 1) — so all tension in the whole design
lives in the ONSET arithmetic (§4). The doc 61 §3(3) conjecture ("the two
demands pull the same direction") is confirmed at inequality level.

## 3. The constants pass [first-pass numbers; every factor named]

- **c_deck:** isolation windows of height H_iso = 8 average zero spacings
  = 8·(2π/log T)-scale suffice (2 edge choices with (C1)-threading room +
  interior slack); demand r·H_iso ≤ ½ gives **c_deck ≈ 1/16**.
- **C′ (rate conversion):** r(N) ≤ [split factor 2] × [dip-layer constants
  3·n_max ≤ 12 on pruned cells] × [dyadic-depth sum over η ∈ (η₀, ¼) absorbed
  into log N with coefficient ≤ 4/3] × ε₀·log N ⟹ **C′ ≤ 32**. ((TIGHT) is
  σ-uniform on [½, 3], so the split argument runs at every depth abscissa;
  deeper zeros dig longer dips — the dyadic sum converges onto the log N
  normalization.)
- **The meeting number:** **ε₀\* = c_deck/C′ ≈ 1/512** — first-pass; the
  promotion pass will move it by small factors, not orders.

## 4. The onset finding [honest catch — the CLT re-promoted for finite heights]

With (TIGHT) alone, λ₀(ε₀\*) = exp(−(½ log log N + C)/ε₀\*) forces taper
feasibility N·ℓ ≥ 1 only once log N ≳ (1/ε₀\*)·log log N ≈ 512·log log N —
an EXPLICIT but astronomical onset (N ≥ e^{~650}-grade). The asymptotic
RH₂-spine statement is closed unconditionally past that onset; ALL heights
are not. Correction to doc 67 §3's demotion: **the lognormal/Selberg-CLT
refinement is load-bearing for the finite range.** And here the arithmetic
turns startling: with CLT-grade λ₀ = e^{−z₀√(½ log log T)} at
Φ(−z₀) = ε₀\* ≈ 1/512 (z₀ ≈ 3.1), the feasibility condition becomes
log N ≥ log(1/ε₀\*) + 2z₀√(½ log log N) ≈ 14, i.e. **onset N ~ e^{14},
T = 2πN² ~ 10^{13} — the boundary of the classically VERIFIED zero-free
range.** First-pass constants, so treat the coincidence with suspicion —
but as computed, the verified range covers below the onset and the
CLT-designed tower covers above it, with no gap.

**CORRECTION (doc 71 §6, after the literature mining).** This §4 coincidence
was too optimistic on two counts. (a) The CLT-grade (Tier-G) onset at
z₀ ≈ 3.1 is UNUSABLE at finite heights: the uniform-in-y Selberg CLT
(Selberg 1992 / Tsang 1984) has additive error O((logloglogT)²/√(loglogT)),
which is O(1)-grade — ~400× the target tail — at T ~ 10¹⁵, and its constant
is not numeric in print. The finite-height design is forced onto the MOMENT
tier (EFF-M14), whose onset at ε₀\* = 1/512 is T ~ 10¹⁷, not 10¹³. (b) The
rigorous verified boundary is 3·10¹² = 10^12.48 (Platt–Trudgian 2021,
interval arithmetic), NOT Gourdon's uncertified 10¹³. Closing the M14-tier
gap to 3·10¹² needs ε₀\* ≈ 1/32 — a factor ~16 in c_deck/C′, not 8. The
no-gap statement survives as a TARGET requiring (EFF-M14) + 16× in the
placement constants; both finite, neither open-problem-shaped. The R–S
error constant is now numeric and a confirmed spectator (doc 71 §6(iv)).

## 5. Status and force order after this pass

- (DOM-W): closed in threading form [sketch]; no new analytic class.
- Constants: ε₀\* ≈ 1/512 first-pass; extraction paths named.
- The single load-bearing analytic item on the Route C-direct spine, for
  ALL heights, is now **(SEL-PS)-lognormal**: the CLT left tail at fixed
  z-score z₀ ≈ 3 for the matched-length plateau sum — measured true
  (flat 0.47 at the median, doc 65 §2), Selberg-1946-technology-shaped,
  with near-line expansions in print for the ζ-instance
  (arXiv:2101.00632, 2301.01925). Everything else on the spine: execution,
  extraction, or classical transplants.
- Force order: (SEL-PS)-lognormal → promotion pass ((TIGHT) boundary terms,
  C′/c_deck tightening, MOAT-W/DEEP-W write-outs) → C2 strata-match →
  k ≥ 2 rungs.

## 6. What this opens

1. (SEL-PS)-lognormal is a MOMENTS statement (Selberg's method = moments of
   log via Dirichlet polynomials); its second moment is doc 59 §2 route 3's
   defect-variance — one object now carries both the cofinality upgrade and
   the onset collapse. Prove once, consume twice.
2. The onset coincidence (10^{13} vs the verified range) deserves its own
   verification card once constants are promoted: if it survives, the
   designed-tower program has NO unconditional gap below its own floor.
3. The threading form of (DOM-W) makes the whole spine placement-native:
   every clause (domination, creation, isolation) is now a measure bound
   plus co-countable placement — one uniform proof idiom for the Lean pass.
