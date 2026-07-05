# 80 — Route C Ground to Terminal State, I: the Standing Map and the (EQD) Attack

**Register: SEARCH except the map statuses (each checked against the named
anchor).** Task #28 (/goal): Route C to a fully formal Lean proof or a
provable, detailed refutation — no partial results. Session seed 1327387142575317405.

## 1. Route C, the standing map (post docs 72–74 collapse)

Route C = the sharp-carrier spine for the RH₂ rung at heights T ≥ T₀,
meeting verified RH below T₀. Carrier: g_N (doc 22's anneal object), no free
parameters but the dip threshold λ₀.

| Link | Statement | Status | Anchor |
|---|---|---|---|
| C-1 | ladder ⟺ rung structure | Lean | `rh_iff_forall_ladder`, `RHLadder` |
| C-2 | window relation on g_N | Lean (incl. seam) | `AnnealWindowRelation`, `SeamCongruence` (doc 79) |
| C-3 | domination | Lean interface + numeric R–S (classical-cited 1.463·t^(−1/4)) or EM carrier (machine-checked, longer N) | `ZetaCarrier`, `EMCarrier` |
| C-4 | thick-dip creation count | Lean | `ThickDips.lean`, `MollifiedDip.lean` |
| C-5 | tail certification (TAIL-6): meas{log\|Z\| ≤ −6.1} ≤ 2.4e−4·T at 3e12 | **OPEN = (EQD)** | docs 72 §8, 73, 74 §4 |
| C-6 | cofinality C1 + C2 | paper (transfer + zones) | doc 70 §3, `SelbergTransfer.lean` |
| C-7 | isolation / consumer | Lean skeleton | doc 57 Tier 2, `MidCentral` |
| C-8 | below T₀: verified RH | external interval arithmetic (Platt–Trudgian 3·10¹²), NOT Lean | doc 71 §1 item 10 |
| C-9 | k ≥ 2 rungs | [CONJECTURE] (HANK-fin)_k — outside Route C proper | doc 38 |

Terminal criteria for the /goal, exactly:
- **PROOF branch:** (EQD) closes C-5 at A ≤ 6.1 ⟹ onset T₀ ≤ 3·10¹² ⟹
  Route C's analytic content complete; then formalize C-3…C-6 fully (the
  EM carrier removes the classical citation; C-8 stays an external
  computation, named as such — its Lean-ification is a separate
  certificate-evaluator program).
- **REFUTATION branch:** a proof that the instrument class cannot reach
  2.4e−4 at 3e12 — which requires making "instrument class" a theorem, not
  a feeling. §3 supplies exactly that: the bandwidth-budget principle
  (worst-case-gap methods = degree budget, PROVED-sketch) plus a census
  computation; if the census itself fails quantitatively, the refutation is
  detailed and named (the collision spectrum is the obstruction), and the
  onset stays 10^21 — Route C then terminates as: proven spine above 10^21,
  unreachable meeting, dead as a finite-height program.

## 2. Why (EQD) is the whole ballgame

Docs 73–74 established: the moment/polynomial class is capped by the shared
degree budget Σ_j 2k_j log Y_j ≤ 2 log T; at T = 3e12 the certified stack
bottoms at ~1.5e−2 vs budget 2–4e−3 (short 5–15×), onset 10^21–10^22. The
single instrument class not priced by that budget: equidistribution of the
prime-frequency torus (doc 74 §4). No prior ETK/Fourier attempt exists in
the corpus (checked 5-failed and docs 00–79 this cycle).

## 3. The (EQD) framework: Fourier–majorant with actual-gap census

Object: S_X(t) = Re P_X(t) = Σ_{p≤X} p^(−1/2) cos(t log p), t ∈ [T, 2T].
Target: certified P_t(S_X ≤ −a) at near-independent-model grade (the model
Chernoff at a = 6.1 is 2.3e−14 — four orders below the budget; the entire
war is the transfer error).

**(i) Majorant.** Take f ≥ 1_{(−∞,−a]} a Beurling–Selberg-type majorant
with supp f̂ ⊆ [−U, U]. Then P_t(S ≤ −a) ≤ E_t f(S) and
E_ind f = P_ind(S ≤ −a) + O(density/U) — at design depths the loss is
harmless already at U ≈ 3.

**(ii) Expansion.** e^{iu S} = ∏_p e^{iu a_p cos(t log p)} expands by
Jacobi–Anger into Σ_n (∏_p i^{n_p} J_{n_p}(u a_p)) e^{it ω_n},
ω_n = Σ n_p log p = log(A/B) for the coprime smooth pair (A,B) determined
by n. Weight bound |∏ J_{n_p}(u a_p)| ≤ (u/2)^{‖n‖₁} / (√(AB) ∏|n_p|!).
The n = 0 term is the independent model, EXACTLY. Averaging over [T, 2T]:
|avg e^{itω}| ≤ min(1, 2/(T|ω_n|)).

**(iii) The three-regime split.**
- |ω_n| ≥ δ: total J-weight ≈ e^{u Σ_p 1/√p} =: e^{uM_X}, contribution
  ≤ 2 e^{uM_X}/(Tδ).
- 1/T ≤ |ω_n| < δ: near-collisions — pairs of X-smooth (or block-rough)
  integers with |A/B − 1| < δ, hence B ≥ 1/(2δ); per-pair weight
  ≤ (u/2)^{Ω(AB)}/(√(AB) ∏ n_p!), averaging gain 2B/(T|A−B|). FINITE
  CENSUS: enumerable below a bound, sieve-priced above (twin-smooth /
  twin-rough counting — Selberg-sieve explicit constants).
- |ω_n| < 1/T: forces max(A,B) > T/2; weight ≤ (u/2)^{‖n‖}/√(AB) < (u/2)^{‖n‖}·(2/T)^{1/2}·…
  — priced with the same census shape.

**(iv) The bandwidth-budget principle [PROVED-sketch this cycle].** If one
prices regime (ii)+(iii) by the WORST-CASE rational gap
|ω_n| ≥ 1/(2max(A,B)) ≥ e^{−H(n)}/2, H(n) = Σ|n_p| log p, the assembled
error is ≥ (1/T)·e^{u Σ_p √p·…-grade} — i.e. the method closes only when
u·(block ℓ¹-mass) ≲ log T. Since a bandwidth-U certification is
information-equivalent to a degree-U moment ladder (Fourier ↔ moments on a
compact-support law), **worst-case-gap Fourier = the doc 72 §2 degree
budget, method-independently.** Consequence: any (EQD) that beats the
moment stack MUST consume actual-gap structure — the collision census is
not an optimization, it is the entire new content. (This upgrades the
degree-budget principle to: the war at 3e12 is won or lost on the
arithmetic statistics of near-collisions among smooth/rough products.)

**(v) Block assembly.** B1 = p ≤ 313 (M = 8.40, u₁ ≤ ~3 within budget even
worst-case); B2 = (313, 10⁴] (rough pairs — near-collisions need
B, B+q both 313-rough: sieve-thin); B3, residual as in doc 74 (residual
stays at deg-4 Christoffel — the Fourier instrument does not apply to it).
Joint bandwidth obeys its own budget; the census decides what survives.

## 4. Pre-registered predictions [written BEFORE any computation; these bind]

Census script census_eqd.py (runpod): exact prime sums; B1 = 313-smooth
enumeration to 10⁸; B2 collision spectrum for ‖n‖ ≤ 4 exact to product
bound 10¹⁰; weights at u₁ = 3, u₂ = 1.8; T = 3·10¹².

- **P-EQ1 (B1 far-regime):** e^{u₁ M₁} with exact M₁ = Σ_{p≤313} p^(−1/2)
  lands in [e^{24}, e^{26}], and with δ₁ = 10^{−2} the far-regime error
  2e^{u₁M₁}/(Tδ₁) ≤ 10^{−3}·…: FAILS at u₁ = 3 (prediction: the naive
  total-weight bound is USELESS even for B1 — only ‖n‖-graded accounting
  with the (u/2)^{‖n‖}/∏n! weights survives; graded version ≤ 3e−4).
- **P-EQ2 (B1 near-collisions):** the weighted near-collision sum over
  313-smooth pairs with |A/B−1| < 10^{−2}, ‖n‖ ≤ 20, AB ≤ 10^{16} is
  ≤ 10^{−4} at u₁ = 3 (the 1/√(AB) ≥ 10^{−1}·δ-floor and factorials kill
  it; dominant term = twin-smooth pairs like 1025/1024 at ~10^{−5}-grade).
- **P-EQ3 (B2 rough census):** among products of ≤ 2 primes from
  (313, 10⁴] (pairs p q vs r s), the minimal |log(A/B)| with A ≠ B,
  AB ≤ 10^{10} exceeds 10^{−9}, and the weighted sum of ALL ‖n‖ ≤ 4
  near-collisions below δ₂ = 10^{−2} is ≤ 10^{−5} at u₂ = 1.8.
- **P-EQ4 (the adjudication):** the assembled certified stack at A = 6.1
  (B1 Fourier + B2 Fourier-or-deg-6 + B3 deg-4 + residual deg-4, optimal
  split) lands ≤ 4·10^{−3} — i.e. (EQD) CLOSES the doc 74 gap at T = 3e12.
  Rough prior: 0.45. If it fails, record WHICH regime eats the budget —
  that regime is then the named obstruction of the refutation branch.
- **P-EQ5 (bandwidth-budget check):** the graded far-regime sum at
  u₁ M₁ ≈ 25 ≈ 0.87·log T is within a factor 30 of its worst-case-gap
  lower bound — confirming §3(iv) empirically (the far regime alone cannot
  be beaten; only the census regimes move).

## 5. Results — §to be appended after the run; predictions above bind.

## 5. Results [MEASURED — census_eqd.py + mixed_twin_probe.py, archived; verdicts against §4, all bind]

- **P-EQ1 PASS (as predicted, and superseded).** Flat far bound
  2W₁/(Tδ) = 0.354 at u₁ = 3, δ = 10⁻² — useless, as predicted. Superseded:
  the double-bandlimited architecture (Beurling–Selberg majorant in t with
  supp Φ̂ ⊆ [−δ, δ]) makes the far regime EXACTLY ZERO — the error is the
  collision census and nothing else. M₁ = 8.4575, W₁(u=3) = 5.3e9, graded
  head W(1) = 25.4, W(2) = 317, …
- **P-EQ2 PASS.** B1 census (3·10⁶ range, q ≤ 500, δ_rel = 10⁻²,
  10.3M coprime pairs): weighted sum 1.32e−6 ≪ 10⁻⁴. The top contributors
  are EXACTLY consecutive-smooth pairs ((2944689, 2944690) etc., 5.8e−11
  each): the twin-smooth census is THE object, confirmed. At the working
  bandwidth δ₁ = 100/T = 3.3e−11 every enumerated pair has ω ≥ 3.3e−7 —
  the in-range collision sum is EXACTLY ZERO; the entire B1 transfer error
  is the twin-smooth census at B ≥ 3.3e10 (enumerable to ~10¹¹–10¹²;
  heuristic total ~1e−4-grade at u₁ = 3).
- **P-EQ3 PASS (strongly).** B2 rough spectrum: min 1v1 gap 2.0e−4;
  min 2v2 gap 2.1e−8 > 10⁻⁹ ✓; weighted ‖n‖ ≤ 4 collision sum
  ≤ 2.2e−10 (1v1) + 6.3e−8 (2v2, dyadic-shell upper) ≪ 10⁻⁵ ✓.
  The rough-block frequency arithmetic is as favorable as doc 74 §6 hoped.
- **P-EQ4 FAILS — and the failing regime is NAMED, per the pre-registration.**
  (i) The per-block union assembly (B1-Fourier + B2 deg-6 + B3 deg-4 +
  residual deg-4) lands at 0.49 (alloc 3.2/0.9/0.8/1.2); the all-Christoffel
  reference at 0.19 — both WORSE than doc 74's 2-block 1.5e−2: union
  splitting across ≥ 3 small-σ blocks is structurally wrong (doc 74's
  diagnosis, reproduced). (ii) The decisive measurement — the mixed
  instrument (Chernoff/Fourier on B1 × moments on the rest) requires the
  twin census of SP = {313-smooth × (≤ 1 prime ≤ 691k)}: measured density
  0.0895 at 3.3e10 (0.0423 at 3.3e11), ~8e9 twin pairs per octave, weighted
  cross-collision mass **2.65 per octave at 3.3e10, 0.74 at 3.3e11** —
  O(1)-grade, five orders above the 2.4e−4 budget. The obstruction: as soon
  as mid primes enter the generating set, prime-cofactor configurations have
  UNSUPPRESSED weights (Ω_smooth small ⟹ no factorial/1.5^Ω damping) and
  the frequency set is effectively δ-dense.
- **P-EQ5 PASS.** The far-regime arithmetic matches the worst-case-gap
  budget by construction; the principle stands (§3(iv)), now with the
  collision side measured too.

## 6. The adjudication: what (EQD) IS and IS NOT

**[MEASURED + PROVED-sketch] The two-sided wall.** Moments and bandlimited-
Fourier are the SAME instrument class seen from two sides: polynomial degree
= Fourier bandwidth; the shared degree budget (doc 73 §4) = the bandwidth
budget (§3(iv)); and the escape hatch (actual-gap census) is open exactly
where the frequency-generating set is arithmetically thin:
- **B1 (65 primes): OPEN HATCH.** Transfer at ANY bandwidth u ≤ ~6 reduces
  to the twin-smooth census at B ≥ 1/δ — measured tiny, enumerable,
  certifiable. B1 is certifiable at near-model grade (Chernoff 2.7e−14 at
  6.1 instead of Christoffel's 1.06e−4 at 4.1): the small block is now
  effectively FREE in the stack.
- **B2 alone (‖n‖ ≤ 4): OPEN HATCH** (rough pairs are sparse — P-EQ3).
- **Any block union containing mid primes at joint bandwidth: CLOSED.**
  The SP twin census is O(1) per octave. No bandlimited functional of the
  full prime sum transfers at T = 3e12 unless its weights suppress
  prime-cofactor configurations — and "suppressing them" IS the degree
  budget. The circle closes: **there is no third instrument class between
  moments and equidistribution; they are one class, and its exact price at
  T = 3e12 is the measured collision census.**

Consequence for Route C's finite-height meeting: the certified stack stays
at doc 74's ~1.5e−2 against a budget of 2–4e−3 ((TAIL-6) at ε₀* ∈
[1/512, 1/256], thickness 4.02). B1-Fourier releases ~0.3–0.5 units of
threshold budget (its component leaves the stack), worth a factor ~e^{ΔA·A/σ²}
≈ 2–3 on the dominant blocks — closing perhaps half the log-gap, not all.
The residue is now fully concentrated in: (a) the mid-block z ≈ 2.5–3
Chebyshev-grade losses (degree-capped, hatch closed), (b) the residual-block
certification (EFF-E, three measured numbers, classical-open).

## 7. What this opens

1. **The B1-Fourier instrument is real and formalizable**: double
   Beurling–Selberg + Jacobi–Anger with explicit remainders + the
   twin-smooth census as a finite certified enumeration. Lean shape: a
   bandlimited-transfer skeleton (no Bessel in mathlib — to be created) +
   `sq_tail_bound`-style consumables. Deliverable regardless of the meeting.
2. **The wall statement is now provable-shaped** (refutation-grade for the
   naive-(EQD) class): "any T-averaged bandlimited certification of the
   full prime sum at T = 3e12 has transfer error ≥ (measured SP-census)
   unless its frequency weights vanish on prime-cofactor configurations" —
   doc 81 target, with the census as its certificate.
3. The meeting's remaining hope, priced: (i) exact-enumeration harvest
   (B1-Fourier + optimal 2-block with released budget — compute the exact
   number next); (ii) (EFF-E) residual certification; (iii) an odd-parity
   counter (doc 72 §9.3) that changes the BUDGET side. If (i)+(ii) still
   land > budget, the finite-height meeting is refuted at instrument-class
   grade and Route C terminates as: spine proven above 10^21, meeting
   impossible with T-averaged instruments — the detailed dead-end record
   the /goal demands.

## 8. TERMINAL POINTER (2026-07-05)

The §1 terminal criteria are RESOLVED on the refutation branch: doc 82
(route-c-verdict) locates the unsound link (the registration gap in
doc 72 §4) and proves the patched spine fails at every threshold and every
height within the certified class. Route C-direct: DEAD (5-failed card:
route-c-direct-registration-gap.md). Living heirs: Route B (mollified,
regains ParityCounting) and the exponential-AFE family (registration
UNTESTED — next object).
