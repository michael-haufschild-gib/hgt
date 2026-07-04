# 43 — (DISC-fin)-Unconditional: Self-Domination, and the Shallow/Deep Cut of the Wall

**Register: SEARCH** (task #130's arithmetic core, opened for direct attack).
Companion measurement: `computations/mwm/oddwindow_phase.py` (P-D1/P-D2,
pre-registered, running). Everything here is labelled; the two lemma-shaped
claims are marked for write-out.

## 1. The recast: remove ζ from the statement

The only ζ-reference in the bridge's arithmetic input is domination
|ζ − g_N| < |g_N|. But |ζ − g_N| has the CLASSICAL UNCONDITIONAL bound: for the
symmetric sharp-cutoff AFE (x = y = √(t/2π), Hardy–Littlewood; Titchmarsh
ch. IV), |ζ(s) − g_N(s)| ≤ E(T) with E(T) = O(T^{−1/4}) effective, uniformly on
the window strip. Define a window **self-dominated** iff

> min over ∂W AND the central line segment of |g_N| > E(T)

— a property of the finite object plus one classical bound. Self-domination ⟹
domination ⟹ (banked transport: Rouché on ∂W for D-equality + segment sign-
matching for L-equality) N_ζ(W) = N_{g_N}(W). The unconditional target is
therefore exactly:

> **(SD-parity):** every self-dominated admissible window of the exact-FE
> truncation has even off-line parity.

No ζ anywhere. (SD-parity) + cofinality of self-dominated windows (#144's
traversal, now with E(T) in place of measured q) ⟹ (WR_1) ⟹ RH_2; iterated
through doc 38's minor chain ⟹ the full ladder. Contrapositive form — the shape
to attack: **an odd pair forces an E(T)-moat: some point of every admissible
∂W-or-segment around it has |g_N| ≤ E(T).**

## 2. The cut: shallow pairs dig their own moat; deep pairs are large deviations

An odd configuration in the right half-window is a zero ρ = 1/2 + η + it₀
together with its FE partner 1 − ρ̄ = 1/2 − η + it₀ — two zeros at the SAME
height, straddling the line at distance η each side.

**(MOAT-shallow) [lemma-shape, elementary — write-out queued].** Factor the
completed carrier: Φ(s) = (s−ρ)(s−(1−ρ̄))H(s). On the line at t₀:
|Z_g(t₀)| = η²·|H(1/2+it₀)|. So whenever

> η² ≤ E(T)/|H| (threshold η₀(T) ≍ √(E/‖H‖) ~ T^{−1/8}·log-corrections),

the central segment point t₀ itself has |g| ≤ E(T): the window is NOT
self-dominated — the pair's own geometry digs the moat. Proof needs only the
two-zero factorization plus an upper bound for H on a disc (Cauchy + Stirling +
trivial bounds on the finite sum; per-window explicit). **Shallow odd pairs
self-exclude from (SD-parity).** This also resolves run 5's q-trend puzzle
(q = 4.72 → 1.17 as r grows, apparently heading under 1): the forced failure
lives on the SEGMENT, which every admissible window contains regardless of r.

**Deep pairs (η > η₀) are exponentially atypical events of the finite sum.**
g_N(ρ) = 0 ⟺ A(ρ) = −χ(ρ)A(1−ρ), and |χ(1/2+η+it)| = (t/2π)^{−η} = N^{−2η}. So
a depth-η zero forces |A(1/2+η+it₀)| = N^{−2η}|A(1/2−η−it₀)| — the polynomial
must sit a factor ~N^{−η} BELOW its rms at the upper point (or symmetrically
above at the lower): a valley of depth e^{−η log N} in a Dirichlet polynomial of
length N. By the Bernstein-type slope bound |d log A/dt| ≲ log N off zeros, such
a valley has t-width ≳ η — deep pairs force WIDE structures, and for η ≥ 1/4 the
valley floor itself sits below E(T) = N^{−1/2}-scale (an automatic wide moat).
**The residual open band is η ∈ (η₀(T), ~1/4): mid-depth pairs.** This is where
the arithmetic must act, and it is a LARGE-DEVIATION statement about the
coherent finite sum — the regime where #146 measured the coherence suppression
(4–5 events per 830 height units for a_n = 1, vs 91–151 for incoherent
streams), and where doc 12's large-deviation rate-separation machinery (banked
salvage: L1a concentration, tilted small-ball) applies to a FINITE object.

## 3. The RS tower: the moat threshold is a dial, not a constant

The carrier upgrades: g^(k) := g_N + (first k Riemann–Siegel correction terms)
— still finite, explicit, exact-FE (RS terms respect the functional equation),
with |ζ − g^(k)| ≤ E_k(T) = O(T^{−(2k+3)/4}) and exp-small at resurgent-optimal
truncation. Two consequences:

1. **Parity is coherent along the tower**: consecutive carriers differ by less
   than E_k + E_{k+1}, so windows self-dominated at one level transport their
   parity to the next by the same Rouché+segment logic — no ζ needed. It
   suffices to prove (SD-parity) at ANY ONE level with cofinal self-dominated
   windows.
2. **η₀(k) grows with k**: at level k the shallow-moat threshold is
   η₀ ~ T^{−(2k+3)/8}→ (log T/T-grade at optimal truncation)^{1/2}·… — the
   shallow regime EXPANDS and the open mid-depth band (η₀(k), 1/4) shrinks from
   below as k grows... [correction: E_k smaller ⟹ η₀ = √(E_k/|H|) SHRINKS — the
   shallow band contracts, but the deep-valley requirement at level k is
   unchanged (χ-modulus is the same), while self-domination becomes easier to
   satisfy (smaller E_k) — the trade is: harder to self-exclude shallow pairs,
   easier to certify windows. The optimal level balances the two; the balance
   point is a computable function of the valley statistics.] The weld reading:
   the RS asymptotic series vs the exact object is precisely the archimedean
   seam of the hgt charter, and (SD-parity) interrogates it level by level.

## 4. The measurable half [running]

If odd events of g_N cluster at truncation transitions (RS phase
p = frac √(T/2π) near integers — the "birth of a term" discontinuity), the
exceptional heights are p-localized and the cofinal family dodges them; the
mid-depth band then needs only a p-locus theorem. Pre-registered (P-D1, prior
0.5): mean |p − nearest integer| ≤ 0.17 over ≥ 25 events. P-D2 (prior 0.7): all
measured pair depths η < 0.35 (no deep pairs at accessible heights —
consistency of the cut). Banked 9 events give mean ≈ 0.20 — inconclusive; the
[1030, 5000) sweep is running.

## 5. What closes (WR_1) from here — the honest ledger

1. (MOAT-shallow) write-out — elementary, one page, per-window explicit. [next]
2. Cofinality of self-dominated windows with the E(T) bound — an |g_N|-lower-
   bound-off-zeros statement for the finite object; classical-technique shape.
3. **The mid-depth band η ∈ (η₀, 1/4)** — the true residue of the wall. Routes,
   in current order: (a) p-locus (if P-D1 passes: transition-birth mechanism +
   traversal); (b) large-deviation exclusion — the valley of a coherent
   (multiplicative, positive) stream of length N cannot reach depth N^{−2η}
   within a self-dominated neighborhood (doc 12 salvage + #146 mechanism);
   (c) the RS-tower balance of §3.
4. Then (WR_1) = RH_2; doc 38's Hankel-minor ladder for k ≥ 2.

The wall has not moved — but it now has a coordinate system: one elementary
lemma, one classical-shape lemma, and ONE named band of exceptional events with
three independent attack routes and a running measurement to pick among them.

## 6. (MOAT-shallow), written out [PROVED HERE]

**Lemma (MOAT-shallow).** Let Φ be the completed carrier (real on the line),
with zeros ρ = 1/2 + η + it₀ and its FE partner ρ' = 1 − ρ̄ (0 < η < r), and
let M_r := max_{|s−s₀|=r} |Φ|, s₀ = 1/2 + it₀. Then

> |Φ(1/2 + it₀)| ≤ η²·M_r/(r − η)².

*Proof.* H := Φ/((s−ρ)(s−ρ')) is analytic on the closed disc (removable
singularities; other zeros of Φ are harmless). On the boundary |s−ρ| ≥ r − η
and |s−ρ'| ≥ r − η, so |H| ≤ M_r/(r−η)² there, and by the maximum principle
also at s₀. Since (s₀−ρ)(s₀−ρ') = −η², the claim follows. ∎

**Corollary (self-exclusion of shallow pairs).** With E*(T) the completed-
normalization AFE bound and η ≤ r/2: if

> η ≤ η₀(T, r) := (r/2)·√(E*(T)/M_r),

then |Φ(1/2+it₀)| ≤ E*(T): the central segment point t₀ already violates
self-domination — no admissible window around the pair is self-dominated. ∎

M_r is explicit per window (Stirling for the γ-factors, trivial bounds for the
finite sums), and the domination ratio is normalization-free on the line, so
the uncompleted and completed statements agree. The open mid-depth band of §2
now has a sharp lower edge: η₀(T, r) with r at the local spacing scale.

## 7. Measurement outcome (same day; archive `computations/mwm/oddphase.out`)

The [1030, 5000) sweep found 28 new odd boxes (37 events total with the banked
9). Refinement succeeded on 20; of these one is a filter leak (T = 1889 refined
onto the line, η = 0.000 — the muller root left the box through the σ = 0.53
edge and the acceptance test used σ > 0.5; pipeline fix needed). Honest stats on
n ≈ 19–20: mean |p − nearest integer| = 0.167 vs uniform 0.25 — a ≈ 2.6σ deficit,
with visible mass very close to integers (p = .003, .010, .019, .027, .081,
.870, .921, .938). **P-D1 FAILS AS REGISTERED** (required n ≥ 25) — the effect
direction is present but the sample and the 12 unrefined events (possible
selection bias) block the claim. **P-D2 PASSES**: every measured depth
η ∈ [0.039, 0.178] — no deep pairs at accessible heights, and the range brackets
the estimated η₀ ~ 0.07: both the shallow regime (self-excluded by §6) and the
mid-depth band are populated. Next round: fix the refinement (winding-guided
subdivision as in run 5, box-strict acceptance), extend to [5830, 12000] for
n ≥ 30, and per-event compute η₀(T, r) to classify each event
shallow-vs-mid-band directly — the fraction of odd events NOT killed by the
proven lemma is the exact size of the remaining wall.

## 8. Correction to §1's definition, and the transport it actually buys

**The §1 definition is broken as stated**: "min over the segment > E(T)" is
violated by every window containing an on-line zero of Z_g (the min is 0).
Corrected:

> **Self-domination (corrected).** (i) min_{∂W} |g_N| > E(T); (ii) between
> consecutive zeros of Z_g on the central segment (and between the segment
> endpoints and their nearest zeros) there is a TEST POINT with |Z_g| > E(T).

Both are properties of the finite object. What transports:

- (i) + banked boundary transport (deck/ANNEAL, #134): **N_ζ ≡ N_g (mod 2)** —
  the parity form needs the boundary only.
- (i) + (ii): the test-point sign pattern of Z_g transfers to Z_ζ
  (|Z_ζ − Z_g| ≤ E < |Z_g| there), so L_ζ ≥ L_g; with Rouché D-equality:
  **N_ζ ≤ N_g** — a one-sided COUNT transport, strictly stronger than parity
  when N_g is small. With N_g = 0: N_ζ = 0 (RH on the window); with N_g = 2:
  N_ζ ∈ {0, 2} (parity via deck + bound via signs).

So the bridge architecture sharpens: on self-dominated windows with N_g = 0 —
the generic case; odd/nonzero events are the measured ~37 boxes per 11800
height units — the transport gives N_ζ = 0 outright, and the parity ladder is
needed only across the exceptional heights (#144's traversal).

**The corridor caveat, and its resolution by the lemma.** The box census counts
only η > 0.03 (the inner box edge); pairs in the corridor η ∈ (0, 0.03) are in
N but invisible to the sweep. But (MOAT-shallow) kills every pair with
η ≤ η₀(T, r) — so the corridor is entirely lemma-excluded at heights where
η₀(T, r) ≥ 0.03, a per-height computable condition (the classification run's
lemma-margins measure exactly this). Census blindness is harmless wherever
η₀ ≥ 0.03.

## 9. Classification outcome: the wall is eight events, all at the seam of the truncation

Run: `oddwindow_classify.py` (guided refinement — 76/81 events clean vs 20/37
before; archive `oddclass.out`). All three registered predictions PASS:

- **P-D1′ PASS** (n = 76): mean |p − nearest integer| = 0.1685 vs uniform 0.25
  — a ≈ 4.9σ deficit. The transition-clustering of odd events is real.
- **P-D2′ PASS**: max η = 0.178 across [200, 12000] — deep pairs (η ≥ 1/4) do
  not occur; §2's upper regime is empty in practice.
- **P-D3 PASS**: **89% of all odd events are SHALLOW — killed by the proven
  §6 lemma** (with the E*-proxy constant 1, r = 0.5). The measured wall is the
  **8 mid-band survivors** in 11,800 height units (≈ 1 per 1,500):

  | T | p | η | lemma-margin |
  |---|---|---|---|
  | 1415.7 | .010 | .171 | 2.74 |
  | 4253.5 | .019 | .115 | 1.35 |
  | 4589.7 | .027 | .178 | 2.51 |
  | 4990.4 | .182 | .142 | 1.63 |
  | 6430.8 | .992 | .116 | 1.25 |
  | 7712.9 | .036 | .096 | 1.19 |
  | 7734.7 | .086 | .097 | 1.08 |
  | 11127.6 | .083 | .122 | 1.66 |

Two structural facts about the survivors: (a) **seven of eight sit within 0.086
of a truncation transition** (survivor mean |p − int| = 0.056 — three times more
concentrated than the odd population, five times more than uniform): the
mid-band mechanism is the BIRTH JUMP at N → N+1. (b) every lemma-margin is
≤ 2.74: a factor-3 sharpening of (MOAT-shallow) — multi-zero factorization
(remove the flanking on-line zeros from H as well; each nearby zero tightens),
per-event r-optimization, or the true AFE constant — would kill every measured
survivor.

**The p-central family.** Define the window family at heights with
p(T) ∈ [0.2, 0.8] (60% of all heights, cofinal by construction). Measured
mid-band survivors in it: **zero** (the closest, T = 4990.4, has p = 0.182).
(SD-parity) restricted to the p-central family has no measured counterexample
in [200, 12000]. The unconditional residue is now: (1) NO mid-depth pairs at
p-central heights — the sharp hard core; (2) cofinality of the restricted
family (classical shape: MV theorem + Paley–Zygmund for test points and
boundaries; small-ball via doc 12's banked (D′) for the |A|-lower bounds);
(3) mine Gonek–Montgomery's rectangle counts (#149: family in print, IMRN 2013;
their 100%-on-line theorem needs N ≤ T^{o(1)} — the AFE-matched regime is open
ground) for a printed off-line density input.
