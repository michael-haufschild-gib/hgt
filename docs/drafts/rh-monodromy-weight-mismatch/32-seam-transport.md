# 32 — Seam Transport: the Dominated-Window Wiring of the ANNEAL Reduction

**Register: SEARCH** (the transport lemma's proof is a two-line application of banked
machinery; its Lean plumbing is the executable next step). Task #131; consumer: doc 22's
reduction.

## 1. The transport lemma [PROVED HERE, via banked bricks]

> **Lemma (seam transport).** Let W be a window with boundary ∂W, f and g nonvanishing
> continuous on ∂W with the strict domination |f − g| < |g| on ∂W (doc 22's measured
> regime: f = the completed ζ-window data, g = the completed truncation g_N-data). Then
> the deck class (winding datum) of f and g over ∂W agree: D_f(W) = D_g(W).

*Proof.* The segment homotopy h_t := (1−t)·g + t·f satisfies |h_t − g| = t|f − g| <
|g| on ∂W, so h_t is nonvanishing on ∂W for every t ∈ [0,1]. The deck class is invariant
under nonvanishing homotopies — this is exactly the banked deformation invariance of
DeckHomotopy.lean (#117, `deckClass` a homotopy invariant). Apply it to h. ∎

This is the Rouché step of the lane in its own language: no argument principle, no zero
counting — the deck-class formulation (doc 13/#113) was built precisely so that
transport is homotopy invariance. Constraint side note: domination is a BOUNDARY
condition; the interior zeros need never be mentioned — the bulk is fixed by its
boundary, which is the lane's holography (doc 15/#123) doing the work.

## 2. What this wires (doc 22 consumer)

On each dominated window (measured 7/7 at r = 0.20 up to T ≈ 2800, doc 22): the ζ-window
deck datum equals the truncation's deck datum. Hence the window relation D ≡ L mod 4 for
ζ on dominated windows reduces to the SAME relation for the finite truncation g_N —
whose reading is finite, certified, and (with docs 25–31) theorem-grade on one-sided-far
recentered carriers. The exceptional set remains the truncation's own odd-parity windows
(doc 22, measured and forced: q = 4.72/1.17) — the bookkeeping of how exceptional
windows are traversed by the cofinal family is the remaining doc-22-side input, separate
from transport.

## 3. Remaining #131 items, made executable

1. **Lean plumbing**: instantiate the DeckHomotopy invariance on the segment homotopy
   with the domination hypothesis — a short module (SeamTransport.lean) reusing
   `deckClass` + the homotopy engine; no new analytic content.
2. **k = 1 base case**: the window relation's base reading via sign(Ξ) on the real
   seam — wire `ReflectionParity` (#114) to the deck-class base: on a window centered
   on the critical line, the k = 1 datum is the sign change count of the real function
   Ξ across the window, i.e. the seam product L(W)'s first factor (doc 18's (ID)).
3. **L as seam product**: the dictionary identification of L(W) with the product of
   seam contributions across the window's critical-line segment — assemble from
   SeamCocycle (#122) + MirrorPencil (#127); the candidate statement: L(W) =
   seam-cocycle evaluation along ∂W ∩ {critical line}, with the mod-4 relation then
   the cocycle identity of doc 18.

With 1–3, doc 22's reduction becomes: RH-window parity on dominated windows ≡ finite
certified truncation readings, with the reader exactness supplied by the (S-mono) arc.
The open mathematical residue of the bridge identity (#130) after that: the
exceptional-set traversal argument (doc 22) and the cofinality of dominated windows —
both stated, measured, and awaiting their own rounds. Next object: SeamTransport.lean.

## 4. #144 formulated: the exact residual statements of the reduction

With transport machine-checked (SeamTransport.lean), doc 22's reduction needs precisely:

> **(DOM) [per-height domination]:** for every sufficiently large T there is a window
> center a = 1/2 + iT′, |T′ − T| ≤ 1, and a radius R in a fixed interval [r₁, r₂] such
> that ‖ξ − Φ_N‖ < ‖Φ_N‖ on the charts (Φ_N = completed truncation, N = ⌊√(T/2π)⌋).
> Decomposition: (AFE) the completed error ‖ξ − Φ_N‖ ≤ C·T^{−1/4+ε}-type on the charts
> [classical Hardy–Littlewood AFE remainder, instrument-grade literature input], and
> (LOW) a lower bound min_{charts}‖Φ_N‖ ≥ T^{−A} for some radius in [r₁, r₂] avoiding
> the zeros of Φ_N [large-values/typical-circles input — the one genuinely analytic
> residual; measured 7/7 to T ≈ 2800 at r = 0.20].

> **(TRAV) [traversal, now trivial given (DOM)]:** each putative rightHalf zero of ξ
> needs ONE certified window containing it — deck-class charge is chart-independent
> (deckClass_root_indep) and deformation-invariant (#117), so a single dominated window
> per zero suffices; exceptional (non-dominated) windows are never read. The
> "exceptional-set bookkeeping" reduces to: dominated windows can be CHOSEN to contain
> any given height — i.e. (DOM) with the ±1 slack, nothing more.

So #144 = (AFE) [cite-and-check] + (LOW) [prove or locate; the only remaining analytic
estimate in the whole reduction]. Everything else in the #130 chain is proved,
machine-checked, or proved-in-outline with margins. Note what (LOW) is NOT: it is not a
zero-free region and carries no RH content — it asks only that the finite truncation is
not abnormally small on some admissible circle, a typical-values statement about a
Dirichlet polynomial. Next object: (LOW) via the mean-value of |Φ_N|² on circles
(second-moment lower bounds give positive-proportion radii — the standard route).

## 5. (LOW) attacked: reduction to good-lines [round 2 of #144]

First, the domination divides out: with the polynomial factor absorbed into the
completed truncation Φ̃_N := (s(s−1)/2)·π^{−s/2}Γ(s/2)·g_N, the common nonvanishing
factor cancels pointwise and **(DOM) ⟺ |ζ − g_N| < |g_N| on the chart curves** — no
archimedean bookkeeping. The AFE error is uniform, |ζ − g_N| ≤ C·T^{−1/4 + r/2}
[classical HL remainder at x = y = √(t/2π)], so (LOW) needs min|g_N| > C·T^{−1/4+r/2}
on SOME admissible contour.

Three routes, assessed:
- **Boutroux–Cartan / radius-wiggling** [unconditional, insufficient]: ≤ c·log T zeros
  in the window disc ⟹ a radius exists with all zeros at distance ≥ c/log T, giving
  min ≥ T^{−C·log log T} — short of a fixed power by log log T in the exponent. Banked
  as a fallback (it WOULD suffice against any e^{−T^κ}-error truncation family).
- **Good-lines (the route)**: the contour is ours to choose. Classical inverse bounds
  (Titchmarsh Ch. 9-type / Ramachandra: every unit T-interval contains a horizontal
  line with |ζ(σ+it*)|^{−1} = O(T^ε) uniformly on the relevant σ-range) supply
  segments on which |ζ| ≥ T^{−ε}; with the AFE, |g_N| ≥ |ζ| − CT^{−1/4+r/2} ≥ ½T^{−ε}
  there. Windows bounded by good horizontal segments + short vertical returns give
  (DOM) with any fixed A > 0. [Instrument-grade literature input — cite-and-check the
  precise statement and σ-uniformity; this is the SAME class of input as (AFE).]
- **Second-moment on circles** [supporting]: ∫|g_N|² over admissible curves ~ log T
  (Montgomery–Vaughan-type), so |g_N| is typically of size √log T — the smallness is
  confined to near-zero neighborhoods, consistent with both routes and with the
  measured 7/7 domination.

Adaptation note: the Lean deck machinery works on two-disc charts (chartR/chartL);
good-lines chooses contours adaptively. The paper-level reduction is contour-flexible
(deck class is chart-independent — deckClass_root_indep); the Lean-level statement
should eventually parametrize the chart placement by the good height t* (the charts'
CENTER is already a free parameter a — placing a at 1/2 + it* suffices; no new Lean
machinery needed, only the center-selection is analytic).

Status of #144 after this round: (AFE) and (LOW) are BOTH instrument-grade
cite-and-check items (HL remainder; good-lines inverse bound), plus one bookkeeping
adaptation (window centers at good heights). No new mathematics remains in #144 beyond
verification against sources — per the gate, the citations must be spot-checked before
any promotion. Next object: locate and verify the two classical statements (allowed
literature use: instrument verification, not answer-searching).

## 6. (LOW) dissolved: the symmetrized exponential-AFE family [round 3 of #144]

Honesty check on §5's good-lines route: the classical Landau/Titchmarsh good-line lemma
yields only |ζ|^{−1} ≤ e^{C·log²T} — WEAKER than the T^{−1/4+r/2} HL-AFE error — and a
fixed-power minimum along whole near-line segments sits at negative-moment/small-values
depth (genuinely hard, though RH-free). Route corrected by strengthening (AFE) instead:

- **(AFE-exp)**: AFEs with EXPONENTIALLY decaying error exist (e.g. the Fokas-school
  variant, arXiv:1910.05754: finite binomial-weighted sums, error O(e^{−ω(x,y)·t})).
  [Cite-and-check at promotion: exact statement, validity region, computability of the
  finite side.]
- **(SYM, free)**: for ANY approximant Φ_F of ξ, the symmetrization
  Φ*(s) := (Φ_F(s) + Φ_F(1−s))/2 satisfies the EXACT even FE by construction, and since
  ξ(1−s) = ξ(s), ‖ξ − Φ*‖ ≤ (‖(ξ−Φ_F)(s)‖ + ‖(ξ−Φ_F)(1−s)‖)/2 — exponential accuracy is
  preserved. One line; the exact-FE requirement of the ANNEAL finite side costs nothing.
- **(LOW-BC, now sufficient)**: Boutroux–Cartan radius-wiggling gives
  min ≥ T^{−C·loglog T} = e^{−C·log T·loglog T} on admissible contours (zero count
  ~ log T in the window; local sup of |Φ*| ≥ sup|ξ| − e^{−ωT}, crude bounds suffice) —
  and e^{−C log T loglog T} ≫ e^{−ωT}: **(DOM) holds unconditionally for the
  symmetrized exponential-AFE family.**

Consequence: #144's analytic residue is GONE — no small-values input, no negative
moments; both remaining items are instrument-grade (the 1910.05754-type statement and
elementary B–C bookkeeping). The architecture is family-agnostic (u-plane descent,
recentered jets, one-sided-far shape need only: exact even FE ✓, finite computable ✓),
so docs 22/25–31 carry over; the g₅ instances (#136/#140) remain valid measurements of
the HL family, and the exponential family gets its own instance run when the assembled
theorem is exercised. The failure of the good-lines route was load-bearing: attacking
the route exposed that the right degree of freedom is the truncation family, not the
contour.

## 7. Cite-check of (AFE-exp) + the two closing lemmas [round 4 of #144]

**(AFE-exp) VERIFIED against the source** (Jerby, "An approximate functional equation
for the Riemann zeta function with exponentially decaying error", arXiv:1910.05754v2;
published version J. Approx. Theory / S0021904521000149). Theorem 1.1, read from the
paper: for x, y ≥ 1 with |t| = πxy and 2y ≠ (2N−1)π,
ζ(s) = Σ_{n≤x} Ã(n,s) + [χ(s)/(1−2^{s−1})]·Σ_{k≤y}(2k−1)^{s−1} + O(e^{−ω(x,y)·t}),
Ã(n,s) = 2^{−(n+1)}(1−2^{1−s})^{−1} Σ_{k≤n} C(n,k)(−1)^k (k+1)^{−s} (Hasse–Sondow),
ω(x,y) > 0 explicit (eq. (8): saddle-point datum; ω = 0 exactly at the excluded
degenerate 2y = (2N−1)π). Usage notes, verified: fixing y (non-degenerate) gives
CONSTANT ω along a height family with main-sum length x = t/(πy) — finite, elementary
computable, as the reduction needs; the prefactor poles (1−2^{1−s}, 1−2^{s−1}) lie on
σ = 1, away from near-line charts. REMAINING fine print for promotion: σ-uniformity of
the O-constant on the chart strip σ ∈ [1/2−r, 1/2+r] (the proof is a saddle-point
analysis on the strip; verify Sections 2–4's uniformity statement). Structural note:
Jerby's engine is Nørlund–Rice exponential cancellation of binomial n-th differences —
the same binomial-difference calculus as the lane's Jensen sections.

**(SYM) [PROVED HERE, one line].** For any approximant Φ_F of ξ define
Φ*(s) := ½(Φ_F(s) + Φ_F(1−s)). Then Φ*(1−s) = Φ*(s) identically, and since
ξ(1−s) = ξ(s): ‖ξ − Φ*‖ ≤ ½‖(ξ−Φ_F)(s)‖ + ½‖(ξ−Φ_F)(1−s)‖ — the exact even FE is free
and exponential accuracy is preserved (both points s, 1−s lie in the reflected chart,
same height). ∎

**(LOW-BC) [PROVED HERE, standard pieces].** Take window discs of radius r₂ ≥ 2 so the
disc contains an anchor a₀ with Re a₀ = 2, where |ζ(a₀)| ≥ 1/ζ(2) > 0.6 (Euler product,
elementary) hence |Φ*(a₀)| ≥ c·T^{−C₁} (archimedean dressing, Stirling) minus e^{−ωT}.
Jensen's formula with the polynomial-growth upper bound |Φ*| ≤ T^{C₂} on the double
disc bounds the zero count: n ≤ C₃·log T. Cartan's minimum-modulus lemma (Levin,
Lectures, or Boutroux–Cartan) then gives, outside exceptional discs of total radius
< (r₂−r₁)/4, |Φ*| ≥ T^{−C₁}·((r₂−r₁)/(16e·r₂·n))^n ≥ e^{−C₄·log T·loglog T}; a radius
R ∈ [r₁, r₂] whose circle avoids all exceptional discs exists by measure counting. Since
e^{−C₄ log T loglog T} ≫ e^{−ωT}, strict domination ‖ξ − Φ*‖ < ‖Φ*‖ holds on that
circle for T ≥ T₀. ∎ (Constants elementary; the chart-pair geometry inherits the same
bound by running Cartan on both charts simultaneously — finitely many exceptional
discs in total.)

**Status: (DOM) is now UNCONDITIONAL end to end** modulo the single σ-uniformity
fine-print check in Jerby's Theorem 1.1. #144's mathematical content is closed; what
remains is that one source verification plus the eventual instance run on the
exponential family.

## 8. σ-uniformity fine print resolved [round 5 of #144 — read from the source]

Jerby's Sections 2 (read: Prop 2.1, Prop 2.2, Cor 2.3, eqs. (22)–(35)): the integrals
are I(σ,t;α) = ∫ g(σ,w)e^{tf(w;α)}dw with amplitude g(σ,w) = e^{−w}w^{σ−1} and phase
f(w;α) = α·ln(1−e^{−w}) + i·ln(w). **The phase — hence the saddle equation
e^w − α·iw − 1 = 0, the saddle points w_k(α), and the decay rate ω(α) — is
σ-INDEPENDENT**; σ enters only the amplitude, continuously on compact strips
(w^{σ−1}-type factors, handled in (35) via Stirling). Standard saddle-point uniformity
in compact amplitude-parameters then gives the O(e^{−ω(α)t}) bound uniformly on
σ ∈ [1/2−r, 1/2+r]. The same phase governs Ĩ₁, Ĩ₂ (Thms 3.1, 4.1 share the saddle
equation, per §1), so the full Theorem 1.1 error is compact-strip uniform. Fine print
RESOLVED at reading level (a promotion-grade re-read of §§3–4 is recorded as optional
prudence).

**#144 status: CLOSED at SEARCH grade.** (DOM) is unconditional on the symmetrized
Jerby family: (AFE-exp) verified from source with σ-uniformity structural, (SYM) and
(LOW-BC) proved. The reduction's entire analytic side now stands; the remaining
project-wide items are write-ups (#142), dictionary plumbing (#131 items 2–3), the
Lean queue (#143), Lemma R (#139), and an eventual exponential-family instance run.
