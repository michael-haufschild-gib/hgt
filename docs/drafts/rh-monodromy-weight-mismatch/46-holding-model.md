# 46 — σ(p) Refutes Pointwise Attraction; the Holding Model Fits to 5%

**Register: SEARCH** (task #130). Certification: `computations/mwm/sigma_profile.py`
(P-S1 pre-registered → FAIL, the registered fail-branch fires) + the survivor
census of doc 43 §9 re-read through the beat phase.

## 1. P-S1 FAIL: the push sign is configurational, not resonant

Uniform p-grids on two fresh intervals (N = 22, 35; 19 p-points × 3 windows):
the λ-derivative of the minimal on-line gap has NO systematic sign profile in p
— attraction and repulsion scatter across the whole interval. Consistent with
first-order theory: at fixed height the marginal term's push on a gap is
ε·c·(1/a₁ + 1/a₂) with c = cos(φ(t)+φ₀) FROZEN in λ — its sign is set by the
local configuration, both signs occur everywhere. The film's clean attraction
at the survivors (doc 45) was therefore SELECTION (survivors are where
collisions completed), and doc 45 §2's "coherent attraction near resonance"
is superseded as the explanation of the p-clustering.

## 2. What survives, and the model that replaces it

Birth = marginal-term-driven collision stands (P-B1/P-B2, λ* ≈ 0.7: the pairs
need ≥ 70% of the term — LOAD-BEARING, not perturbative). The p-clustering is
explained by **holding, not birth**:

> **(HOLD) [CONJECTURE, measured-consistent to 5%]:** an off-line pair of Φ_N
> held by the marginal term persists only while the term's beat phase since its
> stationary point, Δφ(p) = 2πp², stays below a threshold Δφ* ~ 0.2 rad.

Quantitative fit: the 8 survivors' Δφ values are .0004–.21 rad — ALL within
0.21; free placement would reach 1.6 at p = 0.5. Predicted cutoff
p* = √(Δφ*/2π) ≈ 0.18; observed 0.19. And no OTHER term can hold: term n's own
resonance is at 2πn², so at interval N's central heights every non-marginal
term sits at beat phase ≥ 2π(1−p)² ~ 10+ rad. Only the marginal term, only
near ITS stationary point.

## 3. The two-lemma proof shape for (MID-central)

1. **(HOLD-lemma):** a mid-depth pair whose existence equation is dominated by
   a single term (the collided/term-held type — ALL 8 measured survivors are
   this type, dying at λ < 1) requires that term's phase alignment within
   Δφ*; beat-phase accumulation 2πp² excludes p > p*. Shape: oscillatory
   bookkeeping on the explicit pair equation γ(ρ)A(ρ) = −γ(1−ρ)A(1−ρ) with
   the single-term share isolated.
2. **(GEN-valley):** mid-depth pairs with NO load-bearing term (generic
   N^{−2η}-deep cancellation valleys) do not occur on self-dominated windows —
   the doc-12 small-ball object, with a new measured census: ZERO occurrences
   of generic-type mid-band pairs in [200, 12000] (all 8 are term-held).

(HOLD-lemma) + (GEN-valley) + (MOAT-shallow) [proved] + cofinality [classical
shape] = (SD-parity) on the p-central family = (WR_1) = RH_2.

## 4. Openings

1. (HOLD-lemma) write-out: isolate the marginal share in the pair equation at
   the measured survivors (the τ-share statistic), then the beat-phase
   monotonicity — classical oscillatory work on ONE explicit equation.
2. (GEN-valley): the small-ball with the mechanism anchor — a generic valley
   must cancel N^{1/2}-mass to depth N^{−η} WITHOUT a dominant term: doc 12's
   tilted small-ball plus the #146 coherence measurements.
3. Cross-check (HOLD) at one more census decade (T ~ 20000–30000: predicted
   max p of survivors still ≤ 0.18 + depth-dependence: deeper pairs → tighter
   phase window — a refinement worth one run).

## 5. The reach law [measured 8/8; the (HOLD-lemma) anchor]

`computations/mwm/tau_share.py` (P-T1 pre-registered, PASS — stronger than
registered): with reach(ρ) := |P_N(ρ)|/|Φ_N′(ρ)| (the distance the marginal
term can move the zero),

> **(REACH) [CONJECTURE, 8/8 measured, min margin 1.10]:** every mid-band pair
> satisfies η ≤ reach(ρ) — measured reach/η ∈ [1.10, 2.11] across all
> survivors, N = 14…42.

Reading: no pair sits beyond the marginal term's reach; the term that made it
can unmake it. This resolves the amplitude paradox of the film (the term,
nominally N^{−1/2−η} — below the valley floor N^{−η} — moves the zero freely
because |Φ′| inside the valley is itself small: reach ≈ 2w·N^{−1/2} with w the
valley width). Consequences for the proof shape of §3: (REACH), if proved,
SUBSUMES (GEN-valley) — generic (term-independent) mid-band pairs would violate
it, and zero were measured. The residual content of (REACH) is a joint
smallness statement: a mid-depth valley cannot be STIFF (|Φ′| large) — depth
and softness are coupled in the coherent sum. That coupling is a
Hadamard/Borel–Carathéodory-shape fact (a function small in a disc has small
derivative in a sub-disc UNLESS a zero-free obstruction — here the pair itself
IS the zero), suggesting (REACH) may be provable by the same two-zero
factorization technology as (MOAT-shallow): write Φ = (s−ρ)(s−ρ')H near the
pair; then Φ′(ρ) = (ρ−ρ')H(ρ) = 2η·i·... — |Φ′(ρ)| = 2η|H(ρ)| EXACTLY. So
(REACH) ⟺ |P_N(ρ)| ≥ 2η²|H(ρ)| — the SAME η²|H| object as (MOAT-shallow)!
The reach law is the statement that the marginal term dominates the pair's
own moat depth. [Next write-out target: bound |H(ρ)| above via the max
principle (done in doc 43 §6) and |P_N(ρ)| below (explicit Stirling — no
zeros of P_N off the line since it is a single RS-pair term with |γ(ρ)N^{−ρ}|
≠ |γ(1−ρ)N^{ρ−1}| for η > 0 — CHECK: P_N(ρ) = 0 ⟺ the two γ-terms cancel ⟺
modulus equality which fails off-line at rate η·log((t/2π)/N²) = η·(beat) —
SMALL exactly near resonance! P_N has near-zeros off-line near p ≈ 0 — the
lower bound on |P_N| degrades exactly where the survivors live. The reach
law's proof must thread this: the term's strength off-line is controlled by
the SAME beat phase — the (HOLD) phase window and the (REACH) amplitude window
are one object.]

## 6. The final reduction: (BVAL) — rigidity of the under-resolved background

Exact chain (no estimates): a pair of Φ_N at ρ = 1/2 + η + it₀ means
B(ρ) = −P_N(ρ) for the background B := Φ_{N−1}; on the line
|P_N(1/2+it)| = 2|γ|N^{−1/2}|cos φ(t)| with φ = t·log N − θ_γ(t) (stationary at
t = 2πN²); and the pair's depth is read off the line-dip η² = |Φ_N(s₀)|/|H(s₀)|.
So a mid-band pair REQUIRES the background to hold an off-line valley of depth

> |B(ρ)| = |P_N(ρ)| ≤ 2|γ(ρ)|·N^{−1/2−η}

— an N^{−1/2}-deep valley of Φ_{N−1} at a height in interval N, where the
(N−1)-truncation is UNDER-RESOLVED (its matched range ended at 2πN²). The wall,
in its final measured form:

> **(BVAL) [the irreducible statement]:** the one-term-under-resolved carrier
> Φ_{N−1} has no off-line valleys of depth 2|γ|N^{−1/2} at p-central heights of
> interval N.

Instance data already in hand: the film's λ = 0 frames (doc 45 P-B1) ARE (BVAL)
checks — the background was clean at both survivor heights. And (BVAL) points
at the literature's own axis: G–M's 100%-on-line theorem is EXTREME
under-resolution (N ≤ T^{o(1)}); (BVAL) needs one quantitative step of the same
rigidity at mild under-resolution. #149's full-text question is now exact.

**The p-mechanism, derived at sketch grade [CONJECTURE]:** the pair equation
needs (depth ∧ phase) of B to match P_N. Near resonance, |cos φ| is FROZEN over
long stretches — when frozen near its maximum, the required B-valley depth is
the SHALLOWEST possible (2|γ|N^{−1/2}), making pairs maximally easy; off
resonance cos φ oscillates, and the joint requirement is strictly deeper on
average (near quadrature both sides must be doubly small). Resonance = the
frozen-maximum window of the marginal term's line-modulus. This upgrades (HOLD)
from a fit to a mechanism with a computable cos-distribution behind it — the
quantitative write-out is an averaging computation over φ.

The attack's ledger, end of day: ζ removed (self-domination); shallow pairs
killed [PROVED]; deep pairs empty [measured + Bernstein]; survivors term-held
within reach 8/8 [measured, with the exact identity |Φ′(ρ)| = 2η|H(ρ)|];
p-clustering = frozen-maximum window [mechanism sketch]; the irreducible core =
(BVAL), a rigidity statement about under-resolved finite carriers, with the
census decade running as its out-of-sample test.
