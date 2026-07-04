# 29 — The Lattice Theorem: (S-mono) Proved on the Equal-Spacing Model

**Register: SEARCH** (proof outline [PROVED HERE in outline] — every step carries its
argument; the full constant-chase is the write-up task #142). Task #138/#142, round 5.
Setting: the log-lattice t_k = kδ (k = 1..d), equilibria t*_i ∈ (t_i, t_{i+1}) solving
Σ_k coth((t−t_k)/2) = −d; s_i := t_{i+1} − t*_i (near-ahead distance); N = i behind,
M = d−i ahead; S_i = d + W(t*_i), W = ¼Σcsch²((t−t_k)/2); φ(u) := csch²(u)coth(u),
positive and strictly decreasing.

> **Theorem (lattice (S-mono)).** In the outer range (i ≥ d/2 + explicit margin),
> S_{i+1} > S_i. Hence T = 1 and the counting lemma close on the lattice model.

## Proof outline, five steps

**(a) θ < 1/2, log-lattice version.** All |coth| > 1, so Σχ is strictly decreasing between
poles (each term's derivative (1−χ²)/2 < 0). At the gap's log-midpoint the j-th behind and
j-th ahead terms cancel exactly (equal spacing), leaving ≥ 2i − d + O(1) surplus behind
terms, each > 1. So Σχ(midpoint) ≥ 2i − d > −d, and the equilibrium (where Σχ = −d) lies
RIGHT of the midpoint: s_i < δ/2. The surplus 2i grows with i, so s_i is bounded away from
δ/2 by an explicit margin ≳ i/W̄ — the drift deepens outward, as measured. (Also follows
from doc 27 §3 by AM–GM: right of the arithmetic midpoint in x ⟹ right of the geometric
midpoint = the log-midpoint.)

**(b) The s-march is unconditional.** Write the constraint as H(s; N, M) = 0 where
H(s) := coth(s/2) − B(s,N) + A(s,M) − d, B = Σ_{j≤N}coth((jδ−s)/2),
A = Σ_{m<M}coth((s+mδ)/2). H is strictly decreasing in s (every term's s-derivative is
−csch²/2 < 0). The step (N,M) → (N+1, M−1) changes H at fixed s by
−coth(((N+1)δ−s)/2) − coth((s+(M−1)δ)/2) < −2. So H_new(s_i) < −2 < 0 = H_new(s_{i+1}),
and monotonicity gives **s_{i+1} < s_i — one line, no balance needed.** Quantitatively
s_i − s_{i+1} ≥ 2/(2W̄) = 1/W̄ (|H′| = 2W).

**(c) W is decreasing in s on (0, δ/2) — the disjoint-interval bound.** dW/ds =
¼[Σ_{j≤N}φ((jδ−s)/2) − φ(s/2) − Σ_{m<M}φ((s+mδ)/2)]. Pair the sums termwise
(j = m ≤ M−1): the differences φ((jδ−s)/2) − φ((jδ+s)/2) run over DISJOINT intervals
(jδ−s, jδ+s) of length 2s < δ, so their sum is at most φ((δ−s)/2) (φ decreasing,
intervals nested inside successive gaps); the far-behind surplus (j = M..N) is
exponentially small, ≤ 4·coth(1)·e^{−(M−1)δ}/(1−e^{−δ}). Hence
dW/ds ≤ ¼[φ((δ−s)/2) − φ(s/2) + tail(M)] < 0, since s < δ/2 gives φ(s/2) > φ((δ−s)/2)
strictly, with margin controlled by (a)'s bound on δ/2 − s. **This is (L1), proved.**

**(d) The swap term is exponentially small.** At fixed s the step changes W by
+¼csch²(((N+1)δ−s)/2) − ¼csch²((s+(M−1)δ)/2), of magnitude ≤ tail(M).

**(e) Assembly.** ΔS = ΔW = ∫_{s_{i+1}}^{s_i}(−dW/ds) + swap ≥ (s_i − s_{i+1})·
min|dW/ds| − tail(M) ≥ (1/W̄)·¼[φ(s/2) − φ((δ−s)/2)] − tail(M) > 0: for s small the head
is cubic (φ(s/2) ~ 8/s³ vs W̄ ~ 1/s²: gain ≳ 2/s); for s near its upper range the margin
of (a) keeps the bracket positive; for M = O(1) the direct far-end argument (doc 28 (L3))
takes over. ∎(outline)

## What this proves and what it isolates

The constant-δ lattice carries the full mechanism: the one-sided count (each step converts
one ahead-charge to a behind-charge, worth −2 in H) drives the drift; the near-pole energy
responds cubically; spectators enter only through W̄ and exponential tails. On the
DOUBLY-infinite lattice nothing drifts (doc 28 §5c) — the theorem is made entirely out of
the window's one-sidedness. Constraint, not flow.

The single remaining distance to (LEG) on real section fields is **gap variation**: on real
fields ΔH at fixed s acquires gap-flux terms alongside the −2 count term, and the measured
crossing sits where those dominate. The correct object (doc 28 §5c) is the coupled system
Ḋ = −2W̃, Ẇ̃ = −Σχw with jumps; the lattice theorem fixes the technique (monotone
constraint + disjoint-interval domination); what must be added is a one-sided bound on the
gap-flux for NONDECREASING gaps — conjecturally the flux has a sign: widening gaps ahead
only deepen H_new at s_i, preserving (b)'s one-line march. [CONJECTURE, next round's first
check: on nondecreasing-gap fields, H_new(s_i) < H_old(s_i) still holds termwise, because
every ahead-distance at the new equilibrium exceeds its lattice counterpart and coth is
decreasing.] If that termwise variant survives scrutiny, (b) and (c) generalize verbatim
and (LEG) closes for nondecreasing-gap one-sided fields — which is P-J's measured regime
and doc 25's proved tracking complement.
