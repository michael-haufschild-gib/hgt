# 49 — The Tower Walk and the Gauss Phase Lattice

**Register: SEARCH** (task #130; the iterated-sweep bookkeeping on doc 48's
exact dichotomy). Everything labelled; §2's identity is a Taylor computation,
proved as stated.

## 1. The tower as a branching-absorption walk [structure, from proved parts]

Fix a p-central height t; run the tower Φ_k = Φ_{k−1} + P_k up to the matched
level N = ⌊√(t/2π)⌋. By the exact dichotomy (doc 48 §2), each entry P_{j}
updates every existing pair by ONE real number q₀^{(j)} = Z_{P_j}(t_B)/g₀:

> η² ← η² + q₀^{(j)}, absorbed (pair lands ON the line) when η² + q₀ ≤ 0.

The pair's squared depth performs a WALK with an absorbing barrier at 0 —
killed is first-passage, not coin-flip: the survive branch includes both
deepening (q₀ > 0) and SHALLOWING (−η² < q₀ < 0), and shallowed pairs are
primed for absorption at the next entry. Step sizes |q₀^{(j)}| ≈
2 j^{−1/2}|cos φ_j(t)| / ‖g‖. Creation is the reverse dichotomy on soft
on-line pairs (q₀ ≥ v₀²). The matched object's pair population at height t is
the equilibrium of this branching-absorption process — and (MID-central) is
the statement that at p-central this equilibrium is empty in the mid-band.

## 2. The phase lattice [PROVED HERE — Taylor, exact coefficients]

At t = 2π(N+p)², expanding φ_{N−m}(t) = t·log(N−m) − θ_γ(t) in m:

> **φ_{N−m}(t) ≡ φ_N(t) − 4πp·m − π·m² (mod 2π), error O((m³ + p·m² + p²m)/N)**

(from t·m/N ≡ 4πpm, t·m²/2N² ≡ πm² mod 2π). The tower's push phases are a
QUADRATIC GAUSS LATTICE in the entry-offset m, with p as the linear phase
parameter. Three consequences:

1. **p ≈ 0: alternating anti-phase.** The πm² term gives phases
   (0, π, 0, π, …): consecutive sub-marginal entries push in OPPOSITION and
   pairwise cancel — the marginal entry's dominance near resonance is now
   DERIVED, not observed.
2. **Full coherence at p = 1/4 and p = 3/4.** 4pm + m² = m(m + 4p) is even for
   every m exactly when 4p is an odd integer: the whole tower tail pushes IN
   PHASE. Sharp prediction: collective sweep/creation anomalies at
   p ≈ 1/4, 3/4 — the census shows no survivors there, so if the coherence is
   real it SWEEPS (a collective kill zone, not a birth zone). [Testable; also
   note p = 1/2 is NOT coherent — m(m+2) odd for odd m.]
3. **Generic p: square-root cancellation.** The collective push of the last M
   entries is a quadratic-phase (Gauss-type) sum Σ_m a_m e^{−i(4πpm + πm²)} —
   Weyl/Gauss bounds give √M-cancellation away from rational coherence points.
   The tower tail's NET push on any pair is bounded; absorption (first-passage
   of the walk) dominates unchecked deepening. [CONJECTURE at the assembly
   level; the sum bound itself is classical.]

## 3. The de-randomized program

(MID-central) ⟸ four inputs, now typed:
1. the collision dichotomy [PROVED, doc 48];
2. the phase lattice [PROVED, §2];
3. Gauss/Weyl-sum bounds on the collective push [CLASSICAL technology —
   quadratic exponential sums; the equidistribution of {t log j} enters only
   through §2's expansion];
4. creation-rate control (soft-gap density) — the small-ball residue, now
   needed only at RATE level, not absence.

The arithmetic input of the bridge has become QUADRATIC PHASES: the weld
identity, pushed through the cascade, is a Gauss-sum structure — Γ-θ
territory, the hgt charter's home ground. The wall's remaining mathematical
content: (i) run the first-passage bookkeeping with §2's phases replacing
randomness (a deterministic discrepancy argument); (ii) the creation-rate
lemma; (iii) (DEEP-FATE) for the wrong-sign branch (the one sanctioned
computation, when (i) needs its answer).

## 4. Openings

1. First-passage write-out with quadratic phases — the survival bound
   P(k₀ → N) as an explicit function of the Gauss-sum partial maxima.
2. Measure the p = 1/4, 3/4 coherence prediction (one census re-read: the
   SHALLOW-event p-distribution should show structure at quarter-integers if
   the collective coherence acts — free from archived data, no new run).
3. Lean: the dichotomy kill/survive brick (IVT packaging) — this cycle.
4. The m³/N error term caps the coherent range at m ~ N^{1/3}: the effective
   tower tail is N^{1/3} entries — the Gauss sums are SHORT; short-sum bounds
   (Weyl differencing) suffice.
