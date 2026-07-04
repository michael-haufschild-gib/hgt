# 38 — The Hermite Ladder: the DISC Reader Iterates to Every Rung

**Register: SEARCH** (task #148 — the k ≥ 2 bridge audit). Question: does the DISC
reader mechanism reach only (WR_1) — making the lane an RH_2 route — or does it
iterate up the 2^k ladder? Answer: **it iterates; the higher-rung instrument is
already contained in the banked one.** The audit is a shape-of-argument note; every
claim is labelled.

## 1. What a rung needs

(WR_k): D(W) ≡ L(W) (mod 2^{k+1}) for every admissible window; RH ⟺ ∀k (WR_k)
(doc 18, machine-checked). Through the identity D = L + 2N this is **2^k ∣ N(W)**.
The k = 1 reader banked in docs 19–20 reads N mod 2 as the discriminant sign of the
recentered degree-d jet section J^{d,0} at the window center. The question is what
reads N mod 4, 8, ….

## 2. The instrument was always bigger than its shadow [THEOREM, classical]

Hermite (1856): for a real polynomial p of degree d with Newton power sums s_j, the
Hankel (trace) form H(p) = (s_{i+j})_{0≤i,j≤d−1} satisfies

- rank H = number of distinct roots of p,
- signature H = number of distinct REAL roots of p,

hence **(# negative eigenvalues of H) = number of distinct non-real conjugate
pairs = r₂**, and det H = disc(p) for monic p. Two consequences:

1. **The disc sign is the determinant shadow**: sign disc = (−1)^{r₂}. The banked
   k = 1 reader is the top minor of H.
2. **Jacobi's rule** (all leading principal minors D₁, …, D_d nonzero): the number
   of sign changes in the chain (1, D₁, …, D_d) equals the number of negative
   eigenvalues, i.e. equals r₂ — **the exact pair count, not its parity**.

The power sums are Newton-expressible in the jet coefficients γ_m, so each minor is
a polynomial in finitely many jets: the same register of object as (DISC-fin) —
finite exponential-sum sign statements. No new analytic instrument, no new carrier,
no new transport is needed at any rung.

## 3. The generalized arithmetic target

> **(HANK-fin)_k [CONJECTURE, generalizing (DISC-fin) = (HANK-fin)_1]:** on
> dominated windows, the sign-change count of the leading-principal-minor chain of
> the Hermite form of the recentered degree-d jet section of the completed
> symmetric truncation is ≡ 0 (mod 2^k).

With the same (SPUR-R) exactness input that makes the k = 1 reader theorem-grade
(section pair count = window count on dominated windows), rung k follows from
(HANK-fin)_k by the identical transport argument. The blindness no-go (doc 33 §7)
is evaded at every k by the same arithmetic object — it forced ONE reader, not one
reader per rung.

**Multiplicity caveat.** N(W) counts with multiplicity; r₂ counts distinct section
pairs (rank drops at repeated roots). This is the already-open multiplicity thread:
doc 25 covers m ≤ 3, Lemma R (#139) is the multiplicity-uniform upgrade. The thread
carries over to every rung unchanged; nothing new breaks.

**Verdict on the lane's reach.** The program is NOT intrinsically an RH_2 route.
(WR_1) remains the correct first target (already: no odd-multiplicity — in
particular no simple — off-line zeros, unconditionally new if closed). But the
mechanism climbs: rung k consumes strictly more sign data of the same matrix, and
the all-rungs limit — H positive semidefinite, i.e. the recentered section
HYPERBOLIC — reads N(W) = 0 outright.

## 4. Where this lands in the classical landscape [novelty gate]

Hankel positivity of Jensen-type data is the Jensen–Pólya program; the nearest
classical results are the Turán inequalities for ξ (Csordas–Norfolk–Varga) — which
are exactly the D₂ fragment of the minor chain in the GLOBAL frame — and
Griffin–Ono–Rolen–Zagier's eventual hyperbolicity of Jensen polynomials (each
degree d, shift n ≥ N(d)). Run 1/3/4 measurements (DISC-RESULTS) sit precisely
complementary: the off-line-pair signal is visible ONLY at n ∈ {0, 1} and washes
out for n ≥ 2 — **GORZ eventual hyperbolicity is the reader's blindness band seen
from the other side.** All detection capacity lives in the pre-asymptotic band the
classical program leaves as remainder, and the lane's recentering (run 3:
recentering IS localization; run 2: the global frame pays quadratic-in-height
resolution) is what makes that band usable. A literature search produces global
Jensen–Pólya and eventual hyperbolicity; it does not produce window-local
recentered minor chains composed with domination transport — the bridge object is
this lane's.

## 5. A categorical reading [CONJECTURE, unforced]

Rung 1 = sign disc = the square class of det H in ℝ*/(ℝ*)² — a w₁-type invariant of
the trace form. Serre–Fröhlich theory assigns trace forms their Stiefel–Whitney
classes, with w₂ (Hasse–Witt) governing spin-type embedding problems. Candidate:
**rung 2 = the Hasse–Witt invariant of the Hermite form of the section; the 2^k
ladder = the iterated spin/pin lifting tower of the quadratic form attached to the
window.** If this holds, the MWM ladder is literally a Galois-cohomological
obstruction tower of a canonical quadratic form — the weld-native categorical
object the hgt charter asks for. Unverified; separate card if pursued.

## 6. Next generative moves

1. **Margin statistic upgrade (feeds #146):** the minor chain is the canonical
   "how positive" measurement — at ζ windows the prediction is full definiteness
   (every D_i > 0), strictly stronger than disc > 0. Add the minor chain to the
   reader instrumentation; the suppression experiment's margin question becomes
   "which minor goes soft first," a mechanism probe.
2. **Rung-2 instance:** compute the minor chain at the banked g₅/#136 window and at
   a ζ window at the same height — the first measured (HANK-fin)_2 data point.
3. **Recentered Turán inequalities:** the D₂ minor at window centers is a concrete,
   isolated, possibly-provable fragment (classical tools exist for the global
   frame); a proof would be the first rung of (HANK-fin) obtained by pure analysis.
4. §5's Hasse–Witt candidate as its own card if instance data supports it.
