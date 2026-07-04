# 48 — The Collision Dichotomy, Exact: One Real Number Decides the Sweep

**Register: SEARCH → promotion draft** (task #130; the (SWEEP-margin) write-out
of doc 47 §4(2), delivered at exact grade — no local-model asymptotics).

## 1. Setting

Carrier F exact-FE and line-real; v-frame Z(v) := F(1/2 + i(t_B + v)), real
for real v. Background pair: Z_B(v) = (v² + η_B²)·g(v) on a disc D_w =
{|v| ≤ w}, with g analytic, real on reals, zero-free on D_w (the pair at
v = ±iη_B is the only zero pair; w below the local spacing). Perturbation
Z_ε = Z_B + ε·Z_P with Z_P analytic, real on reals (any exact-FE real term —
for the sweep, the marginal RS-pair term, Z_P(0) = 2|γ(s₀)|N^{−1/2}cos φ(t_B)).
Write q(v) := Z_P(v)/g(v) (real on reals, analytic on D_w).

## 2. The dichotomy [PROVED HERE]

Let W(v) := Z_ε(v)/g(v) = v² + η_B² + ε·q(v), and assume the edge condition
W(±w) > 0 and that Z_ε has exactly two zeros in D_w (Rouché from
|εZ_P| < |Z_B| on ∂D_w — checkable per instance).

**(a) Kill (exact).** If ε·q(0) ≤ −η_B², then W(0) ≤ 0, and W(±w) > 0 gives by
the intermediate value theorem a real zero in (−w, 0] and one in [0, w); these
exhaust the two zeros of Z_ε in D_w. **The pair lands ON the line.** ∎

**(b) Survive/deepen (exact).** If ε·q(v) > −η_B² for ALL real v ∈ [−w, w],
then W > 0 on the real segment: Z_ε has NO on-line zeros in D_w, and its two
zeros form a conjugate off-line pair. If moreover q ≈ q(0) on the relevant
scale, the new depth is η² ≈ η_B² + εq(0) — the wrong sign DEEPENS the pair. ∎

**One real number, sign and size:** the sweep of a background pair is decided
by εq(0) = ε·Z_P(t_B-value)/g₀ against −η_B². For the marginal term,
sign(q(0)) = sign(cos φ(t_B))·sign(g₀) — THE PHASE ENTERS EXACTLY HERE, and
only here. (The same formula with η_B² → −v₀² is the CREATION criterion for an
on-line pair at ±v₀, run forward: εq(0) ≥ v₀² — the film's λ* ≈ 0.7 is its
instance.)

## 3. What the dichotomy explains, and the residue it isolates

Explained at once: the film's creation (frozen resonant phase, right sign,
ε grows past v₀²|g₀/P₀|); the sweep kills measured in doc 47 (wrong sign for
survival); the σ(p)-profile noise (the SIGN of q(0) at a random height is
configurational — exactly what Δmingap sampled); the frozen-phase window
(near t*, cos φ holds one sign across the whole window — every background pair
there sees the same, possibly surviving, sign; at p-central the sign
equidistributes).

**The residue — (DEEP-FATE), the open sub-question:** at p-central a surviving
(wrong-sign) pair DEEPENS: η_new² = η_B² + |εq(0)| ~ N^{−1/2}-scale, i.e.
η_new ~ N^{−1/4} ≈ 0.4 — beyond the local disc, where the dichotomy's
hypotheses fail and the census says such pairs DO NOT EXIST (max measured
η = 0.178 in 24,000 units; deepened pairs are also quadratically harder to
kill later, so unchecked deepening would accumulate — it visibly does not).
Something saturates or destroys the deepen branch outside the local model:
candidates [CONJECTURE]: (i) t-migration/skewing once |v| ~ w (the zeros curve
in the real direction; the pair leaves mid-band σ-range); (ii) sign-breaking of
q over the larger disc (partial kills); (iii) the deepened pair's valley cannot
persist through the NEXT entry's Rouché radius. Deciding (DEEP-FATE) is the one
place a computation answers what this analysis cannot: track a single
wrong-sign background pair through its sweep beyond the local disc.

## 4. Status of the (SWEEP-margin) program after this document

- Kill/survive criterion: EXACT and elementary (§2) — Lean-shaped (IVT + Rouché
  packaging; the RHTower Peeling/KummerObstruction substrate already has the
  factorization tools).
- The frozen-window phenomenology: derived from §2 + φ stationarity (no longer
  a fit).
- Open: (DEEP-FATE) — the fate of wrong-sign survivors; then the iterated-sweep
  bookkeeping (a pair faces N − k subsequent entries; kill events per §2, and
  the census bounds multi-sweep survival at zero in 24k units).
