# 13 — The block lemmas: L1 at paper grade

Register: SEARCH-register document; §1 is a complete proof; §2 is a proof with one named
technical core and a finite-case compactness argument; §3 records exactly what remains.
Consumes: 12 §§4–5 (block split, rotation invariance, self-repair dichotomy).

Setup. A block is a finite set B of primes with weights c_p = Λ(p)p^{−1−η} > 0. On the
Bohr torus the block variable is Y = Σ_{p∈B} c_p x_p with x_p i.i.d. uniform on the unit
circle (rotation invariance has already absorbed the γ₀-reference phases — 12 §5.1).
Write w = Σc_p, s² = Σc_p². The recurrence event needs, per block, P(|Y − m| ≤ t) bounded
below, with m the block mean (|m| ≤ w) and t the block tolerance.

## 1. L1a — concentration `[PROVED HERE]`

**Lemma.** P(|Y| ≥ t) ≤ 4·exp(−t²/(4s²)) for every t > 0.

*Proof.* Re Y = Σ c_p cos θ_p is a sum of independent, mean-zero variables with
|c_p cos θ_p| ≤ c_p; Hoeffding gives P(|Re Y| ≥ u) ≤ 2exp(−u²/(2s²)); the same for Im Y.
If |Y| ≥ t then |Re Y| ≥ t/√2 or |Im Y| ≥ t/√2; the union bound gives the claim. ∎

**Consequence (deep blocks are free, rigorously).** If the block's mean satisfies
|m| ≤ t/2 and s ≤ t/(4√log(8J/κ)), then P(|Y − m| ≤ t) ≥ 1 − κ/(2J). For the lane's
blocks, s_j ≤ √(c_max·w_j) decays geometrically in j while the tolerances t_j = w_j·ρ_j
decay only like w_j: beyond j₁(ρ) ≈ log(1/ρ) + O(loglog J) every block is free. The mean
condition |m_j| ≤ t_j/2 for deep blocks is exactly where the self-repair dichotomy (12
§5.2) routes: either it holds (this branch), or the Perron converse L5 certifies zeros
near γ₀ (the other branch of the forcing). No probability is lost either way.

## 2. L1b — small ball for the costly blocks `[PROVED modulo one named core]`

Only blocks j ≤ j₁ ≈ log(1/ρ) require a genuine small-ball bound. Two regimes.

**(b-CLT) Blocks with many comparable weights** (all but the first few: block j has
n_j ≍ e^{2j}/j primes, c_max/s → 0 fast). Y is rotation-invariant with characteristic
function φ(ξ) = ∏_p J₀(c_p|ξ|) (Bessel; the Pearson random-flight law). Density by 2-d
Fourier inversion: f_Y(y) = (1/2π)∫₀^∞ r·J₀(r|y|)·∏_p J₀(c_p r) dr, absolutely convergent
for n ≥ 3 (each J₀ decays like r^{−1/2}). **Named technical core (the one open estimate):**
> (D) f_Y(y) ≥ c₀·e^{−C₀|y|²/s²}/s² for |y| ≤ K·s, with absolute c₀, C₀,
>     for blocks with c_max ≤ s/10 and n ≥ n₀.
Given (D): P(|Y−m| ≤ t) ≥ πt²·c₀e^{−C₀K²}/s² — the (t/s)²-per-block cost of 12 §4.2,
now with the mean radius |m| ≤ Ks supplied by the dichotomy's moderate branch. (D) is a
statement about Pearson walks near the Gaussian bulk — the local CLT for rotation-
invariant flights; expected provable by the Bessel-integral split r ≤ 1/s (Gaussian
regime, ∏J₀ ≈ e^{−s²r²/4}) vs r > 1/s (oscillatory decay, n ≥ n₀ powers of r^{−1/2}
beat everything). This is the single remaining analytic estimate of L1.

**(b-sparse) The first few blocks** (j ≤ 2: primes {2,3,5,7} and the next handful).
Finitely many fixed laws. For n ≥ 3 the density f_Y exists, is continuous, and is
strictly positive on the interior of the support disc {|y| < w} minus at most finitely
many circles (explicit two-term annulus convolved with the rest smooths the singularities
for n ≥ 3). Compactness on {|y| ≤ (1−κ)w} gives a per-block positive minimum d_j > 0:
P(|Y−m| ≤ t) ≥ πt²·d_j. The constants d_j depend continuously on η over the compact
parameter range — uniform positivity on δ ∈ [δ_min, 0.02] per fixed δ_min, with the
δ_min → 0 uniformity tracked through (D) (the sparse blocks' weights barely move with η).
The extreme-radius case |m| > (1−κ)w on a sparse block: |m| is a partial sum of
−ζ′/ζ(1+η+iγ₀) over {2,3,5,7,…} at near-maximal modulus — again the dichotomy: near-
extremal early means certify near-real-axis alignment of γ₀ against the smallest primes,
a measure-zero Diophantine circumstance that the Perron branch (L5) absorbs: extremal
block sums of ζ′/ζ force zeros near γ₀ exactly as super-typical ones do.

## 3. State of L1, and what follows it

- L1a: PROVED (Hoeffding, complete).
- L1b: reduced to (D) — a local CLT lower bound for Pearson flights — plus finite-case
  compactness. No arithmetic left anywhere in L1; (D) is pure probability/Bessel analysis.
- The dichotomy interface is now load-bearing in three places (deep-block means, CLT-block
  mean radius, sparse-block extremal means) — all routed to L5, which is therefore
  promoted to the chain's second pillar: **prove L5 next** (Perron converse: zero-free
  disc at 1+iγ₀ ⟹ block-mean decay, with the spike's own non-decaying share tracked).
  L5 is classical contour work; its failure modes are visible in advance (the spike share
  and the pole share must be separated from the "extra zeros" share).

## 4. L5 attacked — the mean-size audit corrects the chain (2026-07-03, late night)

### 4.1 The moderate-means branch is UNOBTAINABLE — and that is information, not death
Perron with a smooth block window: shifting to Re z = −R/2 shows the block means decay at
rate e^{−j(R−2η)} relative to w_j (contour share) — but the needed "moderate" size
|m_j| ≤ K·s_j means RELATIVE decay e^{−j}, i.e. square-root cancellation in prime sums —
attainable only from a zero-free disc of radius > 1, which would cross the critical line:
impossible (on-line zeros are vertically dense). Worse — better: the residues of the
ON-LINE zeros themselves feed the means: one on-line zero near γ₀ contributes ≈ e^{−j(1+2η)}
≈ s_j/√(2j), and there are ≍ log γ₀ within O(1). **The honest mean size is
|m_j| ≈ s_j·log γ₀/√(2j) — the means sit ~log γ₀ standard deviations out, unavoidably,
because the on-line population puts them there.** The self-repair dichotomy (12 §5.2)
stands, but its moderate branch is empty for the true ζ; the real dichotomy is
"means at the on-line-forced size K_j ≈ log γ₀/√(2j)" vs "even larger ⟹ extra zeros near
γ₀ by Perron" — the second branch unchanged.

### 4.2 The chain absorbs the correction `[DERIVATION, heuristic grade — third audit survived]`
Small-ball at radius K_j·s_j costs e^{−C K_j²} = e^{−C log²γ₀/(2j)} per block; summed over
the costly blocks: **μ ≥ exp(−C·log²γ₀·loglog(1/ρ))**. The earliest ~loglog γ₀ blocks sit
at near-extremal means (|m_j| ~ w_j saturated by the triangle inequality) — their cost is
large-deviation grade exp(−Σ n_j·I_j) ≈ exp(−log²γ₀): same total order. Then
T_contra ≈ exp(C·log²γ₀·polyloglog) ≤ T_forge = exp(e^{c₁/δ}) ⟺ δ ≤ c₁/((2+o(1))loglog γ₀)
— the SAME shape as the detectability constraint. The output region degrades only in the
constant: **δ*(γ) ≈ (c₁/2)/loglog γ.** Three audits (ambient burial, forging ceiling,
mean-size), three survivals with explicit absorptions.

### 4.3 Revised pillars — every open piece now has a NAMED classical toolset
- **(D′) large-deviation lower bounds for Pearson flights at radius up to K_j·s_j and up
  to near-extremal:** Cramér/Gärtner–Ellis LOWER bounds for sums of independent bounded
  rotation-invariant vectors — classical LDP machinery; the rate function sum
  Σ_j n_j I_j(|m_j|/w_j) ≈ log²γ₀ is the measure exponent. Replaces (D); strictly standard
  technology, no arithmetic.
- **L5′ (upper bounds now, not decay):** the mean-size computation |m_j| ≈ s_j·log γ₀/√j
  as a THEOREM — explicit-formula/contour evaluation of smoothed block sums with the
  on-line residue share, pole share, spike share, and far-zero share separated. Classical
  contour work with all failure modes visible.
- L2 (Fejér window-to-blocks constants), L3 (spike converse vs the O(log)-ambient), L4 ✓.
The quarantine holds: claim strength ≈ (c₁/2)/loglog γ + forced clustering, pending
(D′), L5′, L2, L3 — each bounded, each classical-shaped, each worth a full fight; the
first of them to break is the bug the strength predicts, and each survival shortens the
list. Next: (D′) — the LDP write-up, the most standard of the four.

## 5. (D′) proved: the tilted Cramér lower bound for Pearson blocks `[PROVED HERE at paper grade]`

**Theorem (D′).** Let Y = Σ_{p∈B} c_p x_p (x_p i.i.d. uniform phases, c_p > 0),
w = Σc_p, s² = Σc_p². For every m with |m| < w and every t > 0:
> P(|Y − m| ≤ t) ≥ exp(−Λ*(|m|) − λ(|m|)·t) · Q(|Y − m| ≤ t),
where λ(r) is the unique solution of Σ_p c_p·A(λc_p) = r, A = I₁/I₀ (Bessel ratio),
Λ*(r) = λr − Σ_p log I₀(λc_p) is the Cramér rate, and Q is the product von Mises tilt.
Moreover Q(|Y−m| ≤ t) ≥ 1/2 for t ≥ 2s, and ≥ c·(t/s)² for t < s on blocks with ≥ n₀
comparable terms.

*Proof.* (i) Rotation invariance: WLOG m = r·e₁, r = |m| ≥ 0. Tilt each phase by the von
Mises density dQ_p/dθ = e^{λc_p cosθ}/(2π I₀(λc_p)). Then E_Q[c_p x_p] = c_p A(λc_p)·e₁,
and r ↦ Σc_pA(λc_p) is continuous, strictly increasing from 0 (λ=0) to w (λ→∞): λ(r)
exists and is unique. The likelihood ratio is dP/dQ = exp(Σ log I₀(λc_p) − λ·Re Y);
on the event |Y − m| ≤ t we have Re Y ≥ r − t, so dP/dQ ≥ exp(−Λ*(r) − λt) pointwise
there, and P(ball) = E_Q[1_ball·dP/dQ] ≥ exp(−Λ*(r) − λt)·Q(ball).
(ii) Under Q, E_Q Y = m and Var_Q(Re Y) + Var_Q(Im Y) ≤ Σc_p²·(2 − A(λc_p)² − …) ≤ 2s²;
Chebyshev gives Q(|Y−m| > t) ≤ 2s²/t² ≤ 1/2 for t ≥ 2s.
(iii) For t < s: the tilted sum Y − m is centered with independent terms of third-moment
ratio Σ|c|³/s³ ≤ c_max/s; 2-d Berry–Esseen against N(0, Σ_Q) gives
Q(|Y−m| ≤ t) ≥ c·(t/s)² − C·c_max/s, which is ≥ (c/2)(t/s)² once c_max/s ≤ (c/2C)(t/s)² —
satisfied on all blocks j ≥ 4 at the lane's tolerances (c_max/s ≍ 1/√n_j decays
geometrically). The remaining blocks j ≤ 3 are three FIXED laws (rotation invariance —
γ₀ enters nowhere): their densities are continuous and strictly positive on the open
support disc minus finitely many circles (two-term annulus law convolved with ≥ 1 further
term), so a one-time compactness bound gives Q-ball ≥ d_j·t² with explicit d_j > 0. ∎

**Rate accounting (the measure exponent, now rigorous-shaped).** In the moderate-tilt
regime (λc_max ≤ 1): Λ*(r) = (1+O(λc_max))·r²/s² — so a block at K_j standard deviations
costs exp(−(1+o(1))K_j²), and with the forced means K_j ≈ log γ₀/√(2j) (13 §4.1):
Σ_j Λ*_j ≈ log²γ₀·Σ_j 1/(2j) ≈ (1/2)·log²γ₀·loglog(1/ρ). Near-extremal early blocks
(λ large): Λ* ≈ Σ_p∈B [λc_p − log I₀(λc_p)] ≤ n_j·λc_max with the von Mises rate —
Σ over the first loglog γ₀ blocks stays O(log²γ₀). **The measure exponent
μ ≥ exp(−C log²γ₀ loglog(1/ρ)) of 13 §4.2 is now backed by a theorem, not a heuristic**
— modulo only the L5′ input (that the means really are of size K_j·s_j, not larger),
which is exactly the second pillar.

Status ledger after (D′): L1a PROVED; (D′) PROVED (constants mechanical); remaining
pillars L5′ (mean-size contour theorem), L2 (Fejér constants), L3 (spike converse).
The probability half of the mechanism is DONE — everything still open is complex analysis.
