# 35 — (S-mono) with Explicit Constants: the 1→2 Write-Out, Part I

**Register: SEARCH → promotion draft** (this document IS the pipeline card's 1→2 gate
for smono-reader-exactness: every load-bearing inequality of docs 29–31 restated with
explicit constants and complete elementary proofs; no O(·), no ≈ in the chain). Tasks
#138/#142. Part I: setting, toolbox, step (a) (midpoint bound), step (b′) (the march).
Part II (doc 36): step (c) (response bound), (d) (tail), (e) (assembly), per-carrier
protocol, Lemma R constants.

## 0. Setting and hypotheses

Log-field t_1 < … < t_d, log-gaps δ_j := t_{j+1} − t_j, x-field α_j = e^{t_j},
x-gaps Δ_j := α_{j+1} − α_j. Equilibrium of gap i: the unique root t*_i of
Σ_k coth((t − t_k)/2) = −d in (t_i, t_{i+1}); s_i := t_{i+1} − t*_i. Behind distances
B_k := t_{i+1} − t_{i+1−k} (k = 1..i), ahead distances A_j := t_{i+1+j} − t_{i+1}
(j = 1..d−i−1). Constraint function (doc 30 §1, strictly increasing in s):

> G_i(s) = Σ_{k=1}^{i} coth((B_k − s)/2) − coth(s/2) − Σ_{j=1}^{d−i−1} coth((A_j + s)/2).

Energy: S_i = d + W(t*_i), W(t) = ¼ Σ_k csch²((t − t_k)/2).

**Hypotheses (the (F)-class, constants fixed):**

- **(F1) one-sided, outer:** i ≥ (d−1)/2.
- **(F2) x-gap monotonicity:** Δ_j nondecreasing on the span. (Consequences used:
  (i) the doc 27 §3 pairing; (ii) log-gaps δ_j nonincreasing on the outer span — since
  δ_j = log(1 + Δ_j/α_j) with Δ_j growing slower than α_j on hyperbolic section fields;
  where (ii) is not automatic it is part of the per-carrier check.)
- **(F3) gap regularity:** |δ_{j+1} − δ_j| ≤ C₀·δ_j² for all j in the window, with
  **C₀ ≤ 1/2**, and δ_j ≤ 1 on the window.
- **(F4) ahead-span comparability:** δ_j ≥ δ_{i+1}/2 for all j ≥ i+1 in the window.
  For δ_j = c/j-type fields this is a CONSEQUENCE of (F1): the whole ahead span is
  j ∈ (i, d] ⊆ (i, 2i+1], and δ_d = c/d ≥ c/(2i+1) ≥ δ_{i+1}/2. It is listed
  separately because the per-carrier check verifies it directly.

All per-carrier inputs are exactly (F1)–(F4) plus criterion (M) of §3; nothing else
enters below.

## 1. Toolbox: six elementary inequalities, proofs complete

**(T1)** For u > 0: 1/u < coth u ≤ 1/u + u/3.
*Proof.* Partial fractions: coth u = 1/u + Σ_{k≥1} 2u/(u² + π²k²). Every summand is
positive (left inequality), and Σ 2u/(u²+π²k²) ≤ 2u Σ 1/(π²k²) = 2u·(1/6) = u/3. ∎

**(T2)** For u > 0: 1/u² − 1 ≤ csch²u < 1/u².
*Proof.* Right: sinh u > u. Left: csch²u = coth²u − 1 ≥ 1/u² − 1 by (T1). ∎

**(T3)** For 0 < v ≤ 1: coth v − 1 ≥ 2/((e²−1)v) ≥ 0.313/v.
*Proof.* coth v − 1 = 2/(e^{2v} − 1). The function (e^{2v}−1)/v is increasing on (0,1]
(its numerator is convex and vanishes at 0), so e^{2v} − 1 ≤ (e²−1)v there;
2/(e²−1) = 0.31303… ∎

**(T4)** For v ≥ 1: csch²v ≤ 4e^{−2v}/(1−e^{−2})² ≤ 5.36·e^{−2v}; also coth v ≤ coth 1
≤ 1.314.
*Proof.* csch²v = 4e^{−2v}/(1−e^{−2v})²; 1 − e^{−2v} ≥ 1 − e^{−2} = 0.8646…, and
4/0.8646² = 5.351. coth decreasing. ∎

**(T5)** φ(u) := csch²(u)·coth(u) is positive and strictly decreasing on (0,∞), with
1/u³ − 1/u ≤ φ(u) ≤ 1/u³ + 1/(3u).
*Proof.* Product of positive strictly decreasing functions. Bounds: multiply (T1) and
(T2): φ ≥ (1/u² − 1)·(1/u) and φ ≤ (1/u²)(1/u + u/3). ∎

**(T6) (MVT step)** For 0 < a ≤ b: coth(a/2) − coth(b/2) ≤ (b − a)·csch²(a/2)/2.
*Proof.* |d/dx coth(x/2)| = csch²(x/2)/2, and csch² is decreasing, so the derivative on
[a,b] is bounded by its value at a. ∎

## 2. Step (a): the midpoint bound s_i < δ_i/2 — constant-free

**Lemma A.** Under (F1)+(F2)(i): s_i < δ_i/2.

*Proof.* Two stages.

(i) *x-coordinates (doc 27 §3, reproduced).* At the arithmetic midpoint m of
(α_i, α_{i+1}) the field force is F(m) = Σ_k 1/(m − α_k) (the Stieltjes derivative
condition recentered; doc 27 §0). The two gap neighbors contribute
1/(Δ_i/2) − 1/(Δ_i/2) = 0. Pair the j-th charge behind (distance
L_j = Δ_i/2 + Δ_{i−1} + … + Δ_{i−j}) with the j-th ahead (distance
R_j = Δ_i/2 + Δ_{i+1} + … + Δ_{i+j}): (F2) gives Δ_{i+l} ≥ Δ_{i−l} termwise, so
R_j ≥ L_j and 1/L_j − 1/R_j ≥ 0. By (F1) there are at least as many behind charges as
ahead charges; each unpaired behind charge contributes 1/L > 0 strictly. Hence
F(m) > 0; F is strictly decreasing across the gap, and the critical point c_i (where
F(c_i) = ⋯ matches the constraint) lies right of m:
c_i > (α_i + α_{i+1})/2.

(ii) *AM–GM transport.* (α_i + α_{i+1})/2 ≥ √(α_i α_{i+1}), so
c_i > √(α_i α_{i+1}), i.e. t*_i = log c_i > (t_i + t_{i+1})/2, i.e.
s_i = t_{i+1} − t*_i < δ_i/2. ∎

**Remark (coordinates matter).** The pairing must be run in x-coordinates, where (F2)
is stated; re-running it on the log-lattice picture would require gap-regularity
margins that (F2) supplies for free. Doc 29(a)'s lattice version is the special case
Δ_j ≡ const of stage (i) composed with the trivial transport.

## 3. Step (b′): the march s_{i+1} < s_i — explicit cushion domination

Doc 30 §1 [PROVED HERE there, exact]: the march is monotone at step i iff
ΔG(s_i) := G_{i+1}(s_i) − G_i(s_i) > 0, and termwise, exactly,

> ΔG(s) = coth((t_{i+2} − t_1 − s)/2)   [far swap extra]
>   + coth((δ_{i+1} + s)/2)              [near swap extra]
>   + Σ_{k=1}^{i} [coth((B_k − Σ_k − s)/2) − coth((B_k − s)/2)]   [gains; Σ_k := δ_{i+1−k} − δ_{i+1} ≥ 0]
>   + Σ_{j=1}^{d−i−2} [coth((A_j + s)/2) − coth((A_j − Λ_j + s)/2)]  [losses; Λ_j := δ_{i+1} − δ_{i+1+j} ≥ 0]

(signs by (F2)(ii): log-gaps nonincreasing, doc 30 §2). Gains ≥ 0 termwise; both
extras > 1. It remains to dominate the losses explicitly.

**Lemma B (loss bound).** Write δ̂ := δ_{i+1}, and assume (F2)(ii)+(F3)+(F4). Then
Σ_j |loss_j| ≤ 8C₀·(1 + log(5/δ̂)) + 4.4·C₀.

*Proof.* By (T6), |loss_j| ≤ Λ_j · csch²((A_j − Λ_j + s)/2)/2, where
A_j − Λ_j = newA_j = t_{i+2+j} − t_{i+2} is the post-step ahead distance — a sum of j
ahead gaps, so (F4) gives newA_j ≥ j·δ̂/2 for every j. (F3) stepwise with nonincreasing
log-gaps gives Λ_j = δ_{i+1} − δ_{i+1+j} ≤ Σ_{l=1}^{j} C₀δ_{i+l}² ≤ j·C₀δ̂². Two
ranges.

(i) *Near range* j ≤ j₁ := ⌈4/δ̂⌉ (argument jδ̂/4 ≤ 1 + δ̂/4, handled by (T2) which
holds for all u): csch²(jδ̂/4) ≤ 16/(j²δ̂²), so
|loss_j| ≤ (jC₀δ̂²/2)·16/(j²δ̂²) = 8C₀/j. Summing:
Σ_{j≤j₁} 8C₀/j ≤ 8C₀(1 + log j₁) ≤ 8C₀(1 + log(5/δ̂)), using j₁ ≤ 5/δ̂ for δ̂ ≤ 1.

(ii) *Far range* j > j₁ (argument jδ̂/4 ≥ 1): by (T4),
csch²(jδ̂/4) ≤ 5.36·e^{−jδ̂/2}, so |loss_j| ≤ 2.68·C₀δ̂²·j·e^{−jδ̂/2}. With
a := δ̂/2 and a·j₁ ≥ 2: Σ_{j>j₁} j e^{−aj} ≤ (j₁ + 1/a)·e^{−a j₁}/a ≤ 3e^{−2}/a²
= 12e^{−2}/δ̂² ≤ 1.63/δ̂². Total ≤ 2.68·C₀δ̂²·1.63/δ̂² ≤ 4.4·C₀.

Adding (i)+(ii) gives the lemma. There is no third range: (F4) covers the whole ahead
span, which is the structural content of one-sidedness — the far field never
degenerates because the outer window ends at d ≤ 2i+1. ∎

**Lemma C (cushion).** Under s = s_i < δ_i/2 (Lemma A), δ̂ ≥ (1 − C₀δ_i)δ_i ≥ δ_i/2
(from (F3), C₀ ≤ 1/2, δ_i ≤ 1), and δ_i ≤ 1: the near swap extra satisfies
coth((δ̂ + s)/2) − 1 ≥ 0.313·2/(δ̂ + s) ≥ 0.417/δ_i.

*Proof.* (δ̂ + s)/2 ≤ (δ_i + δ_i/2)/2 = (3/4)δ_i ≤ 1, so (T3) applies with
v = (δ̂+s)/2: coth v − 1 ≥ 0.313/v = 0.626/(δ̂+s) ≥ 0.626/((3/2)δ_i) = 0.417/δ_i. ∎

**Theorem B′ (the march, explicit).** Assume (F1)–(F4) and the per-index criterion

> **(M):  8C₀·log(28/δ_i) + 4.4·C₀ ≤ 2 + 0.417/δ_i.**

Then ΔG(s_i) ≥ 2 + 0.417/δ_i − [8C₀(1 + log(5/δ̂)) + 4.4C₀] > 0, hence
s_{i+1} < s_i. Moreover the march increment is quantified:
s_i − s_{i+1} ≥ ΔG(s_i)/(2·W̄_i), where W̄_i := sup_{s∈[s_{i+1},s_i]} G_{i+1}′(s)/2
(finite; G′ = 2W ≤ explicit bound in Part II).

*Proof.* ΔG ≥ [far extra ≥ 1] + [near extra = 1 + cushion, Lemma C] + [gains ≥ 0]
− [losses, Lemma B]. With δ̂ ≥ δ_i/2: 8C₀(1 + log(5/δ̂)) ≤ 8C₀(1 + log(10/δ_i))
= 8C₀·log(10e/δ_i) ≤ 8C₀·log(28/δ_i), so (M) implies positivity. The increment bound
is the mean value theorem for the strictly increasing G_{i+1} between its root
s_{i+1} and the point s_i, where G_{i+1}(s_i) = −d + ΔG(s_i). ∎

**Remark (where (M) holds — the honest evaluation).** For the model class δ_j = c/j:
C₀ = 1/c and δ_i = c/i, so (M) reads, after multiplying by c,
8·log(28·i/c) + 4.4 ≤ 2c + 0.417·i — right side linear in i, left logarithmic.
Explicitly: c = 2 gives i₀ ≈ 150; c = 4 gives i₀ ≈ 120; the dependence on c is weak
(i₀ ≈ 19·log i + O(c)). The i < i₀ band is NOT a gap
in the reader chain: crossings of margin 1 are excluded there by doc 25's tracking
clearance (margin ≥ κ_A d² off the zero set — the transition sits in the far-outer
band, where (M) holds), so (S-mono) is only consumed where it is proved. The
per-carrier verification of (M) + the band bookkeeping is a finite numeric check per
window (Part II §6 protocol).

## 4. Status after Part I

Steps (a) and (b′) of the (S-mono) chain now carry explicit constants end-to-end:
the only hypotheses are (F1)–(F3) + (M), and every inequality above is elementary with
a complete proof. Part II (doc 36) does the same for (c) dW/ds < 0 (the χ2 chase made
exact — the disjoint-interval/pairing bound with (T5)/(T6)), (d) the swap tail, (e)
the assembly ΔS > 0, and closes with the per-carrier (F2)/(F3)/(M) verification
protocol for the u-plane theorem-track carriers. Next object: doc 36.

## 5. SUPERSEDED ITEMS (see doc 37)

Doc 37 §1 found a bookkeeping error in doc 30 §1's ledger display: ΔG's two extras
are the far-BEHIND and far-AHEAD terms; the "near swap extra coth((δ_{i+1}+s)/2)" is
a paired drift term, not an extra, and the O(1/δ) bulk cushion built on it (doc 30
§5) does not exist. Consequently **Lemma C and Theorem B′/(M) above are superseded**
by doc 37's Theorem B″/(M″) (convexity pairing, hypothesis (F5), remainder 200·C₀²).
Lemmas A, B and the toolbox stand and are consumed by doc 37 unchanged.
