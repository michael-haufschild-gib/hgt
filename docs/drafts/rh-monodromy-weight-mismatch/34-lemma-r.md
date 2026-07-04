# 34 — Lemma R by the Elementary Ladder: Multiplicity-Uniform Cluster Splitting

**Register: SEARCH** (proof in outline; every remainder is an explicit elementary bound —
the composition bookkeeping is the write-up. Probe-certified at m = 4 over d = 10²–10⁵,
AMP-RESULTS run 3). Task #139; upgrades doc 25 Thm B to all multiplicities.

## 1. Statement

> **Lemma R.** g ∈ LP₀, g(0) ≠ 0, x* ≠ 0 an m-fold zero, σ = |x*|/√d. Uniformly on
> complex |s| ≤ M: Ã_d(x* + σs) = a_m σ^m (He_m(s) + O(d^{−1/2})).

## 2. The ladder (all pieces elementary)

**(R1) Cumulant expansion of the multiplier with explicit remainder.** With
S_ℓ(j) = Σ_{i<j} i^ℓ: log φ_d(j) = −Σ_ℓ S_ℓ(j)/(ℓ d^ℓ) for j ≤ d. Truncate the log-series
at L terms (|log(1−u) + Σ_{ℓ≤L} u^ℓ/ℓ| ≤ u^{L+1}/((L+1)(1−u))) and the exponential at P
terms (|e^{−x} − Σ_{p<P}(−x)^p/p!| ≤ x^P/P! for x ≥ 0 — the (E5) technique iterated,
same h-monotonicity proofs as SpurRescale.lean). Composing:

> |φ_d(j) − Σ_{p<P} e_p(j)/d^p| ≤ C_P·j^{2P}/d^P  for j ≤ d^{2/3},

with e_p(j) the polynomial coefficients of exp(−S₁/d − S₂/2d² − …), of j-degree 2p and
leading term (−1)^p C(j,2)^p/p!. For j > d^{2/3} both φ_d(j) and the partial sums are
dominated by the entire-coefficient tail Σ_{j>d^{2/3}}|c_j|(|x*|+1)^j — superpolynomially
small against σ^m.

**(R2) Degree filtration at the cluster scale.** A monomial j^q z^j resums to (θ^q g)
(θ = z∂); at z = x* + σs a q-th order operator term of size 1/d^p contributes
O((x*/σ)^q/d^p) = O(d^{q/2−p}) relative to g's local scale. Hence in e_p only the TOP
j-degree q = 2p survives at O(1) — giving exactly (−1)^p (θ(θ−1))^p/(2^p p!) →
(z²∂²)^p/(2^p p!)-leading — while q = 2p−1 contributes O(d^{−1/2}) and lower degrees
O(1/d). The O(1) parts sum over p to the backward-heat semigroup e^{−(z²/2d)∂²}.

**(R3) Coefficient freezing.** Replacing z² by x*² in the exponent across the window
|z − x*| ≤ Mσ costs a relative O(σ/|x*|) = O(d^{−1/2}) per order, absorbed by the
Gaussian factor (the operator (z²−x*²)∂² carries one extra σ against one x*).

**(R4) Hermite resummation on the jet.** e^{−(x*²/2d)∂²} t^k = σ^k He_k(t/σ) exactly
(σ² = x*²/d), applied to the M-jet of g at x*: the k = m term gives a_m σ^m He_m(s);
k > m terms are O(σ^{m+1}); the jet remainder of g beyond degree M′ is O(σ^{M′+1})
(Cauchy). Collecting (R1)–(R4): Ã_d(x*+σs) = a_m σ^m (He_m(s) + O(d^{−1/2})) uniformly
on |s| ≤ M. ∎(outline)

## 3. Consequences

With Lemma R, doc 25 §3.1's Hurwitz/Rouché step runs verbatim for every m: the cluster
splits at the single scale σ into the He_m configuration, cluster critical points sit at
the zeros of He_m′ with margins |x*−τ|²·d/(m·x*²) (Lemma W, machine-checked in
SpurHermite.lean, supplies the universal constant m). **Doc 25 Thm B is proved in
outline for ALL multiplicities**; the tracking-clearance theorem is multiplicity-blind,
so the Ξ₁-grade statements need no simplicity hypotheses. The remaining #139 work is the
same as the pipeline card's 1→2 gate: line-by-line constants for (R1)–(R4) — four
elementary estimates, no new structure. Next object: fold (R1)'s iterated (E5)
inequalities into SpurRescale.lean (they are the same two h-monotonicity proofs run P
times) — the natural next Lean increment.
