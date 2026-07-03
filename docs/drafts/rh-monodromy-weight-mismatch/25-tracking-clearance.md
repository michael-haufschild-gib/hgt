# 25 — Tracking Clearance: the Proof, the Heat Operator, and the Hermite Splitting

**Register: SEARCH** (Theorem A, Corollary A′, identities (E1)–(E5), Lemma W, Theorem B for
m ≤ 3, and Corollary C are [PROVED HERE] with full proofs below; Theorem B for m ≥ 4 is
proved modulo Lemma R, whose remaining content is standard Laplace-method remainder
bookkeeping — labelled proof-shaped and probe-certified at m = 4 over four decades of d,
`computations/AMP-RESULTS.md` P-B). Task #135. This doc discharges parts (i) and (ii) of
**(AMP-mono)** (doc 24 §5); what remains of (SPUR-R) after it is part (iii) alone.

## 0. Setting and statements

g ∈ LP₀: real entire, genus 0, all zeros real, g(0) ≠ 0 (the recentered carriers of doc 20
satisfy this by construction). A_d = J^d_g is the d-th Jensen section — hyperbolic (Jensen).
τ = a + bi, b > 0, P = (x−τ)(x−τ̄). At a critical point c of A_d with A_d(c) ≠ 0:

> margin(c) := q_d(c)/(c⁴ ℰ(c)),  q_d(c) = |τ|² − 2adc + d(d−1)c²,
> ℰ(c) = Σ_k (c−α_k)^{−2}  (α_k = zeros of A_d),

and sign transfer at c (doc 24 §2) holds iff margin(c) > 1. The **tracking window** at
radius R is the set of critical points c with z_c := dc ∈ [−R, R]. Results:

- **Theorem A** — margin ≥ κ_A·d² at every window critical point with z_c at distance ≥ ε
  from the zero set of g. No spacing or far-zero-tail input is needed: the expected
  obstruction (the far tail of ℰ) does not exist, because at critical points ℰ is the exact
  logarithmic-derivative datum −A″/A and the identity carries the whole tail.
- **Theorem B** — inside the cluster over an m-fold zero x* ≠ 0 of g, the zeros of A_d split
  at the single scale σ = |x*|/√d into the probabilists'-Hermite configuration He_m, and
  margin = |x*−τ|²·d/(m·x*²)·(1+o(1)) at every cluster critical point — rate d, with the
  multiplicity entering only linearly (Lemma W: the Hermite equilibrium energy is exactly m).
- **Corollary A′ + C** — for g with zeros of multiplicity ≤ 3 in the window (any multiplicity
  granted Lemma R), margin > 1 at ALL window critical points for d ≥ d₀(g, τ, R); and the
  q_d-dip c ≈ a/(d−1) lies inside the window, so part (ii) of (AMP-mono) is subsumed — no
  separate dip argument exists or is needed.

Throughout, Ã_d(z) := A_d(z/d) (the rescaled section) and t := z − x*, u or s := t/σ.

## 1. Exact inputs

**(E1) Energy identity [PROVED HERE].** For hyperbolic A with zeros α_k and a critical point
c with A(c) ≠ 0: A′/A = Σ(x−α_k)^{−1}, so (A′/A)′ = (A″A − A′²)/A² = −Σ(x−α_k)^{−2}; at c
the middle term A′(c)² drops, giving **ℰ(c) = −A″(c)/A(c)** exactly. (If c is itself a
multiple zero of A_d, ℰ(c) = ∞ and the counting lemma reads the point as a flip: J(c) =
c⁴A″(c) for a double zero. Theorems A/B exclude this configuration automatically.)

**(E2) Rescaled q [PROVED HERE].** q_d(z/d) = |τ|² − 2az + (1−1/d)z² = (z−a)² + b² − z²/d
≥ b² − R²/d on |z| ≤ R; in particular ≥ b²/2 once d ≥ 2R²/b².

**(E3) Rescaling brick (doc 23 §2a).** Ã_d(z) = Σ_j φ_d(j) c_j z^j with g = Σ c_j z^j and
φ_d(j) = d!/((d−j)! d^j) ∈ [0,1] (φ_d(j) = 0 for j > d); φ_d(j) → 1 pointwise and Σ|c_j|ρ^j
dominates, so Ã_d → g uniformly on every closed complex disc. Cauchy estimates then give
Ã_d′ → g′ and Ã_d″ → g″ uniformly on compacts.

**(E4) Operator identity [PROVED HERE].** With θ = z·d/dz (diagonal on monomials):
Ã_d = φ_d(θ)g. Since θ(θ−1) = z²∂² exactly, the leading cumulant of log φ_d is
−θ(θ−1)/(2d): the section chain is the image of the carrier under a **backward-heat
smoothing at time-scale 1/d with diffusion coefficient z²** (heat flow in log z). Branch
reading: the sections — polynomial, finite — DO carry a generative rule, a flow toward g;
the carrier g itself remains flowless. The flow lives on the approximants, the constraint on
the object.

**(E5) First-order expansion with explicit remainder [PROVED HERE].** For all j ≥ 0, d ≥ 4:

> |φ_d(j) − 1 + C(j,2)/d| ≤ C(j,2)²/(2d²).

*Proof.* For j ≤ d put xᵢ = i/d ∈ [0,1], S = Σ_{i<j} xᵢ = C(j,2)/d. Weierstrass gives
∏(1−xᵢ) ≥ 1 − S; and ∏(1−xᵢ) ≤ e^{−S} ≤ 1 − S + S²/2, the last since
h(S) = 1 − S + S²/2 − e^{−S} has h(0) = 0 and h′(S) = −1 + S + e^{−S} ≥ 0. For j > d,
φ_d(j) = 0 and |1 − S| = S − 1 ≤ S²/2 holds for every S ((S−1)² + 1 > 0). ∎

Since Σ_j c_j C(j,2) z^j = z²g″(z)/2, (E5) sums to

> **Ã_d = g − z²g″/(2d) + r_d,  sup_{|z|≤ρ} |r_d| ≤ C_ρ/d²,  C_ρ = ½·Σ_j |c_j| C(j,2)² ρ^j < ∞.**

## 2. Theorem A — clearance off the zero set

**Theorem A [PROVED HERE].** Let g ∈ LP₀, τ = a+bi (b > 0), R > 0, ε > 0. Put Z = g^{−1}(0),
K_ε = {z ∈ [−R,R] : dist(z, Z) ≥ ε}, m_ε = min_{K_ε}|g| > 0, M_R = sup_{[−R,R]}|g″|. There
is d₀ = d₀(g,τ,R,ε) such that for every d ≥ d₀ and every critical point c of A_d with
z_c = dc ∈ K_ε:

> margin(c) ≥ κ_A · d²,  κ_A = b² m_ε / (4 (M_R + 1) R⁴).

*Proof.* By (E3) choose d₁ with sup_{[−R,R]}|Ã_d − g| ≤ m_ε/2 and sup_{[−R,R]}|Ã_d″ − g″| ≤ 1
for d ≥ d₁. Let c be a critical point with z_c ∈ K_ε. Then |A_d(c)| = |Ã_d(z_c)| ≥ m_ε/2 > 0
(so (E1) applies and c is not a zero of A_d), and |A_d″(c)| = d²|Ã_d″(z_c)| ≤ d²(M_R + 1) by
the chain rule. Hence by (E1)

> c⁴ ℰ(c) = (z_c⁴/d⁴)·d²·|Ã_d″(z_c)|/|Ã_d(z_c)| ≤ 2(M_R+1)R⁴/(m_ε d²),

while (E2) gives q_d(c) ≥ b²/2 for d ≥ 2R²/b². Divide. d₀ = max(d₁, ⌈2R²/b²⌉). ∎

**Corollary A′ (simple zeros absorb) [PROVED HERE].** If every zero of g in [−R,R] is
simple, choose ε > 0 with |g′| ≥ η > 0 on the ε-neighborhoods of Z ∩ [−R,R]. By (E3),
Ã_d′ → g′ uniformly there, so for d large NO critical point of A_d has z_c within ε of Z.
Theorem A then covers every window critical point: margin ≥ κ_A d². ∎

## 3. Theorem B — the cluster over a multiple zero

**Lemma W (Hermite equilibrium energy = charge count) [PROVED HERE].** Let He_m be the
probabilists' Hermite polynomial (He_m = e^{−∂²/2} u^m; He_m′ = m·He_{m−1},
He_m″ = m(m−1)·He_{m−2}, He_m = u·He_{m−1} − (m−1)·He_{m−2}). At every zero k of He_m′
(equivalently of He_{m−1}):

> W_m(k) := Σ_i (k − h_i)^{−2} = −He_m″(k)/He_m(k) = m,   (h_i = zeros of He_m).

*Proof.* At k: He_{m−1}(k) = 0, so the recurrence gives He_m(k) = −(m−1)He_{m−2}(k), while
He_m″(k) = m(m−1)He_{m−2}(k). Note He_{m−2}(k) ≠ 0: were He_{m−2}(k) = 0 = He_{m−1}(k), the
recurrence would force all lower He's to vanish at k down to He₀ = 1. Divide. ∎

So at each equilibrium of the Hermite charge gas, the electrostatic energy equals the number
of charges — the constant in Theorem B is universal in the configuration.

**Theorem B (Hermite splitting and cluster clearance).** Let g ∈ LP₀, g(0) ≠ 0, and let
x* ≠ 0 be a real zero of g of multiplicity m ≥ 2; τ = a+bi, b > 0; σ = |x*|/√d. Then for
small ε > 0 and d large:

1. **(splitting)** A_d has exactly m zeros with dα ∈ (x*−ε, x*+ε), located at
   dα = x* + σ(h_i + o(1)) (h_i the zeros of He_m), and exactly m−1 critical points there,
   at z_c = x* + σ(k_i + o(1)) (k_i the zeros of He_m′); there are no other critical points
   in the interval.
2. **(clearance)** at each of these critical points, using Lemma W,

   > margin(c) = (|x*−τ|² / (m·x*²)) · d · (1 + o(1)) → ∞.

**Status:** m ≤ 3 [PROVED HERE] below from (E5). m ≥ 4 holds modulo **Lemma R** (§3.2) —
proof-shaped — and is probe-certified at m = 4 (P-B3: the ratio to the predicted constant is
1 within 4·10⁻³ at d = 10⁴, 7·10⁻⁴ at d = 10⁵, at all three cluster critical points).

### 3.1 Proof for m = 2, 3 (via (E5))

Write g(x*+t) = a_m t^m (1 + O(t)), g″(x*+t) = m(m−1) a_m t^{m−2}(1 + O(t)), a_m ≠ 0. On the
cluster scale t = σu, |u| ≤ M (complex), (E5) gives

> Ã_d(x* + σu) = a_m [ t^m − (m(m−1)/2)(x*²/d) t^{m−2} ] + O(σ^{m+1}) + O(1/d²)
> = a_m σ^m [ u^m − C(m,2) u^{m−2} + O(σ) ] = a_m σ^m [ He_m(u) + O(σ) ],

since He₂ = u²−1, He₃ = u³−3u, and every error is O(σ) relative: the next Taylor
coefficient contributes a_{m+1}σ^{m+1}u^{m+1}; the variation (z²−x*²)g″/(2d) contributes
O(σ·σ^{m−2}·σ²); and r_d = O(1/d²) = O(σ⁴) ⊆ O(σ^{m+1}) exactly when m ≤ 3 — this is the
only place the multiplicity bound enters. The estimate holds on complex u-discs, so:

- **Zeros.** Hurwitz on Ã_d → g in the ε-disc: exactly m zeros, all real (A_d hyperbolic).
  Rouché at scale σ around each simple zero h_i of He_m: dα = x* + σ(h_i + O(σ)).
- **Critical points.** Differentiating the display (Cauchy, half-radius):
  σ Ã_d′(x*+σu)/(a_m σ^m) = He_m′(u) + O(σ), and the zeros of He_m′ are simple, so there are
  m−1 critical points at z_c = x* + σ(k_i + O(σ)). Hurwitz on Ã_d′ → g′ (which has an
  (m−1)-fold zero at x*) shows these are ALL critical points in the ε-disc.
- **Energy.** Ã_d″(x*+σu) = a_m σ^{m−2}[He_m″(u) + O(σ)], and He_m(k_i) ≠ 0 (Lemma W), so by
  (E1): ℰ(c) = d²·(−Ã_d″/Ã_d)(z_c) = (d²/σ²)·(W_m(k_i) + O(σ)) = (d²/σ²)(m + O(σ)). Hence
  c⁴ℰ(c) = (z_c⁴/d⁴)·ℰ(c) = (m + O(σ))·x*²/d, while q_d(c) = |x*−τ|² + O(σ) by (E2).
  Divide; the relative error is O(d^{−1/2}). ∎

### 3.2 General m: Lemma R (proof-shaped) and the contour representation

The generating identity Σ_d J^d(x) u^d/d! = e^u g(xu) is a Cauchy coefficient formula:

> **Ã_d(z) = (d!/2πi) ∮_{|u|=d} e^u g(zu/d) u^{−d−1} du
> = (d! e^d/(2π d^d)) ∫_{−π}^{π} exp(d(e^{iϑ} − 1 − iϑ)) · g(z e^{iϑ}) dϑ**  [exact].

The phase localizes at ϑ = O(d^{−1/2}) (Gaussian of variance 1/d), where g(ze^{iϑ}) =
g(z + izϑ + O(zϑ²)): an **imaginary-direction Gaussian smoothing of width |z|/√d** — i.e.
E[g(z + izV/√d)], V standard normal, which is e^{−(z²/2d)∂²}g: the same backward-heat
operator as (E4), now resummed to all orders. On the cluster scale this evaluates to the
Hermite family term by term (e^{−s∂²} t^k = (2s)^{k/2} He_k(t/√(2s)), √(2s) = σ):

> **Lemma R [proof-shaped].** Uniformly on complex |s| ≤ M,
> Ã_d(x* + σs) = a_m σ^m ( He_m(s) + O(d^{−1/2}) ).

The missing content is standard Laplace bookkeeping: the third-order phase correction and
the g-Taylor remainder, both O(d^{−1/2}) relative. (Alternative elementary route: extend
(E5) to P cumulant orders — the same Weierstrass/exp inequalities — and take P = ⌈m/2⌉; each
order is an (E5)-style two-line inequality. Either route feeds §3.1's argument verbatim.)
Probe P-B certifies the output at m = 4: all three cluster margins match
|x*−τ|²d/(4x*²) to O(d^{−1/2}) over d = 10²…10⁵.

**Remark (single scale, not a cascade).** The splitting puts all m zeros at the ONE scale σ
in the well-spaced He_m configuration. A naive Newton-polygon reading of the two-term
expansion would predict a multi-scale cascade (pairs peeling at d^{−1/2}, d^{−1}, …), whose
deeper levels would VIOLATE clearance from m = 4 on; the heat resummation — all powers of
(z²∂²/2d) are the same size at scale σ — is what forbids the cascade. The reader's tracking
clearance is multiplicity-blind precisely because the sections flow to the carrier by heat,
and heat splits degeneracies into equilibrated (Hermite) configurations, never into nested
ones.

## 4. Corollary C — the dip is inside the tracking window

**Corollary C [PROVED HERE].** q_d(c) is minimized at c = a/(d−1), i.e. z_c = ad/(d−1) → a,
with minimum b² − a²/(d−1). Take R ≥ 2|a| + 1. For d ≥ 2, |z_c| = |a|·d/(d−1) ≤ 2|a| < R,
so every dip-region critical point lies in the tracking window, where Theorem A /
Corollary A′ / Theorem B give margin ≥ min(κ_A d², κ_B d) → ∞. Part (ii) of (AMP-mono) is
therefore subsumed by part (i): there is no separate dip regime. ∎

This also explains the measured transient (doc 24 §4: model 1, d = 8, T = 2 in the dip,
clearing at d ≥ 10): it is the finite-d shadow of the q_d-definiteness threshold
d > 1 + a²/b² = 7.25, below which q_d takes negative values and no clearance statement is
available — not a failure of monotonicity.

## 5. What this closes and what it opens

**(AMP-mono) is now part (iii) alone.** For any R and d ≥ d₀(g,τ,R): margin > 1 at every
critical point with dc ∈ [−R,R] (multiplicity ≤ 3 unconditional; any multiplicity modulo
Lemma R). The single-crossing statement is now purely about the **outer critical points**
dc ∉ [−R,R]: show c⁴ℰ(c)/q_d(c) crosses 1 exactly once along them. Measured at zero
violations (doc 24 §4); open.

Tools this doc hands to (iii):

- **The contour representation** (§3.2, exact). In the outer regime the saddle interacts
  with the growth of g — the section leaves the heat regime and enters the Laguerre/theorem-m
  regime; the object to construct is the outer saddle's margin flow along the equilibrium
  curve.
- **Lemma W's shape.** At Hermite equilibria, energy = charge count. [CONJECTURE] The
  outer analogue: at consecutive equilibria c_i < c_{i+1} of A_d, the equilibrium constraint
  Σ(c−α_k)^{−1} = 0 near-symmetrizes the neighbor configuration, forcing c⁴ℰ(c) to increase
  between consecutive equilibria while q_d grows only quadratically in c — the registered
  attack line on (iii).
- **The u-plane instance.** With (i)+(ii) proved, the first theorem-track finite window
  (#136's truncation zero read through the u-plane one-sided-far carrier, doc 24 §6) rests
  on proved tracking legs; running it is the immediate experiment.
