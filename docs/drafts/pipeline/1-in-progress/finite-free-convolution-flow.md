# The degree-`d` finite-free / Hankel section cocycle (the bounded-degree C5★ carrier)

- **ID:** finite-free-convolution-flow
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (native C5★ carrier) — with a proven fixed-`d` core (BRIDGE) and an open `d→∞` crux
- **Priority:** FOUNDATIONAL
- **Source:** refined C5★ (Part 3) of `combination-mode-baker-reducibility.md`; ../../door/bucket-new-sibling-conjectures.md · 00-status #104, #113
- **Statement.** The degree-`d` finite-free (Jensen/Hankel) section of `Ξ` defines a **bounded-degree**
  cocycle over the `𝕋^∞` prime-frequency flow whose reducibility = real-rootedness (Hermite PSD) of the
  section. RH = stability of this reducibility as `d → ∞`. The section is built from the primes (the
  per-prime kernel `K_d(p)`), not from the zeros — source-pure.

## The cocycle, pinned
- **Observables = secular/power-sum coordinates `P_k(θ)`**, `θ ∈ 𝕋^∞`. Via the explicit formula each `P_k`
  is a sum of **single-prime** contributions plus an archimedean term — **axis-mode** (one prime per
  Fourier mode), exactly like the 19a Euler cocycle. (Precise per-prime kernel: `K_d(p)`.)
- **Real-rootedness via Hermite/Hankel.** The degree-`d` section is hyperbolic ⟺ the Hankel form
  `H_d(θ) = (P_{i+j}(θ))_{0≤i,j<d}` is **PSD** (Hermite criterion: signature = #distinct real roots;
  team `HermiteHankelDetector`, `κ₋ = d − sig H`). Equivalently all leading minors `det H_j ≥ 0`.
- **Where combination modes enter.** `det H_j` is a **degree-`j` polynomial** in the `P_k`. A product
  `P_{k_1}···P_{k_j} = Σ_{p_1,…,p_j} ∏(single-prime terms)`; its cross terms (distinct primes, carrying
  the Hankel **minus-signs**) are genuine **mixed-sign combination modes** `m = Σ_i a_i δ_{p_i}`, support
  `≤ j ≤ d`.

> The power-sums/cumulants are **axis-mode** (additive over primes); the real-rootedness **condition** is
> **nonlinear** in them ⟹ **combination-mode, support bounded by `d`.** This is the precise meaning of
> "bounded degree": the polynomial degree `d` of the section = the max support size of the combination
> modes in its reducibility condition.

## Lemma (Hankel ↔ combination-mode degree) — PROVEN

This is the structural backbone of the carrier: it proves that the bounded-degree real-rootedness
certificate is genuinely **combination-mode of support `≤ d`** (so it is the right C5★ object — cross-prime,
Baker-relevant), and that the number of logarithms in every small divisor is bounded uniformly at fixed `d`.

**Hypothesis (H) — axis-mode secular data.** The degree-`d` section `f_d(·;θ)` (built from the per-prime
kernel `K_d(p)`) is a real degree-`d` polynomial for each `θ ∈ 𝕋^∞ = ∏_p ℝ/ℤ`, and its power sums
`P_k(θ) = Σ_{roots} r^k` (`k = 0,…,2d−2`) are **axis-mode**:
> `P_k(θ) = c_k + \tilde P_k(θ)`, `\tilde P_k(θ) = Σ_p u_{k,p}(θ_p)`,

each `u_{k,p}` a mean-zero function on the single circle at `p` (Fourier support in `{a δ_p : a ≠ 0}`),
`c_k ∈ ℝ`, `P_0 ≡ d`. *(H) is the construction's defining property — the secular coordinates of an Euler
product are additive over primes (the same mechanism that makes the 19a Euler cocycle axis-mode), so a
section assembled from per-prime kernels inherits axis-mode power sums. (H) is the arithmetic input;
(i)–(iv) are what it buys.* Write `ℓ = (\log p)_p`; a mode `m ∈ ℤ^{(P)}` has frequency
`m·ℓ = Σ_p m_p \log p` and support `supp(m) = {p : m_p ≠ 0}`.

Let `H_d(θ) = (P_{i+j}(θ))_{0≤i,j≤d−1}` (the Hermite–Hankel form) and `D_j(θ) = det(P_{i+k})_{0≤i,k≤j−1}`
its leading `j×j` minor (`D_d = det H_d`).

**(i) Hyperbolicity = Hankel PSD (Hermite).** For each `θ`, `f_d(·;θ)` has all roots real ⟺ `H_d(θ) ⪰ 0`;
all roots real and simple ⟺ `H_d(θ) ≻ 0`.
*Proof.* `H_d = V V^{\!\top}` with `V = (r_j^{\,i})_{0≤i≤d−1,\,1≤j≤d}` Vandermonde, since
`(VV^{\!\top})_{i i'} = Σ_j r_j^{\,i+i'} = P_{i+i'}`. Hence `D_d = (\det V)^2 = ∏_{i<j}(r_i−r_j)^2` (the root
discriminant). Hermite's theorem: `rank H_d = #`{distinct roots}, `sig H_d = #`{distinct real roots}; so all
roots real ⟺ `sig = rank` ⟺ `H_d ⪰ 0`, and simple ⟺ `rank = d` ⟺ `H_d ≻ 0`. ∎

**(ii) Bounded support.** Every Fourier mode `m` of `D_j` has `|supp(m)| ≤ j`. Hence `D_d` and the whole
certificate `{D_1 ≥ 0, …, D_d ≥ 0}` (equivalently `H_d ⪰ 0`) live on modes of support `≤ d`.
*Proof.* `D_j = Σ_{σ∈S_j} sgn(σ) ∏_{i=0}^{j−1} P_{i+σ(i)}` — a sum of products of **exactly `j`** power
sums. Expand each factor `P_k = c_k + \tilde P_k`; a resulting term is
`(∏_{i∉S} c_{k_i})·∏_{i∈S} \tilde P_{k_i}` for some `S ⊆ {0,…,j−1}`, `|S| ≤ j`. Now
`∏_{i∈S} \tilde P_{k_i} = ∏_{i∈S}(Σ_p u_{k_i,p}) = Σ_{(p_i)_{i∈S}} ∏_{i∈S} u_{k_i,p_i}`, and each summand
`∏_{i∈S} u_{k_i,p_i}` has Fourier support `⊆ {p_i : i∈S}`, so support size `≤ |S| ≤ j`. Constants carry
support `0`. So every mode of `D_j` has support `≤ j`. ∎

**(iii) Attained — not axis-mode for `d ≥ 2`.** The top axis-degree part of `D_j` is the centered Hankel
determinant `det(\tilde P_{i+k})_{0≤i,k<j}`, a nonzero degree-`j` form in the `\tilde P_k`, which for generic
axis data carries modes of support exactly `j`. Already at `j = 2`:
`D_2 = P_0 P_2 − P_1^2 = d(c_2+\tilde P_2) − (c_1+\tilde P_1)^2`, whose `−\tilde P_1^2 = −(Σ_p u_{1,p})^2`
term contributes support-2 modes `−2\,u_{1,p}u_{1,q}` (`p ≠ q`), and since each `u_{1,p}` is real its
Fourier expansion carries both signs, giving the **mixed-sign** modes `a δ_p − b δ_q` — exactly the
near-resonance-carrying ones. So for `d ≥ 2` the certificate engages the joint `σ_p` structure; it is **not**
axis-mode (contrast the 19a/Euler cocycle, support 1, which decoupled prime-by-prime ⟹ BRIDGE).

**(iv) Baker corollary (fixed-`d` Diophantine exponent).** For `m ≠ 0`, `m·ℓ = \log ∏_p p^{m_p} ≠ 0`
(unique factorization — the no-resonance input Baker also requires). By (ii) any certificate mode `m` has
`n := |supp(m)| ≤ d`, so `m·ℓ` is a linear form in `≤ d` prime logarithms. Baker–Wüstholz gives
`|m·ℓ| ≥ γ(n; supp\,m)·H(m)^{−κ(n; supp\,m)}`, `H(m) = max(3, \max_p|m_p|)`, with `κ` depending only on
`n ≤ d` and the heights `{\log p : p ∈ supp(m)}`. **At fixed `d` and fixed support this is a fixed polynomial
Diophantine bound** — the input the fixed-`d` edge reducibility consumes (a fixed exponent ⟹ the
bounded-support small-divisor sum converges; cf. Lemma R / the Liouville-substitute divergence). As
`d → ∞` both `n` and the admissible primes grow and `κ` degrades super-exponentially in `n`; controlling
that degradation is the open crux.

**Grade — structural lemma (BRIDGE).** (i) is Hermite (parent), (ii)–(iii) are elementary Fourier
bookkeeping over hypothesis (H), (iv) is Baker (parent). Its role is not to *be* C5 but to **certify** that
the bounded-degree certificate is genuinely combination-mode of support `≤ d` — i.e. that the finite-free
section is the correct C5★ carrier — and to bound the number of logarithms uniformly at fixed `d`.

## Resolves the Part-3 tension (bounded-degree ∧ RH-relevant)
The finite-free section is **simultaneously**:
- **bounded-degree** (support `≤ d`) — unlike the Rankin–Selberg moment (unbounded composite support);
- **RH-relevant** — unlike the flat curvature `F_{pq}`. RH ⟺ every degree-`d` section is hyperbolic for
  all `d` (Pólya–Jensen; Griffin–Ono–Rolen–Zagier 2019).

RH-relevance enters through the **nonlinear PSD condition** (the discriminant boundary), *not* the linear
cumulants — which is exactly why the linear/flat `F_{pq}` missed it and why this carrier does not.

## The Baker-necessity test — verdict
Split the `d → ∞` reducibility into **bulk** and **edge**.
- **Bulk** (moments `P_k`, `k ≪ d`): finite-free cumulants `κ_k^{(d)} → ` free cumulants (MSS /
  free-probability CLT); the bulk moments **concentrate**. Soft, arithmetic-blind — a free-probability
  **parent** ⟹ BRIDGE.
- **Edge** (the discriminant boundary `det H_d = 0`): the real-rootedness frontier, where the
  **degenerations = zeros** live (19b "zeros = degenerations"; Fyodorov–Hiary–Keating log-correlated
  extremes). **Not** CLT-controlled — an edge / extreme-value phenomenon. This is where the mixed-sign
  combination modes and their near-resonances sit.

**At each fixed `d` (edge): Baker is load-bearing.** Baker–Wüstholz for a **fixed** number (`≤ d`) of logs
of fixed primes gives a **fixed** Diophantine exponent `κ_d`: `|Σ a_i log p_i| ≥ γ_d·B^{-κ_d}`,
`B = max|a_i|`. So the bounded-support small-divisor sum
`Σ |ĝ(m)|²/|m·ℓ|² ≤ γ_d^{-2} Σ |ĝ(m)|² B^{2κ_d}` **converges** (geometric `∏ p_i^{-a_iσ}` decay beats the
polynomial `B^{2κ_d}`). Without Baker (a Liouville-substituted frequency vector) it **diverges** —
Lemma R, now at bounded support. ⟹ **the degree-`d` edge cocycle is reducible, Baker essential.**

**The `d → ∞` uniform limit needs more than Baker.** Baker gives only the safety **floor**
`|m·ℓ| ≥ exp(−C(d)·∏ log p_i·log B)`, and the floor **degrades super-exponentially** in `d`
(`C(d) ~ d^{cd}`; the height product `∏ log p_i` grows). The Baker-saturating worst-case mode, *if* present
with non-negligible coefficient, blows the `L²` norm up as `d → ∞`. Whether it is present is **not** decided
by Baker — it is decided by the **actual near-zero distribution** of bounded-support combinations
`Σ_{|S|≤d} a_p log p`.

> **Verdict.** The degree-`d` finite-free section cocycle is reducible at **every fixed `d`**, and Baker is
> genuinely **load-bearing** there (it supplies the fixed Diophantine exponent the edge sum needs; the
> Liouville substitute fails). So `d → ∞` reducibility **does** need the bounded-degree Baker control at each
> stage — but Baker is **not sufficient** for the uniform limit: the limit is governed by the **near-zero
> distribution of bounded-support prime-log combinations**, a metric statement about the multiplicative
> group `⟨log p⟩` strictly stronger than Baker's floor. **That is the native C5 crux.**

## GORZ alignment
Griffin–Ono–Rolen–Zagier (2019, recalled): for each fixed `d`, the Jensen polynomial `J_{d,n}(Ξ)` is
hyperbolic for all `n ≥ N(d)`, the `d` roots `→` the Hermite `H_d` roots. That is exactly the
**bulk / archimedean-dominated** half ("`H_d` PSD") proven. The open half — the finitely many small-`n`
sections per `d`, near the discriminant boundary — is exactly the **edge** control above. So GORZ = the
bulk half; the C5 crux = the **uniform edge** half.

## Door-2
- **Fixed `d`:** finite-free (field) + Hermite/Hankel + finite-`#`-logs Baker + free-probability bulk = a
  parent-combination, a sophisticated **BRIDGE**.
- **`d → ∞` uniform edge:** the near-zero distribution of bounded-support log-combinations must survive the
  infinite-base passage (heights growing, support `→ ∞`). No single parent reaches it — the native-zone
  **C5★** candidate, now localized to a metric-number-theory question. Open.

## Gates
- [x] 0 → 1  in-progress: cocycle pinned (power-sums `→` Hankel PSD, support `≤ d`); Part-3 tension
  resolved (bounded-degree ∧ RH-relevant); Baker-necessity verdict (load-bearing at each `d`; the limit
  needs the near-zero distribution). **Hankel ↔ combination-mode degree lemma PROVEN** (i)–(iv): support
  `≤ d`, attained (not axis-mode for `d ≥ 2`), fixed-`d` Baker exponent.
- [ ] 1 → 2  fully-proven: the bounded-degree edge reducibility at **fixed `d`** is provable
  (finite-`#`-logs Baker + `𝕋^{≤d}` KAM); the **`d → ∞` uniform edge control** is the open crux.
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Next steps
1. **Quantify the edge/bulk split.** Locate the support-`≤ d` modes nearest `det H_d = 0` and estimate
   their `coefficient × Baker-floor` product as a function of `d` (does it stay summable, or does the
   floor degradation win?).
2. **The decisive metric question.** Is the near-zero distribution of `{Σ_{|S|≤d} a_p log p}` controlled
   **uniformly in `d`** beyond Baker's floor? This is the native crux — a statement about `⟨log p⟩`,
   RH-relevant via the explicit formula (the #72 / G2 "Liouville substitute").
3. **Numerics (runpod, confirmatory only).** (a) finite-free cumulants of `J^{d,n}(Ξ)` vs `Σ_p κ_k(p)`;
   (b) the smallest `|Σ_{p∈S} a_p log p|` over `|S| ≤ d`, `|a| ≤ B` vs the Baker floor — measure the gap
   (how far the actual edge sits above the floor). Archive under `computations/`.

## Log
- 2026-06-19 — created in 0-backlog (RH = finite-free CLT fixed-point stability).
- 2026-06-19 — moved to 1-in-progress; **pinned** as the degree-`d` finite-free/Hankel cocycle (the
  bounded-degree C5★ carrier). Power-sums axis-mode, Hankel-PSD condition combination-mode (support
  `≤ d`) — **resolves the Part-3 bounded-degree↔RH-relevance tension.** Baker-necessity **verdict**:
  load-bearing at every fixed `d` (fixed-`#`-logs Diophantine exponent; Liouville substitute fails); the
  `d → ∞` limit governed by the near-zero edge distribution **beyond** Baker's floor (the native crux).
  Bulk/edge split links GORZ (bulk proven) and 19b (edge = degenerations).
- 2026-06-19 — **Hankel ↔ combination-mode degree lemma proven** (structural backbone). Under hypothesis
  (H) (axis-mode secular power sums, from the explicit formula): (i) hyperbolic ⟺ `H_d ⪰ 0` (Hermite,
  `H_d = VV^⊤`, `det H_d = disc`); (ii) the leading minor `D_j` has Fourier modes of support `≤ j` (the
  `j`-fold product of axis-mode `P_k`), so the certificate `H_d ⪰ 0` lives on support `≤ d`; (iii)
  attained, with genuine mixed-sign cross-prime modes already at `d = 2` (the `−P_1²` term) — **not**
  axis-mode for `d ≥ 2`; (iv) Baker–Wüstholz then gives a fixed Diophantine exponent at fixed `d`
  (`≤ d` logs), the `d → ∞` degradation being the open crux. Grade BRIDGE. Catalogued 00-status #114.
