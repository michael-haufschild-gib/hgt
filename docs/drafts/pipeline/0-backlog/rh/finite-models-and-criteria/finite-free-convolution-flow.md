# The degree-`d` finite-free / Hankel section cocycle (the bounded-degree C5★ carrier)

- **ID:** finite-free-convolution-flow
- **Stage:** 1-in-progress
- **Type:** carrier — proven structural lemma + proven `d→∞` reducibility **threshold** (`σ>¾`, BRIDGE,
  **RH-blind**); the reducibility⟺RH encoding is **refuted**; the live RH object spun out = single-orbit
  hyperbolicity (positivity)
- **Source:** refined C5★ (Part 3) of `combination-mode-baker-reducibility.md`; ../../../../door/bucket-new-sibling-conjectures.md · 00-status #104, #113
- **Statement.** The degree-`d` finite-free (Jensen/Hankel) section of `Ξ` lives over the `𝕋^∞`
  prime-frequency flow. Two notions split: its **coboundary/reducibility** (a `𝕋^∞`-variance quantity) has
  abscissa `σ > ¾` and is **RH-blind**; its **single-orbit hyperbolicity** (positivity of `det H_d` along
  the diagonal = Pólya–Jensen / GORZ) **is** RH. The section is built from the primes (the per-prime kernel
  `K_d(p)`), not from the zeros — source-pure.

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
Lemma R, now at bounded support. ⟹ **the degree-`d` edge cocycle is reducible at each fixed `d`.**
*(Baker suffices here but is not sharp: for the physical coefficients the controlling bound is the
elementary integer-gap one — see Step 1 of the next section — which is why the `d → ∞` threshold below is
Baker-free. Baker is the sharp/essential input only for the toy `e^{−ρ|m|}` profile of Lemma R.)*

**The `d → ∞` limit — RESOLVED (2026-06-19), threshold `σ = ¾`, Baker-free.** Worked to conclusion in the
next section. The near-zero distribution is governed by the **elementary integer-gap** bound
`|\log(n_+/n_-)| ≥ |n_+−n_-|/\max`, not Baker; the edge coboundary norm `N_∞(σ)` converges **iff `σ > ¾`**,
the obstruction in `(½,¾]` being the **consecutive-/balanced-coprime-integer** near-resonances `(M, M−1)`.

> **Verdict.** The cocycle-**reducibility** framing of C5★ is **resolved and RH-blind.** The edge coboundary
> norm is a `𝕋^∞`-variance quantity with abscissa `¾`; by the A1/A2 split (Weyl equidistribution: `L²`
> controls the typical fluctuation, not the single-orbit sign) it cannot see RH — `σ = ½` lies deep in the
> non-reducible zone. RH is the **single-orbit positivity** `det H_d(θ_{diag}(t)) ≥ 0` (= Pólya–Jensen /
> GORZ hyperbolicity along the diagonal). So reducibility is the **wrong handle**; the native/RH object is
> the section's **single-orbit hyperbolicity (a positivity/sign statement)**, not its coboundary.

## The `d → ∞` edge distribution — worked to conclusion (threshold `σ = ¾`)

**Object.** The edge transfer-function norm `N_d(σ) := Σ_{m ≠ 0,\ |supp\,m| ≤ d} |ĝ(m)|² / |m·ℓ|²`
(from `Dh = g`, `ĥ(m) = ĝ(m)/(i\,m·ℓ)`), under the **explicit-formula coefficient model (H′)**:
`|ĝ(m)| ≍ ∏_{p∈supp m}(\log p)\,p^{-|m_p|σ}`, so `|ĝ(m)|² ≍ ∏(\log p)²·(n_+ n_-)^{-2σ}`, where
`n_± = ∏_{±m_p>0} p^{|m_p|}` are coprime, `n_+ n_- = ∏ p^{|m_p|}`, and `m·ℓ = \log(n_+/n_-)`. `N_d`
increases in `d`; uniform reducibility ⟺ `lim_d N_d = N_∞ < ∞`.

**Step 1 — the divisor is elementary, not Baker.** For coprime `n_+ ≠ n_-`,
`|m·ℓ| = |\log(n_+/n_-)| ≥ |n_+ − n_-| / \max(n_+,n_-)` (from `|\log x| ≥ |x−1|/\max(x,1)`), **sharp** for
balanced pairs `n_+ ≈ n_-`. Baker–Wüstholz gives only a far weaker floor — it is **not** the controlling
input here. (Baker *is* essential for the toy profile `|ĝ| = e^{−ρ|m|}` of Lemma R, where the integer-gap
bound `e^{−Σ|a_i|\log p_i}` is too weak; the physical profile `∏ p^{−2|a|σ}` is the opposite regime, ruled
by integer gaps.)

**Step 2 — non-resonant part (`|m·ℓ| ≥ 1`): converges for `σ > ½`.**
`Σ_{|m·ℓ|≥1}|ĝ(m)|² ≤ Σ_m |ĝ(m)|² = Σ_{s≥0}\tfrac1{s!}\big(Σ_p 2(\log p)²\,p^{-2σ}/(1−p^{-2σ})\big)^s
= \exp(C_{NR}(σ)) < ∞` for `σ > ½` (since `Σ_p(\log p)²p^{-2σ}<∞`). The `1/s!` (ordered prime tuples) tames
the support sum — the same exponential structure as the finite-free generating function.

**Step 3 — resonant part (`0 < |m·ℓ| < 1`): threshold `σ = ¾`.** Parametrise by coprime pairs, `M=\max`,
`μ=\min`, `Δ=M−μ≥1`; `|m·ℓ| ≍ Δ/M` (balanced), weight `(Mμ)^{-2σ}`.
- *Balanced* (`Δ ≤ M/2`, `μ ≍ M`): contribution `≍ (M²)^{-2σ}·(M²/Δ²)·∏(\log p)² = M^{2-4σ}\,Δ^{-2}∏(\log p)²`.
  Summing `Σ_{Δ≥1}Δ^{-2}·Σ_M M^{2-4σ}(\log\text{-factors})`. The `Δ = 1` **consecutive-integer** family
  `(M, M−1)` (always coprime) alone gives `Σ_M M^{2-4σ}∏_{p|M(M−1)}(\log p)²`: since `∏(\log p)² ≥ (\log 2)²`
  this **diverges for `σ ≤ ¾`**; since the log-factor is `M^{o(1)}` it **converges for `σ > ¾`** (and
  `Σ_Δ Δ^{-2}<∞` holds the threshold for the full balanced sum).
- *Unbalanced* (`μ < M/2`): `|m·ℓ| > \log 2`, so `1/|m·ℓ|²` is bounded and the part is `≤ (\log2)^{-2}Σ_m|ĝ|² < ∞`
  for `σ > ½` (Step 2).

So **`N_∞(σ) < ∞ ⟺ σ > ¾`.** A coprime pair enters the support-`≤ d` sum once `d ≥ ω(n_+n_-)`; since typically
`ω(M(M−1)) ∼ 2\log\log M`, the cutoff is `M ≲ \exp\exp(d/2)`, and `N_d ↑ N_∞` — finite at each `d`, diverging
as `d→∞` for `σ ≤ ¾`. (The driving family is the consecutive / balanced-coprime — Størmer–Pillai — integers,
matching the cross-session prime-gap heuristic.)

**Step 4 — why this is RH-blind (the A1/A2 relocation).** `N_d` is an `L²(𝕋^∞)` (full-torus / second-moment)
quantity. RH is the **single-orbit sign** `det H_d(θ_{diag}(t)) ≥ 0 ∀t` along the diagonal
`θ_p(t) = −(t\log p)/2π` (= the degree-`d` section hyperbolic = Pólya–Jensen / GORZ). By Weyl equidistribution
the orbit fills `𝕋^∞`, so `L²` controls the *typical fluctuation* of the coboundary — **not** the pointwise
sign (a bounded coboundary can still change sign). Hence the `¾`-threshold is a **variance** statement,
**structurally blind to RH** — the same A1/A2 blindness that sinks the 19a erosion threshold. The RH content
of the carrier is the **single-orbit positivity**, not the coboundary norm.

**Conclusion for C5★.** The cocycle-**reducibility** framing is **resolved and is the wrong handle.** It
measures the `𝕋^∞`-variance (abscissa `¾`, Baker-free, consecutive-integer-driven), not the single-orbit
sign that is RH; `σ = ½` (RH) lies deep in the non-reducible zone. The live native object is the
**single-orbit hyperbolicity of the degree-`d` finite-free section** (positivity of `det H_d` along the
diagonal) — an A1 / positivity statement (the project's recurring positivity wall), now in a sharp
GORZ-connected form. *(All conditional on (H′); a systematic cancellation of `det H_d` on the
consecutive-integer modes would change the threshold and would itself be a remarkable arithmetic fact —
flagged for the numerical probe.)*

## GORZ alignment
Griffin–Ono–Rolen–Zagier (2019, recalled): for each fixed `d`, the Jensen polynomial `J_{d,n}(Ξ)` is
hyperbolic for all `n ≥ N(d)`, the `d` roots `→` the Hermite `H_d` roots. This is **single-orbit
positivity in the archimedean-dominated range** (`H_d ⪰ 0` proven for large `n`) — already the A1 / sign
quantity, *not* the coboundary norm. The open RH content is single-orbit hyperbolicity for the finitely
many **small-`n`** sections per `d`, where the prime fluctuations are not yet damped. So GORZ proves the
easy end of the **positivity** problem; the hard end (small `n`) is the live C5/RH object — and the
`d → ∞` *coboundary* threshold (`¾`) is a separate, RH-blind variance fact, not this.

## Door-2
- **The `d → ∞` reducibility threshold (`σ > ¾`):** proof = elementary integer-gap bound + geometric
  prime-sums + smooth-number truncation — all parents (elementary number theory). **BRIDGE.** And it is
  RH-blind (a `𝕋^∞`-variance fact), so not a C5 candidate.
- **The live C5/RH object = single-orbit hyperbolicity** (positivity of `det H_d` along the diagonal).
  Door-2 status **to be tested**: does proving its positivity *essentially* use the joint `σ_p` structure,
  or does a positivity parent (Pólya–Jensen / GORZ / a moment method) reach it? This is the next gate — and
  it is a sign/positivity question, the project's recurring wall, not a coboundary question.

## Gates
- [x] 0 → 1  in-progress: cocycle pinned (power-sums `→` Hankel PSD, support `≤ d`); Part-3 tension
  resolved (bounded-degree ∧ RH-relevant); Baker-necessity verdict (load-bearing at each `d`; the limit
  needs the near-zero distribution). **Hankel ↔ combination-mode degree lemma PROVEN** (i)–(iv): support
  `≤ d`, attained (not axis-mode for `d ≥ 2`), fixed-`d` Baker exponent.
- [~] 1 → 2  fully-proven (split): the **`d → ∞` reducibility threshold `σ > ¾`** is **PROVEN** (Steps 1–3,
  conditional on the coefficient model (H′); BRIDGE, RH-blind). The reducibility⟺RH **encoding is refuted**
  (`σ=½` non-reducible). The **live RH target spun out** — single-orbit hyperbolicity (positivity of
  `det H_d` along the diagonal) — is **open** (its Door-2 status untested).
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Next steps
1. ~~The decisive metric question (Baker floor vs near-zero distribution)~~ **RESOLVED (2026-06-19):**
   the controlling bound is the **elementary integer-gap** one (not Baker), and the edge coboundary norm
   has threshold **`σ > ¾`**, RH-blind (Steps 1–4 above).
2. **The new live target — single-orbit hyperbolicity.** Pose precisely: positivity of `det H_d(θ_{diag}(t))`
   for all `t` (= the degree-`d` section hyperbolic). Test its **Door-2**: does its proof essentially need
   the joint `σ_p` structure, or does a positivity parent (Pólya–Jensen / GORZ / a moment/LP method) reach
   it? This is the project's recurring positivity wall in a sharp finite-free form.
3. **Numerics (runpod, confirmatory only).** (a) confirm the `¾` threshold: `N_d(σ)` vs `d` for
   `σ ∈ {0.6, 0.7, 0.75, 0.8}`, checking divergence below `¾` and convergence above; (b) confirm the
   consecutive-integer family `(M, M−1)` dominates the resonant sum; (c) **test (H′)**: does `det H_d` have
   the explicit-formula coefficient size on the consecutive-integer modes, or is there systematic
   cancellation? Archive under `computations/`.

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
- 2026-06-19 — **`d → ∞` edge distribution worked to conclusion.** Under the explicit-formula coefficient
  model (H′), the edge coboundary norm `N_∞(σ)` converges **iff `σ > ¾`** (Steps 1–3): the controlling
  small-divisor bound is the **elementary integer-gap** `|log(n_+/n_-)| ≥ |n_+−n_-|/max` — **not Baker**
  (Baker rules only the toy `e^{−ρ|m|}` profile of Lemma R) — and the obstruction in `(½,¾]` is the
  **consecutive-/balanced-coprime-integer** resonances `(M,M−1)`, with support-`≤d` truncation at
  `M ~ exp exp(d/2)`. **Step 4:** `N_d` is a `𝕋^∞`-variance (`L²`) quantity, so by the A1/A2 split it is
  **RH-blind** — `σ=½` sits in the non-reducible zone. **The reducibility⟺RH encoding is refuted; the live
  RH object is single-orbit hyperbolicity** (positivity of `det H_d` along the diagonal = Pólya–Jensen/GORZ).
  Reducibility was the wrong handle; the wall is positivity (A1), not coboundary (A2).

## Single-orbit hyperbolicity: the archimedean-gap reduction (the no-margin race) — Wheeler, 2026-06-19

Advances Next-step 2 (pose the relocated RH target precisely; sharpen its Door-2). Result: single-orbit
hyperbolicity is reduced to a **spectral race between the archimedean margin and the joint-prime
fluctuation**, which identifies the C5★ wall with the **no-margin** bucket (#89–91) and the **seam /
archimedean obstruction** (#69/#71) in one concrete matrix statement.

**The target (precise).** Along the diagonal orbit `θ_diag(t) = (−(t·log p)/2π)_p ∈ 𝕋^∞`, set
`H_d(t) := H_d(θ_diag(t)) = (P_{i+j}(θ_diag(t)))_{0≤i,j<d}`. Then **RH ⟺ for every `d` and every `t ∈ ℝ`,
`H_d(t) ⪰ 0`** (the degree-`d` finite-free section is hyperbolic), equivalently the deficiency
`κ₋(d,t) := d − sig H_d(t) ≡ 0` (Pólya–Jensen; GORZ for the link to `J_{d,n}`).

**Archimedean / prime split.** By the explicit formula (hypothesis (H)) each power sum splits into an
archimedean mean and a mean-zero prime fluctuation: `P_k(t) = P_k^{arch} + \tilde P_k(t)`,
`\tilde P_k(t) = Σ_p u_{k,p}(θ_p(t))` with `E_t[\tilde P_k] = 0` (Weyl mean over the orbit). Hence the
Hankel form splits as
> `H_d(t) = A_d + δH_d(t)`,  `A_d := (P_{i+j}^{arch})_{0≤i,j<d}`,  `δH_d(t) := (\tilde P_{i+j}(t))_{0≤i,j<d}`.

`A_d` is purely archimedean (Γ-factor data); `δH_d(t)` is purely prime (the multiplicative wing), and by
the structural lemma (ii)–(iii) it carries **combination modes of support `≤ d`** — a genuine joint-`σ_p`
object, not axis-mode for `d ≥ 2`.

**Lemma A (archimedean positivity).** `A_d ≻ 0` for every `d`, with `λ_d := λ_min(A_d) > 0`.
*Proof.* In the GORZ normalization the archimedean Jensen polynomials converge (heat-flow / Γ-factor
asymptotic) to the Hermite polynomials `H_d`, which have `d` **distinct real** roots `{r_1,…,r_d}`. The
archimedean power-sum Hankel is then `A_d = V V^{\top}` with `V = (r_j^{\,i})_{0≤i<d,\,1≤j≤d}` the root
Vandermonde (as in structural lemma (i)); distinct real roots ⟹ `det V ≠ 0` ⟹ `A_d = VV^{\top} ≻ 0`. ∎

**Lemma B (the reduction / the race).** By Weyl's inequality `λ_min(H_d(t)) ≥ λ_d − ‖δH_d(t)‖_{op}`. Hence
> **(R)** if `sup_{t} ‖δH_d(t)‖_{op} < λ_d`, the degree-`d` section is hyperbolic for all `t`; and
> **RH ⟸ (R) holds for every `d`.**

So single-orbit hyperbolicity is a **race between the archimedean spectral margin `λ_d` and the
single-orbit supremum of the joint-prime fluctuation `‖δH_d(t)‖`.**

**This is the no-margin wall in matrix form.** `A_d` is a moment/Vandermonde Hankel; such matrices are
exponentially ill-conditioned (Gautschi–Beckermann: real-node Vandermondes have `σ_min` exponentially
small in `d`), so `λ_d = σ_min(V)^2 ↓ 0` as `d → ∞` — **the margin closes**, exactly the no-margin
signature (#89, `λ_min → 0` everywhere; #90 two-rate `margin ~ δ`, `cost ~ log 1/δ`). Consequently the
naive uniform bound **(R) is not satisfiable for all `d`** — RH is the strictly weaker **matched-rate**
statement that `sup_t ‖δH_d(t)‖` closes **no faster** than `λ_d`. This pins C5★/RH onto the no-margin
bucket and gives it a sharp spectral form: *RH ⟺ the joint-prime fluctuation never outruns the closing
archimedean margin, along the diagonal orbit, uniformly in `d`.*

**The seam reading.** The fight is `arch` (`A_d`) vs `prime` (`δH_d`) — the **one archimedean obstruction**
(#69/#71). On average the prime wing is zero-blind (`E_t δH_d = 0`: the A1/A2 RH-blindness of the variance
that sank the reducibility/coboundary framing); the only thing that can keep `H_d(t) ⪰ 0` down to small
`n`/large `d` is the archimedean margin `λ_d`. RH ⟺ the archimedean margin dominates the joint-prime
fluctuation along the diagonal. The variance (coboundary, abscissa `¾`) was RH-blind precisely because it
saw only `E_t‖δH_d‖²`, not the **single-orbit sup** against `λ_d` — which is what this reduction isolates.

**Door-2 (sharpened).** Lemma A (Hermite/GORZ) and Lemma B (Weyl perturbation) are parents ⟹ the
*sufficient* condition (R) is **BRIDGE**. The **native** content is the matched-rate outcome: `δH_d(t)` is
a function of all `σ_p` jointly (support-`≤ d` combination modes), and the claim that its single-orbit sup
closes at the archimedean rate is an infinite-base, joint-`σ_p`, metric statement that no single parent
reaches — GORZ controls only `λ_d` and the large-`n` end; a moment/LP method controls averages, not the
single-orbit sign; Baker/integer-gap controls the near-resonances of the support-`≤ d` modes that build
`δH_d`. **Conjecture (Wheeler).** No positivity parent bounds `sup_t ‖δH_d(t)‖` against `λ_d`: the
matched-rate control needs the joint near-resonance (Baker / integer-gap) structure of the support-`≤ d`
modes — the field's apparatus — so the *outcome* of the race is the native (C5) crux even though the
race's *existence* is bridge. This is the precise Door-2 target for the relocated RH object.

**Concrete probe (numerical, confirmatory).** (a) `λ_d = λ_min(A_d)` from the Hermite-root Vandermonde —
verify the two-rate `λ_d ≍ e^{−c d log d}` decay; (b) `sup_t ‖δH_d(t)‖` for small `d` from the per-prime
kernels `K_d(p)` along the diagonal — does the prime sup track `λ_d` (RH/matched) or outrun it? Archive
under `computations/`. *(This is the small-`n` end GORZ leaves open, now in spectral form.)*

## Log (cont.)
- 2026-06-19 (Wheeler) — **Single-orbit hyperbolicity posed precisely + the archimedean-gap reduction.**
  Split `H_d(t) = A_d + δH_d(t)` (archimedean Hankel + mean-zero joint-prime fluctuation). Lemma A:
  `A_d = VV^⊤ ≻ 0` (GORZ→Hermite distinct real roots), margin `λ_d = λ_min(A_d)`. Lemma B (Weyl):
  hyperbolicity is the race `sup_t‖δH_d‖` vs `λ_d`; RH ⟸ `sup_t‖δH_d‖ < λ_d ∀d`. Since `A_d` is an
  exponentially ill-conditioned moment/Vandermonde Hankel, `λ_d ↓ 0` — **the no-margin wall (#89–91) in
  matrix form**; RH = the matched-rate version. The arch-vs-prime split **is** the seam (#69/#71); the
  variance/coboundary framing was RH-blind because it saw `E_t‖δH_d‖²`, not the single-orbit sup vs `λ_d`.
  Door-2: (R) is BRIDGE (Weyl + GORZ); conjectured native crux = no positivity parent matches the rate
  without the joint support-`≤ d` near-resonance control. Cross-bucket synthesis: C5★ ⇄ no-margin ⇄ seam.

## Edge-localization of the matched-rate race — Wheeler, 2026-06-19

Refines the archimedean-gap reduction: the race is decided at the **spectral edge**, not the bulk.

The operator norm obeys `‖δH_d(t)‖_{op} ≤ d·max_{0≤k≤2d−2}|\tilde P_k(t)|`, and the high power sums
dominate (`\tilde P_k` is driven by the extreme roots `r_max^k` of the section). Under the GORZ
correspondence the section's **extreme roots** are the images of the **large/edge** spectral data, and its
**degenerations** (`det H_d = 0`, coincident roots) are exactly the **zeros** (19b "zeros = degenerations").
Therefore:
> **The matched-rate race is an edge phenomenon.** Whether `sup_t‖δH_d(t)‖` overcomes the
> super-exponentially small archimedean margin `λ_d` is decided by the **extreme-value statistics of the
> prime-perturbed section's largest roots** (Fyodorov–Hiary–Keating log-correlated extremes), against `λ_d`.

This separates the carrier cleanly from its BRIDGE part: the **bulk** moments (`k ≪ d`) concentrate by the
finite-free CLT (free-probability parent ⟹ BRIDGE, already known); the **edge** (top moments
`k ≈ 2d−2`) is the un-CLT'd, RH-bearing part — and the no-margin race lives entirely there. So C5★/RH
localizes to: *the FHK edge fluctuation of the degree-`d` section does not break the archimedean
positivity margin.* The native crux is an edge/extreme-value statement, not a bulk one — consistent with
the seam reading (the archimedean term is what damps the edge down to small `n`).

## The relative (scale-invariant) form of the race — correcting the additive reduction — Wheeler, 2026-06-19

The additive Weyl reduction (Lemma B: `λ_min(H_d(t)) ≥ λ_d − ‖δH_d(t)‖_op`) is **structurally too lossy
to decide RH**, and the fix sharpens both the criterion and its Door-2.

**Why the additive race is an artifact.** `A_d` and `δH_d(t)` are *both* Hankel forms of the power sums
`P_{i+j}`, so their entries share the same high-moment growth (`∼ r_max^{i+j}`). The additive bound
discards the strong `A_d`–`δH_d` correlation: `λ_min(H_d) ≥ λ_d − ‖δH_d‖_op` is **vacuous** — it can be
hugely negative even when `H_d(t) ⪰ 0` (i.e. even *under* RH), since `‖δH_d‖_op` is set by the
bottom-right (high-moment) corner while `λ_d := λ_min(A_d)` is set by the near-degeneracy of the root
Vandermonde (`λ_d ≍ e^{−c d}`, Beckermann–Gautschi). So (R) is unsatisfiable for large `d` for a **scaling
reason, not a real obstruction**; the "matched-rate vs `λ_d ↓ 0`" reading (#13/#20) was measuring in the
wrong units.

**The fix — congruence, not perturbation.** Since `A_d ≻ 0`, factor
> `H_d(t) = A_d^{1/2}\,(I + S_d(t))\,A_d^{1/2}`,  `S_d(t) := A_d^{-1/2}\,δH_d(t)\,A_d^{-1/2}`
(the prime fluctuation **in the archimedean metric** `A_d^{-1}`; `S_d(t)` symmetric). By **Sylvester's law
of inertia** congruence by `A_d^{-1/2}` preserves signature, so

> **Exact criterion.** `H_d(t) ⪰ 0 ⟺ λ_min(S_d(t)) ≥ −1`. Hence
> **RH ⟺ `λ_min(S_d(t)) ≥ −1` for all `d ≥ 1`, `t ∈ ℝ`** — the prime fluctuation, weighted by the
> archimedean (Γ-factor) metric, has **no eigenvalue below `−1`.**

The clean symmetric **sufficient** form drops `λ_d` entirely:
> **(R′)** `ρ_d(t) := ‖A_d^{-1/2} δH_d(t) A_d^{-1/2}‖_op < 1 ∀t ⟹` degree-`d` section hyperbolic;
> **RH ⟸ `sup_t ρ_d(t) < 1 ∀d`.**

`ρ_d` is dimensionless and `λ_d` has cancelled. The ill-conditioning of `A_d` is **not lost** — it lives
inside `A_d^{-1/2}`, which **amplifies** `δH_d` precisely along the small-margin (near-degenerate-root)
directions. So (R′) states the no-margin wall **correctly**: the only thing that can break positivity is a
prime fluctuation that is large *in the archimedean metric*, exactly where `A_d` is near-degenerate.

**Why this is the right quantity (GORZ confirms it).** Griffin–Ono–Rolen–Zagier's hyperbolicity for
`n ≥ N(d)` is precisely `ρ_d < 1` in the **archimedean-dominated** regime: for large shift the prime
correction is a contraction in the `A_d^{-1}` metric. So `ρ_d` is *literally* what GORZ bounds — which
confirms (R′)/`λ_min(S_d) ≥ −1` is the correct object and pins the open crux to the `sup` over the
**small-`n` / undamped window**, where `ρ_d → O(1)` and the prime near-resonances are not yet damped.

**Door-2 (re-sharpened).** The congruence and (R′) are linear algebra + GORZ ⟹ **BRIDGE**. The native
content is now the *non-artifactual* one: whether `sup_t λ_max(−S_d(t)) < 1` (equivalently
`sup_t ρ_d(t) < 1`) uniformly in `d`, a **single-orbit** quantity in which the archimedean-metric weighting
`A_d^{-1/2}(·)A_d^{-1/2}` couples the Γ-factor and the joint support-`≤ d` prime modes **irreducibly** — the
seam in one scale-invariant inequality. No positivity parent supplies it: GORZ reaches only the damped
large-`n` end; a moment/LP method controls the `t`-average of `ρ_d`, not its single-orbit sup; Baker /
integer-gap controls the near-resonant denominators *inside* `δH_d` (the support-`≤ d` modes), not the
metric coupling. **Conjecture (Wheeler, sharpened C5★ form).** `λ_min(S_d(t)) ≥ −1` (uniform in `d`,`t`) is
native: the `A_d^{-1}`-weighting of the joint primes is an infinite-base, joint-`σ_p`, metric statement
outside every single parent.

**Net correction.** The race is **multiplicative** (`ρ_d(t) < 1`), not additive (`‖δH_d‖ < λ_d`). There is
no `λ_d ↓ 0` rate-mismatch to fear — `λ_d` cancels under congruence; the whole question is whether the
archimedean-metric prime fluctuation `S_d(t)` is a contraction below the `−1` floor, uniformly in `d`. This
is the cleanest finite-free form of the no-margin wall so far, and the exact criterion (`λ_min(S_d) ≥ −1`)
is a genuine ⟺ for RH, not merely a sufficient condition.

**Updated probe (confirmatory, non-blocking).** Replace the additive probe (#321) by the **relative** one:
compute `ρ_d(t) = ‖A_d^{-1/2} δH_d(t) A_d^{-1/2}‖` (and `λ_min(S_d(t))`) for small `d` along the diagonal
orbit from the per-prime kernels `K_d(p)`. The decisive question: does `sup_t ρ_d` stay bounded `< 1`, or
does it approach `1` as `d` grows (the no-margin / matched signature)? `A_d` from the Hermite-root
Vandermonde. Archive under `computations/`.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Corrected the archimedean-gap reduction: additive → multiplicative (congruence).**
  The additive Weyl race `‖δH_d‖_op` vs `λ_d` is structurally too lossy (both are Hankels of the same power
  sums; the bound is vacuous even under RH; `λ_d ↓ 0` was a units artifact). Replaced by the **congruence**
  `H_d(t) = A_d^{1/2}(I+S_d(t))A_d^{1/2}`, `S_d = A_d^{-1/2}δH_d A_d^{-1/2}`: by Sylvester,
  **RH ⟺ `λ_min(S_d(t)) ≥ −1 ∀d,t`** (a genuine ⟺), with clean sufficient form `sup_t ρ_d(t) < 1`,
  `ρ_d = ‖S_d‖`. `λ_d` cancels; the ill-conditioning re-enters as the `A_d^{-1}` metric that amplifies the
  prime fluctuation along the near-degenerate directions = the no-margin wall, correctly stated. GORZ's
  large-`n` hyperbolicity IS `ρ_d < 1` in the archimedean-dominated regime ⟹ confirms `ρ_d`/`S_d` is the
  right object; open crux = `sup` over the small-`n` undamped window. Door-2: (R′) BRIDGE; native crux =
  uniform-in-`d` `λ_min(S_d) ≥ −1`, the `A_d^{-1}`-weighted joint-prime contraction (seam in one inequality).

## Root-displacement form: locating where the joint σ_p is essential (the Door-2 target) — Wheeler, 2026-06-19

Goal: turn the exact criterion `λ_min(S_d(t)) ≥ −1` into a statement about **root reality**, so the Door-2
native content (does a proof essentially need the joint `σ_p`?) becomes visible as a concrete mechanism.

**Rigorous (no model input).**
- **(RD1) `H_d(t) = Ṽ(t) Ṽ(t)^⊤` for the section's own roots.** The degree-`d` section is a real degree-`d`
  polynomial with `d` roots `ρ_1(t),…,ρ_d(t)` (counted with multiplicity); its power sums are
  `P_k(t) = Σ_l ρ_l(t)^k`, so `H_d(t) = (P_{i+j})_{0≤i,j<d} = Σ_l v(ρ_l) v(ρ_l)^⊤`, `v(ρ)=(1,ρ,…,ρ^{d-1})^⊤`.
  This is an identity, for every `t`.
- **(RD2) Positivity = reality (Hermite).** `H_d(t) ⪰ 0 ⟺` all `ρ_l(t)` real; `≻ 0 ⟺` real and distinct.
  A conjugate pair `ρ,ρ̄` contributes `2\,\mathrm{Re}\,v(ρ)v(ρ)^⊤ = 2(aa^⊤ − bb^⊤)` (`v(ρ)=a+ib`), an
  indefinite rank-`≤2` term, dropping the signature below `d` (structural lemma (i)). So
  **`λ_min(S_d(t)) ≥ −1 ⟺` the `d` roots of the section at height `t` are all real** ⟺ the corresponding
  `ζ`-zeros sit on the line. The **`−1` floor is hit exactly at `det H_d = 0`** = discriminant zero = a root
  collision = the hyperbolicity boundary (= 19b "zeros = degenerations"): the transition where a real
  double root is about to split into an off-axis conjugate pair.

**Structural / conjectural (one flagged external input).** Split `ρ_l(t) = r_l + ε_l(t)`: `r_l` the
archimedean (GORZ/Hermite-limit) root, `ε_l(t)` the prime-induced displacement. The displacement is, via the
section's prime coefficients (explicit formula), a **sum over all primes**
> `ε_l(t) = Σ_p K_d(r_l; p)\, c_p(t) + O(\text{2nd order})`,  `c_p(t)` the prime-`p` oscillation along the
> diagonal orbit (`c_p(t) ∼ p^{-1/2} e^{i t \log p}`-type),
with `K_d(r_l;p)` a per-prime kernel concentrated near the node `r_l`. **[FLAG — the precise `K_d(·;p)` is
the one input requiring verification, from the GORZ Taylor-coefficient asymptotic `γ(n+j)/γ(n)`; to be
checked against the source, not recalled. Everything below is conditional on its existence and the
first-order form.]**

**Where the joint `σ_p` is essential (the Door-2 mechanism, conjectural).** First-order root-reality is
preserved while no two displaced roots collide. A collision at node `r_l` needs `ε_l(t)` to grow to the
**Hermite node gap** `Δ_l = |r_{l+1}−r_l|`. Two facts then make the content joint:
1. **Edge sensitivity.** Hermite nodes are sparsest at the edge (`r_max ≍ √{2d}`, gap `Δ_edge ≍ d^{-1/6}`
   vs bulk `Δ_bulk ≍ d^{-1/2}`), but the displacement `ε_l` is *largest* at the edge (the section is least
   archimedean-damped there) — so collisions, hence any RH violation, **localize at the spectral edge**
   (recovering the earlier edge-localization, now in the correct relative metric: the edge is where
   `A_d^{-1/2}` amplifies most).
2. **A single prime cannot collide a pair; a joint near-resonance can.** Each `c_p(t)` is a bounded
   axis-mode oscillation; `|Σ_p K_d(r_l;p) c_p(t)|` reaches the gap `Δ_l` only when many prime phases
   `\{t \log p\}` align **constructively** at height `t` — i.e. a near-resonance
   `Σ_p a_p \log p ≈ 0` within the window, a **support-`≤ d` mixed-sign combination mode** (the objects of
   the structural lemma (ii)–(iii)). So whether `sup_t |ε_l(t)|` reaches `Δ_l` is a question about the
   **joint** Kronecker orbit of `\{t\log p\}_p`, weighted by the archimedean metric — not about any single
   prime.

> **Door-2 reading (conjectural, sharpened).** A proof of `λ_min(S_d(t)) ≥ −1` must bound the joint-prime
> root displacement against the archimedean node gaps, uniformly in `d`. The single-prime (axis-mode) bound
> is decoupling and BRIDGE (cf. §59/§60/19a); the **essential** step is the joint constructive-alignment
> (near-resonance) control at the edge — the support-`≤ d` combination modes, the field's apparatus. This is
> the precise place the joint `σ_p` would be load-bearing, i.e. the C5 candidate inside the carrier.

**Net.** The carrier's RH content is: *the joint-prime displacement of the edge roots never reaches the
archimedean node gap, uniformly in `d`* — a single-orbit, edge-localized, joint-`σ_p` near-resonance
statement. The reduction (RD1)(RD2) is rigorous BRIDGE; the displacement form needs the verified `K_d(·;p)`;
the uniform edge bound is the open C5 crux. This is the most concrete form of the Door-2 target yet, and it
says exactly what to verify next (the kernel) and where any RH violation must come from (edge collisions
driven by joint near-resonances).

## Log (cont.)
- 2026-06-19 (Wheeler) — **Root-displacement reformulation.** Rigorous: `H_d(t)=Ṽ(t)Ṽ(t)^⊤` (Gram of the
  section's own roots), so `λ_min(S_d)≥−1 ⟺` all `d` window-roots real ⟺ `ζ`-zeros on the line; the `−1`
  floor = `det H_d=0` = root collision = hyperbolicity boundary (19b). Structural (conditional on the GORZ
  kernel `K_d(·;p)`, FLAGGED for verification): root displacement `ε_l(t)=Σ_p K_d(r_l;p)c_p(t)`; RH
  violation ⟺ an edge root pair collides, which needs a **joint constructive near-resonance**
  `Σ_p a_p\log p≈0` (support-`≤d` mixed-sign mode) — a single prime can't do it. Locates the Door-2 native
  step precisely: the joint edge near-resonance bound, uniform in `d`. Edge-localization recovered in the
  correct relative metric (`A_d^{-1/2}` amplifies most at the sparsest-node edge).

## Framework correction: the carrier is Jensen-at-variable-base-point (Pólya–LP), GORZ is only its t=0 slice — Wheeler, 2026-06-19

**Verified against the source (arXiv:1902.07321, GORZ 2019), correcting earlier citations.** GORZ's Jensen
polynomials are taken **only at the symmetry point** `s=1/2` (central derivatives `Ξ^{(2n)}(0)`); their
all-orders asymptotic is **purely archimedean** (Γ-factor / functional equation), and **prime/arithmetic
data sit in the error term**, not the main term. So GORZ has **no height-`t` degree of freedom** and does
**not** expose a per-prime kernel. Earlier sections of this card cited "Pólya–Jensen/GORZ" for the *t-orbit*
RH-equivalence — that attribution is wrong; the correct justification is below, and the kernel `K_d(·;p)`
(previous section) is **not** a GORZ output.

**The rigorous RH-equivalence for the orbit (correct parent = Laguerre–Pólya translation invariance).**
- `Ξ(z) = ξ(½+iz)` is real entire, even, order `1`; **RH ⟺ `Ξ` has only real zeros ⟺ `Ξ ∈ LP`** (the
  Laguerre–Pólya class). *(classical.)*
- LP is **closed under real translation**: `Ξ ∈ LP ⟺ Ξ(t+·) ∈ LP` for every `t ∈ ℝ` (translation preserves
  "only real zeros" and the LP growth form). *(classical.)*
- Pólya–Schur/Jensen: a real entire function of order `< 2` is in LP ⟺ **all** its Jensen polynomials (of
  its Taylor coefficients) are hyperbolic. Applied to `Ξ(t+·)`, whose Taylor coefficients are
  `Ξ^{(j)}(t)/j!`:
> **RH ⟺ for every `t ∈ ℝ` and every `d ≥ 1`, `J_d(X;t) := Σ_{j=0}^{d} \binom{d}{j}\frac{Ξ^{(j)}(t)}{j!} X^j`
> is hyperbolic ⟺ `H_d(t) ⪰ 0` (its power-sum Hankel).**

This is exactly the card's single-orbit hyperbolicity target, now with a **rigorous** RH-equivalence — and
note the **depth shift `n` is not needed**: the base-point family at `n=0`, all `d`, all `t`, already
characterizes RH (the `n`-shift = Jensen of `Ξ^{(n)}`, redundant under "all `t`, all `d`"). This simplifies
the index set: **degree `d` × base point `t`**, no separate depth.

**Reconciliation — what GORZ does and does not give.**
- *Gives:* the archimedean model. At the center, GORZ's rescaled `J_{d,n}` → Hermite `H_d`; this is the
  source of the **archimedean Hankel `A_d`** (the smooth-part / Γ-factor Hankel) and the proof that the
  archimedean-dominated end is hyperbolic. `A_d` and `λ_d = λ_min(A_d) ↓ 0` (Vandermonde conditioning)
  stand as before.
- *Does not give:* the **`t`-orbit**. The prime oscillation lives in the base-point dependence of `Ξ^{(j)}(t)`
  (via the Hadamard product `Ξ(z) = Ξ(0)∏_ρ(1−z²/ρ²)` / explicit formula), which is precisely GORZ's
  **error term** at the center. So the split `H_d(t) = A_d + δH_d(t)` is via the **smooth/oscillatory
  (Hadamard) decomposition of `Ξ^{(j)}(t)`**, not via GORZ's `n`-asymptotic; and the per-prime kernel must be
  read off the Hadamard/explicit-formula expansion — **the next input to pin (and verify).**

**Door-2 (strengthened by the correction).** GORZ is the strongest positivity *parent* in play, and it
operates **only at `t=0` with the primes in its error term** — so it is **structurally blind to the
`t`-orbit** that carries the joint-`σ_p` content. This is positive evidence that any native (C5) theorem
must live in the **`t`-direction** (the Bohr/Kronecker base-point orbit), exactly the field's apparatus, and
that no GORZ-style archimedean method can reach it. The relative criterion `λ_min(S_d(t)) ≥ −1` and the
edge-collision/near-resonance mechanism of the previous two sections are unchanged; only their *parent
attribution* is corrected (Pólya–LP for the equivalence; GORZ for `A_d` only).

## Log (cont.)
- 2026-06-19 (Wheeler) — **Framework correction (verified vs arXiv:1902.07321).** GORZ is symmetry-point
  only (central derivatives), archimedean asymptotic, primes in the error ⟹ it does **not** justify the
  `t`-orbit RH-equivalence nor supply `K_d(·;p)`. Correct parent for the orbit = **Laguerre–Pólya
  translation invariance** + Pólya–Schur: **RH ⟺ `H_d(t) ⪰ 0` ∀d, ∀ base point `t`** (depth `n` not needed;
  index set collapses to `d × t`). GORZ now correctly scoped: supplies the archimedean `A_d` (Hermite limit,
  `t=0`) only; the `t`-orbit prime data = GORZ's error term = the Hadamard/explicit-formula expansion of
  `Ξ^{(j)}(t)` (the kernel to pin next). **Door-2 strengthened:** the strongest positivity parent (GORZ) is
  blind to the `t`-direction, so any C5 lives there. Earlier "Pólya–Jensen/GORZ" attributions for the orbit
  equivalence corrected to "Pólya–LP (equivalence) + GORZ (`A_d` only)."

## Grounding hypothesis (H) and the per-prime kernel from ζ'/ζ + Newton — Wheeler, 2026-06-19

Replaces the *posited* hypothesis (H) (axis-mode power sums) with a derivation, and pins the kernel
`K_d(·;p)` to the prime sum `ζ'/ζ`. (Modulo the standard explicit-formula convergence caveat on the
critical line — the prime series is taken in the smoothed/distributional sense; flagged.)

**Power sums are log-derivative coefficients (so they are additive over primes = axis-mode).** For the
degree-`d` section `J_d(X;t)` with roots `ρ_l(t)`, the power sums are the Laurent coefficients at `∞` of the
logarithmic derivative:
> `\frac{J_d'}{J_d}(X;t) = Σ_l \frac{1}{X-ρ_l} = Σ_{k≥0} P_k(t)\,X^{-k-1}`,  `P_k(t)=Σ_l ρ_l(t)^k`.
So `P_k` lives on the **additive** (`log`-derivative) side, where the Euler product linearizes. Concretely,
write `G(z) := \log Ξ(z)`; the prime part of `G` comes through `ζ'/ζ`:
> `\frac{ζ'}{ζ}(s) = -Σ_{p}Σ_{k≥1}(\log p)\,p^{-ks}`,  `s=½+iz`,
hence the prime part of the `i`-th derivative is
> `G^{(i)}_{\mathrm{prime}}(t) = -i\,Σ_{p}Σ_{k≥1}(\log p)(-ik\log p)^{\,i-1}\,p^{-k/2}\,e^{-ikt\log p}`.
Every term oscillates at frequency `k\log p` on the **single circle of prime `p`** (mode `k δ_p`,
`k≥1`) — i.e. **support 1**. Since `P_k(t)` is assembled from the `G^{(i)}` through the additive
log-derivative side (`J_d'/J_d`), its prime Fourier content is a **sum of single-prime contributions**:
> `\tilde P_k(t) = Σ_p u_{k,p}(θ_p(t))`,  `u_{k,p}` supported on `{a δ_p : a≥1}`,
which is **exactly hypothesis (H)** — now *derived* from `ζ'/ζ`'s additivity, not assumed. The per-prime
kernel is read off directly:
> **`K_d`: prime `p` enters `\tilde P_k` with amplitude `≍ (\log p)(k\log p)^{?}\,p^{-k/2}` at frequency
> `k\log p`; dominant harmonic `k=1`: `(\log p)^{?}\,p^{-1/2}e^{-it\log p}`** (the `p^{-1/2}` is the
> critical-line weight; the `(\log p)`-polynomial is the degree-dependent factor).

**Why the combination modes are genuine and arise only at det-level (consistency with the structural
lemma).** The *multiplicative* object `Ξ` itself **does** carry combination modes: `Ξ^{(j)} = Ξ·B_j(\{G^{(i)}\})`
(complete Bell polynomial, Faà di Bruno), a product of `≤ j` log-derivatives ⟹ support `≤ j`. But those are
the **coefficients** in the monomial basis, not the power sums. The power sums sit on the additive
log-derivative side and stay **axis-mode**; the combination modes re-enter only when the certificate
`det H_d` forms **products** `P_{k_1}\cdots P_{k_j}` (structural lemma (ii)–(iii)). So the two derivations
agree: additivity of `ζ'/ζ` ⟹ axis-mode `P_k`; nonlinearity of the PSD condition ⟹ support-`≤ d`
combination modes. The earlier worry (that Bell products might make `P_k` itself combination-mode) is
resolved — Bell acts on the *coefficient* basis, Newton sends it to the *power-sum* basis where the prime
sum is additive.

**Payoff.** (1) Hypothesis (H) is no longer an assumption — it follows from `ζ'/ζ = -Σ Λ(n)n^{-s}` plus
the log-derivative form of power sums. (2) The kernel `K_d(·;p)` is pinned to known data (prime
`p`, harmonic `k`, weight `(\log p)p^{-k/2}`), so the relative quantity `δH_d(t)` and `ρ_d(t)` are now
**explicitly computable** from primes (the runpod probe is fully specified). (3) The frequencies are exactly
the prime logs `\{k\log p\}` = the `𝕋^∞` Kronecker frequencies of the diagonal orbit `θ_p(t)=t\log p/2π` —
confirming the carrier lives natively on the multi-`q` flow.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Derived hypothesis (H) and pinned `K_d(·;p)` from `ζ'/ζ` + Newton.** Power sums
  `P_k(t)` = Laurent coefficients of `J_d'/J_d` ⟹ they sit on the additive log-derivative side, where
  `ζ'/ζ=-Σ_{p,k}(\log p)p^{-ks}` linearizes ⟹ `\tilde P_k(t)=Σ_p u_{k,p}(θ_p)` axis-mode (H **derived**, not
  posited). Per-prime kernel: amplitude `≍(\log p)p^{-k/2}` at frequency `k\log p`, dominant `k=1`. Combination
  modes are consistent: the multiplicative `Ξ^{(j)}=Ξ·B_j(\{G^{(i)}\})` (Bell) carries support-`≤j` modes in
  the *coefficient* basis, but Newton sends to the *power-sum* basis (additive/axis-mode); combination modes
  re-enter only via the nonlinear `det H_d` products (structural lemma ii–iii). Net: (H) grounded, kernel
  pinned to primes, `ρ_d(t)` now explicitly computable (probe fully specified). Caveat: explicit-formula
  convergence on the line (smoothed/distributional) — flagged.

## The spectral face of the seam: A_d is the σ-invariant (Haar) average, and it admits no clean σ-split — Wheeler, 2026-06-19

Synthesis with DeWitt's Ш repair (chat id=43) and Professor's Stieltjes weld (id=42). The three welds are
**one mechanism**: the Haar/time average is the unique σ-invariant projection, and it fails to give a clean
splitting in three categories.

**`A_d` is the Haar average.** By Weyl equidistribution the time-average over the diagonal orbit equals the
`𝕋^∞`-Haar average: `A_d = E_t[H_d(t)] = ∫_{𝕋^∞} H_d`. This is exactly the **σ-invariant projection** of the
power-sum Hankel (the zero-Fourier-mode part), and `δH_d(t) = H_d(t) − A_d` is the mean-zero (moving) part.
So the carrier's split `H_d = A_d + δH_d` **is** the σ-invariant ⊕ mean-zero decomposition — driven by the
*same Haar average* that DeWitt's R3 needed.

**The shared failure (three faces of one seam, #69/#71).** The Haar average exists but does not split cleanly:
- **C3 / cohomology (DeWitt, id=43).** The Haar projection `ε: 𝒪 → ℂ` is **not a ring retraction** (no
  σ-equivariant `𝒪 → ℂ`; a retraction = evaluation at a fixed torus point `ξ_p = p^{-1}ξ_p ⟹ ξ_p = 0 ∉ ℂ^*`).
  ⟹ `Ш` does not split const ⊕ arith.
- **G2 / Diophantine (Professor, id=42).** The Stieltjes `γ_n` (continuation) cannot be decoupled from the
  multiplier logs `{log p}`; the residual top-weight `c_N ∈ R_N` cannot be removed.
- **C5 / spectral (here).** `A_d` (the σ-invariant average) admits **no σ-equivariant metric-orthogonal
  complement carrying `δH_d`**: hyperbolicity is not decided by `A_d` alone nor `δH_d` alone but by the
  contraction `ρ_d = ‖A_d^{-1/2} δH_d A_d^{-1/2}‖ < 1` — the fluctuation measured **in the average's own
  metric**, and that metric `A_d^{-1}` is near-degenerate exactly where it weights `δH_d` most. The
  multiplicative (prime) `δH_d` and the archimedean (continuation) `A_d` are **inseparable** in the
  positivity question.

**One statement.** *The seam = the obstruction to a σ-equivariant splitting of (archimedean / σ-invariant) ⊕
(prime / mean-zero), because the dilations have no fixed point on `𝕋^∞` (no single Frobenius F₁).* It shows
up cohomologically as the non-retraction of `ε` (C3), Diophantine-ally as the non-decoupling of `γ_n` from
`{log p}` (G2), and spectrally as `ρ_d` coupling `δH_d` to `A_d^{-1}` (C5). The `S_d` weld is the **spectral
face** of the same no-fixed-point obstruction the other two threads found — strengthening that C5★ and the
seam are the same wall.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Spectral face of the seam (synthesis with DeWitt id=43, Professor id=42).**
  Identified `A_d = E_t[H_d(t)]` as the `𝕋^∞`-Haar/σ-invariant projection (Weyl) — the SAME Haar average
  DeWitt's Ш-retraction needed. The three welds are one mechanism: Haar average exists but no clean
  σ-equivariant split (no fixed point on `𝕋^∞`/no F₁). C3: `ε` not a ring retraction (DeWitt). G2: `γ_n` not
  decoupled from `{log p}` (Professor). C5: `ρ_d` couples `δH_d` to the average metric `A_d^{-1}` (here). Same
  seam (#69/#71), three categorical faces; banks C5★ ⇄ seam tighter.

## Probe result — the no-margin is ONE-SIDED, and `ρ_d<1` is the wrong form (corrects (R′)) — Wheeler, 2026-06-19

First run of `computations/2026-06-19-relative-rho-probe.py` (real `Ξ`, Jensen polynomials at base point
`t∈[0.5,60]`, 81 points, dps 35, `d=2..6`; `A_d=E_t[H_d(t)]`, `S_d=A_d^{-1/2}δH_d A_d^{-1/2}`):

| `d` | `sup_t ρ_d=‖S_d‖` | `min_t λ_min(I+S_d)` | `cond(A_d)` | reliable? |
|----|----|----|----|----|
| 2 | 47.9 | `1.20e-3` | `4.4e2` | ✓ |
| 3 | 43.4 | `1.79e-7` | `1.6e7` | ✓ |
| 4 | 76.3 | `6.16e-13` | `8.9e13` | ✓ |
| 5 | 76.0 | `3.05e-21` | `5.1e23` | precision-limited |
| 6 | 73.0 | `−3.5e-35` (noise) | `2.1e41` | **dps floor exceeded** |

**Finding 1 — `ρ_d<1` (the two-sided sufficient form) is FALSIFIED and must be dropped.** `ρ_d=‖S_d‖≈40–76≫1`
for every `d`, yet `λ_min(I+S_d)≥0` (positivity holds). So `‖S_d‖` is **dominated by a large positive
eigenvalue of `S_d`** — a direction in which the prime fluctuation, measured in the `A_d^{-1}` metric, is
huge but **adds to positivity** (makes an eigenvalue of `I+S_d` large). It does **not** threaten
hyperbolicity. The earlier "clean sufficient form `sup_t ρ_d<1`" is therefore vacuous/misleading and is
**withdrawn**; the operative criterion is the **one-sided** exact one, `λ_min(S_d(t))≥−1`. *The no-margin is
asymmetric:* the prime fluctuation may greatly **increase** some relative eigenvalues, but RH is exactly the
constraint that it never **decreases** one below the collision floor `−1`.

**Finding 2 — the relative margin closes super-exponentially (no-margin, quantified).** On the reliable rows
(`d≤4`), `min_t λ_min(I+S_d) > 0` (local hyperbolicity, as RH requires in the verified zero region) and
**closes like `≈ C/cond(A_d)`** (`1.2e-3, 1.8e-7, 6e-13` against `cond = 4.4e2, 1.6e7, 8.9e13`). Since
`cond(A_d)` grows super-exponentially (Vandermonde/Hankel ill-conditioning, Beckermann–Gautschi), the
relative hyperbolicity margin `↓ 0` super-exponentially in `d` — **the no-margin wall (#89–91) confirmed
numerically in the correct (scale-invariant) metric**, and the closing rate is the archimedean
conditioning rate. The `d=6` apparent negative (`−3.5e-35`) is numerical: `cond=2.1e41` exceeds the dps-35
floor (`λ_min` relative error `~cond·10^{-35}≫1`), so `d≥5` needs higher precision to certify the sign.

**Finding 3 — the worst margin is at the top of the `t`-range / mid-range, not `t=0`.** The minimizing `t`
sits at the largest sampled heights (`t≈49–60`), i.e. where more zeros and more prime oscillation are in the
window — consistent with the **edge / extreme-value localization** (the margin is hardest to hold where the
joint-prime fluctuation is largest). 

**Consequences for the thread.** (i) The exact criterion `λ_min(S_d(t))≥−1` is vindicated as the right object;
the two-sided `ρ_d` form is dropped. (ii) The no-margin is real and **one-sided** — RH = the prime
fluctuation never pushes a *negative* relative eigenvalue past `−1`, while it is free to push positive ones
arbitrarily high. (iii) The closing rate `≈1/cond(A_d)` ties the margin precisely to the archimedean
conditioning = `λ_d` of the additive picture, but now correctly inside the scale-invariant criterion. Next:
rerun at dps≥80 to certify `λ_min(I+S_d)>0` for `d=5,6,7` and pin the closing-rate exponent; then the live
C5 question is whether `min_t λ_min(I+S_d)` stays `≥0` **uniformly in `d`** (RH) — the one-sided no-margin.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Relative-`ρ_d` probe run (archived `computations/2026-06-19-relative-rho-probe.out`).**
  Real `Ξ`, base-point Jensen polys, `d=2..6`. **Falsifies the two-sided sufficient form `ρ_d=‖S_d‖<1`**
  (`ρ_d≈40–76≫1` always, yet `λ_min(I+S_d)≥0`): `‖S_d‖` is dominated by an irrelevant large *positive*
  eigenvalue; the no-margin is **one-sided** — operative criterion is `λ_min(S_d)≥−1`. **Confirms the
  no-margin quantitatively:** `min_t λ_min(I+S_d) ↓ 0` super-exponentially `≈C/cond(A_d)` (`1.2e-3,1.8e-7,
  6e-13` for `d=2,3,4`), staying `≥0` (RH-consistent in the verified region). Worst `t` at the top of the
  range (edge/extreme-value localization). `d=6` negative is dps-35 precision noise (`cond=2e41`). Two-sided
  `ρ_d` form withdrawn from the card; one-sided criterion stands. Next: dps≥80 rerun for `d=5,6,7`.

## The carrier's proven floor vs open crux (faithful restriction / Door-5) — Wheeler, 2026-06-19

Locating exactly what is proven inside the carrier `RH ⟺ H_d(t) ⪰ 0 ∀d,t` confirms it is a **faithful** RH
encoding (recovers known low-order results — unlike the RH-blind coboundary) and isolates the native crux.

- **`d=2` (base point):** `H_2(t) ⪰ 0 ⟺ 2P_2−P_1² ≥ 0 ⟺ Ξ'(t)²−Ξ(t)Ξ''(t) ≥ 0` — the **first Laguerre
  inequality**. Via the even Hadamard product, `L_1(Ξ)(t) = 2Ξ(t)²Σ_n (ρ_n²+t²)/(ρ_n²−t²)²`, manifestly
  `≥ 0` when the zeros `ρ_n` are real. Its **coefficient-level instance** (the **Turán inequalities** for
  the Taylor coefficients of `Ξ`) is proven **unconditionally** — Csordas–Norfolk–Varga 1986, *The Riemann
  hypothesis and the Turán inequalities*, Trans. AMS 296(2):521–541 (verified). *The pointwise-in-`t`
  unconditional status of `L_1(Ξ)(t) ≥ 0` I have not re-verified to a source this session — flagged; either
  way it is a known low-order instance, not the native content.*
- **`d ≤ 8` (center `t=0`):** hyperbolicity of the central Jensen polynomials — **proven, GORZ 2019**
  (arXiv:1902.07321), and a density-1 subset for every `d` via the Hermite asymptotic.
- **Uniform in `d` (all base points):** `Ξ ∈ LP` ⟺ **RH** — open.

**Reading.** The carrier reproduces the Laguerre/Turán floor (`d=2`) and the GORZ band (`d≤8`, center); both
are **archimedean-dominated / parent-provable (BRIDGE)**. The open content is the **uniform-in-`d`, all-`t`**
one-sided no-margin `λ_min(S_d(t)) ≥ −1` (probe: the margin closes `≈1/cond(A_d)` but stays `≥0`), where the
joint-prime fluctuation at the spectral edge must never cross the collision floor — the native (C5) crux.
This is the correct **Door-5** picture: faithful restriction to low order recovers Laguerre/Turán/GORZ; the
strict extension is the joint-`σ_p` uniform edge bound no archimedean parent reaches.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Mapped the carrier's proven floor (Door-5/faithful restriction).** `d=2` base-point
  = first Laguerre inequality (`L_1(Ξ)=2Ξ²Σ(ρ_n²+t²)/(ρ_n²−t²)²≥0` for real zeros); its coefficient-level
  Turán form proven unconditionally (CNV 1986, verified); pointwise-`t` unconditional status flagged
  unverified. `d≤8` center = GORZ (proven). Uniform-in-`d` = RH (open). Confirms the carrier is a FAITHFUL RH
  encoding (recovers Laguerre/Turán/GORZ at low order, BRIDGE) with the native crux = the uniform-in-`d`
  one-sided edge no-margin. Sources: CNV Trans. AMS 296 (1986); GORZ arXiv:1902.07321.

## Theorem M is the WITH-MARGIN model of the carrier — energy+sign-transfer template, and the ζ difference — Wheeler, 2026-06-19

Read the team's own preprint `publications/theorem-m/docs/preprint/main.tex` (Haufschild; Lean-verified,
zero sorry, 3 axioms). It is the *same kind of object* as this carrier, in the provable (with-margin) regime,
and it hands the carrier a concrete proof template.

**Theorem M (recap).** Critical Laguerre family `C_d(w) = ₁F₁(−d;½;w²/4d) = He_{2d}(w/√{2d})/He_{2d}(0)` (the
even Hermite family, degree `2d`). Its **moment deformation** `Ψ_d(w) = Σ_k (−1)^k (d^{\underline k} M_k /
d^k(2k)!) w^{2k} = E[C_d(√U·w)]`, `U∈(0,1]` compound-Poisson with **atom `p=P(U=1)=√(2/e)≈0.858`**. Decompose
`Ψ_d = p·C_d + ∫_{(0,1]}C_d(v·)dμ`, `μ≥0`, mass `1−p`. **Theorem:** all `2d` zeros of `Ψ_d` real & simple,
every `d` — **unconditional, formally verified.** Engine: **(i) energy lemma** `E:=C_d²+C_d'²`,
`E'(x)=(x/d)C_d'(x)²≥0` on `x≥0`, `E(0)=1` ⟹ `|C_d(c)|≥1` and **segment domination** `|C_d(vc)|≤|C_d(c)|`
(`0≤v≤1`) at each critical point `c`; **(ii) sign-transfer**: since `p>½`,
`|Ψ_d(c_m)−p C_d(c_m)| ≤ (1−p)|C_d(c_m)| < p|C_d(c_m)|` ⟹ `sgn Ψ_d(c_m)=sgn C_d(c_m)=(−1)^m` ⟹ `d` sign
changes ⟹ all zeros real.

**The connection.** My `A_d` is the Hankel of `He_{2d}`'s power sums — the **same even Hermite family** `C_d`.
My carrier `H_d(t)` is a deformation of `He_{2d}` by the *prime/explicit-formula* data (`δH_d(t)`), exactly
as `Ψ_d` deforms it by `M_k`. So **Theorem M and the carrier are deformations of one family**, and:
- The **energy lemma is a property of `C_d`=`He_{2d}` alone** (deformation-independent) — it is reusable for
  the carrier verbatim. Hyperbolicity-preservation of *any* deformation reduces to the **sign-transfer at
  `C_d`'s critical points `c_m`** (the Hermite-extremal heights).
- **Theorem M is the WITH-MARGIN instance:** its deformation is a **positive averaging** over rescalings
  `v∈(0,1]` (`μ≥0`) with atom `p=√(2/e)`, i.e. a **factor `p/(1−p)≈6` margin** (Remark sharp: the budget is
  endpoint-sharp only as `v→1`, but `p>½` is used with room). It is provable & formalizable precisely
  because the deformation is a positive measure with a dominant atom.

**The ζ difference (the crux, sharpened).** ζ's prime deformation `δH_d(t)` is **signed/oscillatory**
(mean-zero, both signs — the multiplicative wing) and, by the probe, has **NO margin** (`λ_min(I+S_d)↓0`).
So the carrier is the **signed, zero-margin** analogue of Theorem M:
> **RH ⟺ ζ's signed prime deformation still satisfies the Theorem-M sign-transfer** — `|δH_d-induced
> displacement of Ψ at c_m| < (atom)·|C_d(c_m)|` at every Hermite critical point, **uniformly in `d`, but at
> the marginal atom (zero `√(2/e)`-slack)**. Theorem M = positive μ, atom `>½`, factor-6 margin (proved).
> ζ = signed μ, atom marginal, no margin (RH).

The one-sided no-margin from the probe is exactly this: a *positive* (atom-like, `v<1`) part dominates and
helps; the *signed* residual is what must not break the sign-transfer. Theorem M proves the positive case
elementarily; the signed/zero-margin case is the C5/seam wall.

**Door-2 / research path.** This is the sharpest C5 template to date: the native crux = *control the signed
prime residual at the Hermite critical points `c_m` uniformly in `d`, at zero margin*, governed by the joint
near-resonance structure of the support-`≤d` modes (the field's apparatus); Theorem M shows the
positive-margin sibling is a parent (BRIDGE) result. Concrete next step: build the dictionary
"Jensen polynomial of `Ξ` at base point `t`" ⟷ "deformation of `C_d`," then test whether the prime residual
admits a *signed* Theorem-M bound `|∫C_d(v c_m)dμ_{prime,t}(v)| < (atom)|C_d(c_m)|`. **[Dictionary to nail:
the prime data is not literally a coefficientwise moment multiplier `M_k`; the precise map deformation↔orbit
is the bridge to make rigorous — flagged.]**

## Log (cont.)
- 2026-06-19 (Wheeler) — **Linked the carrier to Theorem M (team's Lean-verified preprint).** Both are
  deformations of the even Hermite family `He_{2d}=C_d`. Theorem M = the WITH-MARGIN case: positive averaging
  `Ψ_d=p C_d+∫C_d(v·)dμ`, atom `p=√(2/e)>½`, factor-6 margin ⟹ sign-transfer ⟹ hyperbolic, unconditional.
  Mechanism (energy lemma `E'=(x/d)C_d'²≥0` + sign-transfer) is `C_d`-only, reusable. The carrier = the
  **signed, zero-margin** analogue (prime `δH_d` is signed/oscillatory; probe: `λ_min↓0`). RH ⟺ ζ's signed
  prime deformation keeps the Theorem-M sign-transfer at the Hermite critical points, uniformly in `d`, at the
  marginal atom. Matches the probe's one-sided no-margin (positive part helps, signed residual is the threat).
  Door-2 crux = signed-residual sign-transfer bound, joint near-resonance; positive sibling is BRIDGE
  (Theorem M). Dictionary deformation↔base-point-orbit flagged to make rigorous.

## High-precision rerun (dps 100): λ_min>0 certified for d≤7 — Wheeler, 2026-06-19

`computations/2026-06-19-relative-rho-probe-hp.out` (dps 100, `d=2..7`, 61 base points):

| `d` | `min_t λ_min(I+S_d)` | `cond(A_d)` |
|----|----|----|
| 2 | `1.73e-3` | `3.0e2` |
| 3 | `2.45e-8` | `1.2e8` |
| 4 | `5.62e-13` | `1.1e14` |
| 5 | `1.85e-21` | `6.2e23` |
| 6 | `4.78e-38` (was `−3.5e-35` at dps 35) | `2.6e41` |
| 7 | `5.51e-32` | `2.7e37` (anomalous, see below) |

**Certified.** `λ_min(I+S_d) > 0` for **all `d=2..7`** — local hyperbolicity (RH-consistency) holds, and the
`d=6` apparent negative from the dps-35 run is confirmed to be **numerical noise** (`+4.78e-38` at dps 100,
where `cond=2.6e41` is well within the dps-100 floor). The relative margin closes super-exponentially,
consistent with `λ_min(I+S_d) ≈ C/cond(A_d)` (`d=2..6`). **The one-sided no-margin is now numerically solid
up to `d=7`.**

**Flagged anomaly (`d=7`):** `cond(A_7)=2.7e37 < cond(A_6)=2.6e41` (non-monotonic), and correspondingly
`λ_min(I+S_7) > λ_min(I+S_6)` (consistent with `λ_min≈C/cond`). Likely cause: the `t`-average `A_d=E_t[H_d]`
is **under-resolved** at `d=7` (NT=61 too coarse for the faster high-degree prime oscillations `e^{ikt log p}`,
`k≤2d−2=12`), so `A_7` is contaminated by incomplete averaging. Not fundamental — a finer `t`-grid (or longer
`t`-range / exact archimedean `A_d` from the Hermite roots rather than the empirical average) would fix it.
Does **not** affect the `λ_min>0` certification (sign is robust). Re-run with NT≥201 (runpod) to restore
monotone `cond(A_d)` and pin the closing exponent cleanly.

## Log (cont.)
- 2026-06-19 (Wheeler) — **dps-100 rerun: `λ_min(I+S_d)>0` certified for `d=2..7`** (the dps-35 `d=6`
  negative was noise → `+4.78e-38`). Relative margin closes super-exp `≈C/cond(A_d)`; one-sided no-margin
  numerically solid to `d=7`. Anomaly: `cond(A_7)<cond(A_6)` — under-resolved `t`-average at `d=7` (NT=61 too
  coarse for `k≤12` oscillations); fix with finer grid / exact Hermite `A_d`. Sign certification unaffected.

## My lane (per user directive / Professor's split): the sign-transfer ASSEMBLY for the prime deformation — Wheeler, 2026-06-19

Division of labor (chat id=58): Wheeler = single-orbit positivity (uniform-in-`d` `λ_min(S_d)≥−1`);
Professor = the per-prime kernel `K_d(r_l;p)` (Hadamard/explicit formula); DeWitt = the support-`≤d`
near-resonance / integer-gap bound on the modes of `δH_d`. This section builds the **assembly** that turns
their two inputs into the bounded-`d` native lemma, via the Theorem-M mechanism. It defines the **shared
target inequality.**

**The reduction (Theorem-M template, applied to the prime deformation).** Write the degree-`d` section at
base point `t` as `F_d(w;t) = C_d(w) + D_d(w;t)`, where `C_d = He_{2d}` (the archimedean reference, normalized
`C_d(0)=1`) and `D_d(·;t)` is the prime deformation (the `δH_d`-carrier in value form). Let `c_0<…<c_{d-1}`
be the nonnegative critical points of `C_d`. Two facts are **reused verbatim from Theorem M** (properties of
`C_d=He_{2d}` alone, deformation-independent):
- **Energy floor:** `|C_d(c_m)| ≥ 1` (`E=C_d²+C_d'²`, `E'=(x/d)C_d'²≥0`, `E(0)=1`).
- **Alternation:** `sgn C_d(c_m) = (−1)^m`, tail sign `(−1)^d`.

**Sign-transfer ⟹ hyperbolicity.** If at every Hermite critical point
> **(ST)** `|D_d(c_m;t)| < |C_d(c_m)|`   (sufficient: `|D_d(c_m;t)| < 1`, since `|C_d(c_m)|≥1`),
then `sgn F_d(c_m;t) = sgn C_d(c_m) = (−1)^m`: the prime deformation **cannot flip the archimedean critical
sign**. With the tail sign this gives `d` sign changes ⟹ (Theorem-M Step 3) all `2d` roots real. **So (ST),
uniform in `t` and `d`, ⟹ RH.**

**This is the matrix no-margin in value form.** `λ_min(I+S_d)↓0` (probe) ⟺ the section nears a double root
⟺ `F_d(c_m;t)≈0` at some `c_m` ⟺ `D_d(c_m;t) ≈ −C_d(c_m)` ⟺ `|D_d(c_m)|→|C_d(c_m)|`. So **(ST) is exactly the
one-sided no-margin**: the prime deformation approaches the archimedean critical value (cancellation) but,
under RH, never reaches it. The slack in (ST) is the relative margin the probe measured closing.

**The SHARED TARGET INEQUALITY (what the three lanes jointly need):**
> `sup_{t∈ℝ,\,0≤m<d} |D_d(c_m;t)| \;<\; \min_{0≤m<d}|C_d(c_m)|`, **uniformly in `d`.**
- **Professor's kernel** gives `D_d(c_m;t) = Σ_p Σ_k K_d(c_m;p,k)\,e^{-ikt\log p}` (the prime deformation
  evaluated at the Hermite critical points) — a support-`≤d` combination-mode sum.
- **DeWitt's near-resonance bound** controls `sup_t |Σ_p…e^{-ikt\log p}|` against the archimedean floor
  `|C_d(c_m)|≥1` (the integer-gap / Baker control of the support-`≤d` modes at the worst `t`).
- **My job (the assembly):** (ST) above + the energy floor (reused) + the count; plus the open analytic
  pieces below.

**Open / flagged (my lane).**
1. **Even vs general `t`.** Theorem M's count uses **evenness** (`Ψ_d` even). `F_d(·;t)` is even only at
   `t=0`; at general `t` the clean route is either (a) the matrix criterion `λ_min(S_d)≥−1` (even-free,
   robust — the fallback), or (b) a perturbation argument: if (ST) holds with enough slack, `F_d`'s critical
   points stay near `C_d`'s and the Rolle/alternation count survives. (b) is the Theorem-M-style route and is
   the cleaner one **if** the slack can be made uniform — but the no-margin says the slack vanishes, so the
   general-`t` count needs care. **This is the genuine architectural gap on my side.**
2. **Dictionary** `F_d(·;t) = C_d + D_d` with `C_d=He_{2d}`: requires the archimedean part of the base-point
   Jensen polynomial to be the (rescaled) Hermite uniformly in `t` — Professor's kernel lane supplies this.

**Status:** (ST) and the reduction are the **assembly**; the energy floor + alternation are **proved**
(Theorem M, reused). The bounded-`d` native lemma = (ST) verified via {Professor kernel} ∧ {DeWitt
near-resonance}, with my open piece = the general-`t` count (perturbation vs matrix fallback). Door-2: (ST)'s
*statement* is BRIDGE (Theorem-M template); the *uniform-in-`d` verification at zero margin* via joint
support-`≤d` near-resonance is the native (C5) content — the multiplicative side is RH-blind (Professor's
faces-orthogonality), so it must live here.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Accepted lane (user directive, split id=58): lead single-orbit positivity.** Built
  the **sign-transfer assembly**: `F_d(w;t)=C_d(w)+D_d(w;t)`, `C_d=He_{2d}`; reuse Theorem M's energy floor
  `|C_d(c_m)|≥1` and alternation; **(ST)** `|D_d(c_m;t)|<|C_d(c_m)|` ∀`m,t,d` ⟹ no critical-sign flip ⟹ RH.
  Showed (ST) = the matrix no-margin in value form (`λ_min↓0 ⟺ D_d(c_m)→−C_d(c_m)`). Defined the **shared
  target inequality** `sup_{t,m}|D_d(c_m;t)|<min_m|C_d(c_m)|` uniform in `d`, slotting Professor's kernel
  (`D_d` at `c_m`) and DeWitt's near-resonance bound (sup over `t`). My open piece: the **general-`t` count**
  (Theorem M's count uses evenness; need perturbation route or matrix fallback) + the `C_d=He_{2d}` dictionary
  (Professor's lane). Door-2: native content = uniform zero-margin verification via joint near-resonance.

## Resolving the general-t count: a quantitative C¹-perturbation lemma (even-free) — Wheeler, 2026-06-19

Closes my flagged architectural gap. Theorem M's sign-count uses evenness (valid only at `t=0`); the
following is **even-free**, works at every base point `t`, and reduces hyperbolicity to **two pointwise bounds
on the prime deformation `D` and its derivative `D'`** — exactly the inputs DeWitt's near-resonance lane can
deliver.

**Setup.** `C := C_d = He_{2d}` (monic, leading coeff `>0`), with critical points `x_1<…<x_{2d-1}` (the
simple real roots of `C'`). Define
- the **energy floor** `F_0 := min_i |C(x_i)| ≥ 1` (Theorem-M energy lemma, reused);
- the **curvature floor** `m_2 := min_i |C''(x_i)| > 0` (`x_i` simple roots of `C'`);
- the **curvature cap** `M_2 := max_i |C''(x_i)|`;
- the **min critical gap** `δ := min_i (x_{i+1}-x_i) > 0`;
- the **leading-coefficient margin** `a_{2d}` = leading coeff of `C`.
(For `He_{2d}` these are classical: `x_i ∈ (-\sqrt{4d},\sqrt{4d})`, `δ ≍ (2d)^{-1/6}` at the edge / `(2d)^{-1/2}`
in the bulk; exact `m_2,M_2,F_0` asymptotics are Professor's archimedean lane.)

**Lemma (general-`t` hyperbolicity by `C¹` perturbation).** Let `F = C + D` be a real polynomial of degree
`2d` with `\deg D ≤ 2d` and leading-coeff`(D)| < a_{2d}` (tail-sign preserved). If
> **(b)**  `\sup_{w}|D'(w)| \;<\; \tfrac12\,m_2\,δ`,   and
> **(a′)**  `\sup_{w}|D(w)| \;+\; \tfrac{M_2}{2}\Bigl(\tfrac{\sup|D'|}{m_2}\Bigr)^2 \;<\; F_0`,
then `F` is hyperbolic (all `2d` roots real). Uniform in `t,d` ⟹ **RH.**

*Proof.* **(i) `F'` hyperbolic, critical points near `x_i`.** Near `x_i`, `C'(w)=C''(x_i)(w-x_i)+O((w-x_i)^2)`,
so `|C'(x_i±ε)| ≥ m_2 ε` for `ε ≤ δ/2` (gaps keep the linear term dominant). By (b), `\sup|D'| < m_2 δ/2`, so
take `ε_* := \sup|D'|/m_2 < δ/2`: then `|C'(x_i±ε_*)| ≥ m_2 ε_* = \sup|D'| > |D'(x_i±ε_*)|`, so `C'` and
`F'=C'+D'` agree in sign at `x_i±ε_*`; since `C'` changes sign across `x_i`, IVT gives a root `x_i'` of `F'`
in `(x_i-ε_*,x_i+ε_*)`. The `2d-1` intervals are disjoint (`ε_*<δ/2`), giving `2d-1` real simple roots of
`F'` ⟹ `F'` hyperbolic and `|x_i'-x_i|<ε_*`. **(ii) Sign preserved at the `x_i'`.** Since `C'(x_i)=0`,
`|C(x_i')-C(x_i)| ≤ \tfrac12 M_2 (x_i'-x_i)^2 ≤ \tfrac12 M_2 ε_*^2`. Hence
`|F(x_i')-C(x_i)| ≤ |D(x_i')| + \tfrac12 M_2 ε_*^2 ≤ \sup|D| + \tfrac{M_2}{2}(\sup|D'|/m_2)^2 < F_0 ≤ |C(x_i)|`
by (a′), so `\sgn F(x_i') = \sgn C(x_i)`. **(iii) Count.** `C(x_i)` alternate in sign (interlacing of
`He_{2d}` with `He_{2d}'`), so `F(x_i')` alternate over the `2d-1` critical points of `F` ⟹ `2d-2` sign
changes between them; the preserved leading sign gives `F→+∞` at both tails ⟹ `2` outer roots. Total `2d`
real roots. ∎

**What this buys.**
- The **general-`t` gap is closed**: hyperbolicity at *every* base point follows from the two sup-bounds
  (a′),(b) on the prime deformation — no evenness needed. The matrix criterion `λ_min(S_d)≥−1` is no longer
  the only general-`t` route.
- **DeWitt's target sharpens:** bound **both** `\sup_t|D_d(\cdot;t)|` (against `F_0≥1`) **and**
  `\sup_t|D_d'(\cdot;t)|` (against `\tfrac12 m_2 δ`). The derivative `D_d'` brings down an extra frequency
  factor `k\log p` on each mode — still a support-`≤d` combination-mode sum, so within his near-resonance /
  integer-gap method, but the **`m_2 δ` floor is the demanding one** (it shrinks with `d`: `δ_edge≍(2d)^{-1/6}`
  and `m_2` from the Hermite curvature).
- **The no-margin, located precisely:** (a′) has a fixed floor `F_0≥1` (comfortable), but **(b) is the binding
  constraint** — `\tfrac12 m_2 δ` shrinks as `d→∞`, so the *derivative* bound is where the margin closes. RH ⟺
  the prime deformation's derivative `\sup_t|D_d'|` stays below the (shrinking) `m_2δ` floor uniformly in `d`.
  This refines the earlier "edge no-margin": it is a **slope** (`D'`) control at the edge, not a value control.

**Door-2.** The perturbation lemma is classical real analysis (quantitative Rolle/IVT) ⟹ **BRIDGE**; the
native content is the **uniform-in-`d` slope bound** `\sup_t|D_d'(c\text{-region};t)| < \tfrac12 m_2 δ`, a
joint support-`≤d` near-resonance statement at the spectral edge — the field's apparatus. The C5 crux is now
a *derivative* (slope) no-margin at the edge.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Closed the general-`t` count gap: even-free `C¹`-perturbation lemma.** `F=C+D`,
  `C=He_{2d}`; conditions **(b)** `sup|D'|<½ m_2 δ` (keeps `F'` hyperbolic, critical points shift `<δ/2`) and
  **(a′)** `sup|D|+½M_2(sup|D'|/m_2)²<F_0=min|C(x_i)|≥1` (keeps critical signs) ⟹ `F` hyperbolic, all `t`.
  Proof = quantitative Rolle/IVT (BRIDGE). Sharpens DeWitt's target to **both** `D` and `D'`; the binding
  constraint is **(b)** (the slope bound vs the shrinking `m_2δ` edge floor), relocating the no-margin to a
  **derivative/slope** control at the spectral edge. Door-2 native content = uniform-in-`d` slope bound.

## Localizing the perturbation lemma + correcting the edge-vs-bulk question — Wheeler, 2026-06-19

The lemma's condition (b) used a global `sup_w|D'|`, but the proof only reads `D'` in `δ_i/2`-neighborhoods of
the critical points `x_i`. Localizing gives the sharp form and exposes the binding critical point.

**Localized lemma (sharp).** With `δ_i := min(x_i-x_{i-1}, x_{i+1}-x_i)` (adjacent critical gap),
`κ_i := |C''(x_i)|` (local curvature), `M_i := max_{|w-x_i|≤δ_i/2}|C''|`, `F_i := |C(x_i)| ≥ 1`: if for **every**
`i`
> **(b_i)**  `\displaystyle \sup_{|w-x_i|≤δ_i/2}|D'(w)| \;<\; \tfrac12\,κ_i\,δ_i`,  and let `ε_i := \sup_{|w-x_i|≤δ_i/2}|D'|/κ_i < δ_i/2`,
> **(a_i)**  `|D(x_i')| + \tfrac12 M_i\,ε_i^2 \;<\; F_i`   (`x_i'` the root of `F'` in `(x_i-ε_i,x_i+ε_i)`),
then `F=C+D` is hyperbolic. *(Proof: the global proof applied interval-by-interval; each `(b_i)` yields one
real root `x_i'` of `F'` in its window, giving all `2d-1` ⟹ `F'` hyperbolic; each `(a_i)` preserves the
critical sign; the count is unchanged.)*

So **only the prime deformation near the Hermite critical points matters** — `D'` in the bulk away from the
`x_i` is irrelevant. The binding constraint is at the critical point minimizing the **barrier**
`β_i := \tfrac12 κ_i δ_i` (the slope room) relative to the local `\sup|D_d'|`.

**Where is the binding `i`? (corrects my earlier "edge localization.")** Honest re-examination: the barrier is
`β_i = \tfrac12|C''(x_i)|δ_i`. For `C=He_{2d}` (roots/critical points spread on `[-\sqrt{4d},\sqrt{4d}]`,
semicircle density — **densest at the center, sparsest at the edge**):
- **gaps** `δ_i`: **smallest in the bulk/center** (`≍ d^{-1/2}`), **largest at the edge** (`≍ d^{-1/6}`,
  Airy);
- **curvature** `κ_i=|C''(x_i)|` and the barrier height `≍ \max_{gap}|C'|`: `|C'|=2d|He_{2d-1}|` has peaks
  that **grow toward the edge** (Plancherel–Rotach), so `β_i` is plausibly **smallest in the bulk**.

⟹ **The binding critical point is plausibly the BULK (smallest-gap, center) one, NOT the edge.** This
*revises* my earlier "edge/extreme-value localization" claim — which was tied to the **operator norm** of
`δH_d` (the now-**withdrawn** two-sided `ρ_d`, dominated by top moments / extreme roots). The *slope/perturbation*
criterion is governed by the **smallest barrier**, a different quantity, plausibly bulk. **[Flag — the exact
`He_{2d}` asymptotics for `δ_i` and `β_i=\tfrac12κ_iδ_i`, hence the location and `d`-scaling of `min_i β_i`,
are Professor's archimedean lane; do not assume edge.]** The earlier edge claim stands only for the withdrawn
operator-norm picture and should not be carried into the slope analysis.

**Sharpened target (replaces the global one).** RH ⟸ for all `d`,
> `\displaystyle \max_i \frac{\sup_{|w-x_i|≤δ_i/2}|D_d'(w;t)|}{\tfrac12 κ_i δ_i} < 1`, uniformly in `t`,
i.e. the prime-deformation slope, **measured against the local Hermite barrier at each critical point**,
never reaches `1`. This is the no-margin in its sharpest (local-slope) form; the binding `i` (bulk vs edge)
is set by `min_i β_i`, an archimedean computation.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Localized the perturbation lemma; corrected edge→bulk.** (b),(a′) replaced by
  per-critical-point `(b_i)`: `sup_{|w-x_i|≤δ_i/2}|D'|<½κ_iδ_i`, `(a_i)` value bound — only `D'` NEAR the
  Hermite critical points matters. Binding `i` = min barrier `β_i=½κ_iδ_i`. Honest revision: for `He_{2d}`
  gaps are smallest in the BULK (`≍d^{-1/2}`) not the edge (`≍d^{-1/6}`), and barrier peaks grow toward the
  edge, so the binding critical point is plausibly **bulk**, not edge — my earlier "edge localization" was for
  the WITHDRAWN operator-norm `ρ_d`, not the slope criterion, and is not carried over. Sharp target:
  `max_i sup_t|D_d'|_{loc}/(½κ_iδ_i)<1` uniform in `d`. Exact `β_i` scaling flagged for Professor.

## CORRECTION: the geometric barrier β is O(1); the Hankel no-margin overstates the difficulty — Wheeler, 2026-06-19

A computation of the Hermite barrier forces a correction to the "super-exponential no-margin" reading of the
probe. The barrier does **not** shrink with `d`; the Hankel `λ_min↓0` is a representation (conditioning)
artifact.

**The barrier, computed (classical, on my lane).** In Theorem M's critical scaling, `C_d=He_{2d}(w/√{2d})/He_{2d}(0)`
solves `C_d''=(w/2d)C_d'−C_d`. At a critical point `c_m` (`C_d'(c_m)=0`):
> `C_d''(c_m) = −C_d(c_m)` ⟹ **`κ_m := |C_d''(c_m)| = |C_d(c_m)| ≥ 1`** (energy floor).
The critical points `c_m` are the roots of `C_d'`, at **unit mean density** in this scaling (the defining
property of the critical scaling), and Hermite roots/critical points **do not cluster** (no anomalously small
gaps — they are eigenvalues of a Jacobi matrix, gaps `≍` local density), so the min critical gap
`δ_min ≍ O(1)`, bounded below uniformly in `d`. Therefore
> **`β_min = ½ min_m κ_m δ_m ≍ O(1)`** — the geometric hyperbolicity barrier is bounded below, independent of `d`.
*(Exact constant is classical Hermite asymptotics; the point is the `d`-uniform lower bound, not the value.)*

**Consequence — the probe's `λ_min↓0` is a conditioning artifact, not a closing geometric margin.** A
degree-`2d` polynomial with `2d` *well-separated* real roots **still** has a power-sum Hankel with
`cond ~ e^{cd}` (Vandermonde/Beckermann–Gautschi) — ill-conditioning is generic to the representation, not a
sign of near-collision. The relative `λ_min(I+S_d)=λ_min(A_d^{-1/2}H_d A_d^{-1/2})` is the geometric margin
**seen through** that ill-conditioned metric, so its super-exponential decay (`1.2e-3,1.8e-7,6e-13,…`)
reflects `cond(A_d)`, **not** the geometric distance to a root collision. The true geometric margin is the
`O(1)` barrier `β`. *(Sanity check: with no prime deformation `D_d=0`, `H_d=A_d`, `λ_min(I+S)=1` — the closing
is entirely the interaction of `δH_d` with the conditioning, not the archimedean geometry.)*

**The corrected, cleaner criterion (replaces the "matched-rate" worry).** By the localized perturbation
lemma, with `β_min ≍ O(1)`:
> **RH ⟸ `sup_{t}\,|D_d'(w;t)|` (for `w` near the Hermite critical points) `< ½β_min ≍ O(1)`, uniformly in `d`.**
The threshold is an **`O(1)` constant**, not a super-exponentially shrinking quantity. So the live C5 question
is the **honest** one: does the prime-deformation slope `sup_t|D_d'|_{loc}` stay **bounded (O(1)) as `d→∞`**,
or grow? The Hankel probe **did not** measure this (it conflated it with conditioning). A clean geometric
probe is needed — measure `D_d'` near the critical points directly, in the critical scaling.

**Honest status of the earlier probe claims.** The dps-100 probe still **certifies RH-consistency**
(`λ_min(I+S_d)≥0` for `d≤7`) — that stands. But its "super-exponential no-margin, matched-rate" narrative is
**withdrawn**: that closing was Vandermonde conditioning. The genuine margin is `O(1)`; the genuine open
question is the **uniform-in-`d` boundedness of the prime-deformation slope** against an `O(1)` barrier — a
materially more hopeful (and more correctly posed) target.

## Log (cont.)
- 2026-06-19 (Wheeler) — **CORRECTION: geometric barrier `β≍O(1)`; probe no-margin was conditioning.**
  Computed (Theorem-M ODE) `κ_m=|C_d''(c_m)|=|C_d(c_m)|≥1`; critical points at unit mean density (no Hermite
  clustering) ⟹ `δ_min≍O(1)` ⟹ `β_min=½κ_mδ_m≍O(1)`, `d`-uniform. Hence the probe's super-exp `λ_min↓0` is
  Vandermonde/Hankel **conditioning** (`cond(A_d)~e^{cd}`, generic to any growing-degree hyperbolic family —
  `D_d=0` gives `λ_min=1`), **not** a geometric near-collision. **Withdrew** the "matched-rate / closing
  no-margin" narrative; the RH-consistency certification (`λ_min≥0`, `d≤7`) stands. Corrected criterion:
  **RH ⟸ sup_t|D_d'|_loc < ½β_min ≍ O(1) uniform in `d`** — an O(1) slope-boundedness question, not a
  shrinking race. Need a geometric (not Hankel) probe of `sup_t|D_d'|_loc`. Materially more hopeful target.

## Validation against support-extraction-log + tempering the O(1)-barrier optimism — Wheeler, 2026-06-19

Per user directive, checked this thread against `docs/support-extraction-log.md`. **Not redundant** — the
thread *advances* mined seeds — but a prior PROVED result tempers the last section's optimism.

**Prior seeds this thread advances (credited).**
- **SEED-AB (log §1410–1421):** the finite-free convolution flow `Ξ_d^{(P)}=H_d⊞_d K_d(p_1)⊞_d…`, RH =
  stability of the finite-free CLT fixed point under arithmetic cumulant drift. *(This card's stated source.)*
- **Attack 5 (log §1396–1405):** `σ_p` is a Pólya–Schur multiplier; RH ⟺ `ξ` an LP-limit (prime-deformed
  Hermite). *(My base-point/LP-translation framing sharpens this — and shows the depth shift `n` is
  redundant.)*
- **G5/Face A (log §642–671):** Hankel/Hermite face, `κ₋`=Hankel-negative-eigenvalue count
  (`secularHankel_posSemidef` Lean), RH ⟺ uniform total positivity ⟺ `Ξ∈LP` ⟺ `Λ=0`. GORZ (asymptotic TP_d)
  and CNV/Turán **already cited there**.
- **New beyond the log:** the exact criterion `λ_min(S_d(t))≥−1` (congruence form); the Theorem-M with-margin
  model (postdates the log); the `C¹`-perturbation lemma + localization; the `β`-barrier computation.

**The tempering (corrects the previous section's "materially more hopeful").** Log **§664–666 Thm 7**
(PROVED): an off-line zero at distance `δ` breaks total positivity only at an order that **grows as `δ→0`
with vanishing magnitude** — "**no fixed-order TP test certifies RH**"; and **§668–671**: the CNV/Turán margin
is **"scale-free, monotonically ↓ — the no-margin trend"**; "RH is the **uniform completion**." So the
no-margin trend is **prior-established and real** — I must not claim it away.

**Reconciliation (honest).** Both stand, and they fit:
- The **Hankel conditioning** `λ_min(I+S_d)~1/cond(A_d)~e^{-cd}` (my probe) **is** a representation artifact —
  generic to any growing-degree family. ✓ (unchanged).
- The **geometric archimedean barrier** `β=½κ_mδ_m≍O(1)` is bounded below. ✓ (unchanged).
- **But the genuine no-margin (Thm 7 / CNV) is real** — so it must live **neither** in `β` (O(1)) **nor** in
  pure conditioning, but in the **`d`-growth of the prime-deformation slope** `sup_t|D_d'|_{loc}` against the
  `O(1)` barrier. The prior "margin ↓ / no fixed-order test" then **predicts** `sup_t|D_d'|_{loc} ↑` with `d`,
  so the true margin `½β − sup_t|D_d'|_{loc} ↓` (possibly `→0` = the no-margin). **Revised statement:** the
  target threshold is `O(1)` (a correct simplification of the Hankel artifact), but whether it is *met* is
  exactly the prior open no-margin — the difficulty is **relocated, not removed**, to the uniform-in-`d`
  boundedness of `sup_t|D_d'|_{loc}`, consistent with Thm 7. The "more hopeful" phrasing is **withdrawn**;
  the correct gain is a **cleaner, correctly-scaled target**, not an easier problem.

**Net of validation.** No duplication; the thread is the live deepening of SEED-AB/Attack-5/Face-A. The one
correction: re-anchor the O(1)-barrier result to the prior PROVED no-margin (Thm 7, CNV §664–671) — the
no-margin is real and now precisely located in `sup_t|D_d'|_{loc}`'s `d`-growth.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Validated thread vs support-extraction-log (user directive).** Not redundant:
  advances SEED-AB (§1410, finite-free flow), Attack 5 (§1396, σ_p Pólya–Schur / LP-limit), G5/Face-A
  (§642–671, Hankel/Hermite/`κ₋`/`Λ=0`); GORZ+CNV already cited there. New: exact `λ_min(S_d)≥−1`, Theorem-M
  model, perturbation lemma, `β`-barrier. **Tempered** the prior section: log §664–666 Thm 7 (no fixed-order
  TP test certifies RH; margin~δ, cost~order↑) + §670 (CNV margin monotonically ↓) are PRIOR-PROVED — the
  no-margin trend is real. Reconciliation: Hankel `λ_min↓` = artifact (✓), `β≍O(1)` (✓), but the genuine
  no-margin relocates to **`sup_t|D_d'|_{loc}` growing with `d`** vs the O(1) barrier. "More hopeful"
  withdrawn → "cleaner correctly-scaled target"; difficulty relocated, not removed.

## Integration: Professor's kernel is DELIVERED (the flag is cleared) + the σ=½ divergence — Wheeler, 2026-06-19

Standing-order search of `2-fully-proven` found that the per-prime kernel I had **flagged** as
"Professor's lane, awaiting verification" is already **delivered and proven**:
`2-fully-proven/c5-jensen-prime-kernel.md` (BRIDGE; Lean anchor `C5JensenPrimeKernel.lean`). Clearing the flag
and folding it in.

**Kernel (Professor, delivered).** At the Hermite critical points `c_m` (my Theorem-M evaluation points):
> `D_d(c_m;t) = Σ_{p,k} K_d(c_m;p,k)\,e^{−ikt\log p}`, `K_d(c_m;p,k) = \frac{p^{−k/2}}{k}\,Q(k\log p;c_m)`,
> `Q(x;c_m)=Σ_{i=1}^{2d}(−ix)^i B_i(c_m)`, a degree-`≤2d` polynomial in the frequency with **archimedean
> (Hermite) coefficients** `B_i(c_m)`; `c_p=p^{−1/2}`.
This is exactly the input my shared target `sup_{t,m}|D_d(c_m;t)|<min_m|C_d(c_m)|` needed — **the dictionary
flag (deformation↔orbit) is discharged for the value.** My earlier "kernel flagged for verification" notes
are superseded by this card.

**Professor's `σ=½` divergence (proved) — reinforces and sharpens my tempering.** The deformation has **no
absolute and no `L²` bound** at the critical line: `|K_d(c_m;p,1)|≍p^{−1/2}(\log p)^{≤2d}` and
`Σ_p p^{−1/2}(\log p)^a=Σ_p p^{−1}(\log p)^a=∞`. So `sup_t|D_d(c_m;t)|` is **intrinsically a
cancellation/large-values quantity** — never a triangle/`L²` bound. This is the value-level form of exactly
what my tempering note concluded (the no-margin is real, control = phase cancellation), and it is the prior
`support-extraction-log` Thm 7 ("no fixed-order test") in kernel form.

**My lane's addition on top of the value target — the SLOPE.** Professor's §6 gives the *value* `D_d(c_m;t)`
(the even/`t=0` sign-transfer route). My `C¹`-perturbation lemma shows the **general-`t`** count needs, in
addition, the **slope** `D_d'(c_m\text{-region};t)` controlled (condition (b), `<½κδ`). By the kernel, the
slope carries **one extra frequency factor** per mode:
> `D_d'(\cdot;t)` has amplitudes `≍ p^{−k/2}(\log p)^{≤2d}\cdot(k\log p)` — **more divergent** than the value.
So the slope is the **more binding** large-values/cancellation quantity (confirming my "binding is the slope"
finding), and it is the genuinely-general-`t` requirement Professor's value target does not yet cover. The
two together (value (a′) + slope (b)) are the full bounded-`d` hyperbolicity input.

**Edge vs bulk — reconcile with Professor's §4.** Professor's §4 phrases the collision at the **edge**
(`Δ_{edge}≍d^{−1/6}`). My localized-barrier analysis argues the binding critical point (min barrier
`β_i=½κ_iδ_i`) is plausibly the **bulk** (smallest gap `≍d^{−1/2}`), since the edge has the *largest* gaps.
**Both can hold**: the kernel amplitude `p^{−1/2}(\log p)^{≤2d}` is `c_m`-dependent through `Q(\cdot;c_m)`, so
the binding `c_m` is set by `min_m [β_m^{-1}·(\text{large-values of } Σ_p…Q(\cdot;c_m))]`, not by the gap
alone — an archimedean × arithmetic competition. **Flag for Professor:** recompute the binding `c_m` using the
*ratio* `(\text{kernel large-values at }c_m)/β_m`, not the gap `Δ` alone; my bulk argument used only the
geometric barrier, his edge used only the gap. The true binding `c_m` needs both.

**Net.** The three lanes now connect into one assembly: Professor's kernel (value, proved divergence) + my
perturbation lemma (adds slope, general-`t`) + DeWitt's near-resonance (the large-values bound). The C5 crux
is the single, sharply-posed question (Professor §6): is `sup_t` of the (regularized, divergent-amplitude)
Bohr sum controlled by a **parent large-values method (Halász/Montgomery ⟹ BRIDGE)** or does it **need the
support-`≤2d` near-resonance (Baker/integer-gap ⟹ native C5)**? — for both the value and (harder) the slope.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Integrated Professor's delivered kernel (`2-fully-proven/c5-jensen-prime-kernel.md`,
  found via the standing-order search).** Flag cleared: `D_d(c_m;t)=Σ_{p,k}(p^{−k/2}/k)Q(k\log p;c_m)e^{−ikt\log p}`,
  `Q` degree-`≤2d` in the frequency with archimedean coeffs; feeds my shared target exactly. Folded in
  Professor's **proved `σ=½` divergence** (no absolute/`L²` bound ⟹ cancellation/large-values only) — matches
  my tempering and the prior Thm 7. **My addition:** the general-`t` count needs the **slope** `D_d'` too,
  which the kernel shows is *more* divergent (extra `k\log p` per mode) ⟹ the slope is the binding quantity.
  **Reconciled edge(Professor §4)/bulk(my localization):** binding `c_m` is set by (kernel large-values)/`β_m`,
  not the gap alone — flagged for Professor to recompute. Assembly now spans all three lanes; C5 crux =
  Professor §6's large-values-vs-near-resonance dividing line, for value and slope.

## Answer to the S_d-normalization decision (DeWitt §5 of c5-near-resonance-large-values) — Wheeler, 2026-06-19

DeWitt's card poses the decisive crux to me: does `S_d=A_d^{-1/2}δH_d A_d^{-1/2}` have a **bounded** sup
(integer-gap lane closes C5) or a **large-values** sup (resonance-method needed)? Answer, with a sharpening.

**(1) The two-sided sup IS large-values (confirms DeWitt §2).** `A_d^{-1/2}` is **`t`-independent**, so it
cannot uniformly damp a `t`-dependent spike — at a Bondarenko–Seip resonance `t*` where the prime phases
align, `δH_d(t*)` spikes and so does `S_d(t*)`. Indeed my probe found `sup_t ρ_d=‖S_d‖ ≍ 40–76 ≫ 1`. So
`sup_t‖S_d‖` is large-values; the first horn (archimedean damping of the two-sided norm) is **false**.

**(2) But that is the WRONG quantity — the RH-bearing one is ONE-SIDED.** RH ⟺ `λ_min(S_d(t)) ≥ −1`, i.e. the
**negative** extreme `λ_max(−S_d(t))`, not `‖S_d‖=max(|λ_max|,|λ_min|)`. My probe (dps-100, `d≤7`,
`t∈[0.5,60]`): `‖S_d‖` is large (40–76) **yet** `λ_min(I+S_d)≥0` throughout — i.e. the large-values live in
the **positive** eigendirection (which *helps* positivity), while the RH-bearing negative direction stays
bounded below `−1`. So **`sup_t‖S_d‖` being large-values does NOT imply the RH-bearing
`sup_tλ_max(−S_d)` is large-values.** DeWitt's §2 (Bondarenko–Seip on the axis-mode sum) bounds the wrong
(two-sided / positive-dominated) quantity.

**(3) Refined decision question (the sharp form of §5).** The crux is therefore:
> Is `\sup_t λ_max(−S_d(t))` (the **negative** spectral extreme) large-values, or bounded?
A targeted probe (measure `λ_max(−S_d)` at the resonance `t*`, not just `‖S_d‖`) decides it. The probe data
so far says **bounded** (`λ_min(I+S)≥0`, no approach to `−1` even where `‖S‖` spikes), but `t≤60`,`d≤7` is far
from the large-values regime — not decisive.

**(4) Conjecture (Wheeler) — the resonance is positive-direction.** At a full phase-alignment `t*`, the
coherent prime contribution to the Hankel `δH_d(t*)=(\tilde P_{i+j}(t*))` plausibly concentrates in a
**moment-Hankel-like (PSD) direction** (coherent contributions to power sums behave like moments of a
positive measure), so the resonance spike adds to `λ_max(S_d)` (positive) and **leaves `λ_min` controlled**.
If so, the **RH-bearing negative direction is the mean-zero / oscillatory residual** — exactly the object the
integer-gap/variance lane controls — which would **reverse** DeWitt's §3 verdict ("integer-gap lands on the
RH-blind half"): after the one-sided split, the integer-gap-controlled residual may be the RH-bearing half.
*(Conjecture — the PSD-resonance mechanism is not proved; the empirical bounded-`λ_min` is solid only for
`d≤7`,`t≤60`. The decisive test is §3's targeted probe + a structural proof that the aligned `δH_d(t*)` is
asymptotically PSD.)*

**Net for the decision.** Neither clean horn: `A_d^{-1/2}` does **not** bound the two-sided sup (it's
large-values), **but** the RH content is the one-sided negative extreme, which the data and the
PSD-resonance conjecture suggest **is** bounded / variance-controlled. So C5★ may be an **integer-gap theorem
after the one-sided split** — contingent on proving the resonance is positive-direction. This is the sharp,
testable next step, and it relocates the win/lose line from "sup bounded?" to "is the resonance spike
sign-definite (PSD)?".

## Log (cont.)
- 2026-06-19 (Wheeler) — **Answered DeWitt's §5 `S_d`-normalization decision.** (1) `A_d^{-1/2}` is
  `t`-independent ⟹ the two-sided `sup_t‖S_d‖` is large-values (confirms §2; probe `ρ_d~40–76`). (2) But the
  RH-bearing quantity is the **one-sided** `λ_min(S_d)≥−1`, and the probe shows the large-values live in the
  **positive** direction (`‖S‖` large yet `λ_min(I+S)≥0`) — so two-sided-large-values ⇏ RH-quantity
  large-values. (3) Sharp question: is `sup_tλ_max(−S_d)` (negative extreme) large-values or bounded? (4)
  **Conjecture:** the resonance spike is positive-direction (aligned `δH_d(t*)` ≈ moment-Hankel/PSD), so it
  doesn't threaten `λ_min`; the RH-bearing negative residual may be variance/integer-gap-controlled —
  potentially **reversing** §3 (integer-gap → RH-bearing half). Decisive test: probe `λ_max(−S_d)` at
  resonance `t*` + prove aligned `δH_d` is asymptotically PSD. Win/lose line moves from "sup bounded?" to
  "resonance sign-definite?".

## The decoupling: prime large-values (large |ζ|) ≠ the RH-bearing collision regime (small |ζ|) — Wheeler, 2026-06-19

A structural reason the PSD-resonance conjecture should hold — and a reframe of the Door-2 win/lose line.

**Two distinct `t`-regimes.**
- **Prime-resonance large-values (DeWitt §2, Bondarenko–Seip):** occur where the prime sum
  `Σ_p p^{-1/2}\cos(t\log p+\dots)` aligns large-**positive**, i.e. at large `\log|ζ(½+it)|` ⟹ **large `|ζ|`**.
  Large `|ζ|` means `t` is **far from any zero** (`ζ` vanishes at zeros). There the nearby zeros are at normal
  spacing, the Jensen section `J_d(\cdot;t)` is **robustly hyperbolic** (roots well-spread), so the prime
  deformation has spread the roots **outward**: `H_d(t)⪰A_d`, `δH_d(t)⪰0` — the **positive** eigendirection.
  These large-values bump `λ_max(S_d)` (giving `ρ_d~40–76`) and are **harmless** to `λ_min`.
- **RH-bearing collision regime:** `λ_min(S_d(t))→−1` ⟺ two section roots collide ⟺ a root pair is about to
  leave the real axis ⟺ an off-line zero of `Ξ`. This happens **near a zero** of `ζ` (small `|ζ|`), where the
  section is near-degenerate — **not** at a prime large-value. (Under RH/GUE, zeros repel and stay on the
  line, so no collision: `λ_min≥0`. A violation is an off-line zero, a small-`|ζ|` event.)

**Consequence — the prime large-values are the WRONG extremal problem for RH.** The Bondarenko–Seip /
resonance-method control of `\max_t|ζ|` bounds the **large-`|ζ|`, far-from-zero, positive** direction — which
does not threaten hyperbolicity. The RH-bearing question is the **section's behavior near its own
near-degeneracies (small `|ζ|`, near zeros)** — a **local** question about zero spacing / off-line excursions,
not a large-values-of-`ζ` bound. This **decouples** DeWitt's §2 (large-values, harmless) from the RH crux,
and supports the PSD-resonance conjecture: the norm-maximizing resonance spreads roots (`δH_d⪰0`), so it
cannot drive `λ_min` below `−1`.

**Door-2 reframe (sharper win/lose).** The C5 crux is therefore **not** "bound the prime large-values"
(that's the harmless positive direction, and it's a parent large-values estimate ⟹ would be BRIDGE *if it
were the question*). It is "control the section near its near-collisions, uniformly in `d`" — the **negative**
eigendirection of `S_d` in the small-`|ζ|` regime. Whether *that* is a parent estimate or needs the joint
near-resonance is the real Door-2 line, and it is a **different, more local** object than `\max|ζ|`.

**Testable prediction (decisive).** If the decoupling holds, then in the probe **`argmax_t ‖S_d(t)‖` and
`argmin_t λ_min(I+S_d(t))` sit at DIFFERENT `t`** (the former at large `|ζ|`/far from zeros, the latter near a
zero). Equivalently: at the norm-maximizing `t*`, `δH_d(t*)⪰0` (PSD, all eigenvalues `≥0`). A targeted probe
(report both argmax/argmin `t`, and the signature of `δH_d` at the `‖S‖`-max `t`) decides it directly.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Decoupling: prime large-values ≠ RH-bearing collision regime.** Bondarenko–Seip
  large-values are at large `|ζ|` (far from zeros) ⟹ section robustly hyperbolic, `δH_d⪰0` (positive
  direction, harmless, drives `ρ_d`). The RH-bearing collision (`λ_min→−1` = off-line zero) is a **small-`|ζ|`
  / near-zero** event — a different `t`-regime. So DeWitt's §2 large-values bound the WRONG (positive)
  direction; the C5 crux is the **local near-collision** control (negative direction), not `\max|ζ|`.
  Supports the PSD-resonance conjecture. Decisive test: `argmax_t‖S‖` vs `argmin_tλ_min` should differ, and
  `δH_d`⪰0 at the `‖S‖`-max `t`. Probe queued.

## Pre-registered interpretation of the decoupling probe — Wheeler, 2026-06-19

To keep the next step decisive (not post-hoc), fixing in advance what each outcome of
`computations/2026-06-19-decoupling-probe.py` means for C5. The probe reports, per `d`: `argmax_t‖S_d‖` and
`argmin_t λ_min(I+S_d)` (with `|ζ|` at each), and the eigenvalue signature of `δH_d` at the `‖S‖`-max `t`.

- **Outcome A (decoupling confirmed):** the two `t`'s differ — `argmax‖S‖` at large `|ζ|` (far from zeros),
  `argmin λ_min` at small `|ζ|` (near a zero) — and `δH_d(t_{‖S‖max})⪰0` (PSD). ⟹ the prime large-values are
  the **positive/harmless** direction; the RH-bearing crux is the **local near-zero** regime. DeWitt's §2
  Bondarenko–Seip bound is then about the wrong direction; the C5 win/lose line moves to the **local
  near-collision** control (a more local, possibly variance/integer-gap-controllable object). **Action:** push
  the structural PSD-resonance proof + tell DeWitt his integer-gap lane may control the RH-bearing residual
  after the one-sided split (reverses his §3).
- **Outcome B (no decoupling):** the two `t`'s coincide, or `δH_d` is indefinite at the `‖S‖`-max. ⟹ the
  large-values regime **does** carry the negative direction; the RH crux genuinely needs resonance-method
  large-values control of a signed extreme (DeWitt §2 stands). **Action:** the crux is a large-values theorem;
  Door-2 grade hinges on whether resonance-method (parent ⟹ BRIDGE) or support-`≤2d` near-resonance (native)
  controls the **signed** extreme.
- **Outcome C (mixed / `d`-dependent):** the separation holds at small `d` but degrades — flag the `d`-trend;
  the no-margin would then re-enter via the separation closing, and a finer (runpod) probe is needed.

Either way the probe **sharpens the Door-2 grade**: it tells us whether the RH-bearing object is the
local near-collision (potentially BRIDGE-or-better) or the signed large-values extreme (the resonance wall).

## Log (cont.)
- 2026-06-19 (Wheeler) — pre-registered the decoupling-probe interpretation (Outcomes A/B/C) so the next tick
  is decisive. A = decoupling holds (prime large-values harmless/positive, RH-crux local near zeros; push PSD
  proof, integer-gap may bite the RH-bearing half); B = no decoupling (resonance-method needed on the signed
  extreme); C = `d`-dependent (finer probe). Probe (`decoupling-probe.py`, NT=161, `d≤6`) running.

## Decoupling probe RESULT — two conjectures refuted, structure refined to rank-1-positive + bounded-negative — Wheeler, 2026-06-19

`computations/2026-06-19-decoupling-probe.out` (`d=2..6`, NT=161, `t∈[0.5,80]`):

| `d` | `argmax_t‖S‖` (`\|ζ\|`) | `argmin_t λ_min` (`\|ζ\|`) | same `t`? | `δH_d` signature at `‖S‖`-max |
|----|----|----|----|----|
| 2 | 4.97 (0.73) | 59.6 (0.34) | **N** | `+1/−1` |
| 3 | 24.4 (0.80) | 48.7 (0.68) | **N** | `+1/−2` |
| 4 | 47.7 (0.53) | 48.7 (0.68) | **N** | `+1/−3` |
| 5 | 21.4 (0.38) | 50.2 (0.64) | **N** | `+1/−4` |
| 6 | 15.9 (1.46) | 51.7 (2.03) | **N** | `+1/−5` |

**Confirmed: the weak decoupling.** `argmax_t‖S_d‖ ≠ argmin_t λ_min(I+S_d)` for every `d` — the
norm-maximizing (large-values) `t` and the RH-bearing (`λ_min`-minimizing) `t` are **distinct**. So the
large-values regime and the near-degeneracy regime are genuinely different points — DeWitt's §2
Bondarenko–Seip large-values bound a `t`-regime **disjoint** from the one where `λ_min` is threatened.

**REFUTED (honest):**
- **The strict PSD-resonance conjecture is false.** `δH_d` at the norm-max is **not** PSD — signature
  `(1, d−1)` (one positive, `d−1` negative eigenvalues).
- **The `|ζ|`-size mechanism is not supported.** `|ζ|` is *comparable* at `argmax‖S‖` and `argmin λ_min`
  (not large-vs-small), so the decoupling is **not** a "large `|ζ|` vs small `|ζ|`" phenomenon. My structural
  explanation via `|ζ|` size was wrong; the two `t`'s differ, but not for that reason.

**Refined structure (what the data actually shows).** By Sylvester, `S_d` has the same signature as `δH_d`:
**one large positive eigenvalue** (`λ_max(S)~40–76`, driving `‖S‖` — the rank-1 resonance alignment
`≈ vv^⊤ ⪰ 0`) **plus `d−1` negative eigenvalues**, which (hp probe, `d≤7`) stay `≥ −1`. So
> `S_d(t) ≈ (\text{rank-1 large positive resonance}) + (\text{(d−1)-dim bounded-negative residual})`.
The **norm / large-values is the rank-1 positive direction (harmless** — it lifts `λ_max`, not lowers
`λ_min`); the **RH-bearing condition is that the `(d−1)`-dim negative residual never reaches `−1`.** That
residual is *not* a rank-1/large-values object and *not* PSD — it is the delicate part.

**Net for C5 (corrected).** The bare decoupling stands (large-values `t` ≠ RH-bearing `t`), but the clean
"PSD-resonance ⟹ integer-gap closes it" route is **closed off**. The RH-bearing object is the
`(d−1)`-dimensional **negative-eigenvalue residual** of `S_d` staying above `−1` uniformly — a genuinely
spectral, non-rank-1, non-PSD condition. The win/lose line is now: control `λ_min` of the
**residual after removing the rank-1 resonance** — neither a `\max|ζ|` large-values bound (that's the removed
rank-1 positive) nor a PSD argument. **Outcome ≈ A-partial then C:** decoupling yes, but the mechanism is
rank-1-positive-removal, and the `d`-growth of the residual's negative extreme is the open question (finer
probe + structure of the residual).

**Honest status of my recent conjectures:** PSD-resonance — **refuted**; `|ζ|`-size decoupling — **refuted**;
weak decoupling (distinct `t`'s) — **confirmed**; one-sided no-margin (the threat is the negative residual,
not the norm) — **confirmed and sharpened** to "the `(d−1)`-dim negative residual, post rank-1 removal."

## Log (cont.)
- 2026-06-19 (Wheeler) — **Decoupling probe run; two conjectures REFUTED, structure refined.** CONFIRMED:
  `argmax_t‖S‖ ≠ argmin_tλ_min` ∀`d` (the large-values and RH-bearing `t`'s are distinct). REFUTED: (i) strict
  PSD-resonance — `δH_d` at norm-max has signature `(1,d−1)`, not PSD; (ii) the `|ζ|`-size mechanism — `|ζ|`
  comparable at both `t`'s. Refined: by Sylvester `S_d ≈ rank-1-large-positive (the resonance, drives ‖S‖,
  harmless) + (d−1)-dim bounded-negative residual (≥−1, the RH-bearing part)`. So the C5 crux = the negative
  residual after rank-1 removal staying `>−1` uniformly in `d` — not a `\max|ζ|` bound, not PSD. Win/lose line
  corrected accordingly. Next: structure of the residual + its `d`-trend (finer probe).

## CURRENT STATE — synthesis (read this for the live picture) — Wheeler, 2026-06-19

The carrier has accreted many steps (and self-corrections); this fixes the live state.

**PROVEN (BRIDGE, live).**
1. **Exact criterion.** RH ⟺ `λ_min(S_d(t)) ≥ −1` ∀`d,t`, `S_d=A_d^{-1/2}δH_d(t)A_d^{-1/2}` (prime fluctuation
   in the archimedean metric). Equivalently `RH ⟺ H_d(t)⪰0 ∀d,t` (Jensen-section hyperbolicity at every base
   point), via **Pólya–LP translation invariance + Pólya–Schur + Hermite + Sylvester congruence**. Depth `n`
   redundant.
2. **Perturbation lemma** (`../../../3-formalized/not_new_scientific_knowledge/c5-jensen-perturbation-lemma.md`): general-`t` (even-free)
   hyperbolicity from value+slope bounds; `He_{2d}` barrier `β≍O(1)`.
3. **Kernel** (`../2-fully-proven/c5-jensen-prime-kernel.md`, Professor): `D_d(c_m;t)` explicit, `c_p=p^{-1/2}`;
   **proved `σ=½` divergence** (control is phase-cancellation, not triangle/`L²`).
4. **Theorem M** (`publications/theorem-m`) = the with-margin model (same Hermite family, positive deformation,
   atom `>½` ⟹ unconditional hyperbolicity).

**ESTABLISHED NUMERICALLY (probes, `d≤7`, `t≤80`).**
- `λ_min(I+S_d)≥0` (RH-consistent; the `d=6` dps-35 negative was conditioning noise, `+` at dps-100).
- The Hankel `λ_min↓0` super-exp = Vandermonde **conditioning artifact**, not geometric margin (`β≍O(1)`).
- **Decoupling:** `argmax_t‖S_d‖ ≠ argmin_t λ_min` ∀`d`; `‖S_d‖` driven by **one large positive** eigenvalue
  (rank-1 resonance, harmless); RH-bearing part = the **`(d−1)`-dim negative residual**, eigenvalues `≥−1`.

**WITHDRAWN (tested/refuted — do not reuse).**
- Additive race `‖δH_d‖<λ_d` (lossy); two-sided `ρ_d<1` (wrong quantity — one-sided is correct).
- "Edge localization" for the slope (it was the withdrawn operator-norm picture; barrier plausibly bulk).
- **Strict PSD-resonance** (`δH_d` at norm-max is signature `(1,d−1)`, not PSD).
- **`|ζ|`-size decoupling mechanism** (`|ζ|` comparable at the two extremal `t`'s).
- "Materially more hopeful" (the prior Thm 7 / CNV no-margin is real; difficulty relocated, not removed).

**THE OPEN C5 CRUX (one line).** Does `μ_d(t):=λ_min(S_d(t))` stay `> −1` **uniformly in `d`** (and ∀`t`)?
This is the `(d−1)`-dim negative-residual extreme; by Professor's divergence it is a phase-cancellation
quantity, **not** a `\max|ζ|` large-values bound (that's the harmless rank-1 positive) and **not** PSD.
Door-2: BRIDGE iff a parent (Halász/Montgomery large-values, or Montgomery pair-correlation/GUE for the local
near-degeneracy) controls the signed residual; native iff the support-`≤2d` joint near-resonance is essential
(DeWitt's lane). **This is the win/lose point** and is squarely frontier-adjacent (`μ_d>−1 ∀d` ⟺ RH).

**Flagged observation (worth understanding, maybe artifact).** `argmin_t λ_min` clusters at `t≈48.7,48.7,
50.2,51.7` for `d=3,4,5,6` — near-constant across `d` (nearest zeros `γ_{12,13,14}≈48.0,49.8,53.0`, no
anomalously small gap). Likely a `t`-range/normalization artifact (average `A_d` over `[0.5,80]`), but if real
it would localize the RH-bearing degeneracy — check with a wider/finer `t`-range (runpod) before reading into it.

## Log (cont.)
- 2026-06-19 (Wheeler) — wrote the CURRENT STATE synthesis: proven BRIDGE (criterion, perturbation lemma,
  kernel, Theorem M); numerically established (RH-consistent `λ_min≥0`, conditioning≠margin, decoupling +
  rank-1-positive/`(d−1)`-negative structure); withdrawn (additive race, two-sided `ρ_d`, edge-loc, strict
  PSD, `|ζ|`-mechanism, "more hopeful"); the one-line open crux (`μ_d=λ_min(S_d)>−1` uniform in `d`); flagged
  the `argmin λ_min` `t≈49–52` clustering for a finer probe.

## Answering Professor's circularity challenge: the gap-difference is the independent (non-tautological) quantity — Wheeler, 2026-06-19

Professor (chat id=86) is right that `λ_min(S_d)≥−1 ⟺ roots real` is a Hermite **tautology**, so the carrier
is C5 only if some quantity bounds hyperbolicity **without presupposing it**. There is one, and it is exactly
the residual: the **adjacent-displacement-difference**.

**The independent quantity.** The section `J_d(·;t)` is a **real** polynomial (`Ξ^{(j)}(t)∈ℝ`), so its
first-order root displacements `ε_l(t) = −δJ_d(r_l;t)/∂_X J_d^{arch}(r_l;t)` are **real** Bohr sums (Professor's
kernel: `ε_l(t)=Σ_p p^{-1/2}K_d(r_l;p;t)e^{-it\log p}`, real after conjugate pairing). A root **collision**
(the only way to leave the real axis) between adjacent `ρ_l<ρ_{l+1}` needs `ρ_l→ρ_{l+1}`, i.e.
> **the gap-difference** `Δε_l(t) := ε_l(t)−ε_{l+1}(t) \to Δ_l := r_{l+1}-r_l` (the Hermite gap).
Hence the **independent sufficient condition**:
> **(GD)** `\sup_t |ε_l(t)-ε_{l+1}(t)| < Δ_l`  for all adjacent `l` (and all `d`)  ⟹ no collision ⟹ hyperbolic ⟹ RH.

**This is NOT a restatement of "roots real."** `Δε_l(t)` is an **explicit prime Bohr sum** (the kernel
difference at adjacent Hermite nodes, weighted `p^{-1/2}`), and `Δ_l` is an explicit **archimedean** Hermite
gap — both computed with **no reference to whether the roots are real**. (GD) **implies** hyperbolicity but is
strictly **stronger** (a first-order sufficient bound; roots could stay real with larger displacements via
higher order). So it is a genuine independent handle, exactly what Professor's test demands — passing it.

**It also resolves the resonance / rank-1-positive structure (and the decoupling), cleanly.** Differencing
**annihilates the coherent (uniform) shift**: if `ε_l(t)≈ε(t)` for all `l` (the rank-1 resonance — all roots
translate together, gaps preserved), then `Δε_l≈0` — harmless. So
> the **rank-1 positive** direction = the **uniform shift** = `\ker` of the difference operator; the
> **`(d−1)`-dim negative residual** = the `d−1` **gap-differences** `{Δε_l}`.
This is why the probe saw signature `(1,d−1)` and `‖S‖` driven by a positive rank-1 mode that does not
threaten `λ_min`: the norm is the (gap-preserving) coherent shift; the RH-bearing part is the
gap-differences. **Structurally complete — and matches Professor's first-order form
`q(V)=Σ_l ε_l\,2V(r_l)V'(r_l)`.**

**What it does NOT escape (honest, conceding Professor's deeper point).** `Δε_l(t)` is still a `p^{-1/2}`
Bohr sum, so by Professor's §6 divergence `\sup_t|Δε_l|` is a **cancellation / large-values** quantity (no
triangle/`L²` bound). So (GD) **dissolves the circularity** (the quantity is independent of hyperbolicity)
but **not** the large-values crux: whether `\sup_t|Δε_l| < Δ_l` uniformly in `d` is BRIDGE (parent
large-values: Halász/Montgomery) or native (support-`≤2d` near-resonance: Baker/integer-gap, DeWitt) is **the
unchanged Door-2 win/lose line**. The carrier is **non-tautological** (answering Professor); whether it is C5
is the large-values-vs-near-resonance grading, not circularity.

**Net.** Professor's test: "is there a bound that does not presuppose hyperbolicity?" — **Yes:** the
gap-difference `\sup_t|ε_l-ε_{l+1}|<Δ_l`, an explicit prime-Bohr-sum-vs-Hermite-gap inequality, with the
coherent shift correctly annihilated. The carrier is not dBN/Hermite-circular. The genuine open content is the
uniform large-values control of the gap-difference — which **is** a non-tautological arithmetic statement, and
which coincides (gap-normalized) with my perturbation-lemma slope condition `(b)`.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Answered Professor's circularity challenge (id=86).** The non-tautological
  independent quantity = the **adjacent-displacement-difference** `Δε_l(t)=ε_l-ε_{l+1}` (explicit real prime
  Bohr sum, kernel-difference weighted `p^{-1/2}`) vs the Hermite gap `Δ_l`: **(GD)** `sup_t|Δε_l|<Δ_l ∀l,d ⟹
  hyperbolic`, NOT a restatement of "roots real" (computed without it; strictly stronger). Resolves the
  rank-1/residual structure: differencing annihilates the coherent (uniform-shift) resonance — that's the
  rank-1 positive `\ker`; the `(d−1)` gap-differences are the RH-bearing residual (explains the `(1,d−1)`
  signature). Honest concession: `Δε_l` is still a `p^{-1/2}` divergent sum (§6) ⟹ the large-values crux
  stands (Door-2: Halász/Montgomery BRIDGE vs Baker/integer-gap native). So the carrier is non-tautological;
  C5-vs-BRIDGE is the large-values grading. (GD) = gap-normalized slope condition `(b)`.

## CORRECTION (Professor id=91): the J'-sign-flip — differencing does NOT suppress; no-margin persists in (GD) — Wheeler, 2026-06-19

Professor concedes (GD) passes the circularity test (good), but corrects my "differencing annihilates the
coherent shift ⟹ harmless" claim. He is right; fixing it.

**The sign-flip.** `ε_l = −δJ(r_l)/J'(r_l)`, and at consecutive simple roots of `J^{arch}`, `J'` **alternates
sign**. So for a slowly-varying prime `δJ` (`δJ(r_l)≈δJ(r_{l+1})`, `|J'(r_l)|≈|J'(r_{l+1})|=:|J'|`):
> `ε_{l+1} ≈ −δJ/J'(r_{l+1}) = −δJ/(−|J'|) = +δJ/|J'| ≈ −ε_l` (since `ε_l≈−δJ/|J'|`),
hence `Δε_l = ε_l − ε_{l+1} ≈ 2ε_l` — a **SUM**, full displacement scale, **NOT a suppressed difference.** My
"coherent shift ⟹ `ε_l≈ε_{l+1}` ⟹ small `Δε_l`" was wrong: the `J'`-sign-flip gives `ε_l≈−ε_{l+1}`.

**What IS annihilated.** Only the exact **translation mode** `δJ ∝ J'` (⟺ uniform root shift `ε_l≡c`) gives
`Δε_l=0`. The probe's rank-1 positive eigendirection = this `δJ∝J'` component; the `(d−1)` negative residual =
the gap-distorting modes, which carry **full** displacement scale. A generic *prime* `δJ` is **not** `∝J'`, so
its `Δε_l` is full-scale.

**⟹ The no-margin PERSISTS in (GD) (Professor's point).** `Δ_l↓0` (edge `≍d^{-1/6}`, bulk `≍d^{-1/2}`) is a
**real** shrinking RHS, and `Δε_l` (a `p^{-1/2}` Bohr sum) does **not** shrink with it. So `|Δε_l|/Δ_l` genuinely
faces the no-margin; (GD) is non-tautological (still true) but **not easier** — the prior Thm 7/CNV no-margin is
intact. **(GD) is the correct, non-circular, NON-margin-free target.**

**Honest meta-note.** This is my third over-optimistic reframe this session (additive race; "O(1)-barrier more
hopeful"; "rank-1 suppression harmless"), each corrected back to: the no-margin is **robust** — every
reparametrization relocates it (additive→relative→one-sided→gap-difference) but none removes it, consistent
with "RH = the uniform completion" (log §671). The genuine content of the carrier is **structural** (the exact
non-tautological criterion + the kernel + the Theorem-M model + the perturbation engine), and the **wall** is
the uniform large-values control of `Δε_l` vs `Δ_l↓0` — squarely the seam/no-margin, frontier-adjacent. I
will stop claiming the no-margin is tamed and treat it as the robust wall it is.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Corrected (Professor id=91): `J'`-sign-flip.** At consecutive `J^{arch}` roots `J'`
  alternates sign ⟹ generic `δJ` gives `ε_l≈−ε_{l+1}` ⟹ `Δε_l≈2ε_l` (SUM, full scale), NOT a suppressed
  difference. Only `δJ∝J'` (uniform root shift) is annihilated (= the probe's rank-1 positive); the `(d−1)`
  gap-distorting residual carries full scale. So the no-margin **persists** in (GD): `Δ_l↓0` real, `Δε_l`
  doesn't shrink. (GD) stays non-tautological but is not easier. Meta: third over-optimism corrected — the
  no-margin is robust; I'll treat it as the wall. Carrier's value is structural; the wall is the uniform
  large-values control of `Δε_l/Δ_l` (seam, Fields-adjacent).

## Gap-margin probe RESULT — no-margin confirmed (gaps shrink, never cross); RH-consistent to d=8 — Wheeler, 2026-06-19

`computations/2026-06-19-gap-margin-probe.out` (full real section roots via `polyroots`, `d=2..8`,
`t∈[0.5,80]`, NT=161; relative min gap `g_d(t)=min_l(ρ_{l+1}-ρ_l)/mean_l(\cdot)`):

| `d` | `min_t g_d` (worst-`t`) | `mean_t g_d` | complex-root `t`'s |
|----|----|----|----|
| 2 | 1.0 | 1.0 | 0/124 |
| 3 | 4.6e-3 (t=24.4) | 0.405 | 0/122 |
| 4 | 5.6e-4 (t=47.7) | 0.222 | 0/119 |
| 5 | 1.6e-3 (t=48.7) | 0.133 | 0/115 |
| 6 | 7.5e-4 (t=15.9) | 0.086 | 0/111 |
| 7 | 6.3e-4 (t=44.2) | 0.067 | 0/106 |
| 8 | 1.7e-4 (t=30.3) | 0.051 | 0/101 |

**RH-consistent.** **No complex section roots** at any `t`, any `d≤8` — the degree-`d` Jensen sections of `Ξ`
are hyperbolic throughout, well-conditioned-ly confirmed (root-based, not Hankel).

**The no-margin is REAL (confirms Professor's correction, refutes my suppression hope).** At the worst `t`
the relative min gap `min_t g_d ↓` (`~10^{-3}–10^{-4}`), i.e. `Δε_l` gets within `~10^{-4}` of closing the
Hermite gap `Δ_l` — but **never crosses** (no collision, gaps stay positive). So the gap-difference
`Δε_l` does approach `Δ_l` (the no-margin), exactly as Professor's `J'`-sign-flip predicts (`Δε_l` carries
full displacement scale, not suppressed); RH is the statement that it never reaches. The `mean_t g_d` decay
(`~1/d`) is partly generic packing; the **`min_t g_d` shrinking is the genuine no-margin signal**.

**Two earlier claims settled numerically.** (i) My "differencing suppresses ⟹ harmless" — **refuted** (gaps do
shrink). (ii) My `t≈49–52` clustering — **refuted as a sampling artifact** (worst-`t` here: 24.4, 47.7, 48.7,
15.9, 44.2, 30.3 — scattered). 

**Caveat / next.** `min_t g_d` is noisy in `d` (NT=161 catches different near-collisions per `d`); a clean
shrink-rate needs finer `t`-sampling near each worst-`t` (runpod, adaptive grid) and higher `d`. The decisive
quantity remains `min_t g_d` vs `d` — does it `→0` polynomially (matching `Δ_l↓0`, RH-true marginal) or hit a
floor? Either way **no collision through `d=8`** is solid RH-consistency.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Gap-margin probe (well-conditioned, root-based).** No complex section roots `d≤8`,
  `t≤80` (RH-consistent). `min_t` relative min gap shrinks with `d` (`~10^{-3}–10^{-4}`) but stays `>0` — the
  **no-margin confirmed** (gaps approach, never cross), vindicating Professor's `J'`-sign-flip (no suppression).
  Refuted numerically: my "differencing suppresses" and the `t≈49–52` clustering (worst-`t` scattered). Clean
  shrink-rate needs adaptive finer `t` + higher `d` (runpod). RH-consistency solid through `d=8`.

## Resolving Professor's decisive test #93 analytically: the resonance avoids the translation mode (moment-order structure) — Wheeler, 2026-06-19

Professor's id=93 left the make-or-break mechanism **open**: (GD) escapes the §7 large-values problem **iff**
the prime resonance concentrates in the translation mode `δJ(·;t*) ∝ J^{arch}'`. The card so far only *asserts*
"a generic prime `δJ` is not `∝J'`" (line ~1450) and supports it numerically (the gap-margin probe). Here I
settle the mechanism **analytically** from the kernel structure.

**The moment-order regrouping.** Regroup Professor's §2 first-order expansion (`c5-jensen-prime-kernel.md`) by
**derivative order `i`** instead of by prime frequency:
> `δJ_d(X;t) = Σ_{i=0}^d P^{(i)}(t)·B_i(X;t)`,  `P(t)=\log ζ(½+it)` (prime part),
> `B_i(X;t) = Σ_{j=i}^d \frac{\binom{d}{j}\binom{j}{i}}{j!} Ξ_{arch}^{(j-i)}(t)\,X^j`  (archimedean-only).
The scalar coefficients are the **`t`-derivatives of the single prime field**:
`P^{(i)}(t) = Σ_p p^{-1/2}(-𝔦\log p)^i e^{-𝔦t\log p}` (+ prime powers). This is a clean **separation of
variables**: prime Bohr-field derivatives (`t`) × archimedean geometry polynomials (`X`) — the seam
(`∂_t` = the archimedean generator acting on the prime field `P`) made explicit at the deformation level.

**Two structural facts read off `B_i`.**
- (S1) `B_i` has lowest term `X^i` (sum starts at `j=i`), and the top one is a pure monomial
  `B_d(X;t) = \frac{Ξ_{arch}(t)}{d!}X^d`. The `i=0` term is `B_0 = J^{arch}` itself — a pure **rescaling** of
  the section, **root-blind** (`B_0(r_l)=J^{arch}(r_l)=0`), so it drops from the displacement
  `ε_l=-δJ(r_l)/∂_XJ^{arch}(r_l)`. (This is why the displacement sum runs `i≥1`.)
- (S2) `P^{(i)}` is **more divergent for larger `i`**: its prime amplitude is `p^{-1/2}(\log p)^i`, and the
  resonance-method extreme value gains a `(\log X)^i` factor over the resonating primes `p≲X`. So the §7
  large-values (the `sup_t`) are dominated by the **highest** moments `P^{(d)},P^{(d-1)},…`.

**The translation direction is the LOW-moment direction.** Translation = `ε_l≡const`. Honest correction to a
first guess: translation **is** reachable in principle — the `d` vectors `(B_i(r_l))_{l}`, `i=1..d`, span `ℝ^d`
at the `d` nonzero Hermite nodes (`He_{2d}(0)≠0`, so all `r_l≠0`; the matrix is `\mathrm{diag}(r_l)·`Vandermonde,
full rank), so the constant vector `𝟙` lies in their span. But the combination realizing `𝟙` is weighted toward
the **low** `B_i` (low degree ≈ slowly varying ≈ near-constant on the nodes); the high-degree `B_i`
(`B_d∝X^d`, edge-blown-up, strongly `l`-varying) are **transverse** to `𝟙`.

**⟹ The resonance cannot concentrate in translation.** By (S2) the resonance `t*` maximizes the
high-`i` moments, which by (S1) ride the edge-concentrated `B_i` (`B_d∝X^d`). The resulting displacement
profile `{ε_l(t*)}` is therefore dominated by the edge/high-degree modes, **structurally far from** the
constant translation direction. For translation to win, the resonance would have to be carried by the `i=1`
moment — the **least** divergent. It is not. Hence differencing does **not** suppress the spike; `Δε_l` carries
full displacement scale, and `|Δε_l|/Δ_l` inherits the §7 value-form large-values (`sup_t=∞` regularized).

**Verdict.** **Professor's #93 resolves NEGATIVE, analytically:** the prime resonance lives in the high-moment,
edge-concentrated, gap-distorting modes — never the translation mode. So **(GD) does not escape §7**; its
sup-crux is the parent large-values quantity ⟹ **BRIDGE**. This confirms the team's `C5 ⇔ apex` verdict
(DeWitt id=92/96, Professor id=88) **from the kernel structure** (analytic), complementing the gap-margin probe
(numerical, `min_t g_d↓` to `~10^{-4}` at `d=8`). The carrier's value is unchanged — the exact criterion
`λ_min(S_d)≥−1`, the kernel, the Theorem-M model, the (now Lean-ready) perturbation lemma — and the wall is
unchanged: the uniform large-values control of `Δε_l/Δ_l`, squarely the seam/no-margin (frontier-adjacent).

**Honest caveats.** (i) First-order kernel only (pre-collision regime). (ii) (S2)'s "higher `i` more divergent"
uses resonance-method extreme-value scaling, not a hard uniform theorem; the **structural ordering**
(translation = low-moment = least divergent; resonance = high-moment = edge) is the robust part. (iii) I
retract an intermediate over-claim (a "constant-term obstruction" forbidding translation outright) — translation
is reachable in principle; the correct statement is that the **resonance** avoids it on divergence-ordering
grounds.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Answered Professor's open #93 mechanism analytically.** Regrouped the first-order
  prime deformation by derivative order: `δJ_d=Σ_{i≥1}P^{(i)}(t)B_i(X)` (clean seam separation: prime-field
  `t`-derivatives × archimedean `X`-polynomials; `i=0`=root-blind rescaling drops). `B_d∝X^d` (S1) and `P^{(i)}`
  most divergent at high `i` (S2) ⟹ the resonance is dominated by high-degree edge-concentrated modes,
  **transverse to the low-moment translation direction**. So the prime resonance does **not** concentrate in
  translation ⟹ differencing doesn't suppress ⟹ (GD)'s sup = §7 large-values = **BRIDGE**. Confirms `C5⇔apex`
  from kernel structure (analytic), complementing the gap-margin numerics. Retracted an intermediate
  constant-term over-claim (translation IS reachable in principle; the resonance avoids it). Wall unchanged.

## RE-DIRECTION (from the source corpus `docs/rh-corp`, user pointer 2026-06-19) — the additive margin is the WRONG coordinate; go multiplicative (chain-sequence)

Mining `docs/rh-corp` (the source corpus) on the user's pointer: `speculation2.md` names **this carrier's
route — uniform Jensen/Laguerre–Pólya/Pólya–Schur hyperbolicity — as the #1 RH route** ("the first proof is
more likely a uniform Jensen/LP hyperbolicity proof than a direct F₁ construction"), with the decisive clue I
**underweighted**: the proof must satisfy the **additive (finite-free/Jensen/dBN) AND multiplicative
(Pólya–Schur/LP multiplier-sequence) structures at once** — an *"Euler-loaded Pólya–Schur stability theorem"* —
and **ordinary finite-free cone / additive-margin tools do NOT bridge to the multiplier-sequence property.**
And `worklog-professor.md` §937 already has the concrete multiplicative form:
> **RH ⟺ the prime-explicit `a_n = λ_n/(b_{n-1}b_n)` is a chain sequence** (`g_n∈[0,1) ∀n`), with `b_n,λ_n`
> from the **cumulant moments `m_k=Σ_ρ u_ρ^{-k}`** (prime-explicit via `log ξ` / explicit formula, **no
> zeros**); lever = the **Wall–Chihara near-boundary criterion** (`a_n→¼` ⟺ a Hellinger–Wall series condition
> on the excess `e_n`), evaluated by **PNT/Mertens** asymptotics of the cumulant moments.

**The connection (Hankel↔Jacobi↔chain duality, textbook Chihara).** My finite-free `H_d` is the Hankel of the
section power sums; a Hankel moment matrix ↔ orthogonal polynomials ↔ Jacobi recurrence `(b_n,λ_n)` ↔ the
chain sequence `a_n=λ_n/(b_{n-1}b_n)`. So **additive hyperbolicity (`H_d⪰0`) ⟺ the multiplicative
chain-sequence condition (`a_n` chain).** Same object, dual coordinates.

**The re-direction (the advance).** The **no-margin** — a hopeless large-values race in MY additive
coordinates (`sup_t` of the prime deformation vs the shrinking Hermite gap `Δ_l~d^{-1/6}`; graded parent/
BRIDGE) — is, in the MULTIPLICATIVE chain coordinates, the **natural boundary `a_n→¼`** (the maximal-chain
edge): RH ⟺ `a_n` stays a chain sequence ⟺ `a_n` approaches but never crosses `¼`. This is the *"no-margin
EQUALITY, not inequality"* the corpus insists on (speculation/speculation2), and it is governed by the
**Wall–Chihara series on the prime-explicit `e_n`**, a CONCRETE PNT/Mertens computation — **not** a sup-control.
> **So my carrier's additive margin race was the wrong coordinate.** The live route is the **multiplicative
> chain-sequence persistence** (Wall–Chihara + PNT/Mertens on the prime-explicit cumulant moments
> `m_k=Σ u_ρ^{-k}`), where the no-margin is the `a_n→¼` chain-boundary. This realizes speculation2's
> "both structures at once": my additive `H_d` (finite-free) and the prof's multiplicative `a_n` (chain) are
> dual views of one object; the chain view is where the no-margin is tractable.

**Concrete next target (the open frontier, now in the right coordinates):** the **infinite chain-sequence
persistence** — prove `{a_n}` (prime-explicit, `a_n→¼`) is a chain sequence for ALL `n` via the Wall–Chihara
series condition on `e_n`, evaluated by PNT/Mertens asymptotics of `m_k=Σ_ρ u_ρ^{-k}` (= `log ξ` Taylor/
cumulant coeffs, Euler-explicit). Finite-`n` is floor (rh-corp Critic); the infinite/persistence is the wall.
**[FLAG: pin the exact Wall–Chihara constant/criterion from Chihara Ch.III; numerically pre-certify the
cumulant-moment asymptotics before any claim — do NOT assert from memory (the prof's own caution).]**
This is the multiplicative complement to the additive carrier — the same object, the tractable coordinate.

## Log (cont.)
- 2026-06-19 (Wheeler) — **RE-DIRECTION from `docs/rh-corp` (user pointer).** Mined the source corpus:
  `speculation2.md` = this carrier's route is the #1 RH bet, with the underweighted clue = JOINT additive
  (finite-free) + multiplicative (Pólya–Schur) stability ("Euler-loaded Pólya–Schur"); additive-cone tools
  don't suffice. `worklog-professor.md §937` = the concrete multiplicative criterion: RH ⟺ prime-explicit
  `a_n` (from cumulant moments `m_k=Σ u_ρ^{-k}`, Euler-explicit) is a chain sequence, via Wall–Chihara +
  PNT/Mertens. Connected to the carrier by the textbook **Hankel↔Jacobi↔chain duality** (`H_d⪰0 ⟺ a_n` chain).
  **Re-direction:** the no-margin is a hopeless large-values race in my ADDITIVE coords but the natural
  `a_n→¼` chain-boundary in MULTIPLICATIVE coords (the "no-margin equality" the corpus demands), tractable
  via Wall–Chihara + PNT/Mertens — so the additive margin race was the wrong coordinate. Concrete target:
  the infinite chain-sequence persistence on the prime-explicit cumulant moments. Constants flagged for
  Chihara-Ch.III verification + numeric pre-certification (prof's caution). Mining+connection+re-direction
  grounded in the source corpus; the proof itself (chain-persistence) is the open frontier, now in the right
  coordinates.

## Chain-sequence diagnostic PRE-CERTIFIED (the rh-corp redirect's flagged numeric) — Wheeler, 2026-06-19

Per §1580 + worklog-professor §914–941: RH ⟺ the secular-measure Jacobi `a_n = λ_n/(b_{n−1}b_n)` is a chain
sequence (`g_0=0`, `g_n=a_n/(1−g_{n−1})`, chain ⟺ `g_n∈[0,1) ∀n`; no-margin `a_n→¼`, `g_n→½`); `b_n,λ_n` from the
moments `m_l=Σ_ρ u_ρ^{−l}`, `u_ρ=(ρ−½)/i` (`=γ`, REAL iff RH). The flag demanded a numeric pre-certification
**before** any claim — executed (`computations/2026-06-19-wheeler-chain-sequence-precert.py/.out`, Chebyshev
moment→recurrence algorithm, `dps=50`, `N=80` zeros). **Three findings:**

1. **Algorithm validated** (sanity: a positive measure on `(0,1)` gives `g_n∈[0,1)`, `a_n→¼`).
2. **RH-side certified.** With real `γ` (RH true), `g_n` is **real and in `[0,1)`**, hovering near **½**
   (`0.36–0.49` for `n≤8`), and `a_n` near **¼** (`0.21–0.42`). So the secular chain sits exactly at the
   **no-margin / ¼ boundary** the corpus predicts (`g_n≈½`). Chain-consistent. ✓
3. **The off-line separator works — at finite `n` — once FE-symmetry is respected (a real correction).**
   - *Naive (wrong) model:* moving **one** zero off the line breaks the functional equation, making the moments
     **complex** ⟹ `g_n` trivially complex. A real signal, but not the genuine test.
   - *Correct model (FE-symmetric quadruple `{½±β±iγ}`):* the moments **stay real** (conjugate+negation
     cancellation), but the measure is **non-positive**, so `g_n` (real) **EXITS `[0,1)` at finite `n`**:
     `β=0.2` → `g_3=1.44` (`a_4=−2.06<0`); `β=2.0` → `g_2=−0.10`, `g_3=1.21`. The chain criterion **fails**, and
     **earlier for deeper off-line zeros** — detection at small finite `n`, confirming worklog §941's DH test.

**Verdict (pre-certification PASSED).** The chain-sequence diagnostic is **real and finite-`n` falsifiable**:
on the line `g_n∈[0,1)` at the `½` no-margin edge; an FE-symmetric off-line zero forces `g_n` out of `[0,1)` (and
`a_n<0`) at small finite `n`. This validates the **multiplicative chain coordinate** as the right one (the
additive margin race, by contrast, was RH-blind / a large-values race, §1334). **Honest scope:** this uses the
*zeros* (a validation / pre-cert), not the *prime-explicit* moments `m_k` (the proof input via the cumulant
ladder + PNT/Mertens) — and it certifies the diagnostic at finite `n`, not the **infinite-`n` persistence**
(the genuine `(b)` wall). What is now de-risked: the coordinate is correct, the no-margin is the `g_n=½`/`a_n=¼`
boundary, and off-line detection is finite-`n` — so the chain-persistence target (`{a_n}` prime-explicit stays a
chain ∀`n`, via the Wall–Chihara series on `e_n=a_n−¼`) is posed in a numerically-validated coordinate.

## Log (cont.)
- 2026-06-19 (Wheeler) — **PRE-CERTIFIED the chain-sequence diagnostic** (the rh-corp redirect's flagged
  numeric). Chebyshev moment→Jacobi on `m_l=Σ u_ρ^{−l}`, `dps=50`, `N=80`. (1) algorithm validated (sanity);
  (2) RH-side: `g_n∈[0,1)` near `½`, `a_n` near `¼` — the no-margin boundary; (3) off-line separator works at
  finite `n` **once FE-symmetry is respected** (self-caught flaw: single-zero off-line → complex moments,
  trivial; the FE-symmetric quadruple `{½±β±iγ}` keeps moments real and makes `g_n` exit `[0,1)` at `n=2–3`,
  `a_n<0`, earlier for deeper β). Validates the multiplicative chain coordinate as RH-bearing and finite-`n`
  falsifiable. Uses zeros (validation), not prime-explicit `m_k` (proof input); infinite-`n` persistence remains
  the wall — now in a certified coordinate. Archived `computations/2026-06-19-wheeler-chain-sequence-precert.*`.

## The chain-persistence criterion, DERIVED (parabolic discrete-Riccati near g=½) — Wheeler, 2026-06-19

The flag said *do not recall the Wall–Chihara constant* — so I derive the near-`¼` persistence criterion from the
minimal-parameter map itself. RH ⟺ `J_μ⪰0` ⟺ `a_n` chain ⟺ `g_n<1 ∀n`, `g_n=a_n/(1−g_{n−1})`, `g_0=0` (worklog
§920). Write `a_n=¼+e_n` (`e_n` prime-explicit via the cumulant moments).

**The fixed point is PARABOLIC.** `g=a/(1−g)` at `a=¼` solves `g(1−g)=¼ ⟺ (g−½)²=0` — a **degenerate** (double)
fixed point `g*=½`. So the no-margin is not a hyperbolic edge but a **parabolic** one; persistence is governed by
the *accumulated* perturbation, not a pointwise bound (this is exactly why "`a_n≤¼` pointwise" is the wrong
reading — a chain sequence may exceed `¼`).

**Exact baseline (`e_n≡0`).** `g_n = n/(2(n+1))` (check: `g_1=¼, g_2=⅓, g_3=⅜, g_4=⅖,…→½⁻`), so with `h_n:=g_n−½`,
> `h̄_n = −1/(2(n+1))` — the maximal constant chain approaches `½` **from below** like `−1/(2n)`, never reaching
> `1`. (Confirms `a_n≡¼` is a chain; `g_n→½`.)

**Exact perturbed recursion.** From `(½−h_{n−1})(½+h_n)=¼+e_n`:
> `h_n = (h_{n−1}+2e_n)/(1−2h_{n−1})`  (a Möbius/discrete-Riccati map; quadratic `2h_{n−1}²` on expansion — the
> destabilizing term of the parabolic point).

**Linearization around `h̄_n` (`h_n=h̄_n+δ_n`).** With `D=1−2h̄_{n−1}=(n+1)/n`, to first order
`δ_n = δ_{n−1}·[1/D+2h̄_{n−1}/D²] + 2e_n/D = δ_{n−1}·\dfrac{n²}{(n+1)²} + \dfrac{2n}{n+1}e_n`. The homogeneous
factor telescopes, `∏_{k≤n}k²/(k+1)² = (n+1)^{−2}`, so by variation of parameters
> `δ_n = \dfrac{1}{(n+1)²}\,\sum_{j\le n} 2\,j(j+1)\,e_j \;\approx\; \dfrac{2}{n²}\sum_{j\le n} j²\,e_j.`

**The criterion (derived).** The linearization holds while `|δ_n| ≲ |h̄_n| = 1/(2(n+1))`; the parabolic blow-up
(`h_n` crosses `0` ⟹ the dropped `2h²` drives `g_n→1`, chain fails) triggers exactly when `δ_n` overtakes `−h̄_n`:
> **`\displaystyle \sum_{j\le n} j(j+1)\,e_j \;<\; \frac{n+1}{4}` for all `n`  ⟺  the chain persists  ⟺  `J_μ⪰0`  ⟺  RH**
> (linearized form; `e_j=a_j−¼` prime-explicit; weight `j(j+1)≈j²`, boundary `(n+1)/4≈n/4`).

This is the **explicit form of the Wall–Chihara/Hellinger–Wall series** the corpus flagged — **derived**, not
recalled: weight `j(j+1)`, threshold `(n+1)/4`, from the parabolic fixed point. Sanity: `e_j≡0` ⟹ sum `=0<n/4`
∀`n` ⟹ persists (the maximal chain) ✓.

**Honest grade.** The derivation (parabolic fixed point, exact baseline `g_n=n/(2(n+1))`, exact Riccati,
linearization → weight `j(j+1)`, threshold `(n+1)/4`) is exact algebra, **verifiable by re-checking** (the
baseline is confirmed by hand). The **RH-equivalence** routes through the classical chain⟺`J_μ⪰0`⟺secular-measure
positivity (worklog §920, BRIDGE). **What remains the wall:** evaluating `Σ_{j≤n}j(j+1)e_j` on the
**prime-explicit** `e_j` (cumulant moments `m_k=Σγ^{−2k}` via the explicit-formula ladder + PNT/Mertens) and
proving it stays `<(n+1)/4` ∀`n` — the genuine `(b)` persistence target, now with an **explicit weighted-series
boundary** instead of an abstract "chain condition." Verification needs high-precision cumulants (Professor's
id=405 ill-conditioning caveat applies — the noisy zero-based `a_n` at `n>6` were conditioning, not signal).

## Log (cont.)
- 2026-06-19 (Wheeler) — **DERIVED the chain-persistence criterion** (instead of recalling the Wall constant).
  The minimal-parameter map has a **parabolic** fixed point `g=½` at `a=¼` (`(g−½)²=0`); exact baseline
  `a_n≡¼ ⟹ g_n=n/(2(n+1))`, `h̄_n=−1/(2(n+1))` (→½ from below); exact Riccati `h_n=(h_{n−1}+2e_n)/(1−2h_{n−1})`;
  linearization → homogeneous `(n+1)^{−2}`, `δ_n=(n+1)^{−2}Σ_{j≤n}2j(j+1)e_j`. Parabolic blow-up at
  `Σ_{j≤n}j(j+1)e_j=(n+1)/4`, giving the **explicit Wall–Chihara series**: RH ⟺ `Σ_{j≤n}j(j+1)e_j<(n+1)/4 ∀n`
  (weight `j(j+1)`, boundary `(n+1)/4`, `e_j=a_j−¼` prime-explicit). Sanity `e≡0` ✓. Derivation is exact algebra
  (baseline hand-verified); RH-equivalence via classical chain⟺`J_μ⪰0` (BRIDGE). Wall: evaluate the weighted
  series on prime-explicit cumulants (PNT/Mertens) — needs high-precision cumulants (id=405 caveat). The abstract
  "chain persistence" is now a concrete weighted-series boundary problem.

## The no-margin IS the discrete Hardy/Chihara oscillation constant ¼; chain ⟺ Li-positivity (FE-symmetric σ_k) — Wheeler, 2026-06-19

Two upgrades fold the derived chain-boundary into established prime-explicit machinery.

**(A) FE-symmetric moments (Professor id=409).** The right secular moments are not bare `Σγ^{−2k}` but the
FE-symmetric **secondary sums** `σ_k := Σ_ρ (ρ(1−ρ))^{−k} = Σ_γ (¼+γ²)^{−k}` — i.e. the secular measure has atoms
at `x_ρ = 1/(ρ(1−ρ)) = 1/(¼+γ²)`, invariant under `ρ↔1−ρ` (matching the `a_n≡¼` baseline), manifestly positive
on the line, and better-conditioned (the `¼` offset). These are exactly the **Keiper–Li secondary sums**; the Li
coefficients `λ_n^{Li}=Σ_ρ[1−(1−1/ρ)^n]` are ℚ-polynomials in the `σ_k`, and **RH ⟺ `λ_n^{Li}≥0 ∀n`** (Li's
criterion). So the derived chain-boundary (`J_μ⪰0 ⟺ a_n` chain, worklog §920) is a **Jacobi / Wall–Chihara
repackaging of Li-positivity** — RH-equivalent, inside the established Keiper `σ_k` machinery (Keiper's `σ_k`
recursion = the cumulant→Jacobi map, sidestepping a from-scratch Stieltjes algorithm). *Not a shortcut:*
Li-positivity is the transverse/curvature regime (Professor's `phase-cancellation-crux`), the genuine RH content.

**(B) The no-margin = the discrete oscillation constant ¼.** Apply the derived criterion
(`Σ_{j≤n}j(j+1)e_j<(n+1)/4`) to the soft-edge rate `e_n=a_n−¼ ~ λ/n²`:
`Σ_{j≤n} j(j+1)(λ/j²) ≈ λ Σ_{j≤n}(1+1/j) ≈ λ·n < (n+1)/4 ⟺ ` **`λ ≤ ¼`**. So the chain persists (RH) ⟺ the
**subleading coefficient `λ` of `e_n ~ λ/n²` is `≤ ¼`** — the **discrete Hardy/Chihara oscillation constant**
(`a_n=¼+λ/n²` is a chain sequence iff `λ≤¼`). My parabolic-Riccati derivation **independently reproduces the
classical `¼` threshold** (a check: built only from the parabolic fixed point, it yields the textbook constant).
RH is the **marginal/critical** case (`a_n→¼`, the maximal chain); the RH-bearing quantity is `λ` vs `¼`.

**(C) `λ` is set by the secular measure's edge — prime-explicit.** The atoms `x_ρ=1/(¼+γ²)` accumulate at `0`
with density fixed by `N(T)~(T/2π)log(T/2π)`: near `x=0`, `dμ ~ const·x^{−3/2}|log x| dx` (from `γ=x^{−1/2}`,
`dN/dγ~(1/2π)logγ`). The recurrence's `1/n²` coefficient `λ` is an edge/density functional of `μ`, hence
**prime-explicit** (the `σ_k` via Keiper / the explicit formula). **RH ⟺ this prime-explicit `λ ≤ ¼`.**

**The situated chain of equivalences.**
`RH ⟺ Li-positivity (λ_n^{Li}≥0) ⟺ J_μ⪰0 ⟺ {a_n} chain (g_n<1) ⟺ Σ_{j≤n}j(j+1)e_j<(n+1)/4 ∀n ⟺ [e_n~λ/n², λ≤¼]`.
The boundary is **explicit (`¼`)** and the handle **prime-explicit (Keiper `σ_k`)**; the wall is computing/bounding
the prime-explicit `λ`. Honest: RH-equivalent throughout (not a crossing); the oscillation-constant form is the
sharpest concrete target, and the FE-symmetric `σ_k` is the well-conditioned coordinate.

## Log (cont.)
- 2026-06-19 (Wheeler) — **oscillation-constant reframing + Li-positivity situating (with Professor id=409).**
  (A) Adopted the FE-symmetric secular moments `σ_k=Σ(¼+γ²)^{−k}` (Keiper–Li); the chain-boundary is a
  Jacobi/Wall–Chihara repackaging of **Li-positivity** (`λ_n^{Li}≥0`), in established prime-explicit machinery.
  (B) The derived `Σj(j+1)e_j<(n+1)/4`, on `e_n~λ/n²`, gives `λ≤¼` — the **discrete Hardy/Chihara oscillation
  constant**, reproduced independently by the parabolic-Riccati derivation. RH = the marginal case; RH-bearing
  quantity = `λ` vs `¼`. (C) `λ` is the prime-explicit edge functional of `μ` (atoms `1/(¼+γ²)` accumulate at 0
  with density `~x^{−3/2}|log x|`). Re-running the chain numerics in the better-conditioned `σ_k` coordinate to
  estimate `λ` (`computations/2026-06-19-wheeler-chain-oscillation-constant.*`). Grep-confirmed novel reframing;
  RH-equivalent (not a crossing); sharpest concrete target = prime-explicit `λ≤¼`.

### λ-estimate numeric (FE-symmetric σ_k coordinate) — result, honest

`computations/2026-06-19-wheeler-chain-oscillation-constant.out` (dps=60, N=120, Chebyshev). Two findings:
- **Criterion holds on the reliable range.** `Σ_{j≤n}j(j+1)e_j` vs `(n+1)/4`, ratio for `n=1..6`:
  `0.69, 0.81, 0.39, −0.04, 0.06, 0.04` — all `< 1` ⟹ `Σj(j+1)e_j < (n+1)/4` ⟹ chain-consistent (RH). ✓
- **`e_n` SIGN-OSCILLATES** (`+.17,+.04,−.018,−.022,+.005,−.0007,…`), so `n²·e_n` does NOT converge to a clean `λ`
  — the naive `e_n~λ/n²` is too smooth; the **zero fluctuations** (GUE/pair-correlation) add an oscillatory part.
  The oscillation constant `¼` governs the **smooth/average** part; the criterion must (and on `n≤6` does) hold
  **including** the fluctuations. `n≥7` is conditioning noise (Chebyshev instability; Professor id=405 caveat).

**Refinement (honest).** RH ⟺ `λ_smooth ≤ ¼` is the *average*-part statement; the full criterion
`Σj(j+1)e_j<(n+1)/4 ∀n` carries the fluctuations too, and is the exact target. Pinning `λ_smooth` and bounding
the fluctuation sum need the **prime-explicit `σ_k`** (Keiper, well-conditioned) + a stabler-than-Chebyshev
recurrence map — the next step (Professor id=409 offered the first ~20 prime-explicit `σ_k` as a cross-check).

## A leap (per @user id=408): the oscillation constant ¼ IS the Hardy constant — RH as edge sub-criticality, log-improved — Wheeler, 2026-06-19

Not a deduction — a transfer from a distant domain, then tested. The discrete chain oscillation constant `¼`
(`a_n=¼+λ/n²` chain ⟺ `λ≤¼`) is the **same object** as the continuous **Hardy inequality constant**:
`∫_0^∞|y'|²dx ≥ ¼∫_0^∞|y|²/x²dx` (sharp, never attained). This is not a numerical coincidence — it is the
**established chain-sequence ↔ inverse-square/Bessel correspondence**: the chain recurrence `a_n→¼` is the
discretization of the Bessel/inverse-square operator `H_g = −d²/dx² + g/x²`, whose bounded-below /
non-oscillation threshold is the Hardy coupling `g = −¼`, and the discrete `λ≤¼` is its Kneser-oscillation
discretization. So:

> **Conjecture (HP as Hardy sub-criticality).** The secular measure `μ` (atoms `1/(¼+γ²)`, FE-symmetric `σ_k`)
> has a Krein/string operator `H_μ` whose **edge** behaves as an inverse-square operator with coupling `g_μ`
> fixed by `μ`'s edge density. **RH ⟺ `H_μ` is Hardy-SUB-critical at the edge (`g_μ ≥ −¼`, equivalently the
> oscillation constant `λ_smooth ≤ ¼`).** This is Hilbert–Pólya recast **not** as "self-adjoint with
> eigenvalues = zeros" but as **edge sub-criticality / a positivity** — the constraint-not-flow reading
> (a bound, not a generated spectrum), and it is the operator face of Li-positivity.

**Why this is more than a ¼-relabel (the specific, testable content).** The secular edge density I derived is
`dμ ~ const·x^{−3/2}|log x| dx` (from `N(T)~(T/2π)log(T/2π)`). The bare power `x^{−3/2}` sits at the inverse-square
scaling, and the `|log x|` factor puts the edge operator **exactly in the regime of the LOG-IMPROVED Hardy
inequality** `∫|y'|² − ¼∫|y/x|² ≥ \tfrac14∫\dfrac{|y|²}{x²(\log x)²}dx` (Hardy–Rellich with logarithmic remainder).
So the RH-bearing deficit `¼ − λ_smooth` is conjecturally the **log-Hardy remainder functional** of `μ`'s edge —
a positive quantity with a specific (`1/(x²\log²x)`) form *matched to the zero-counting log*. That match (log in
the density ↔ log in the improved-Hardy remainder) is non-generic — it is what distinguishes this from a generic
inverse-square reframing.

**Door-2 honesty.** RH-equivalent (it routes through the chain↔inverse-square correspondence and Li-positivity,
both BRIDGE) — **a kinship, not yet a crossing.** Its value is the **toolkit**: the improved/remainder Hardy
inequalities (Brezis–Vázquez, Filippas–Tertikas log-Rellich) become applicable to the edge deficit, which the
additive/variance tools were blind to. **Test (what would refute or advance it):** compute `g_μ` (the edge
coupling) from the `σ_k` — if `g_μ` is forced `≥ −¼` by the log-Hardy remainder being a *positive* prime-explicit
functional, that is a genuine handle; if the remainder can be negative, the leap dies. The coupling/remainder
computation is the next step (needs the prime-explicit `σ_k`, with Professor).

## Log (cont.)
- 2026-06-19 (Wheeler) — **a grounded leap (per @user id=408): oscillation constant ¼ = Hardy constant.** Via
  the established chain↔inverse-square/Bessel correspondence, the chain criterion `λ_smooth≤¼` is the edge
  **Hardy sub-criticality** (`g_μ≥−¼`) of the secular Krein/string operator `H_μ` — Hilbert–Pólya recast as a
  **positivity/sub-criticality**, not a self-adjoint spectrum (constraint-not-flow; the operator face of
  Li-positivity). Specific (non-relabel) content: the edge density `x^{−3/2}|log x|` matches the **LOG-improved
  Hardy** regime, so the deficit `¼−λ_smooth` is conjecturally the log-Hardy remainder functional of `μ`'s edge
  (log-in-density ↔ log-in-remainder, non-generic). Door-2: RH-equivalent (kinship, not crossing); value = the
  improved-Hardy toolkit, newly applicable. Test: compute the edge coupling `g_μ` from prime-explicit `σ_k`
  (with Professor) — positive log-Hardy remainder ⟹ handle; negative ⟹ refuted.

## CORRECTION (testing my own leaps against reality, per @user id=408): the asymptotic ¼/edge-coupling is AUTOMATIC — RH is the FINITE-n persistence — Wheeler, 2026-06-19

Mining my own error (the koan's discipline). My previous two sections read RH as `λ_smooth≤¼` (oscillation
constant) and as "edge Hardy-sub-criticality." **Both conflate an automatic backdrop with the RH content.**

**The error, precisely.** By Chihara's *forward* direction, the recurrence of **any** real positive measure on a
bounded set is **always** a chain sequence with `a_n→¼` and `g_n∈[0,1) ∀n`. So:
- `a_n→¼` (the oscillation constant `¼`) — **automatic**, holds for every positive measure;
- `λ_smooth≤¼` (the asymptotic subleading) — **automatic** (it is the chain property of a real measure);
- the smooth edge coupling (the Bessel order from the `x^{−3/2}|log x|` density → formal `g≈α²−¼≈2`,
  sub-critical) — **automatic**, fixed by the zero *density* (the same smooth count on or off the line).

**None of these is RH.** RH is whether the **prime-explicit** `σ_k` (real, FE-symmetric, agnostic to where the
zeros sit) are the moments of a **positive** measure — i.e. **Li-positivity `λ_n^{Li}≥0` at every FINITE `n`** —
equivalently the chain does **not fail at any finite `n`**. An off-line zero keeps `σ_k` real but breaks
positivity, so the chain **fails at finite `n`** (my FE-symmetric separator: `g_n` exits `[0,1)` at `n=2,3`).
The RH content lives in the **finite-`n` fluctuation failures**, NOT the `n→∞` constant.

**What survives, what is demoted.**
- **Survives (correct):** the **derived finite-`n` family** `Σ_{j≤n} j(j+1)e_j < (n+1)/4 ∀n` (the linearized
  chain persistence). This IS the right RH-equivalent — one condition per finite `n` = Li-positivity per order.
  And the FE-symmetric `σ_k` / Keiper machinery, and the off-line separator (the genuine finite-`n` diagnostic).
- **Demoted to structural backdrop (NOT the criterion):** the oscillation constant `¼`, the `λ_smooth≤¼`
  asymptotic, and the Hardy/inverse-square edge sub-criticality. They are real structural features (the chain's
  asymptotic sits at the maximal-chain edge; the operator is inverse-square) but **automatic for any positive
  measure** — they describe the *backdrop*, not the RH-bearing fluctuations. The "no-margin = ¼" is the generic
  backdrop, not where ζ's RH-content sits.

**Corrected target (sharper).** RH ⟺ Li-positivity = the **infinite family of finite-`n` conditions**
`Σ_{j≤n}j(j+1)e_j<(n+1)/4` on the prime-explicit `σ_k` — the **fluctuation control at each finite order**, not an
asymptotic constant. The Hardy leap's residual value is narrow: improved-Hardy *remainder* tools might bound the
finite-`n` fluctuation sum (not the automatic asymptotic) — re-aimed accordingly. This correction prevents the
lane (and me) from chasing the automatic `¼` as if it were RH.

## Log (cont.)
- 2026-06-19 (Wheeler) — **CORRECTION (mined my own error, per @user id=408 / test-against-reality).** The
  oscillation-constant `λ_smooth≤¼` and the Hardy edge-sub-criticality are **automatic for any positive measure**
  (Chihara forward: a real positive measure's recurrence is always a chain, `a_n→¼`) — so they are **backdrop,
  NOT the RH criterion.** RH is the **finite-`n` chain persistence** (Li-positivity `λ_n≥0 ∀ finite n`), which the
  FE-symmetric off-line separator tests (`g_n` exits at `n=2,3`). What survives: the derived finite-`n` family
  `Σ_{j≤n}j(j+1)e_j<(n+1)/4 ∀n` (= Li-positivity per order) on the prime-explicit `σ_k`; the asymptotic
  `¼`/edge-coupling is demoted to structural backdrop. Hardy tools re-aimed at the finite-`n` fluctuation sum.
  Honest self-correction; sharpens the target to finite-`n` fluctuation control, not an asymptotic constant.

## CONVERGENCE: the smooth/fluctuation split IS Bombieri–Lagarias; the criterion in split form — Wheeler (with DeWitt id=418, Professor id=419), 2026-06-19

DeWitt + Professor placed my smooth/fluctuation split exactly onto the **standard Bombieri–Lagarias
decomposition** of the Keiper–Li coefficients, `λ_n = λ_n^{arch} + λ_n^{prime}`:
- **`λ_smooth` (my automatic `¼`-baseline) `= σ_k^{arch} = λ_n^{arch}`** — the explicit **Γ-factor / trivial-zeros**
  term (closed form in `γ_E, logπ, log2, ζ(2k)`), driven by the Riemann–Siegel `θ`, `θ'(t)=(1/2π)log(t/2π)` —
  which **is** the `|log x|` of my edge density `~x^{−3/2}|log x|`. No zeros needed. This is *why* the asymptotic
  `¼`/oscillation constant is automatic (my correction): it is the archimedean baseline.
- **My fluctuation (`e_n` sign-oscillation) `= σ_k^{prime} = λ_n^{prime} = S(T)`** — the nontrivial-zero part.
  This is the RH-bearing wall.

**The criterion, in split form.** Writing `e_j = e_j^{arch} + e_j^{prime}` (from `σ_k = σ_k^{arch}+σ_k^{prime}`),
the derived finite-`n` family `Σ_{j≤n}j(j+1)e_j<(n+1)/4` becomes
> **RH ⟺ `Σ_{j≤n} j(j+1)\,e_j^{prime} < s(n) := (n+1)/4 − Σ_{j≤n} j(j+1)\,e_j^{arch}` for all `n`** —
> the **prime fluctuation** weighted sum stays below the **explicit archimedean slack** `s(n)`.

`s(n)` is computable in closed form from `σ_k^{arch}` (DeWitt is computing it). So the wall is cleanly isolated:
bound the `S(T)`/prime-fluctuation weighted sum `Σ j(j+1)e_j^{prime}` against the explicit `s(n)`. The first read:
the **sign and growth of `s(n)`** — how much slack the archimedean `¼`-baseline leaves for the prime fluctuation.

**Honest grade.** RH-equivalent (this is the chain/Wall–Chihara coordinate of Bombieri–Lagarias / Li-positivity;
all BRIDGE) — situated, not a crossing. Value: (i) the split is now in established machinery (Bombieri–Lagarias),
so the lane is no longer a parallel invention; (ii) the explicit archimedean slack `s(n)` + my weight `j(j+1)`
give a concrete inequality for the prime fluctuation, the genuine `S(T)` wall. Next: DeWitt's `σ_k^{arch}` →
compute `s(n)` → read its sign/growth → bound `Σ j(j+1)e_j^{prime}` (the `S(T)` content).

## Log (cont.)
- 2026-06-19 (Wheeler) — **CONVERGENCE (DeWitt id=418, Professor id=419): my split = Bombieri–Lagarias
  `λ_n=λ_n^{arch}+λ_n^{prime}`.** `λ_smooth`=`σ_k^{arch}`=`λ_n^{arch}` (explicit Γ/θ trivial-zeros term, the
  `|log x|=θ'` edge — confirms the asymptotic is automatic/archimedean); fluctuation=`σ_k^{prime}`=`λ_n^{prime}`
  =`S(T)` (the wall). Sharpened the criterion to **split form: RH ⟺ `Σj(j+1)e_j^{prime} < s(n):=(n+1)/4 −
  Σj(j+1)e_j^{arch}` ∀n** (prime fluctuation below the explicit archimedean slack). DeWitt computing `σ_k^{arch}`
  (→ `e_j^{arch}`, `s(n)` closed form); Professor auditing row-010 `P_k↔λ_n` Newton/Keiper transform. RH-equiv
  (situated in Bombieri–Lagarias, not a crossing); the genuine wall is now the explicit inequality for the
  `S(T)`/prime fluctuation vs `s(n)`.

## CORRECTION 2: the arch/prime split is LINEAR (λ_n / Bombieri–Lagarias), the chain is NONLINEAR — the chain split-form is withdrawn — Wheeler, 2026-06-19

Stress-testing my own previous section (koan discipline). The split-form criterion
`Σ_{j≤n}j(j+1)e_j^{prime}<s(n)` assumed the chain `e_j` decomposes **linearly** as `e_j^{arch}+e_j^{prime}` along
`σ_k=σ_k^{arch}+σ_k^{prime}`. **That is invalid.** The Chebyshev moment→Jacobi map is **nonlinear** (rational):
`α_0=m_1/m_0`, `β_1=m_2/m_0−(m_1/m_0)²`, … — so `a_j=a_j(σ_1,…,σ_{2j})` is a rational function of the moments,
and `σ=σ^{arch}+σ^{prime}` does **NOT** give `a_j=a_j^{arch}+a_j^{prime}`. The chain does not inherit the additive
split. **The split-form chain criterion is withdrawn.**

**What is exact (use this coordinate for the split).** The Bombieri–Lagarias split is **linear**: the Keiper–Li
`λ_n=Σ_k c_{n,k}σ_k` is a *linear* form in the moments, so `λ_n=λ_n^{arch}+λ_n^{prime}` is exact, and
> **RH ⟺ `λ_n^{prime} ≥ −λ_n^{arch}` for all `n`** (standard Bombieri–Lagarias),
with `λ_n^{arch}` the explicit Γ-factor/trivial-zeros term (DeWitt's `σ_k^{arch}` fed through the *linear*
Keiper transform — **not** the nonlinear chain) and `λ_n^{prime}` the `S(T)` fluctuation. **This** is where the
arch/prime separation is clean and the explicit archimedean baseline `−λ_n^{arch}` is the handle.

**What survives (two distinct valid RH-equivalents — do not merge them).**
1. **Linear λ_n / Bombieri–Lagarias** (`λ_n^{prime}≥−λ_n^{arch}`): exact additive arch/prime split; the right
   coordinate for DeWitt's explicit subtraction.
2. **Chain / Wall–Chihara** (`Σj(j+1)e_j<(n+1)/4`, the parabolic-Riccati form): a separate valid RH-equivalent
   (Li-positivity ⟺ chain persistence), but **nonlinear** in the moments — it does **not** carry the additive
   split. Its value is the parabolic-edge geometry, not an arch/prime decomposition.

My error was applying the *linear* BL split to the *nonlinear* chain. The convergence insight (smooth content is
archimedean Γ/θ; fluctuation is prime `S(T)`) is correct; only its expression in the chain coordinate was wrong.
**Actionable target unchanged in substance:** bound the prime fluctuation against the explicit archimedean
baseline — but in the **linear λ_n coordinate** (`λ_n^{prime}≥−λ_n^{arch}`), where DeWitt's `λ_n^{arch}` applies.

## Log (cont.)
- 2026-06-19 (Wheeler) — **CORRECTION 2 (mined my own error again): the chain does not split linearly.** The
  Chebyshev moment→Jacobi map is nonlinear (`β_1=m_2/m_0−(m_1/m_0)²`), so `σ=σ^{arch}+σ^{prime}` does NOT give
  `e_j=e_j^{arch}+e_j^{prime}` — **the split-form chain criterion (prev section) is withdrawn.** The arch/prime
  split is exact only in the **linear** `λ_n` coordinate: **RH ⟺ `λ_n^{prime}≥−λ_n^{arch}` ∀n** (standard
  Bombieri–Lagarias), with DeWitt's explicit `λ_n^{arch}` the handle. Two distinct RH-equivalents stand
  separately — linear BL (carries the split) and the nonlinear chain/Wall–Chihara (parabolic geometry, no
  split). The convergence insight (smooth=archimedean, fluctuation=prime `S(T)`) is correct; only its chain-coord
  expression was wrong. Target: `λ_n^{prime}≥−λ_n^{arch}` in the linear coordinate.

## HONEST TERMINUS of the chain/power-sum lane (DeWitt id=425) — converges to standard Bombieri–Lagarias — Wheeler, 2026-06-19

DeWitt's decisive catch, accepted: the power-sum chain is **not** the right coordinate for the arch/prime
subtraction.
- **`σ_k=Σ(¼+γ²)^{−k}` is `γ_1`-dominated** at large `k` (`~2(¼+γ_1²)^{−k}`, `γ_1≈14`), so the chain's smooth
  moment behavior is set by the **first zero / the seam**, NOT by the archimedean Γ-factor. There is **no
  archimedean smooth baseline** to subtract in the power-sum normalization.
- **The power-sum arch/prime split is seam-blocked** (Γ and ζ entangle at `s=0,1` — the F₁ archimedean seam
  itself, structural not bookkeeping; DeWitt's two attempts gave `1.86` and `−0.31`, both wrong for this reason).
- The clean B-L archimedean baseline exists **only in the LI `λ_n` coordinate** (`λ_n=Σ[1−(1−1/ρ)^n]`), a
  **different linear transform** than the power-sums — i.e. standard Bombieri–Lagarias, not this chain.

**Verdict.** Combined with the two prior self-corrections (the asymptotic `¼` is automatic; the nonlinear chain
does not split linearly), this lane's honest terminus is: **the power-sum chain / Wall–Chihara reformulation is
a VALID RH-equivalent (Li-positivity ⟺ chain persistence) that converges to standard Li/Bombieri–Lagarias with
NO archimedean-baseline advantage.** It is a kinship, not a crossing. The **one distinct, correct residue** is
the **parabolic-edge geometry** (§ "chain-persistence criterion, DERIVED": the no-margin is a parabolic fixed
point `g=½`, `(g−½)²=0`; the threshold `¼` is the discrete Hardy/Chihara oscillation constant) — banked as that,
a clean structural fact, nothing more. The archimedean-subtraction / split-form lines are **withdrawn**. The
actionable RH target is the **standard B-L `λ_n^{prime} ≥ −λ_n^{arch}`** in the Li coordinate (DeWitt/Professor's
lane), where the archimedean baseline is genuinely explicit. **Chain lane closed; do not re-extend it.**

## Log (cont.)
- 2026-06-19 (Wheeler) — **HONEST TERMINUS (DeWitt id=425): chain/power-sum lane closed, converges to standard
  B-L.** Power-sums `σ_k` are `γ_1`-dominated (no archimedean baseline in this normalization) and the split is
  seam-blocked (Γ/ζ entangle at `s=0,1`); the clean B-L baseline is the Li `λ_n` (different transform). Dropped
  the archimedean-subtraction/split-form idea. Net (with the two prior corrections): the chain is a valid
  RH-equivalent (Li-positivity ⟺ chain) with **no archimedean advantage** — kinship, not crossing. Distinct
  residue banked = the **parabolic-edge geometry** (no-margin = parabolic `g=½`; `¼` = discrete Hardy constant).
  Actionable target = standard B-L `λ_n^{prime}≥−λ_n^{arch}` (Li coordinate, DeWitt/Professor). Lane closed.
