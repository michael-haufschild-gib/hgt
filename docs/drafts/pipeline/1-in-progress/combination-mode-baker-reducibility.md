# Combination-mode reducibility genuinely needs no-resonance + Baker (the first C5 lead)

- **ID:** combination-mode-baker-reducibility
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (native C5 candidate) — with a proven supporting lemma (BRIDGE)
- **Priority:** FOUNDATIONAL
- **Source:** the combination-mode criterion of `../2-fully-proven/erosion-cocycle-reducibility.md` + ../../door/door-C5-irreducibility-and-door-2-retest.md · 00-status #112, #113
- **The test (from the user / the C5 criterion):** does a *combination-mode* object's cocycle /
  cohomology **genuinely** need (a) unique-factorization-no-resonance and (b) Baker's effective bound on
  linear forms in `{log p}`? If yes, it is a real C5 candidate (Door-2-surviving) — unlike the
  axis-mode objects (§59, §60, the 19a cocycle) that decouple over primes.

---

## Step 1 — rule out the two obvious candidates

**Curvature `F_{pq}` (§16): FREE for the diagonal, no Baker.** For the rank-1 arithmetic module the
multipliers `A_p` are scalars depending on disjoint coordinates `x_p`, and `σ_p, σ_q` act on disjoint
coordinates, so `σ_q(A_p) = A_p` and `F_{pq} = A_q^{-1}σ_q(A_p)^{-1}A_pσ_p(A_q) = 1`. The connection is
**flat automatically** — the dilations commute because they live on independent circles. So flatness is
free and engages nothing arithmetic. (The hard `H²` class is the *monoidality* `ω` of G4, a different
object — not a clean Baker test.) **F_pq fails the test.**

**Rankin–Selberg `log L(s, π×π′)`: AXIS-mode, no Baker.** `log` of any Euler product is a **sum** over
primes of single-prime local terms, so its Fourier support on `𝕋^∞` is axis modes `kδ_p`. It decouples
prime-by-prime exactly like the 19a cocycle ⟹ BRIDGE. The combination modes of RS live in the
*product/moment* (`|L|²`, `ζ(s)ζ(s+α)` — convolution coefficients `d(n)`), **not** in `log L`. **RS-log
fails the test.**

> Lesson: "combination mode" is necessary but not sufficient. The axis/all-positive modes (`kδ_p`,
> `δ_p+δ_q`) have frequencies `≥ log 2` — no small divisors. Baker only bites on **mixed-sign** modes.

## Step 2 — the right object: mixed-sign combination modes (the near-resonances `p^a ≈ q^b`)

A mode `m = aδ_p − bδ_q` has frequency `m·ℓ = a log p − b log q = log(p^a/q^b)`, which is **small** when
`p^a ≈ q^b` (e.g. `2^{19}/3^{12} = 524288/531441`, `|m·ℓ| ≈ 0.0135`). These mixed-sign modes are exactly
the **near-resonances**, and they are precisely the modes the additive/diagonal/Euler observables never
carry. The relation lattice `Λ = {m : m·ℓ = 0}` is `{0}` (unique factorization), but the *near*-zero
values of `m·ℓ` are governed by Baker.

**Observable.** Fix an analytic `g` on `𝕋^∞` with Fourier support on a sequence of mixed-sign
combination modes `m^{(j)}` and coefficients `ĝ(m^{(j)}) = e^{-ρ|m^{(j)}|}` (`|m| = Σ_p |m_p|`),
`ĝ(0)=0`. Cohomological equation over the prime-frequency Kronecker flow: `Dh = g`, i.e.
`ĥ(m) = ĝ(m)/(i\,m·ℓ)`.

## Step 3 — Theorem (proven): Baker is load-bearing

> **Lemma R.** With `ω = (log p)_p`: (i) `m·ℓ ≠ 0` for all `m ≠ 0` (unique factorization) — so `ĥ(m)`
> is *defined*; (ii) `|m·ℓ| ≥ γ·H(m)^{-κ}` with `H(m)=max(3,\max_p|m_p|)` and effective `γ,κ`
> (**Baker / Baker–Wüstholz**, lower bound for linear forms in logarithms of the primes in the finite
> support). Hence for the analytic `g` above, `‖h‖²_{L²} = Σ_j e^{-2ρ|m^{(j)}|}/(m^{(j)}·ℓ)² ≤
> γ^{-2} Σ_j e^{-2ρ|m^{(j)}|} H(m^{(j)})^{2κ} < ∞` — `h` exists (analytic, smaller radius). The cocycle
> is reducible. **Conversely, replace `ω` by a Liouville-independent vector `ω′` (same modes): one can
> force `|m^{(j)}·ω′| ≤ e^{-|m^{(j)}|²}` along a subsequence, whence the term
> `e^{-2ρ|m^{(j)}|}·e^{2|m^{(j)}|²} → ∞` and `h ∉ L²` — the cocycle is NOT reducible.**

*So the very same combination-mode cohomological equation is solvable for the prime frequencies and
unsolvable for Liouville frequencies. The difference is exactly Baker's effective bound.* **Both** test
criteria are load-bearing: (a) unique factorization to *divide* (`m·ℓ ≠ 0`), (b) Baker to keep the
quotient *summable* (`|m·ℓ|` not super-exponentially small). ∎

This is the **first object in the programme where Baker is genuinely load-bearing** — in sharp contrast
to §59/§60 and 19a, where the qualitative `Λ={0}` sufficed and no effective bound was ever needed.

## Step 4 — Door-2 verdict, split by base size

- **Finite base (finitely many primes):** Lemma R is the classical `𝕋^d` small-divisor / cohomological
  lemma (Herman/KAM/Avila reducibility) with the Diophantine condition *supplied by* Baker. Proof =
  `𝕋^d` harmonic analysis (parent) + Baker (parent). Two parents combined ⟹ **BRIDGE** — but a *deeper*
  bridge than the axis-mode ones: it is the first that engages Baker, and finite-`d` KAM does prove it.
- **Infinite base (all primes), uniform:** a single `h` must handle the **infinitely many** combination
  modes at once, under a **uniform** Baker bound across all primes. Finite-`d` KAM does **not** reach
  this — infinite-dimensional small divisors with the arithmetic frequency vector `(log p)_p` are no
  parent's theorem (single-`q` Mahler: one base; differential Galois: wrong category; `𝕋^∞` harmonic
  analysis: has the modes but not the arithmetic Diophantine input; Baker: no dynamics). This is the
  **Door-4 native zone** (infinite ∩ difference ∩ multi-base).

## The C5 candidate (precisely stated, OPEN)

> **Conjecture C5★ (infinite-base Baker–KAM reducibility).** There is a class of combination-mode
> cocycles over the `𝕋^∞` prime-frequency Kronecker flow that are **uniformly reducible** (a single
> transfer function `h` of controlled regularity solving `Dh=g` across all primes), and the proof
> **requires the uniform Baker bound** `|Σ_{p∈S} m_p log p| ≥ γ·H(m)^{-κ}` holding with constants
> controlled as `|S|→∞`. No single parent proves it: it is `𝕋^∞`-infinite-dimensional KAM glued to
> Baker via the field's native frequency vector. *If proven with Baker essential and the infinite-base
> uniformity irremovable, this is a NATIVE (C5) theorem — the first.*

**Why this is the right shape for C5:** it is the only place so far where (i) the object is genuinely
combination-mode (cross-prime, not decoupling), (ii) Baker is *provably* load-bearing (Liouville
counterexample), and (iii) the infinite-base uniformity puts it outside every single parent. It uses
the `σ_p` **jointly** (mixed-sign cross-prime modes) and **irreducibly** (the infinite-d uniform
Diophantine control).

---

## C5★ attacked (2026-06-19): the uniform-Baker obstruction forces bounded degree

**Part 1 — uniform control FAILS for unbounded support (rigorous).** Two facts collide.
- *Dirichlet pigeonhole (divisors are exp-small in `|m|`).* Fix a support `S`, `|S| = s`. Among the
  `N^s` exponent vectors with `|m_p| ≤ N`, the values `m·ℓ = Σ_{p∈S} m_p log p` lie in an interval of
  length `≤ 2N Σ_{p∈S} log p`; two coincide to within `N^{-s}` of it, so their difference `m` (support
  `⊆ S`, `|m| ≤ 2Ns`) has `|m·ℓ| ≤ C·N^{-s} = C·e^{-(|m|/2N)\log N}` — **exponentially small in `|m|`.**
  So `(log p)_∞` is **not polynomially Diophantine** over unbounded-support modes: no fixed exponent `τ`
  makes `|m·ℓ| ≥ γ|m|^{-τ}` hold for all `m`.
- *Baker only degrades.* Baker–Wüstholz gives `|m·ℓ| ≥ exp(−C(s)·∏_{p∈supp}log p·log B)`, but the
  constant `C(s)` grows **super-exponentially** in the number of logs `s` (it carries `s!` and `s^{s}`
  factors), and the height product `∏ log p` grows too.

Standard KAM / cocycle reducibility needs a **fixed-exponent** Diophantine condition; by the above it
**fails for `(log p)_∞` over unbounded support.** *So the naive C5★ (infinite-support uniform
reducibility) is unprovable by KAM and effectively false — the erosion→reducibility picture breaks at
unbounded-support modes.* This is itself a native-zone finding: **the infinite base is the obstruction**,
not removable by any finite-`d` parent.

**Part 2 — the pin: C5★ must be BOUNDED-DEGREE.** Restrict to modes of support `≤ d`. Then the number of
logs is bounded (`s ≤ d`), `C(s) ≤ C(d)` is fixed, and only the heights `log p` grow — the
single-exponential regime where Baker is usable. So the correct C5★ carrier is a **bounded-degree**
cohomology/cocycle, with `d → ∞` taken *after* the Diophantine control, not inside it.

**Part 3 — the tension (the real crux, OPEN).** The two natural bounded-degree carriers pull apart:
- **Curvature `F_{pq}` / `H²` (degree 2):** bounded-degree ✓, but `F_{pq} = 1` (flat) for the rank-1
  diagonal `ζ` — trivial/free, RH-irrelevant; nontrivial only for higher-rank (automorphic) modules.
- **Rankin–Selberg moment (`|ζ|²`, `ζ(s)ζ(s+α)`):** RH-relevant ✓, but its modes `log(m/n)` have
  **unbounded support** (composite `m,n`).

The open problem is a **bounded-degree, RH-relevant, nontrivial** cocycle. The natural reconciliation is
the **degree-`d` Jensen / finite-free section** of `Ξ` (`finite-free-convolution-flow.md`,
SEED-AB): bounded degree `d` by construction (Baker uniform, `s ≤ d`), real-rootedness preserved by `⊞_d`
(MSS), additive cumulants `κ_k = Σ_p κ_k(p)`; reducibility = the `d → ∞` stability of the finite-free
fixed point. **Refined C5★:** *the degree-`d` finite-free section cocycle is reducible, with the
`d → ∞` limit controlled by Baker on the (bounded-`d`) combination modes.*

**Part 4 — RH/G2 relevance.** The Baker-controlled near-resonances are the **G2 multiplicity estimate /
#72 "Liouville substitute"** in dynamical dress: a relation among the zeros pushes (Weil explicit
formula) to a prime-side relation `Σ m_p log p ≈ 0`, which Baker forbids from being too small. So
combination-mode Baker reducibility **is** the prime-side non-resonance blocking accidental `ℚ`-relations
among `{γ_n}` — the dynamical face of DSS/G2. That is where it is RH/G2-relevant.

**Door-2 (refined).** Finite degree `d`: field's `H²`/finite-free + Baker + (for summability over pairs)
prime-gap density — a parent-combination, sophisticated **BRIDGE**. The `d → ∞` *uniform* limit, where
bounded-degree control must survive the infinite-base passage with the heights growing, is the
native-zone candidate — **still open**, now sharply located at the bounded-degree↔RH-relevance tension.

## Carrier pinned (2026-06-19): the finite-free/Hankel section + the Baker verdict

The refined-C5★ carrier is now pinned — full statement in `finite-free-convolution-flow.md`. Summary:
- **The object.** The degree-`d` finite-free (Jensen/Hankel) section of `Ξ`. Its power-sums `P_k` are
  **axis-mode** (one prime per Fourier mode), but real-rootedness ⟺ the **Hankel form `H_d=(P_{i+j})` PSD**,
  and `det H_j` is a degree-`j` polynomial in the `P_k` ⟹ the reducibility condition carries **mixed-sign
  combination modes of support `≤ d`.** "Bounded degree" = polynomial degree `d` = max combination-mode support.
- **Tension resolved.** It is **bounded-degree ∧ RH-relevant** at once (RH ⟺ all sections hyperbolic,
  Pólya–Jensen / GORZ) — RH-relevance enters through the **nonlinear PSD condition**, which is why the flat
  linear `F_{pq}` missed it and the unbounded-support RS moment was the wrong axis.
- **Baker-necessity verdict.** Split into **bulk** (moments concentrate by the finite-free CLT — soft,
  BRIDGE) and **edge** (`det H_d = 0`, where the degenerations = zeros live — 19b / FHK). At **each fixed
  `d`** Baker is load-bearing on the edge (fixed `#`-logs ⟹ fixed Diophantine exponent `κ_d` ⟹ the
  bounded-support small-divisor sum converges; the Liouville substitute diverges — Lemma R at bounded
  support). The **`d → ∞`** uniform edge control needs **more than Baker**: Baker's floor degrades
  super-exponentially, so the limit is governed by the **near-zero distribution of bounded-support
  `{Σ a_p log p}`** — strictly stronger than the floor. **That metric statement about `⟨log p⟩` is the
  native C5 crux.**
- **Answer to the test.** Yes — `d → ∞` reducibility genuinely needs the bounded-degree Baker control (no
  single parent supplies the edge at any `d`); Baker is necessary but not sufficient for the uniform limit.
  GORZ = the bulk half proven; the C5 crux = the uniform edge half.

## Gates
- [x] 0 → 1  in-progress: object identified; Lemma R (Baker load-bearing, finite base) **proven** with
  a Liouville counterexample; C5★ stated, attacked, and **refined to bounded degree** (Part 1 killed the
  naive infinite-support version).
- [ ] 1 → 2  fully-proven: the naive infinite-support C5★ is **killed** (Part 1); the live target is the
  **bounded-degree** C5★ (degree-`d` finite-free section, `d → ∞`), still open.
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Next steps
1. ~~Make the uniform Baker constants explicit~~ **DONE (2026-06-19):** they do **not** control —
   `C(s)` is super-exponential in support size and `(log p)_∞` is not polynomially Diophantine over
   unbounded support (Part 1). Naive infinite-support C5★ is dead; **bounded degree is forced.**
2. ~~Resolve the bounded-degree ↔ RH-relevance tension (Part 3)~~ **DONE (2026-06-19):** carrier pinned
   as the **degree-`d` finite-free / Hankel section** (`finite-free-convolution-flow.md`) — bounded-degree
   ∧ RH-relevant; reducible at each fixed `d` (Baker load-bearing on the edge). The **live native crux** is
   now the `d → ∞` uniform edge control = the **near-zero distribution of `{Σ_{|S|≤d} a_p log p}`** beyond
   Baker's floor.
3. **Track `C(d)` and the height growth** so the `d → ∞` passage is uniform — the irremovable
   infinite-base step (the Door-2 native crux). Numerically: compute the smallest `|Σ_{p∈S} m_p log p|`
   over bounded `S, |m|` (runpod) to see the degradation rate empirically.

## Log
- 2026-06-19 — created in 1-in-progress. Ran the test: `F_pq` (flat/free) and RS-`log` (axis-mode) do
  NOT need Baker; the right object is **mixed-sign combination-mode** cohomology. Proved **Lemma R**
  (Baker load-bearing for combination-mode reducibility, finite base, with Liouville counterexample) —
  the first place Baker bites. Stated the native **C5★** candidate (infinite-base uniform Baker–KAM
  reducibility) and the finite/infinite Door-2 split (BRIDGE / native-zone).
- 2026-06-19 — **C5★ attacked.** Part 1 (rigorous): uniform Baker control FAILS for unbounded support
  (super-exp `C(s)`; Dirichlet pigeonhole ⟹ `(log p)_∞` not polynomially Diophantine), so naive
  infinite-`d` KAM is dead and **bounded degree is forced.** Pinned the carrier to bounded-degree
  cohomology; found the **bounded-degree ↔ RH-relevance tension** (curvature flat-for-ζ vs RS-moment
  unbounded-support), with the **degree-`d` finite-free section** the candidate resolution. G2 link:
  combination-mode Baker = the #72 Liouville substitute. Refined C5★ = bounded-degree, still open.
- 2026-06-19 — **carrier pinned.** The refined-C5★ carrier is the **degree-`d` finite-free/Hankel
  section** of `Ξ` (`finite-free-convolution-flow.md`, moved to 1-in-progress): power-sums axis-mode,
  Hankel-PSD reducibility condition combination-mode (support `≤ d`) — **resolves the Part-3
  bounded-degree↔RH-relevance tension.** Baker-necessity **verdict** (bulk/edge split): load-bearing at
  every fixed `d`, the `d → ∞` limit governed by the near-zero distribution of bounded-support
  `{Σ a_p log p}` beyond Baker's floor (the native crux). GORZ = bulk half; crux = uniform edge half.
