# The parity vortex of the squarefree Gibbs gas

- **ID:** `squarefree-gibbs-parity-vortex`
- **Stage:** 1-in-progress
- **Type:** THEOREM (new structural law) + OPEN CORE (infinite-volume seam-flux)
- **Parent:** `route-e-squarefree-exponential-gibbs-parity.md` (the (G2) card) — this card
  turns its asserted mechanism ("three primes destroy real stability; the attack must use
  the multiplicative cutoff boundary") into exact theorems and locates the seam-flux
  observable geometrically.
- **RH used:** no.  All theorems below are unconditional and finite.

## The object

For a finite set `S` of distinct primes (any pairwise-coprime integers ≥ 2 work), `x > 0`:

```text
P_S(z, x) := Σ_{T ⊆ S} z^{|T|} · exp(−x·Π_{p∈T} p),     k := |S|,  m := Π S.
```

This is the diagonal of the partition polynomial of the *multiplicative-energy* lattice
gas (energy of a configuration = product, not sum, of occupied primes — the Laplace/Gibbs
cutoff `e^{−nx}` of Route E).  Its parity point is `z = −1`:

```text
P_S(−1, x) = Σ_{n | m} μ(n) e^{−nx}   — the finite Möbius–Laplace current.
```

The (G2)/RH frontier is the `S → all primes` current at scale `x^{1/2}`.

## Theorems (paper proofs complete; dependency-closed)

**T0 (cutoff recursion).**  `P_{S∪{p}}(z, x) = P_S(z, x) + z·P_S(z, p·x)` for `p ∉ S`.
*Proof.* Split `T` by `p ∈ T`; `e^{−x·p·ΠT'} = e^{−(px)·ΠT'}`.  ∎
This is the "multiplicative cutoff boundary" of the parent card as an exact two-scale map:
adjoining a prime couples the ensemble to itself at the dilated scale `px`.

**T1 (two-prime Lee–Yang, all x).**  For distinct `p, q ≥ 2` the quadratic
`P_{p,q}(·,x)` has two distinct real negative roots for every `x > 0`:

```text
Δ₂ = (e^{−px} + e^{−qx})² − 4e^{−pqx} ≥ 4e^{−(p+q)x} − 4e^{−pqx} > 0
```

by AM–GM and `p + q < pq` (i.e. `(p−1)(q−1) > 1`).  ∎

**T2 (parity-jet law).**  Substituting `z = −1 + w`:

```text
P_S(−1+w, x) = Σ_T (w−1)^{|T|} e^{−x·ΠT};      at x = 0 this is  w^k;
∂_x|_{x=0} P_S(−1+w, x) = −Σ_T (w−1)^{|T|} ΠT = −Π_{p∈S} (p·w − (p−1)).
```

(The product identity is `Σ_T Π_{p∈T} a_p = Π_p (1+a_p)` at `a_p = p(w−1)`.)  Hence the
exact first-order law at the parity point:

```text
P_S(−1+w, x) = w^k − x·Π_{p∈S}(p·w − (p−1)) + R,   |R| ≤ (x²/2)·Π_p(1 + p²|w−1|),
```

using `0 ≤ e^{−u} − 1 + u ≤ u²/2`.  Consequences: the resolvent polynomial
`R_S(w) = Π(pw − (p−1))` has all roots real in `(1/2, 1)` at `w_p = 1 − 1/p`; its value at
the parity point is `R_S(0) = (−1)^k φ(m)` — **Euler's totient is the vortex intensity**:

```text
P_S(−1, x) = (−1)^{k+1} φ(m)·x + O(x²).
```

**T3 (parity-vortex theorem, k = 3).**  For any distinct primes `p, q, r` and all
sufficiently small `x > 0`, `P_S(·,x)` has exactly one real and two strictly complex
roots: writing `P_S(−1+w,x) = e₃w³ + e₂w² + e₁w + e₀`, the cubic discriminant obeys

```text
Δ(x) = −27·φ(pqr)²·x² + O(x³) < 0,
```

because `e₀ = φ(m)x + O(x²)`, `e₁ = −(3σ₃−2σ₂+σ₁)x + O(x²)`, `e₂ = (3σ₃−σ₂)x + O(x²)`,
`e₃ = 1 + O(x)`, so every discriminant monomial except `−27e₃²e₀²` is `O(x³)`.  A real
cubic with three real roots has `Δ = e₃⁴·Π_{i<j}(r_i−r_j)² ≥ 0` (Vieta ring identity), so
`Δ < 0` excludes any real factorization.  ∎

**T3′ (current–discriminant identity, exact).**  For the monic-normalized cubic jet,

```text
27·e₃²·e₀² = −Δ + 18·e₃e₂e₁e₀ − 4e₂³e₀ + e₂²e₁² − 4e₃e₁³ .
```

The squared parity current is an explicit polynomial in the higher jet and the
discriminant.  Real-rootedness (`Δ ≥ 0`) FORCES the current bound
`27e₃²e₀² ≤ 18e₃e₂e₁e₀ − 4e₂³e₀ + e₂²e₁² − 4e₃e₁³`; conversely a large current forces
`Δ < 0` — the vortex.  **Any lower bound on the cluster discriminant is an upper bound on
the parity current.**  This is the seam-flux observable in exact algebraic form: a
sign-definite functional (a discriminant — a squared zero-repulsion) that reads the
coherent current, structurally outside the mean-square σ-algebra.

**T4 (general k ≥ 3 vortex; Hurwitz form).**  Rescaling `w = x^{1/k}·ω`, the parity
cluster converges to the regular star `ω^k = (−1)^k φ(m)`: a `k`-gon of radius
`(φ(m)·x)^{1/k}` centered at the parity point, of which at most two vertices are real.
So for every `k ≥ 3` at least `k − 2` roots are strictly complex for small `x`: Lee–Yang
reality fails maximally — the parity point is a **vortex center of charge k**, not a
Lee–Yang point.

## What is new (relative to literature and corpus, July 2026)

- The Lee–Yang/primon-gas literature (Julia, Spector; Yang–Lee theory surveys) treats
  Dirichlet-weighted arithmetic gases `n^{−s}`, whose partition polynomials factor over
  primes and have trivially real zeros.  The Laplace-weighted (multiplicative-energy)
  gas does not factor; its parity-point zero geometry — the vortex law, the totient
  intensity, the current–discriminant identity — appears in no literature found.
- The corpus's (G2) card asserted "two-prime tables strictly Rayleigh, three primes
  destroy real stability" without proof.  T1/T3 prove the diagonal form exactly and
  identify the *mechanism*: the parity current itself is the obstruction
  (`Δ ≈ −27·current²`), and the failure is maximal (equiangular star), not marginal.
- Consequence for Route E: every real-stability / strong-Rayleigh / negative-dependence
  route to (G2) is dead structurally (not merely unverified): the parity evaluation
  point is a vortex center for `k ≥ 3`.  The surviving mechanism is exactly the T0
  two-scale recursion (the cutoff boundary) and the T3′ geometry: parity cancellation
  ⟺ zero-repulsion lower bounds at the parity cluster.

## [OPEN CORE]

The infinite-volume seam-flux law: a lower bound on the parity-cluster discriminant
(zero-repulsion) of the full ensemble `Σ_{n squarefree} z^{ω(n)}e^{−nx}` at scale `x`,
strong enough that T3′-type identities bound the current by `x^{1/2−ε}·Z(x)`.  At full
strength this is (G2) = RH; partial repulsion bounds give partial current bounds — a new
graded route whose rungs are geometric (cluster separations), not zero-free regions.

## Falsifiers / hostile tests

- T1–T3′ are finite and exact; any arithmetic error falsifies on a 3-prime instance.
- The vortex must NOT be an artifact of the diagonal: the multivariate polynomial already
  fails real stability at 3 primes (Rayleigh violation exists), consistent.
- If some literature source is found with the multiplicative-energy gas zero geometry,
  the novelty claim retracts to the current–discriminant identity and the Route E link.

## Log

- 2026-08-05 — card created; T0–T4 paper-proved (this card, self-contained); SOTA search
  (Lee–Yang × Möbius/squarefree; ω-generating polynomials): no overlap found.  Next:
  Lean formalization of T0, T1, T2 (eval-level), T3, T3′ (ring identities + limit-form
  discriminant negativity), unconditional.

## 2026-08-05 FORMALIZED: `RHTower/GibbsParityVortex.lean`

Wired into `RHTower.lean`; targeted build 8655 jobs; axioms only
`propext, Classical.choice, Quot.sound`; zero warnings.  Namespace `RHTower.GibbsGas`:

- `gibbsDiag` (the gas), `gibbsDiag_insert` (**T0**, the cutoff recursion),
  `gibbsDiag_zero` (free limit `(1+z)^k`), `gibbsDiag_singleton`;
- `hasDerivAt_gibbsDiag_parity` (**T2**, the parity-jet law: coupling-derivative
  `−∏(pw−(p−1))` at the shifted parity point) and `hasDerivAt_gibbs_current`
  (`(−1)^{k+1}∏(p−1)`: the totient intensity);
- `two_prime_real_rooted` (**T1**: explicit distinct real roots, AM–GM discriminant);
- `cubic_vieta` (Vieta from a pointwise factorization, by `linear_combination` at
  `w = 0, ±1`), `cubic_discrim_nonneg_of_real_rooted` (`Δ = a₃⁴·∏(rᵢ−rⱼ)²`),
  `current_sq_le_of_real_rooted` (**T3′**, the current–discriminant inequality);
- `parity_vortex_three` (**T3**: `∀ᶠ x in 𝓝[>]0`, no real factorization of the parity
  cubic — via `Δ(x) = x²·G(x)`, `G → −27φ² < 0` by slope limits, and the Vieta
  discriminant identity).

Lean traps: `set`-bound reals are opaque to `ring` (unfold with the defining equation
before `convert`-free value rewrites); a `HasDerivAt` chain's function/value trees must be
mirrored exactly (build the value by a `show ... from by ring` rewrite, not `convert`);
`Finset.sum` of function-valued summands needs `congr_of_eventuallyEq` + `Finset.sum_apply`
to become a `HasDerivAt` of the pointwise sum; `simp` leaves numerals like `−1−1+3−1`
unevaluated (finish with `norm_num`); `{q} ≠ insert q ∅` syntactically.

- 2026-08-05 — T0–T3′ formalized unconditionally; T4 (general k, Hurwitz form) remains
  paper-level on this card.
