# Dirichlet Series with Infinite Prime Support → HT (Resonance Theorem)

- **ID:** dirichlet-prime-resonance-ht
- **Stage:** 3-formalized (not new scientific knowledge; zeta application machine-checked 2026-07-12)
- **Type:** CANDIDATE THEOREM [CONJECTURE + COMPLETE PROOF SKETCH]
- **Source:** Wheeler, 2026-06-24 (resonance argument, corrected version)

## Statement

**Theorem (Resonance Obstruction):** Let f(s) = Σ_{n=1}^∞ a_n n^{-s} be a Dirichlet series
converging absolutely for Re(s) > σ₀, with a_1 = c ∈ ℂ and a_p ≠ 0 for infinitely many
primes p. Then f is hypertranscendental (satisfies no polynomial algebraic differential
equation P(s, f, f', ..., f^{(n)}) = 0 over ℂ[s]).

**Application to ζ:** ζ(s) = Σ_{n=1}^∞ n^{-s} has a_p = 1 ≠ 0 for ALL primes p, so ζ
is HT. **The proof uses only:**
1. Fundamental Theorem of Arithmetic (unique factorization)
2. Euclid: infinitely many primes
3. Polynomial algebra (infinitely many roots → zero polynomial)

No Baker's theorem, no functional equation, no Nevanlinna theory.

## Proof (complete, elementary)

Let f = c + u where u(s) = Σ_{n: a_n≠0, n≥2} a_n n^{-s}. Note u → 0 as Re(s) → +∞
(absolute convergence). Similarly f^{(k)} → 0 for k ≥ 1.

**Assume** P(s, y₀, y₁, ..., y_n) is a polynomial of degree D with P(s, f, f', ..., f^{(n)}) = 0
for all Re(s) > σ₁ (some large σ₁).

Taylor-expand P around the background point (y₀, ..., y_n) = (c, 0, ..., 0):

  P(s, c + u₀, u₁, ..., u_n) = L₀(s) + L₁(s; u) + L₂(s; u) + ... + L_D(s; u)

where L_k is the degree-k homogeneous part in u = (u₀, u₁, ..., u_n), with u_j = f^{(j)}(s)
(all → 0). The coefficients of L_k are polynomials in s.

**Step 0 (zeroth order):**
The zeroth-order term L₀(s) = P(s, c, 0, ..., 0) is a polynomial in s alone. Since
P(s, f, ...) = L₀ + (exponentially decaying terms) = 0, and a polynomial in s with
exponentially decaying corrections must be zero: L₀(s) ≡ 0.

**Step 1 (prime isolation, zeroing L₁):**
For any prime p with a_p ≠ 0, consider the coefficient of p^{-s} = e^{-s log p} in
P(s, f, f', ..., f^{(n)}).

**Key: the coefficient of p^{-s} in L_k is ZERO for all k ≥ 2 when k ≤ D.**

Proof: L_k involves products of k copies of correction terms. A correction term at rate
e^{-s log n} (with n ≥ 2) contributes to rate e^{-s(log n₁ + ... + log n_k)} = e^{-s log(n₁···n_k)}
from a product of k terms. To get rate e^{-s log p} from k ≥ 2 factors: need n₁···n_k = p.
Since p is prime and all n_i ≥ 2, no such factorization exists. ∎

So the coefficient of p^{-s} in P(s, f, ...) comes ENTIRELY from L₁:

  [p^{-s} coefficient]: Σ_j (∂P/∂y_j)|_{(s,c,0,...,0)} · a_p · (-log p)^j = 0

Since a_p ≠ 0, the polynomial in (log p):

  Q(λ) := Σ_j (∂P/∂y_j)|_{background} · (-λ)^j = 0

at λ = log p for infinitely many primes p. Since Q has degree ≤ n and has infinitely many roots:
Q ≡ 0, i.e., (∂P/∂y_j)|_{background} ≡ 0 (as a polynomial in s) for j = 0, ..., n.
Therefore **L₁ ≡ 0**.

**Step k (induction, zeroing L_k):**
Inductive hypothesis: L₁ = L₂ = ... = L_{k-1} = 0.

For k distinct primes p₁ < p₂ < ... < p_k (all with a_{p_i} ≠ 0), consider the coefficient of
(p₁p₂···p_k)^{-s} in P(s, f, ...).

**Claim:** After L₁ = ... = L_{k-1} = 0, this coefficient comes ENTIRELY from L_k.

Proof: The contribution from L_j (for j < k) to rate log(p₁···p_k) requires j Dirichlet
factors multiplying to n₁···n_j = p₁···p_k. Each n_i ≥ 2. Since j < k and each factor
contributes at least a factor of 2 (so n₁···n_j ≥ 2^j), this is achievable — for example
n₁ = p₁···p_k (using the Dirichlet term of f directly). But this contribution is killed by
L_j = 0 for j < k (the L_j coefficient function is zero).

More precisely: the L_j term with j < k, contributing at rate (p₁···p_k)^{-s}, requires
choosing j Dirichlet factors whose rates sum to log(p₁···p_k). The corresponding coefficient
involves L_j evaluated on those factors — which is 0 by induction hypothesis. ∎

So after L₁ = ... = L_{k-1} = 0, the coefficient of (p₁···p_k)^{-s} is:

  [coefficient]: Σ_{r₁,...,r_k} (∂^k P / ∂y_{r₁}···∂y_{r_k})|_{background}
                · a_{p₁} · (-log p₁)^{r₁} · ... · a_{p_k} · (-log p_k)^{r_k} = 0

Define the symmetric multilinear form:
  M_k(λ₁, ..., λ_k) := Σ_{r₁,...,r_k} (∂^k P / ∂y_{r₁}···∂y_{r_k})|_{background}
                       · (-λ₁)^{r₁} · ... · (-λ_k)^{r_k}

The constraint is: M_k(log p₁, ..., log p_k) = 0 for all k-tuples of distinct primes
(p₁, ..., p_k) with a_{p_i} ≠ 0.

**Zeroing M_k by sweeping:** M_k(λ₁, ..., λ_k) is a polynomial in (λ₁, ..., λ_k) of degree ≤ n
in each variable. Fix λ₂ = log p₂, ..., λ_k = log p_k. Then M_k(λ₁, log p₂, ..., log p_k) is a
polynomial in λ₁ of degree ≤ n with infinitely many roots {log p₁ : p₁ ≠ p₂,...,p_k prime,
a_{p₁}≠0} (there are infinitely many such p₁ by assumption) → M_k(·, log p₂,...,log p_k) ≡ 0.

So each coefficient (as a polynomial in s) of λ₁^j in M_k(λ₁, log p₂,...,log p_k) is 0.
These coefficients are polynomials in (log p₂, ..., log p_k) with infinitely many roots
{(log p₂, ..., log p_k) : distinct primes}. By induction on k (sweeping each variable),
all coefficients of M_k vanish → M_k ≡ 0 → **L_k ≡ 0**.

**Conclusion:**
By induction from k = 1 to k = D: L₁ = L₂ = ... = L_D = 0.
Together with L₀ = 0 (Step 0): P = L₀ + L₁ + ... + L_D = 0. Contradiction with P ≠ 0. ∎

## What makes this work (structural insight)

**Prime isolation (Step 1):** Primes cannot be multiplicatively decomposed into factors ≥ 2.
This makes the p^{-s} term in a Dirichlet series "invisible" to nonlinear polynomial ODE
cross-terms at the first order. This is EXACTLY the arithmetic structure that ζ's Euler
product encodes.

**Inductive layer stripping (Step k):** After zeroing lower-order terms, the k-almost-prime
rate (p₁···p_k)^{-s} is "clean" — visible only to the L_k term. The lower-order terms are
killed by induction, not by arithmetic isolation.

**Polynomial finiteness:** P has finite degree D. The induction terminates at k = D. ∎

## What does and does NOT use Baker's theorem

- Baker's theorem is NOT used. The argument uses only:
  - FTA (unique factorization)
  - Euclid (infinitely many primes)
  - Polynomial algebra
- Baker would be needed for a different argument (e.g., showing {log p} are Q-linearly
  independent). Here we don't need Q-linear independence — just infinitely many distinct
  prime-level exponential rates.

## Applications

1. **ζ(s):** a_p = 1 for all primes → HT. Elementary proof from Euler product structure.
2. **Dirichlet L-functions:** L(s, χ) = Σ χ(n) n^{-s} has χ(p) ≠ 0 for all p ∤ q (where q
   is the conductor). So infinitely many prime coefficients are nonzero → L(s, χ) is HT.
3. **Dedekind zeta functions:** ζ_K(s) = Σ N(a)^{-s} (sum over nonzero ideals of a number field
   K); for any prime p ∈ ℤ, the ideal (p) factors in O_K, giving terms p^{-s} (or p^{-2s}
   etc.). If infinitely many primes split completely in K (always true), we get infinitely many
   prime-level terms → ζ_K is HT.
4. **Selberg zeta functions:** Z_Γ(s) = Π_γ (1 - N(γ)^{-s}) where γ ranges over primitive
   closed geodesics. If the geodesic lengths {log N(γ)} are Q-linearly independent (Selberg
   spectral independence conjecture), same argument applies with geodesic lengths playing the
   role of log p.

## Comparison to Turing's linear-subcase result

Turing (id=1951) settled the linear case of the spectral-rank barrier via classical Newton-polygon
asymptotics: linear order-n ODE → finitely many Newton-polygon slopes → finitely-generated frequency
module. This uses LINEAR asymptotic theory.

The resonance argument is DIFFERENT: it handles all-order POLYNOMIAL ODEs directly, without
passing through asymptotics or Newton polygons. It works at the level of Dirichlet series
expansion, not formal Newton-Puiseux expansion. Complementary, not redundant.

## Status of ζ(s) HT in the literature

[OPEN QUESTION] Is ζ(s) HT (no polynomial ODE of any order) a known result or an open problem?
Known facts:
- ζ not D-finite (no linear ODE): PROVED (classical)
- ζ not order-1 DA: likely follows from Malmquist/Steinmetz, needs source check
- ζ HT (all orders): STATUS UNCERTAIN — needs literature verification.

If ζ HT is OPEN: the resonance theorem is a major new result.
If ζ HT is KNOWN: the resonance theorem gives a new elementary proof + the general obstruction
certificate for all Dirichlet series with infinite prime support.

## Gate to 2-fully-proven

[x] Proof sketch complete (Steps 0-k, induction, contradiction)
[ ] Verify Step k induction is fully rigorous (the "sweeping" argument in multiple variables)
[ ] Literature check: is ζ HT already proved? What method?
[ ] Formalize: handle the convergence (replacing "Re(s) large" by "on the half-plane Re(s) > σ₀")
[ ] Check: does the argument extend to Dirichlet series with finitely many nonzero prime terms?
    (Answer should be: NO — finite prime support → DA is possible. Need to verify this boundary.)
[ ] Second agent verification (Turing or Professor)

## Log

- 2026-06-24 Wheeler: opened. Original formulation in id=1952 had gap (claimed Q-independence needed;
  actually only FTA needed). Corrected in id=1955 (pointed toward correction) and in this card.
  Proof by induction: Step 1 (prime isolation) → Steps 2...D (inductive layer stripping) → P≡0.

## 2026-06-24 Haiku literature/audit note: zeta HT is known; resonance theorem must be graded as a proof method

First-pass literature check shows that the application `zeta is HT over C(s)` is
not open. Cambridge's abstract for Nagoshi, *Hypertranscendence of L-functions
for GL_m(A_Q)*, explicitly says it generalizes Hilbert's result asserting that
the Riemann zeta function is hypertranscendental over `C(s)`, and that the paper
also extends Ostrowski's result on ordinary Dirichlet series. MathOverflow and
recent zeta/gamma differential-equation papers point to the same Hilbert/Ostrowski
line.

Therefore this card cannot be promoted on the basis that it proves zeta HT. Its
possible value is narrower:

1. a short elementary proof method for a known theorem;
2. a generalized resonance obstruction for a stated class of Dirichlet series;
3. a source/landscape lesson: infinite prime support obstructs finite algebraic
   differential flow.

Technical audit of the proof sketch:

- The induction idea is plausible, but the write-up still needs a rigorous
  uniqueness lemma for generalized Dirichlet series with polynomial-in-`s`
  coefficients after products are expanded.
- In Step `k`, the coefficient at `(p_1...p_k)^(-s)` from `L_k` is clean only
  because the primes are distinct and there are exactly `k` nontrivial factors;
  this should be stated as the squarefree `k`-prime isolation lemma.
- The theorem should explicitly exclude conclusions stronger than the coefficient
  hypotheses allow. If coefficients at infinitely many primes vanish, the proof
  sees only the infinite nonzero-prime support.

Corrected status: keep `1-in-progress`; downgrade novelty of the zeta application
to `known/import`. The anti-theatre value, if any, is the resonance certificate
as a compact proof pattern, not the result `zeta is HT`.

Sources checked: Nagoshi 2016, Cambridge Core abstract/refs; MathOverflow reference
thread on zeta differential equations; Li--Ye 2010 metadata and related zeta/gamma
algebraic differential-equation literature.

## 2026-07-12 Card closure: zeta application fully formalized, machine-checked

The Lean kernel now plays the role of the second-agent verification, and every open
mathematical gate of the card is settled for the zeta application.

`[PROVED IN LEAN, axiom-clean]` **`GaloisForLFunctions.hypertranscendental_riemannZeta`** —
`Hypertranscendental riemannZeta` (no algebraic differential equation over `ℂ[s]`, any order),
unconditional, depending only on `propext, Classical.choice, Quot.sound`. This is the first
concrete unconditional `Hypertranscendental` instance in the tree; the definitional frontier that
`Hypertranscendence.lean` set up is now inhabited by the actual ζ.

Three new modules:

1. `LSeriesPolynomialWeightUniqueness.lean` — the uniqueness backbone the audit demanded
   ("rigorous uniqueness lemma for generalized Dirichlet series with polynomial-in-s
   coefficients"): `lseries_polyWeightFamily_coeff_eq_zero`. A finite family
   `Σ_a x^a·L(g_a)(x) = 0` on a real ray kills every coefficient, by pinned-index peeling with
   the exponential domination `‖n^x·L(g)(x) − g n‖ ≤ C·(n/(n+1))^x`, which beats every
   polynomial weight.
2. `ZetaJetExtraction.lean` — the resonance engine, in coefficient space and sharper than the
   card's sketch: no multivariable "sweeping" is needed. `jetProd_family_coeff_eq_zero`: a
   finite combination of Dirichlet products of jet atoms `(log n)^j·1_{n≥2}` vanishing at every
   positive integer has zero coefficients. Mechanism per layer `k`: a product of `k` atoms
   vanishes below `k` prime factors (with multiplicity); at `n = q·m` with `q` prime, `q ∤ m`,
   `Ω(n) = k`, the product is a polynomial in `log q` whose coefficients are the peeled products
   at `m` (`jetProd_apply_prime_mul`); primes give infinitely many roots, so the layer reindexes
   to strictly smaller multisets. The squarefree hypothesis of the sketch is not needed — the
   count `Ω` alone drives the induction.
3. `ZetaHypertranscendental.lean` — assembly: value-slot shift `y₀ ↦ 1 + y₀`, jets of
   `ζ − 1` as `(−1)^j·L((log·)^j·1_{≥2})` via mathlib's `LSeries_iteratedDeriv`, monomialwise
   expansion into the polynomially weighted family, uniqueness, extraction, contradiction.

Gate answers:
- Step-k rigor: settled by the machine-checked slot-peeling induction (stronger than the sketch).
- Convergence handling: settled — everything runs at `x ≥ 2` on the real ray with explicit
  summability at `x₀ = 2`.
- Finite-prime-support boundary `[SEARCH]`: sharp as expected — `f = (1 − 2^{−s})^{−1}` has
  finite prime support and IS differentially algebraic (`u = 2^{−s}` solves `u' = −(log 2)u` and
  `f` is rational in `u`), so infinite support is essential to the obstruction.
- Literature: the zeta statement is Hilbert/Stadigh/Ostrowski — KNOWN; graded not-new. The value
  banked here is the elementary method made fully rigorous plus, to our knowledge, the first
  machine-checked hypertranscendence proof of a concrete named function.

The general resonance class (arbitrary Dirichlet series with infinitely many nonzero prime
coefficients) remains paper-level and reduces to Ostrowski 1920; no separate promotion.

## What this opens

The engine is reusable: `jetProd_family_coeff_eq_zero` is stated for arbitrary finite
combinations of jet monomials, so hypertranscendence of further concrete Dirichlet series
(Dirichlet L-functions via twisted atoms, Dedekind zetas via split primes) is now an
atom-swap away rather than a new proof. The genuinely open direction stays the non-Dirichlet
carriers: geodesic-length "primes" (Selberg zetas), where unique factorization must be replaced
by a length-spectrum independence input.

## Gates (updated)

[x] Proof sketch complete
[x] Step k induction rigorous — machine-checked, sweeping eliminated
[x] Literature check — ζ HT known (Hilbert/Ostrowski line); graded not-new
[x] Formalize with convergence — three modules, axiom-clean, lint green
[x] Finite-prime-support boundary — sharp, DA witness at single prime
[x] Verification — Lean kernel
