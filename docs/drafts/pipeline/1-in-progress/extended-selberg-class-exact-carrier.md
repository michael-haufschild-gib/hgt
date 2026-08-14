# Exact extended Selberg-class carrier

- **ID:** `extended-selberg-class-exact-carrier`
- **Status:** Stage 1 — specification frozen; Lean implementation in progress
- **Novelty:** `[LITERATURE]` infrastructure
- **Sources:** Selberg's axioms; Kaczorowski–Perelli's standard definition of `S♯`; exact notation
  in arXiv:2405.03186, §§1–2
- **Role:** unavoidable concrete carrier for formalizing published twist frontier and Conjecture 3

## Representation

An extended Selberg datum consists of:

1. arithmetic coefficients `a : ArithmeticFunction ℂ`, not identically zero;
2. absolute convergence of `LSeries a` for every `Re(s)>1`;
3. `m : ℕ` and an entire finite-order function `H` such that, away from `s=1`,
   `F(s)=H(s)/(s-1)^m`, and this value equals `LSeries a s` on `Re(s)>1`;
4. concrete gamma data `Q>0`, finitely many `λ_j>0`, `Re(μ_j)≥0`, and root number `ω` with
   `|ω|=1`;
5. the functional equation for the concrete completed meromorphic function
   `Q^s ∏_j Γ(λ_j s+μ_j) F(s)`.

Meromorphic functions in Mathlib are total functions whose values at poles are irrelevant.
Accordingly, equality of functional equations is equality on the codiscrete filter; this identifies
the functions away from a discrete singular set and does not impose false values at poles.

## Exact finite-order predicate

For an entire `H`, finite order is represented by existence of real `A,B,ρ` with `A,B>0`, `ρ≥0`,
and

`|H(z)| ≤ A exp(B |z|^ρ)` for every `z∈ℂ`.

This is the standard global exponential-power characterization of finite order. The usual
large-radius definition is equivalent by enlarging `A` on a compact disk; that equivalence is a
required theorem, not an assumed interface.

## Derived invariants

For concrete gamma data:

- `degree = 2 ∑_j λ_j`;
- `conductor = (2π)^degree Q² ∏_j λ_j^(2λ_j)`;
- `internalShift = (2/degree) Im(∑_j μ_j)` when degree is positive, totalized to `0` at degree zero.

The values must initially be named *presentation* invariants. Calling them invariants of `F`
requires formal proof that two admissible gamma presentations give the same three values. This
gamma-presentation uniqueness theorem is a mandatory downstream gate; storing invariant values as
trusted fields is forbidden.

## Full Selberg-class extension

The exact `S` carrier extends `S♯` by:

1. `a(1)=1`;
2. Ramanujan: for every `ε>0`, `a(n)=O(n^ε)`;
3. concrete Euler-log coefficients `b(n)`, supported on positive prime powers;
4. `b(n)=O(n^θ)` for some `θ<1/2`;
5. absolute convergence of their L-series on `Re(s)>1` and
   `exp(LSeries b s)=F(s)` there.

Exponentiating the Euler-log identity avoids incorrectly identifying the analytic logarithm with
the principal branch of `Complex.log`.

## Hostile checks

- A totalized `F(1)` is never used to encode a pole; `H` carries the removable product.
- Gamma's totalized values at nonpositive integers are ignored by codiscrete meromorphic equality.
- Degree/conductor/internal shift are not silently assumed independent of gamma presentation.
- Functional equation, continuation, Ramanujan, and Euler product remain concrete formulas.
- No closure, classification, or twist theorem is a structure field.

## Gates

- [x] Primary-source axiom audit
- [x] Pole-safe representation chosen
- [x] Branch-safe Euler-log representation chosen
- [x] Core Lean definitions compile
- [x] Meromorphy of represented `F` and completed function
- [x] Equality/uniqueness of analytic continuation from coefficients
- [x] Finite-order characterization equivalence
- [ ] Gamma-presentation invariance of degree, conductor, internal shift
- [x] Exact `S` extension
- [ ] Product monoid and conjugation closure
- [ ] Primitive element/factorization definitions on semantic equality
