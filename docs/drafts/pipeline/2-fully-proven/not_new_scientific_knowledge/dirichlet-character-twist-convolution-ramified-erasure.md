# Dirichlet-character twist: convolution law and ramified erasure

## Status

- Pipeline: fully proven on paper
- Novelty: `[LITERATURE]` / `[REDISCOVERED]`
- Proof status: `[PAPER-PROVED]`
- Lean status: not yet formalized
- Role: exact algebraic prerequisite for Selberg Conjecture 3; not claimed as frontier progress

## Exact claim

Fix `q : ℕ`, a Dirichlet character `χ` modulo `q`, and complex-valued arithmetic
functions `f,g`.  Define coefficientwise twist

`T_χ(f)(n) = χ(n) f(n)`

and level-`q` depletion

`E_q(f) = T_1(f)`,

where `1` is the principal character modulo `q`.  Then:

1. `T_χ(f * g) = T_χ(f) * T_χ(g)` for Dirichlet convolution `*`;
2. `T_ψ(T_χ(f)) = T_(ψχ)(f)` for every character `ψ` modulo `q`;
3. `T_(χ⁻¹)(T_χ(f)) = E_q(f)`.

In particular, inverse twisting is not generally identity: it erases exactly coefficients at
integers whose residue class modulo `q` is not a unit (equivalently, those not coprime to `q`).

## Dependency-closed proof

For every `n`, complete multiplicativity of `χ` gives

`χ(n) = χ(ab) = χ(a)χ(b)` whenever `ab=n`.  Hence

`T_χ(f*g)(n)
 = χ(n) ∑_{ab=n} f(a)g(b)
 = ∑_{ab=n} (χ(a)f(a))(χ(b)g(b))
 = (T_χ(f)*T_χ(g))(n)`.

For composition, pointwise commutativity in `ℂ` gives

`T_ψ(T_χ(f))(n)
 = ψ(n)χ(n)f(n)
 = (ψχ)(n)f(n)
 = T_(ψχ)(f)(n)`.

Taking `ψ=χ⁻¹` and using `χ⁻¹χ=1` in the character monoid gives

`T_(χ⁻¹)(T_χ(f)) = T_1(f) = E_q(f)`.

The principal character modulo `q` is `1` on units of `ZMod q` and `0` on nonunits, proving the
final interpretation.  No analytic continuation, Euler product, Selberg-class axiom, or
unproved hypothesis is used.

## Hostile checks

- `q=1`: every residue is a unit, so depletion is identity.
- Composite `q`: coefficients at all `n` sharing a prime factor with `q` vanish.
- `n=0`: arithmetic functions and multiplicative characters both vanish at zero in the intended
  Lean carriers, so all three equalities remain valid.
- The false stronger statement `T_(χ⁻¹) ∘ T_χ = id` is explicitly rejected for `q>1`.

## Significance for Selberg Conjecture 3

This isolates the finite-prime obstruction that any exact proof must control.  Character twisting
is multiplicative for Dirichlet convolution, but it is not an automorphism before restoring the
Euler factors at primes dividing the conductor.  Consequently, a factorization argument that
silently cancels a twist is invalid; the correct reversible object must remember ramified local
data.

## Next formal target

Formalize the three identities using Mathlib's `ArithmeticFunction ℂ` and
`DirichletCharacter ℂ q`, then inspect axioms and move the exact theorem to pipeline stage 3.
