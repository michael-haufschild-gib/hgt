# Global rational orbit preservers are Laurent Adams maps

- **ID:** alst-global-rational-orbit-preservers-are-laurent-adams
- **Stage:** 2-fully-proven
- **Type:** PAPER PROOF; Lean formalization incomplete, not counted
- **Statement:** Let `N_p,D_p : MvPolynomial Nat.Primes ℂ` be a rational coordinate family defined on the whole prime orbit and preserving it. No common finite invariant prime set is assumed. Then there are unique `n∈ℤ`, `b∈ℝ` with `N_p X_p^{(-n).toNat}=C(p^(−ib)) D_p X_p^{n.toNat}` for every prime `p`. Real or integer coefficients force `b=0`.

## Research consequence
This removes the finite invariant prime-set restriction from rational
Frobenius rigidity. Allowing successive coordinates to introduce new primes
still gives no new orbit-preserving maps. Fixed points satisfy
`(n−1)t+b=0`; two distinct fixed orbit points force the identity.

## Proof
Write `λ(α)=Σ_p α_p log p`. Unique factorization makes `λ` injective on
finitely supported natural exponent vectors. Polynomial restriction is the
finite wave `Σ_α c_α exp(−iλ(α)t)`; its Bohr coefficients recover every
polynomial coefficient. In particular, restriction to the full orbit is
injective, although no finite set contains every coordinate's variables.

Each coordinate numerator and denominator extends to an entire finite
exponential sum with subquadratic Nevanlinna proximity. For an output prime
`p`, choose a distinct output prime `q`. The local normalized-logarithm
argument of the finite classification applies to these two quotients:
the shared clock forces proportional logarithmic derivatives. Clearing
denominators and analytic continuation extend the identity to the plane.
Integer residues and irrationality of `log p/log q` force equal numerator
and denominator divisors. Entire-quotient rigidity and unit modulus on the
real axis give `N_p(t)/D_p(t)=c_p exp(iγ_p t)`.

Orbit preservation at zero gives `c_p=p^(−ib)` for a common real `b`.
The two output coordinates `2,3` determine the normalized clock. Character
clock rigidity gives `u(t)=at+b`, without assuming regularity of `u`.
The character identities then give `γ_p=−a log p` for every output prime.
A nonzero denominator Bohr coefficient, shifted by `γ_p`, must occur in
the numerator spectrum. Thus `a log p=λ(α_p)−λ(β_p)`, with finite exponent
vectors depending on `p`. Exponentiation gives
`exp(a log p)=primeProduct(α_p)/primeProduct(β_p)∈ℚ`.

Suppose `a` were transcendental. An integer relation between `1,a` would
supply a nonzero linear polynomial vanishing at `a`; hence these numbers
are rationally independent. The three prime logarithms `log 2,log 3,log 5`
are rationally independent. All six exponentials formed from these two
rows and three columns are nevertheless rational, contradicting the
six-exponentials theorem. Therefore `a` is algebraic.

Use the frequency identity at output prime `2` and the finite prime set
`{2}∪support(α_2)∪support(β_2)`. Its coefficients
`α_2(p)−β_2(p)−a·1_{p=2}` are algebraic. Baker independence makes every
coefficient zero, so `a=α_2(2)−β_2(2)∈ℤ`. This replaces the determinant
trick: no finite invariant lattice is assumed.

With `a=n`, the orbit identities and injectivity of polynomial restriction
give the stated cross-polynomial identities, including arbitrary common
factors. Conversely these identities give the clock `nt+b`; the canonical
numerator and denominator monomials are everywhere nonzero on the orbit.
Two-prime orbit injectivity gives uniqueness and the fixed-point equation.
Real coefficients make all origin values real; squaring their unimodular
translation factors gives a common torsion return. The coordinates `2,3`
force `b=0`. Coefficient-map injectivity gives the real and integer identities.

## Formalization
The corpus inputs `SixExponentials.six_exponentials`,
`SixExponentials.prime_logs_independent`, and the finite classification's
analytic and Baker inputs have only `propext`, `Classical.choice`, and
`Quot.sound` as transitive axioms.

Two modules passed plain Lean checks with those same axiom audits:

- `GlobalPrimeOrbitPolynomials.lean`: injective full-orbit restriction, finite signed quotient frequencies, and entire extensions with subquadratic proximity.
- `GlobalPrimeClockMultipliers.lean`: `global_prime_frequency_dilation_is_int` and `global_prime_character_clock_linear` remove the finite invariant prime-set premise.

The classification, converse, uniqueness, fixed-point theorem, and
real/integer descent remain under verification. No contribution is counted yet.
