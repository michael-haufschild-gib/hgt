# Polynomial-drift rational-outer-factor rigidity

- **ID:** `polynomial-drift-rational-outer-factor-rigidity`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Scientific status:** `[BRIDGE] [PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; primitive ramification
- **Statement:** In a rational composition of a finite-order entire function with nonzero polynomial affine-symmetry drift, the entire inner factor is necessarily first-order DA.

## Theorem

Let `W` be an entire function of finite order. Suppose there are an affine automorphism

`sigma(z)=az+b`, `a!=0`,

and a nonzero polynomial `Q` such that

`W(sigma(z))-W(z)=Q(z).`

If

`W(z)=P(g(z))`

for an entire function `g` and a polynomial `P` of degree at least two, then `g` is DA of minimal order at most one.

## Proof

The function `g` has finite order because `P(g)=W`. Put

`A(z)=g(sigma(z))-g(z)`

and let

`B(z)=(P(g(sigma(z)))-P(g(z)))/(g(sigma(z))-g(z))`

be the polynomial divided difference of `P`, evaluated at the two entire functions. Then `B` is entire and

`A(z)B(z)=Q(z).`

Since `Q!=0`, neither factor is identically zero. Every zero of `A` or `B` is a zero of `Q`, so both have only finitely many zeros. Hadamard factorization for finite-order entire functions gives polynomials `P_1,P_2,S_1,S_2` such that

`A=P_1 exp(S_1)`,

`B=P_2 exp(S_2).`

Since `AB=Q`, comparison of zero divisors and zero-free factors gives

`P_1P_2=cQ`,

`S_1+S_2=constant`

after absorbing a nonzero constant. Put `E=exp(S_1)`. Then `exp(S_2)` is a constant multiple of `E^(-1)`.

The identity `g(sigma(z))=g(z)+A(z)` makes `B` a polynomial of degree `deg(P)-1` in `g(z)` with coefficients in `C(z,E)`. Its leading coefficient is `deg(P)` times the leading coefficient of `P`, hence nonzero. Therefore this identity is a nontrivial algebraic equation for `g` over `C(z,E)`.

The hyperexponential generator satisfies

`E'=S_1'(z)E`.

Thus `C(z)<E>` has transcendence degree at most one, and the same is true after adjoining the algebraic element `g`. Consequently `g` satisfies a first-order ADE.

No genuinely order-two inner function can occur in such a polynomial factorization.

## Rational outer functions

The same conclusion holds if

`W=R o g`

with `R` rational and `g` entire. Since `W` is entire, `g` omits every pole of `R`. A nonconstant entire function omits at most one finite value, so `R` has at most one distinct pole.

If `R` has no finite pole, it is polynomial and the theorem applies directly. Otherwise let `a` be its unique pole and put

`u=1/(g-a).`

The function `u` is entire, and `R(g)` is a polynomial in `u`. Applying the polynomial theorem to this factorization shows that `u` is first-order DA. Since

`g=a+1/u`,

the function `g` is first-order DA as well.

Thus nonzero polynomial affine-symmetry drift eliminates the full rational outer-function exception allowed by pseudo-primality.

## Composition consequence

Let `w` be a first-order entire DA function of the form

`w(z)=L(exp(cz))+R(z)`,

where `L` is a Laurent polynomial, `c!=0`, and `R` is a polynomial. If `W'=w` and `T=2 pi i/c`, then

`(W(z+T)-W(z))'=R(z+T)-R(z)`.

Thus `W(z+T)-W(z)` is a polynomial. If it is nonzero, the theorem excludes every polynomial order-two right factor. If it is zero, the explicit primitive formula forces `R` to be constant with its contribution cancelling the constant Laurent coefficient of `L`; consequently `W` itself is a Laurent polynomial in `exp(cz)`. Then `W` is first-order DA, and every `g` algebraic over `W` has differential order at most one.

Hence this complete Laurent-exponential-plus-polynomial first-order class cannot furnish any polynomial-factor shadow-recovery counterexample.

## Parent-theory verdict

The proof is an application of Hadamard factorization to a polynomial divided difference. It closes a broad explicit class but is routine from classical entire-function theory, so it is a bridge.

## Gates

- [x] Complete proof.
- [x] Zero and nonzero polynomial-drift cases classified.
- [x] All rational outer factors excluded for the Laurent-exponential-plus-polynomial derivative class.
- [x] Anti-theatre gate; bridge verdict.
- [x] Formalized in Lean 4, unconditionally.

## Lean formalization

`formal/GaloisForLFunctions/HTGeometry/PolynomialDriftRationalOuterFactorRigidity.lean`

| Card claim | Lean declaration |
|---|---|
| `A = g∘σ - g`, and `P(g+A) - P(g) = Q` | `affineDrift`, `drift_inner_relation` |
| every zero of `A` is a zero of `Q`, so `A` has finitely many zeros | `drift_finite_zeroSet` |
| `Q ≠ 0` forces `A ≢ 0` | `drift_ne_zero` |
| `g`, hence `A`, has finite order because `P(g) = W` | `finiteOrderEnvelope_drift` (via `finiteOrderEnvelope_of_comp_polynomial`) |
| Hadamard: `A = P₁ exp S₁` | `RHTower.exists_polynomial_mul_expPolynomial_of_envelope` |
| `B` is a polynomial of degree `deg P - 1` in `g` with leading coefficient `deg P · lead P ≠ 0` | `driftCoeff`, `eval_driftCoeff_expansion`, `eval_driftCoeff_pred` |
| `E′ = S₁′ E`, so `ℂ(z)⟨E⟩` has transcendence degree at most one | `deriv_analyticMeroElement_exp` + `exists_state_algebraic_of_polynomial_drift` |
| `g` algebraic over `ℂ(z)(E)` ⟹ order-one ADE | `differentiallyAlgebraicOfOrder_of_algebraic_over_states` |
| **the theorem** | `polynomial_drift_rigidity` |
| rational outer factor: `u = 1/(g-a)` entire, `R(g)` polynomial in `u`, `g = a + 1/u` | `rational_outer_factor_rigidity` |

New reusable infrastructure built for this card:

* `HTGeometry/FiniteOrderHadamard.lean` — `FiniteOrderEnvelope` and zero-free Hadamard at every
  finite order;
* `RHTower/FiniteZeroHadamardProduct.lean` — the divisor-carrying Hadamard product at every finite
  order (`f = p · exp q` for `f` entire of finite order with finitely many zeros);
* `HTGeometry/PolynomialDriftExpansion.lean` — the shift expansion `P(y+a) - P(y)` with its exact
  top coefficient `n · lead(P) · a`;
* `HTGeometry/FiniteOrderPolynomialDescent.lean` — finite order descends through a polynomial
  outer factor;
* `HTGeometry/AlgebraicOverStateFieldOrder.lean` — the order bound for elements *algebraic over*
  a state field (the corpus previously required membership);
* `HTGeometry/ExpPolynomialRational.lean` — `G · exp T = Q` with `G, Q` nonzero polynomials forces
  `T` constant.

All declarations audited with `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.

The composition-consequence section (`w = L(exp cz) + R(z)`) is the specialization of
`polynomial_drift_rigidity` to `Q(z) = R(z+T) - R(z)` with `T = 2πi/c`; the degenerate branch
`Q = 0` is the Laurent-polynomial case, in which `W` itself is first-order DA.

## Primary reference

1. Classical Hadamard factorization theorem for finite-order entire functions.
