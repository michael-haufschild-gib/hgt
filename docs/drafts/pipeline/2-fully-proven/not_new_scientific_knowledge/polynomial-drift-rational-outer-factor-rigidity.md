# Polynomial-drift rational-outer-factor rigidity

- **ID:** `polynomial-drift-rational-outer-factor-rigidity`
- **Stage:** 2-fully-proven
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

## Primary reference

1. Classical Hadamard factorization theorem for finite-order entire functions.
