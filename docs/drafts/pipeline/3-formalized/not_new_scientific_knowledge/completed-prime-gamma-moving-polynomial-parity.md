# Completed prime--Gamma moving polynomial parity interface

- **ID:** `completed-prime-gamma-moving-polynomial-parity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[BRIDGE]`
- **Scientific status:** `[PROVED INTERFACE] [OPEN SOURCE INPUT] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaMovingPolynomialParity.lean`

## Statement

Lean defines the finite moving polynomial test

\[
  \mathcal Q_P(\sigma)=\sum_k [X^k]P(X)^2\,c_k(\sigma)
\]

for the explicit completed odd-logarithmic-derivative moments.  It proves

\[
\mathcal Q_P(1/2)=\operatorname{primeArchSourceTraceHankel}(P),\qquad
\mathcal Q_P(1-\sigma)=\mathcal Q_P(\sigma),\qquad
\mathcal Q_P(\bar\sigma)=\overline{\mathcal Q_P(\sigma)}.
\]

It packages two source inputs:

1. every nonzero integer-polynomial test has a positive real far-right anchor;
2. every such test has a finite even-multiplicity real factorization on each compact right
   segment.

From these inputs Lean proves the complete countable prime--Gamma quadratic cone and hence RH.
Unlike the leading-determinant route, the factorization may contain the center, so no central
nonvanishing premise occurs.

Lean additionally reduces the first source input to the scalar completed-moment limits

\[
x^{2k+1}\operatorname{Re}c_k(x)\longrightarrow
\frac{(-1)^k}{2(2k+1)}.
\]

For a nonzero polynomial, the proof isolates the lowest coefficient of its square and shows that
all higher moments vanish after the corresponding scaling.  Thus no asymptotic uniformity in the
polynomial degree is required.

## Formal declarations

- `completedOddLogDerivPolynomialHankel`;
- `completedOddLogDerivPolynomialHankelReal`;
- `completedOddLogDerivPolynomialHankel_one_half`;
- `completedOddLogDerivPolynomialHankel_one_sub`;
- `completedOddLogDerivPolynomialHankel_conj`;
- `completedOddLogDerivPolynomialHankel_ofReal_im`;
- `CompletedOddLogDerivPolynomialFarRightPositive`;
- `CompletedOddLogDerivPolynomialRightEvenFactorization`;
- `CompletedOddLogDerivMomentFarRightAsymptotic`;
- `completedOddLogDerivPolynomialHankelReal_eq_sum`;
- `tendsto_scaled_completedOddLogDerivPolynomial_sum`;
- `completedOddLogDerivPolynomialFarRightPositive_of_momentAsymptotic`;
- `primeArchSourceTraceHankelIntNonnegative_of_movingPolynomialFarRight_evenFactorization`;
- `riemannHypothesis_of_movingPolynomialFarRight_evenFactorization`;
- `riemannHypothesis_of_momentAsymptotic_movingPolynomial_evenFactorization`.

## Gates

- [x] imported by the RHTower umbrella
- [x] exact center consumer wired
- [x] generic factorization-sign theorem wired from HTGeometry
- [x] polynomial far-right positivity reduced to scalar moment asymptotics
- [x] no central nonvanishing input
- [x] no placeholders or project axioms
