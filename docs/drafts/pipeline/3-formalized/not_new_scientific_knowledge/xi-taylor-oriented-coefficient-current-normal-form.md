# Xi Taylor oriented coefficient-current normal form

- **ID:** `xi-taylor-oriented-coefficient-current-normal-form`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean) / ALGEBRAIC BRIDGE
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The imaginary logarithmic derivative of every finite Xi Taylor polynomial is its
  orientation-sensitive Hermitian coefficient current divided by the squared modulus of its
  value.  A strict denominator-cleared sublinear current inequality therefore forces the
  anisotropic finite-Taylor flux condition and, for a super-accurate schedule, RH.

## Finite current

For a complex polynomial `P`, define

```text
J_P(z) = Im(P'(z) conjugate(P(z))).                            (1)
```

This is a finite Hermitian quadratic expression in the coefficients of `P`.  Direct complex
division gives

```text
Im(P'(z)/P(z)) = J_P(z)/|P(z)|^2                              (2)
```

whenever `P(z) != 0`.

More sharply, if

```text
J_P(z) < B |P(z)|^2,                                         (3)
```

then `(3)` itself forces `P(z) != 0`, since both sides would be zero at a zero of `P`; division by
the positive squared modulus then gives

```text
Im(P'(z)/P(z)) < B.                                          (4)
```

## Xi specialization

Let `T_n` be the ordinary polynomial formed from the first `n` one-dimensional Cauchy--Taylor
coefficients of `XiC`.  Then

```text
T_n(z)  = xiCTaylorApprox(n,z),
T_n'(z) = deriv(xiCTaylorApprox n,z).                         (5)
```

For a schedule `N`, impose at the anisotropic centered mesh point `z_(sigma,n)` the finite
coefficient inequality

```text
J_(T_k)(z_(sigma,n))
  < epsilon (n+1) |T_k(z_(sigma,n))|^2,                      (6)

k = N(xiCTaylorAnisotropicScheduleStage(sigma,n)).
```

If `(6)` holds eventually for every positive `epsilon` and every open-left-strip base point, then
the canonical finite Taylor logarithmic derivative has sublinear upper flux on every such fibre.
Together with a super-accurate schedule, the formalized pole-amplification gate yields RH.

## Anti-theatre verdict

Equation `(6)` is the exact denominator-cleared target.  It isolates orientation and removes every
zero/nonvanishing side condition, but it does not explain why the canonical Xi coefficients obey
the inequality.  It is therefore a source-facing normal form, not the requested source producer
and not an RH proof.

## Lean certificate

Module:

- `formal/GaloisForLFunctions/RHTower/XiCTaylorOrientedCoefficientCurrent.lean`

Principal declarations:

- `orientedPolynomialCurrent`
- `polynomial_logDeriv_im_eq_orientedCurrent_div_normSq`
- `polynomial_logDeriv_im_lt_of_orientedCurrent_lt`
- `xiCTaylorPolynomial`
- `xiCTaylorPolynomial_eval`
- `xiCTaylorPolynomial_derivative_eval`
- `XiCTaylorAnisotropicOrientedCoefficientSublinearUpper`
- `xiCTaylorAnisotropicLogDerivSublinearUpper_of_orientedCoefficient`
- `riemannHypothesis_of_xiCTaylorAnisotropicOrientedCoefficientSublinearUpper`

Exact module build passes.  The capstones use only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] paper identity and automatic nonvanishing proved
- [x] canonical Cauchy--Taylor partial sums identified with ordinary finite polynomials
- [x] denominator-cleared coefficient current implies sublinear Taylor flux in Lean
- [x] super-accurate schedule plus coefficient current implies RH in Lean
- [x] bridge status separated from the open source inequality

