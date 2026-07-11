# The exact constrained prolate exterior Weil form has a universal positive leading law

- **ID:** `constrained-prolate-exterior-weil-leading-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`,
  pending independent audit
- **Parent results:** the constrained radial leakage/divisibility spectrum, the exact finite-aperture
  radial off-diagonal bounds, `ccm-countable-log-chirp-renormalization-law.md`, the aperture shift
  cutoff, and Suzuki's archimedean multiplier formula
- **Statement:** The exact lower exterior CCM tail, and therefore the corresponding CCM seed by
  the radical quotient identity, has archimedean Weil energy
  `D_arch*d_1(lambda)log(2*pi*lambda^2)+o(d_1 log lambda)`, where
  `D_arch=(8/(11*pi))sum_(k>=1)arcsin(1/k)/k>0`. Its radial prime charge is only order `d_1`, and
  its Poisson zero-mode correction is `o(d_1)` in the finite-aperture form.

## Exact exterior tail

Let

```text
R_lambda(s)=sum_(k>=1)H_(lambda,k)(s),
H_(lambda,k)(s)=sqrt(lambda*e^s)q_lambda(k*lambda*e^s),

C_lambda(s)=g_lambda(0)/(2*sqrt(lambda))*e^(-s/2),
b_lambda=R_lambda-C_lambda,
c=2*pi*lambda^2.                                                (1)
```

Poisson summation identifies `b_lambda` with the exact lower exterior CCM tail. The constrained
source satisfies

```text
g_lambda(0)=O(d_1(lambda)).                                      (2)
```

## Radial norm law

The diagonal radial spectrum is

```text
G_lambda(k,k)/d_1(lambda)
 ->8/(11*pi*k)arcsin(1/k),
G_lambda(k,k)/d_1(lambda)<=C/k^2.                               (3)
```

The exact nonstationary, low first-row, and high-radial BV theorems make the complete off-diagonal
sum `o(d_1)`. Hence

```text
||R_lambda||_2^2/d_1(lambda) ->D_arch,                           (4)

D_arch=8/(11*pi)sum_(k>=1)arcsin(1/k)/k.                         (5)
```

The series in `(5)` converges absolutely and is strictly positive.

## Archimedean logarithmic law

Use Suzuki's symbol

```text
A(u)=1/(2*pi)integral_R m(xi)|hat(u)(xi)|^2dxi,
m(xi)=Re psi(1/4+i*xi/2)-log pi
     =log|xi|-log(2*pi)+O(|xi|^(-2)).                            (6)
```

For fixed `k`, Dunster's radial phase gives local Mellin frequency comparable to `c*k*e^s`.
The logarithmic-chirp lemma therefore yields

```text
A(H_(lambda,k))/log c=||H_(lambda,k)||_2^2+o(d_1).               (7)
```

Distinct radial indices have separated phases. The countable log-chirp renormalization theorem
proves that, after subtracting the scalar `log(c)I`, their total archimedean cross contribution is
`O(d_1)`.
The uniform diagonal bound in `(3)` also gives

```text
sum_(k>=1)(1+log k)G_lambda(k,k)/d_1<=C,                         (8)
```

and `ccm-countable-log-chirp-renormalization-law.md` passes the finite-index logarithmic-chirp law
to the full radial sum. Equations `(3)`--`(8)` prove

```text
A(R_lambda)/(d_1(lambda)log c)->D_arch.                          (9)
```

## Poisson center is lower order

The fixed profile `1_(s>=0)e^(-s/2)` belongs to the archimedean form domain. From `(2)`,

```text
||C_lambda||_A^2=O(d_1(lambda)^2/lambda)=o(d_1).                 (10)
```

Cauchy--Schwarz in a positive constant shift of the archimedean form gives

```text
A(R_lambda,C_lambda)=o(d_1).                                    (11)
```

Thus `(9)` remains true with `b_lambda` in place of `R_lambda`.

For the finite-aperture prime form only shifts `q<=lambda^2` occur. The central--central term is
bounded by

```text
C*d_1^2/lambda *sum_(q<=lambda^2)Lambda(q)/q=o(d_1),             (12)
```

and the two cross terms are `o(d_1)` by Cauchy--Schwarz, the radial norm law `(4)`, the elementary
bound `sum_(q<=X)Lambda(q)/sqrt(q)=O(sqrt(X)log X)`, and the fixed-mode Fuchs fact that
`sqrt(d_1(lambda))` beats every power of `lambda`. Hence the zero-mode correction does not alter
the first leakage-scale prime constant.

## Exterior Weil law

The cofinal finite-aperture radial prime law gives

```text
Q_prime(R_lambda,R_lambda)/d_1(lambda)
 ->-16/(11*pi)sum_(k>=2)log(k)/k*arcsin(1/k).                    (13)
```

This is one logarithmic order below `(9)`. Equations `(9)`--`(13)` prove the positive leading law

```text
[A+Q_prime](b_lambda,b_lambda)
 /(d_1(lambda)log c)
 ->D_arch>0.                                                     (14)
```

## Positive route consequence

Let `a_lambda` be the restricted CCM seed and `b_lambda` its exterior representative. The exact
radical quotient identity proves

```text
QW(a_lambda,a_lambda)=QW(b_lambda,b_lambda).                     (15)
```

Thus `(14)` is the actual seed Rayleigh law, not one side of a future interior cancellation:

```text
QW(a_lambda,a_lambda)
 =D_arch*d_1(lambda)log(2*pi*lambda^2)
  +o(d_1(lambda)log lambda).                                    (16)
```

Completion contributes the one archimedean valuation direction and fixes the coefficient `(5)`;
the independent infinite arithmetic carrier supplies the lower-order prime constant `(13)`.

The positive remaining theorem is now exact. If `epsilon_0(lambda)` is the true even ground energy,
`Gap_lambda` its true next-level gap, and `L_lambda<=epsilon_0(lambda)` a certified lower bound, one
must prove

```text
[D_arch*d_1(lambda)log(2*pi*lambda^2)-L_lambda]
 /Gap_lambda=O(lambda^(-1)).                                    (17)
```

Together with simple-evenness, `(17)` is precisely the source theorem needed for projective
ground-vector and determinant transfer.

The fixed-mode ladder suggests the stronger pair

```text
epsilon_0(lambda)>=-C*d_1(lambda),
Gap_lambda>=c_0*lambda^8*d_1(lambda)*log lambda.                  (18)
```

Indeed `(16)` and `(18)` give

```text
[QW(a_lambda,a_lambda)+C*d_1(lambda)]/Gap_lambda
 =O(lambda^(-8)),                                                (19)
```

which is far stronger than `(17)`. However, the first inequality in `(18)` already squeezes
`epsilon_0(lambda)->0`, because the negative allowance `C*d_1(lambda)` tends to zero and the seed
Rayleigh value tends to zero. By `ccm-cofinal-weil-spectral-floor-criterion.md`, it proves RH
directly. It must therefore be classified as the direct spectral-floor core, not as a preliminary
determinant estimate. The collapse is recorded in
`ccm-rayleigh-transfer-collapses-to-spectral-floor.md`.

Equation `(14)` is not a positivity theorem for the complete restricted Weil operator: the
ground lower bound and true gap in `(17)` remain open.

## Novelty and significance verdict

### Novelty: provisional pass

The literature supplies the archimedean multiplier, radial PSWF asymptotics, and prolate/zeta
spectral constructions separately. Searches for the arcsine radial divisibility spectrum and its
von Mangoldt/prolate combination found no formula `(5)`, `(13)`, or `(14)` in the CCM or PSWF
literature.

### Significance: provisional pass, 8/10

The theorem evaluates the leading sign and coefficient of the exact CCM seed Rayleigh value and
turns the previous vague tail problem into the explicit gap comparison `(17)`. It does not prove
RH because the true lower bound, simple-evenness, and gap comparison remain open.

The result remains candidate-new pending an independent audit of the exact CCM normalization,
logarithmic cross-term summation, and finite-aperture center estimate.

## References

- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096, Section 2.4.
- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699.
- A. Connes, H. Moscovici, *Prolate Spheroidal Operator and Zeta*, arXiv:2112.05500.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.

## Lean decision

`formal/GaloisForLFunctions/ConstrainedProlateExteriorWeil.lean` now formalizes both universal
series coefficients used by the paper theorem. In particular, Lean proves absolute convergence,
`D_arch > 0`, the stronger explicit bound `4/11 <= D_arch`, and strict negativity of the signed
lower-order prime coefficient in `(13)`. These results are unconditional and assume no Weil-operator
positivity, spectral floor, gap bound, or RH-equivalent statement.

The full asymptotic law `(14)` is not yet formalized. The tree now has the concrete compact,
self-adjoint constrained prolate leakage operator in
`formal/GaloisForLFunctions/RHTower/ConstrainedProlateOperator.lean`, but still lacks concrete
interfaces for its radial PSWF defect measure, the archimedean multiplier form, and the
finite-aperture prime form.
The card therefore remains at paper-proven stage: the formal module establishes its exact constants
and their signs, but does not replace the missing analytic realization by abstract assumptions.

## Gates

- [x] full radial norm coefficient summed after the high first-row tail
- [x] archimedean logarithmic chirp law transferred to all radial indices
- [x] Poisson zero mode shown lower order in the finite-aperture form
- [x] raw radial prime constant inserted
- [x] positive exterior Weil coefficient obtained
- [x] radical quotient identity available to transfer a proved exterior law to the seed
- [ ] independent normalization and cross-term audit
- [ ] certify a true ground-energy lower bound
- [ ] compare the explicit seed value with the true even gap
- [ ] prove the direct RH-sufficient negative-floor theorem in `(18)`
