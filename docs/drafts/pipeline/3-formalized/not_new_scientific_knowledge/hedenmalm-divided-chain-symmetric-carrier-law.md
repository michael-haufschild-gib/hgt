# Hedenmalm divided-chain symmetric carrier law

- **ID:** `hedenmalm-divided-chain-symmetric-carrier-law`
- **Stage:** 3-formalized
- **Type:** BRIDGE / TARGET-FED DIAGNOSTIC NORMAL FORM
- **Scientific status:** `[FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [SIGNIFICANCE GATE FAILED]`
- **Formal modules:**
  `formal/GaloisForLFunctions/RHTower/XiHedenmalmMultiplicityChain.lean` and
  `formal/GaloisForLFunctions/RHTower/XiHedenmalmSymmetricMultiplicity.lean`, and
  `formal/GaloisForLFunctions/RHTower/XiHedenmalmJordanMatrix.lean`.

## The exact multiplicity-depth law

Let `alpha` be a centered Xi zero of analytic multiplicity `m`. Define the canonical divided chain

```text
Q_(alpha,0)=XiC,
Q_(alpha,k+1)=dslope(Q_(alpha,k),alpha).
```

Every `Q_(alpha,k)` is entire. The first nonzero center value occurs at exactly depth `m`:

```text
Q_(alpha,k)(alpha)=0       for k<m,
Q_(alpha,m)(alpha)!=0,
XiC(z)=(z-alpha)^m Q_(alpha,m)(z).                         (1)
```

More generally, for every `k<=m`,

```text
XiC(z)=(z-alpha)^k Q_(alpha,k)(z),                         (2)
```

and none of the functions `Q_(alpha,k)` with `k<=m` is identically zero. The original transformed
Hedenmalm eigenfunction is `I Q_(alpha,1)`. Consequently,

```text
the Hedenmalm quotient is nonzero at its base point
  iff m=1.                                                  (3)
```

This identifies what the divisor-value carrier loses at a multiple zero: not the eigenfunction as
an entire function, but all center jets below the multiplicity depth.

## The Jordan recurrence

Spectral-coordinate multiplication `M_z F(z)=zF(z)` acts on the chain by

```text
M_z Q_(alpha,k+1)=alpha Q_(alpha,k+1)+Q_(alpha,k),
                                                          0<=k<m. (4)
```

After quotienting the common source `Q_(alpha,0)=XiC`, the first divided quotient becomes an
eigenvector and the second becomes its first generalized eigenvector. Thus an order-`m` zero
forces a canonical Jordan chain of length `m` in every quotient which retains these divided
levels.

## Symmetric carrier theorem

Let `J` be a complex-linear map from entire functions to an inner-product space `H`, and let `S`
be a symmetric linear operator on `H`. Suppose, at one Xi zero `alpha`, that

```text
J(XiC)=0,
J(Q_(alpha,1))!=0,
S J(Q_(alpha,1))=J(M_z Q_(alpha,1)),
S J(Q_(alpha,2))=J(M_z Q_(alpha,2)).                       (5)
```

Then the zero is real and has multiplicity exactly one. Indeed, the first intertwining identity
turns `J(Q_(alpha,1))` into a nonzero eigenvector, so symmetry makes `alpha` real. If `m>=2`, the
second identity and `(4)` give a nonzero length-two Jordan step. But symmetry gives

```text
||v_0||^2
 = <(S-alpha)v_1,v_0>
 = <v_1,(S-alpha)v_0>
 = 0,
```

contradicting `v_0!=0`.

If `(5)` holds for every Xi divisor support point for one common pair `(J,S)`, then

```text
RH holds and every Xi zero is simple.                      (6)
```

This is a positive carrier classification. A successful Hedenmalm Hilbert--Polya completion must
simultaneously:

1. annihilate the common theta source;
2. retain every first divided eigenfunction nontrivially;
3. transport coordinate multiplication on the first two divided levels;
4. make the transported operator symmetric.

Those four concrete requirements already force the full Xi divisor to be real and simple.

## Canonical assumption-free normal form

For a support point `rho`, let `J_rho` be the `m_rho` by `m_rho` matrix with centered spectral
point `alpha_rho` on the diagonal and ones on the first superdiagonal. Equation `(4)` identifies
this matrix as the local root-module action of spectral-coordinate multiplication after the common
source is quotiented out. The exact local theorem is

```text
J_rho is Hermitian
  iff alpha_rho is real and m_rho=1.                       (7)
```

Consequently the whole canonical family satisfies the assumption-free equivalence

```text
every J_rho is Hermitian
  iff RH holds and every Xi zero is simple.                (8)
```

Unlike `(6)`, theorem `(8)` contains no carrier or operator-existence premise. It is the concrete
multiplicity-exact terminal normal form which any source-side construction must reach.

## Formal theorem surface

- `xiThetaDividedChain_local_order`;
- `xiThetaDividedChain_partial_factorization`;
- `xiThetaDividedChain_ne_zero_of_le_multiplicity`;
- `xiThetaEigenFourier_self_ne_zero_iff_multiplicity_one`;
- `xiCoordinateMultiplication_dividedChain`;
- `no_symmetric_jordan_step`;
- `xiSpectralPointSupport_eq_ofReal_of_symmetric_sourceQuotient`;
- `no_symmetric_sourceQuotient_realization_of_multiple_xi_zero`;
- `xiSupportMultiplicity_eq_one_of_symmetric_sourceQuotient`;
- `symmetric_xiSourceQuotient_implies_rh_and_simple`.
- `xiLocalJordanMatrix_isHermitian_iff`;
- `all_xiLocalJordanMatrix_isHermitian_iff_rh_and_simple`.

Every declaration is axiom-clean apart from the standard logical foundations `propext`,
`Classical.choice`, and `Quot.sound`. Exact module builds pass.

## Parent-theory collision

The package is an exact specialization of classical local analytic factorization and elementary
symmetric-operator theory. The multiplicity-depth statement is Taylor factorization at a zero;
the recurrence is the standard divided-quotient/root-chain recurrence; the no-Jordan lemma is the
semisimplicity of symmetric operators. Writing these facts in Hedenmalm's notation is useful for
the project but does not create a new theorem family.

The matrix normal form is also target-fed: its diagonal entries and block sizes are read directly
from the Xi divisor. Likewise, the global source-quotient implication assumes the faithful
symmetric carrier whose construction is the substantive Hilbert--Polya problem. It therefore
classifies what such a carrier would have to preserve without constructing it.

## Significance assessment

Honest score: **40/100**. The package is axiom-clean, precise, and reusable, but it fails the
NOVEL x SIGNIFICANT gate. Its value is diagnostic: it records exactly how multiplicity appears as
a root chain and prevents later arguments from silently erasing generalized levels. It is not a
publication result and does not materially advance RH until a non-target-fed theta/prime
construction supplies the quotient, metric, and symmetric operator.

## Gates

- [x] exact analytic multiplicity depth
- [x] every initial divided quotient entire and nonzero as a function
- [x] exact Jordan recurrence
- [x] symmetric no-Jordan theorem
- [x] local real-and-simple carrier theorem
- [x] global carrier theorem implies RH plus simplicity
- [x] canonical local Jordan block Hermitian iff real and simple
- [x] global canonical blocks Hermitian iff RH plus simplicity
- [x] exact builds
- [x] axiom audit
- [x] parent-theory collision identified
- [x] reclassified as not new scientific knowledge
- [ ] construct the carrier from theta/prime data without Xi-divisor input
