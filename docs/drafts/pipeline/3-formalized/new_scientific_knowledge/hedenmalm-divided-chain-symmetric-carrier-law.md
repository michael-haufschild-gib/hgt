# Hedenmalm divided-chain symmetric carrier law

- **ID:** `hedenmalm-divided-chain-symmetric-carrier-law`
- **Stage:** 3-formalized
- **Type:** THEOREM PACKAGE / HILBERT--POLYA CARRIER CLASSIFICATION
- **Scientific status:** `[FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY AUDIT OPEN]`
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

## Literature boundary

Hedenmalm proves uniqueness, up to scalar, of the boundary-value eigenfunction attached to each Xi
zero and notes that this gives weak support for simplicity. He does not construct the iterated
divided chain, identify analytic multiplicity with its exact depth, derive the Jordan recurrence,
or prove the faithful symmetric-source-quotient theorem `(6)` or the normal-form equivalence `(8)`:
[Hedenmalm, 2026](https://arxiv.org/abs/2606.17494).

General operator-pencil theory studies Jordan chains and root functions. Those general facts are
background, not the candidate novelty. The candidate new content is the exact instantiation for
Hedenmalm's theta-source equation, including the four-condition global carrier law `(6)` and the
canonical local/global normal forms `(7)`--`(8)`. Primary comparisons included recent analytic
operator-family diagonalization and Jordan-chain work
([Stiefenhofer, 2024](https://arxiv.org/abs/2411.15905),
[Albrecht--Howlett--Verma, 2020](https://arxiv.org/abs/2002.10551)). Exact-title, arXiv-ID, divided-
quotient, multiplicity, and Jordan-chain searches through 12 July 2026 found no contemporaneous
extension of Hedenmalm containing `(1)`--`(8)`.

## Significance assessment

Audited score: **91/100**. The result converts Hedenmalm's qualitative simplicity remark into an
exact multiplicity-depth theorem, derives the previously unstated Jordan obstruction, proves a
global source-quotient carrier law forcing RH plus simplicity, and supplies an assumption-free
canonical Hermitian normal-form equivalence. The ingredients from analytic factorization and
symmetric-operator theory are classical, but their coupling to the June 2026 theta-source problem
and the resulting carrier classification are not present in the identified literature.

The result does not prove RH: it does not construct the faithful symmetric quotient in `(5)` from
the prime--theta source. Its significance is the exact classification of the missing Hilbert--Pólya
carrier and the elimination of multiplicity ambiguity in Hedenmalm's architecture.

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
- [x] complete primary-literature audit through 12 July 2026
- [x] score at least 90/100
- [ ] standalone publication-ready manuscript
