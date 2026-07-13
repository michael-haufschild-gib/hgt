# Prime--archimedean dual Cauchy, RSK, Fredholm determinant, and RH

- **ID:** `prime-arch-dual-cauchy-rsk-fredholm-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [SOURCE TENSOR FACTORIZATION]`
- **Lean inputs:** `formal/GaloisForLFunctions/RHTower/MobiusFiniteSchurTransfer.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeWordYoungShapeNoGo.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeArchDualCauchyTensor.lean`,
  `formal/GaloisForLFunctions/FredholmDeterminantExamples.lean`,
  `formal/GaloisForLFunctions/FredholmDeterminantZeta.lean`,
  `formal/GaloisForLFunctions/AdamsOperations.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeArchThetaAllOrderCumulant.lean`, and
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedSource.lean`
- **Consumer:** `prime-theta-young-thoma-schur-rh.md`
- **Statement:** `[CONJECTURE]` The square-coordinate Xi Taylor determinant is the fermionic
  Fredholm determinant of a positive trace-class tensor product

  ```text
  prime diagonal diag(p^(-2)) tensor completed archimedean operator K_infinity.
  ```

  Equivalently, finite prime--archimedean binary incidence matrices carry a dual-RSK Schur measure
  whose locally uniform partition function limit is the normalized square-coordinate Xi function.
  Positivity of the tensor spectrum forces every centered Xi zero onto the real axis and proves RH.

## 1. Exact determinant target

Use the source-defined entire function

```text
A(u)=sum_(n>=0) a_n u^n,
a_n=thetaCuspRawEvenMoment(n)/((2n)! thetaCuspRawEvenMoment(0)),
XiC(z)/XiC(0)=A(-z^2).
```

Define its alternating logarithmic power sums without referring to any zero:

```text
c_n=(-1)^(n-1) n [u^n] log A(u),       n>=1.              (1)
```

For a positive trace-class operator `K`,

```text
det(I+uK)=exp(sum_(n>=1)(-1)^(n-1)Tr(K^n)u^n/n).          (2)
```

Thus a source construction satisfying

```text
K>=0,   K trace class,   Tr(K^n)=c_n for every n>=1       (3)
```

identifies `A(u)=det(I+uK)` first near zero and then everywhere by analyticity.  The nonzero zeros
of the determinant are `-1/lambda_j`, where `lambda_j>0` are the nonzero eigenvalues of `K`.
Therefore every zero of `A` is negative real, every zero of `XiC` is real, and RH follows.

The converse consumer is standard: under RH the positive diagonal operator with eigenvalues
`gamma^(-2)`, repeated with Xi multiplicity, satisfies `(2)--(3)`.  The proof-bearing content is a
divisor-free construction of `K` from primes and the completed theta/Gamma source.

## 2. Prime tensor factorization

Let

```text
D_2=diag(p^(-2))_(p prime),
P(s)=sum_p p^(-s).
```

This is positive trace class and

```text
Tr(D_2^n)=P(2n).                                          (4)
```

The proposed second alphabet is one positive trace-class operator `K_infinity`, built from the
theta/Gamma completion before any Xi divisor is inspected.  Put

```text
q_n=c_n/P(2n).                                            (5)
```

The exact source theorem is

```text
Tr(K_infinity^n)=q_n for every n>=1.                      (6)
```

Then the positive tensor product `K=D_2 tensor K_infinity` obeys

```text
Tr(K^n)=Tr(D_2^n)Tr(K_infinity^n)=P(2n)q_n=c_n.           (7)
```

The multiplication in `(7)` is the operator version of the already-formalized Adams power-sum
tensor law.  Equation `(5)` is allowed only as a falsification coordinate.  An acceptable proof of
`(6)` must construct `K_infinity` from theta atoms, the Gamma/polar weld, or an existing positive
Sonin incidence operator and then prove its traces equal `(5)`; reconstructing it abstractly from
the target sequence is circular.

## 3. Dual-Cauchy and RSK face

At finite prime and archimedean apertures let

```text
x_p=p^(-2),       y_j=eigenvalue_j(K_infinity).
```

The finite determinant is

```text
det(I+u D_2 tensor K_infinity)
  =product_(p,j)(1+u x_p y_j).                            (8)
```

The finite algebraic core is now formalized in Lean: pair-product power sums factor exactly, and
every zero of `(8)` is a negative real reciprocal `-(x_p y_j)^(-1)` whenever both alphabets are
positive.

The dual Cauchy identity expands the same object as

```text
product_(p,j)(1+u x_p y_j)
  =sum_lambda u^|lambda| s_lambda(x)s_(lambda')(y).       (9)
```

For nonnegative alphabets every term is nonnegative.  Dual RSK realizes `(9)` by binary
prime-by-archimedean incidence matrices; revealing occupied cells gives one-box interlacing paths,
and growing the aperture gives the corresponding Schur process.  This supplies the completed
Young weights and deletion coherence sought in `prime-theta-young-thoma-schur-rh.md` without
postulating each Jacobi--Trudi minor separately.

The one-alphabet limit is now understood exactly.  If the archimedean alphabet has one entry, only
pure-column shapes survive.  Lean proves the source version sharply:

```text
primeWordMultiplicityPartition(w).parts=[1^length(w)]
  <-> w is squarefree.                                    (10)
```

Hence the positive Bernoulli law in `MobiusFiniteSchurTransfer.lean` is precisely the one-column
dual-Cauchy floor.  A genuine second alphabet is not optional: repeated incidences in a prime row
are exactly the row-lengthening data missing from the squarefree channel.

## 4. Numerical falsification gate

The first twelve source logarithmic power sums computed from the theta integral are positive:

```text
c_1  = 2.310499311541897078893381043e-2
c_2  = 3.717259928526968616486626247e-5
c_3  = 1.441739314009732796953815561e-7
c_4  = 6.630316802529908698732720820e-10
c_5  = 3.213664150616601216102116600e-12
c_6  = 1.587693451491015351898283881e-14
c_7  = 7.903325724046737911098930617e-17
c_8  = 3.946471399998846133796329066e-19
c_9  = 1.973265073744967276523596222e-21
c_10 = 9.872165383297157593570283688e-24
c_11 = 4.940256352281979047470881245e-26
c_12 = 2.472494444328769346059036641e-28.
```

For the canonical prime-square split `(5)`,

```text
q_1 = 5.1089275674189505e-2
q_2 = 4.8280404460828930e-4
q_3 = 8.4459987030234291e-6
q_4 = 1.6325178612285659e-7
q_5 = 3.2343524452773891e-9
q_6 = 6.4533440294781297e-11
q_7 = 1.2904569473472594e-12
q_8 = 2.5824267956068562e-14.
```

The leading Hankel determinants of `(q_(i+j+1))` are positive through size six and the shifted
ones through size five in this test.  This is necessary for a positive operator moment model but
is far weaker than `(6)` and does not prove the route.

The exponent is load-bearing.  Replacing `p^(-2)` by `p^(-sigma)` gives residual moments
`q_n(sigma)=c_n/P(sigma n)`.  The tested leading Hankel tower fails at finite order for weak prime
damping: at `sigma=1.01` the size-two determinant is negative, at `sigma=1.1` size three is
negative, and at `sigma=1.5` size four is negative.  The prime-square value `sigma=2` survives all
tested orders.  This turns those no-gos into a positive threshold statement: any tensor producer
of this form needs sufficient prime damping, and the square coordinate of Xi supplies the first
canonical surviving exponent.

## 5. Hard attacks and positive successors

1. **One-alphabet attack.**  The squarefree Möbius/Bernoulli channel produces only column shapes.
   **Positive successor:** retain it as the exact prime alphabet and add a source-built
   archimedean alphabet; `(10)` identifies precisely what must be added.
2. **Target-moment attack.**  Declaring an operator with traces `q_n` simply restates positivity.
   **Positive successor:** build `K_infinity` entrywise from theta/Gamma or Sonin incidence first,
   then prove `(6)` as a source comparison.
3. **Moment-measure attack.**  Hankel positivity of `(q_n)` yields at most a weighted moment
   measure.  A Fredholm determinant requires one actual trace-class spectrum with integer
   eigenvalue multiplicities.
   **Positive successor:** require a positive compact operator, not merely a representing measure.
4. **Rank-one attack.**  A one-mode archimedean operator would give `q_2=q_1^2`, whereas the tested
   values satisfy `q_2<q_1^2`.
   **Positive successor:** the strict defect `q_1^2-q_2` is the second exterior trace and certifies
   a genuinely multimode archimedean alphabet.
5. **Weak-damping attack.**  Small `sigma` produces explicit negative residual Hankel minors.
   **Positive successor:** the first failed minor is a quantitative damping threshold; retain the
   prime-square split and reject every exponent at its first certified negative minor.
6. **Arbitrary RSK attack.**  Applying RSK after fitting a binary matrix to Xi coefficients reads
   the target backward.
   **Positive successor:** matrix rows are primes, columns are named theta/Gamma atoms, and cell
   odds are fixed pair products before the determinant comparison.
7. **Finite-aperture attack.**  Every finite positive determinant has negative roots, but an
   unrelated coefficient limit need not be Xi.
   **Positive successor:** prove trace-norm convergence of the source operators; Fredholm
   determinant continuity then gives locally uniform convergence and preserves the exact limit.
8. **Generic positive-operator attack.**  Positivity of an existing Sonin/prolate operator does not
   identify its trace powers with `(5)`.
   **Positive successor:** treat its moment mismatch as an explicit residual sequence and test
   whether a source-prescribed compression or tensor corner closes it; do not rename the operator.

## 6. Exact open cores

- `[OPEN CORE A]` Construct the finite archimedean matrices `K_(infinity,N)>=0` directly from theta
  atoms and the Gamma/polar completion.
- `[OPEN CORE B]` Prove their trace powers converge to `q_n=c_n/P(2n)` simultaneously at every
  finite cutoff, without using Xi zeros.
- `[OPEN CORE C]` Prove trace-norm convergence to one positive trace-class `K_infinity` and identify
  the tensor Fredholm determinant with `A` on an open disk.
- `[OPEN CORE D]` Formalize the finite dual-Cauchy/Fredholm expansion and compose its locally uniform
  limit with the existing square-coordinate Xi identity and RH endpoint.

## 7. Parent results

- Okounkov, *Infinite wedge and random partitions*, arXiv:math/9907127, for the Schur measure;
- Okounkov--Reshetikhin, *Correlation function of Schur process with application to local geometry
  of a random 3-dimensional Young diagram*, arXiv:math/0107056;
- the dual Cauchy identity and dual RSK correspondence;
- the trace-class Fredholm determinant and tensor-product trace law.

## Kill conditions

Retire the tensor producer if a source-computed residual Hankel minor at `sigma=2` is negative; if
every canonical theta/Gamma matrix has a negative eigenvalue; if the required spectrum is obtained
only from the Xi divisor; if the trace identities hold only degree by degree with incompatible
operators; or if the finite operators fail trace-norm compactness.  Preserve as positive output the
maximal Schur-positive shape family, the first negative residual minor and its damping threshold,
or any compatible positive finite-rank tensor corner.

## Gates

- [x] square-coordinate determinant target and RH consumer closed
- [x] exact prime tensor trace factor isolated at exponent two
- [x] dual-Cauchy/RSK interpretation of the two alphabets stated
- [x] finite tensor power-sum law and negative-real zero classification formalized
- [x] squarefree one-alphabet sector classified exactly in Lean as pure column
- [x] first twelve logarithmic power sums and residual moment tests computed
- [x] weak-damping no-go converted into a positive finite-order threshold
- [ ] source-defined positive archimedean matrices constructed
- [ ] simultaneous residual trace-power identities proved
- [ ] trace-norm cofinal limit and Fredholm determinant comparison proved
- [ ] RH capstone formalized
