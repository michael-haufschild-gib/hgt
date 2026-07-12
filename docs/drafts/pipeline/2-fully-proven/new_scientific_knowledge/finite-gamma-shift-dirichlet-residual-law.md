# Finite Gamma-jet annihilators expose the Dirichlet value flag

- **ID:** `finite-gamma-shift-dirichlet-residual-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / PARTIAL LEAN CERTIFICATE
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED]`
- **Statement:** Every finite family of distinct Euler-Gamma translates, with arbitrary prescribed
  finite jet multiplicities, has a canonical monic consecutive-shift annihilator. Applied to any
  nonzero ordinary Dirichlet series, this operator is nonzero and asymptotically preserves the
  first nonzero Dirichlet coefficient with the universal multiplier `(-1)^N s^N`, where `N` is
  the total number of Gamma jet values. Applied simultaneously to the first `q` zeta jets, its
  residual determinant exposes exactly the initial Dirichlet packet `{1,...,q}`.

## The values

Fix distinct complex values and positive jet multiplicities

```text
lambda_1,...,lambda_r,     d_1,...,d_r>=1,
N=d_1+...+d_r.                                                    (1)
```

and write

```text
R_k(X)=X(X+1)...(X+k-1),     R_0(X)=1.                            (2)
```

For each `s`, expand the monic polynomial with the prescribed root multiplicities in the
ascending-factorial basis:

```text
prod_(i=1)^r (X-s-lambda_i)^(d_i)
  =R_N(X)+sum_(k=0)^(N-1) a_(E,d,k)(s) R_k(X).                    (3)
```

The basis is triangular and monic, so the coefficients `a_(E,d,k)(s)` are unique polynomials in
`s`. Define the associated value operator

```text
(L_(E,d) f)(s)=f(s+N)+sum_(k=0)^(N-1) a_(E,d,k)(s)f(s+k).         (4)
```

The theorem identifies simultaneously the values annihilated by `(4)` and the arithmetic value
which survives it.

## Theorem A: exact confluent Gamma Casoratian and canonical jet annihilator

`[PROVED HERE]` Away from the Gamma poles,

Index the columns by `(i,m)` with `1<=i<=r` and `0<=m<d_i`. Then

```text
det[Gamma^(m)(s+lambda_i+k)]_(0<=k<N, (i,m))
 =prod_(i=1)^r Gamma(s+lambda_i)^(d_i)
  prod_(i=1)^r prod_(m=0)^(d_i-1)m!
  prod_(1<=i<j<=r)(lambda_j-lambda_i)^(d_i d_j).                 (5)
```

In particular the determinant is nonzero. Moreover,

```text
L_(E,d) Gamma^(m)(s+lambda_i)=0,     0<=m<d_i.                    (6)
```

### Proof

Put `x_i=s+lambda_i`. The Gamma functional equation gives

```text
Gamma(s+lambda_i+k)=R_k(s+lambda_i)Gamma(s+lambda_i).             (7)
```

Differentiate `(7)` `m` times with respect to `x_i`:

```text
Gamma^(m)(x_i+k)
 =sum_(q=0)^m binom(m,q) R_k^(m-q)(x_i) Gamma^(q)(x_i).           (8)
```

Within the `i`-th jet block, `(8)` is a triangular column change from the columns
`R_k^(m)(x_i)` to the Gamma-jet columns. Its diagonal value is `Gamma(x_i)`, repeated `d_i`
times. The remaining determinant is the confluent Vandermonde for the monic successive-degree
polynomials `R_0,...,R_(N-1)`. The standard confluent formula is

```text
det[R_k^(m)(x_i)]_(k,(i,m))
 =prod_i prod_(m<d_i)m! prod_(i<j)(x_j-x_i)^(d_i d_j).           (9)
```

Together with the triangular Gamma factors, `(9)` proves `(5)`.

Let `P_s(X)` denote the left side of `(3)`. Holding `s` fixed, `(7)` gives

```text
(L_(E,d) (Gamma^(m)(. + lambda_i)))(s)
 = [D_X^m (Gamma(X)P_s(X))]_(X=s+lambda_i).                     (10)
```

The value `s+lambda_i` is a root of `P_s` of multiplicity `d_i`, so every derivative in `(10)`
with `m<d_i` vanishes. This proves `(6)`. Uniqueness follows from `(3)`, equivalently from the
nonzero determinant `(5)`. `QED`

## Theorem B: first-Dirichlet-value preservation

Let

```text
D(s)=sum_(n>=1)c_n n^(-s)                                      (11)
```

be a nonzero ordinary Dirichlet series, absolutely convergent on a right half-plane, and let

```text
n_0=min{n:c_n!=0}.                                              (12)
```

`[PROVED HERE]` As real `s->+infinity`,

 ```text
(L_(E,d) D)(s)
 =c_(n_0)n_0^(-s)((-1)^N s^N+O(s^(N-1))).                      (13)
```

Consequently `L_(E,d) D` is not identically zero. Thus every finite Gamma-jet value family has a
canonical arithmetic residual, and that residual remembers the first nonzero Dirichlet coefficient.

### Proof

Put

```text
A_(E,d)(s,T)=T^N+sum_(k=0)^(N-1)a_(E,d,k)(s)T^k.                (14)
```

Absolute convergence permits termwise translation in a smaller right half-plane, so

```text
(L_(E,d) D)(s)=sum_(n>=1)c_n n^(-s) A_(E,d)(s,n^(-1)).          (15)
```

The triangular basis change in `(3)` gives

```text
deg_s a_(E,d,k)<=N-k.                                           (16)
```

At `X=0`, all `R_k(0)` with `k>=1` vanish. Hence

```text
a_(E,d,0)(s)=(-1)^N prod_i(s+lambda_i)^(d_i)
             =(-1)^N s^N+O(s^(N-1)),                           (17)
```

whereas every `a_(E,d,k)` with `k>=1` has degree at most `N-1`. For each fixed nonzero `T`,

```text
A_(E,d)(s,T)=(-1)^N s^N+O(s^(N-1)).                            (18)
```

Apply `(18)` to `T=n_0^(-1)`. Choose a real `sigma` in the half-plane of absolute convergence.
The remaining terms in `(15)` satisfy, for `s>=sigma`,

```text
sum_(n>n_0)|c_n|n^(-s)|A_(E,d)(s,n^(-1))|
 <=C(1+s)^N n_0^(-s)
   (n_0/(n_0+1))^(s-sigma)
   sum_(n>n_0)|c_n|n^(-sigma).                                 (19)
```

This is exponentially smaller than the `n_0` term. Equations `(15)`, `(18)`, and `(19)` prove
`(13)`. `QED`

## Corollary: the zeta-jet first-atom readout

For `j>=1`, termwise differentiation gives

```text
zeta^(j)(s)=sum_(n>=2)(-log n)^j n^(-s).                       (J1)
```

Its first nonzero Dirichlet coefficient occurs at `n=2` and equals `(-log 2)^j`. Theorem B
therefore gives the exact two-level readout

```text
(L_(E,d) zeta)(s)=(-1)^N s^N+O(s^(N-1)),

(L_(E,d) zeta^(j))(s)
 =(-1)^(N+j)(log 2)^j 2^(-s)(s^N+O(s^(N-1))),    j>=1.          (J2)
```

Thus the same operator which removes the complete finite Gamma-jet packet reads `zeta` first at
the neutral Dirichlet atom `n=1`, reads every positive zeta derivative first at the prime atom
`n=2`, and records the derivative order in the value `(-log 2)^j`.

## Theorem C: augmented value determinant

Order the Gamma jet columns first and the Dirichlet column last. Row elimination using `(3)` gives
the exact identity

```text
det [ Gamma^(m)(s+lambda_i+k) | (i,m) ; D(s+k) ]_(0<=k<=N)

 =prod_i Gamma(s+lambda_i)^(d_i)
  prod_i prod_(m<d_i)m!
  prod_(i<j)(lambda_j-lambda_i)^(d_i d_j)
  (L_(E,d) D)(s).                                              (20)
```

By `(13)`, the determinant is nonzero for all sufficiently large real regular `s`. Hence the
Dirichlet value column adds one exact consecutive-shift dimension to every finite family of
distinct Gamma-translate jet columns.

For `D=zeta`, `n_0=1` and `c_1=1`, so

```text
(L_(E,d) zeta)(s)=(-1)^N s^N+O(s^(N-1)).                       (21)
```

This is an unconditional finite mixed zeta-Gamma value relation. Its exact scope is the linear
consecutive-shift value space; nonlinear differential independence from the field generated by all
Gamma translates is the additional value studied separately.

## First two multiplicity-one instances

For one value `lambda`,

```text
(L_{lambda}f)(s)=f(s+1)-(s+lambda)f(s),
(L_{lambda}zeta)(s)=-s+O(1).                                   (22)
```

For two distinct values `lambda_1,lambda_2`,

```text
(L_E f)(s)
 =f(s+2)-(2s+lambda_1+lambda_2+1)f(s+1)
  +(s+lambda_1)(s+lambda_2)f(s),

(L_E zeta)(s)=s^2+O(s).                                        (23)
```

The corresponding Gamma determinant is

```text
(lambda_2-lambda_1)Gamma(s+lambda_1)Gamma(s+lambda_2).          (24)
```

## RH and hypertranscendence significance

The law distinguishes two exact multiplier alphabets under the same unit translation:

```text
Gamma jet block:       derivatives of R_k(s+lambda)Gamma(s+lambda),
Dirichlet atom n^(-s): n^(-k).                                 (25)
```

The polynomial `(3)` vanishes to the prescribed order at every finite archimedean multiplier
value `s+lambda_i`, while its monomial shadow `(14)` retains the first arithmetic multiplier
`n_0^(-1)`. This gives a canonical finite mixed value that removes any prescribed finite Gamma-jet
family and keeps the leading arithmetic coefficient.

For zeta the preserved coefficient is `c_1=1`; for `-zeta'/zeta` it is the first nonzero von
Mangoldt coefficient. The theorem can therefore seed finite determinant observables in which the
archimedean values are eliminated exactly before prime coefficients are measured. An RH-strength
use additionally requires positivity or a zero-sensitive relation; `(20)` itself is an
unconditional value-separation law.

## Theorem D: simultaneous zeta-jet Dirichlet flag

Fix `q>=1`. Form the square consecutive-value matrix with `N+q` rows, the `N` Gamma-jet columns
from Theorem A, and the `q` zeta-jet columns

```text
zeta(s+k), zeta'(s+k), ..., zeta^((q-1))(s+k),
0<=k<N+q.                                                       (D1)
```

Write `C_(Gamma,E,d)(s)` for the right side of `(5)`. `[PROVED HERE]` The determinant in `(D1)`
has the exact factorization

```text
det(D1)
 =C_(Gamma,E,d)(s)
  det[(L_(E,d) zeta^(j))(s+h)]_(0<=h,j<q).                      (D2)
```

Define the positive double-Vandermonde value

```text
V_q=prod_(1<=a<b<=q)(1/a-1/b) log(b/a) > 0.                    (D3)
```

Then, as real `s->+infinity`,

```text
det[(L_(E,d) zeta^(j))(s+h)]_(0<=h,j<q)
 =(-1)^(Nq) V_q (q!)^(-s) s^(Nq)(1+O(1/s)).                   (D4)
```

Consequently the full mixed matrix `(D1)` is invertible for every sufficiently large real regular
`s`. The complete finite linear family of prescribed Gamma jets together with
`zeta,zeta',...,zeta^((q-1))` therefore contributes exactly `N+q` consecutive-shift value
dimensions.

### Proof of the exact factorization

For `h=q-1,q-2,...,0`, replace row `N+h` by

```text
row_(N+h)+sum_(k=0)^(N-1)a_(E,d,k)(s+h) row_(h+k).              (D5)
```

Descending order ensures that every source row in `(D5)` still has its original values. By
Theorem A, the Gamma-jet entries in the new row vanish. Its `j`-th zeta entry is exactly
`(L_(E,d)zeta^(j))(s+h)`. The transformed matrix is block upper triangular: its upper-left block
is the Gamma Casoratian `(5)` and its lower-right block is the residual determinant in `(D2)`.
The row replacements preserve determinant, proving `(D2)`.

### Proof of the asymptotic flag

From `(15)`, for `0<=h,j<q`,

```text
(L_(E,d)zeta^(j))(s+h)
 =sum_(n>=1)n^(-(s+h)) A_(E,d)(s+h,n^(-1))(-log n)^j.           (D6)
```

Regard the residual matrix as the product of the infinite matrices

```text
B_(h,n)=n^(-(s+h)) A_(E,d)(s+h,n^(-1)),
C_(n,j)=(-log n)^j.                                            (D7)
```

Absolute convergence and finite `q` justify Cauchy--Binet. A repeated Dirichlet index contributes
zero. For an increasing packet `n_1<...<n_q`, one has `n_a>=a`, so

```text
prod_a n_a >= q!,                                              (D8)
```

with equality only for the initial packet `(n_1,...,n_q)=(1,...,q)`. Every other packet is
exponentially smaller. For the initial packet, `(18)` gives

```text
det[B_(h,n)]_(h,n=1,...,q)
 =(-1)^(Nq)s^(Nq)(q!)^(-s)
  det[n^(-h)]_(h,n)(1+O(1/s)).                                 (D9)
```

The two remaining determinants are Vandermonde determinants:

```text
det[n^(-h)]_(h,n=1,...,q)
 det[(-log n)^j]_(n=1,...,q,j)
 =V_q.                                                         (D10)
```

Equations `(D6)`--`(D10)` prove `(D4)`. `QED`

## Positive additional value for the open mixed differential family

The active finite family

```text
{zeta^(j)} union {Gamma^(k)(s+lambda)}                           (26)
```

contains nonlinear differential monomials, whereas Theorem D now classifies its complete linear
value space simultaneously. Extending `(D2)` to algebraic relations in `(26)` requires Casoratian
columns indexed by mixed Gamma and zeta jet monomials rather than individual jets. The present
theorem supplies every individual jet block, their confluent determinant, and the exact initial
Dirichlet flag against which that monomial determinant must be compared.

## Novelty audit

`[NOVELTY UNVERIFIED]` The determinant input is classical and is not claimed as new by itself.
Normand evaluates generalized Vandermonde determinants built from shifted factorials and Gamma
values. Classical Ostrowski and later difference-independence theorems imply broad independence
statements for Dirichlet series.

The candidate-new unit is the combined law `(3)`--`(20)`: the canonical minimal Gamma-jet
annihilator, the explicit Dirichlet coefficient transform `(15)`, the universal first-coefficient
asymptotic `(13)`, the zeta-jet readout `(J2)`, and the augmented mixed-value determinant `(20)`.
The simultaneous extension `(D2)`--`(D4)` identifies the whole initial Dirichlet packet and its
positive double-Vandermonde value.
Searches for `Gamma shift
Casoratian Dirichlet series`, `finite Gamma translate annihilator Dirichlet coefficient`, and
equivalent factorial-basis formulations located the classical determinant parent but not this
residual theorem. A full-text comparison with the modern Gamma--Dirichlet independence papers is
still required before publication.

Primary adjacent sources:

- J.-M. Normand, *Calculation of some determinants using the s-shifted factorial*, J. Phys. A 37
  (2004), 5737--5762, arXiv `math-ph/0401006`.
- A. Ostrowski, *Ueber Dirichletsche Reihen und algebraische Differentialgleichungen*, Math. Z. 8
  (1920), 241--298.
- X.-M. Li, H. Tahir, X.-Y. Gao, *On the algebraic difference independence of the Euler Gamma
  function and Dirichlet series*, Constr. Approx. 58 (2023), 121--149.
- Q. Wang, X. Yao, *Differential and difference independence of zeta and Gamma*, J. Differential
  Equations 412 (2024), 797--807.

## Lean status

`formal/GaloisForLFunctions/GammaShiftCasoratian.lean` proves, without new axioms:

- `det_ascPochhammerEvalMatrix`;
- `Complex.Gamma_add_nat_eq_ascPochhammer_mul`;
- `det_gammaShiftValueMatrix`;
- `det_gammaShiftValueMatrix_ne_zero`;
- `existsUnique_gammaShiftAnnihilatorValues`;
- `dirichletFlagVandermonde_ne_zero`.

These theorems formalize the multiplicity-one specialization of `(5)`, its nonvanishing, the
unique pointwise monic relation, and the noncollision of the reciprocal/logarithmic Dirichlet
signatures in `(D3)`. The confluent jet determinant, coefficient-polynomial construction in `(3)`,
and Dirichlet asymptotic `(13)` remain paper-proved.

## Gates

- [x] exact values and operator specified
- [x] Gamma annihilation proved
- [x] Dirichlet residual asymptotic proved
- [x] zeta specialization proved
- [x] all positive zeta derivatives given their exact first-prime readout
- [x] simultaneous initial zeta-jet determinant factored and its leading Dirichlet packet proved
- [x] determinant core formalized in Lean
- [x] classical determinant parent identified
- [ ] exact residual package cleared against full texts of adjacent Gamma--Dirichlet papers
- [ ] coefficient transform and first-coefficient asymptotic formalized in Lean

## Log

- 2026-07-11 -- extracted from the unresolved finite zeta--multiple-Gamma-shift value family;
  proved the canonical factorial-basis annihilator, its arbitrary Gamma-jet confluent extension,
  the universal first-Dirichlet-value residual, and the simultaneous zeta-jet initial-packet law;
  formalized the multiplicity-one Gamma Casoratian and both Dirichlet-flag Vandermonde values in
  Lean.
