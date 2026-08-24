# Rational Euler readout aperture equals visible character-lattice rank

- **ID:** `finite-euler-exact-differential-order-aperture-law`
- **Stage:** 3-formalized / Lean 4 proof complete
- **Type:** THEOREM (paper) / POSITIVE DIFFERENTIAL-STATE LAW / GENERAL HT LANDSCAPE
- **Scientific status:** `[PROVED] [SEARCH] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Every rational scalar readout of `k` rationally independent exponential source
  coordinates has minimal autonomous algebraic-differential order exactly equal to the rank of its
  visible Taylor-character lattice. It has order below `k` exactly when it is invariant under a
  positive-dimensional algebraic subtorus of the source phases. In particular, a finite Euler product, its inverse
  anchor, its logarithmic derivative, and its finite diagonal determinant realization over a prime
  set `S` all have minimal differential order exactly `#S`, both over the constants and over the
  Euler--Gamma differential field `C(s)<Gamma>`. Thus every retained independent prime contributes
  one irreducible scalar differential-state coordinate; rational readout and Gamma completion
  cannot compress this cost.

## 1. Differential aperture

For a differential field `K` of meromorphic functions with derivation `D=d/ds`, define the
**differential aperture** of `f` over `K` by

```text
ap_K(f)=min{n>=0:
  there exists 0!=P in K[Y_0,...,Y_n]
  with P(f,Df,...,D^n f)=0},                               (1)
```

with `ap_K(f)=infinity` when no such `n` exists. Thus `ap_K(f)=infinity` is
hypertranscendence over `K`, while finite aperture quantitatively records the least number of
successive derivatives needed by any algebraic differential constraint.

Let `lambda_1,...,lambda_k` be positive real numbers linearly independent over `Q`. Put

```text
x_i(s)=exp(-lambda_i s),
D x_i=-lambda_i x_i.                                      (2)
```

Let `B in C(X_1,...,X_k)` be nonconstant and regular at the origin. Write its convergent Taylor
expansion there as

```text
B(X)=sum_(alpha in N^k)c_alpha X^alpha.                   (3a)
```

Define its visible character lattice and rank by

```text
L_B=span_Z{alpha:c_alpha!=0, alpha!=0} subset Z^k,
r_B=rank_Z L_B.                                           (3b)
```

On a sufficiently far right half-plane put

```text
f_B(s)=B(x_1(s),...,x_k(s)).                               (4)
```

`[PROVED]` The exact rational-readout law is

```text
ap_C(f_B)=r_B.                                            (5a)
```

Thus rational scalar observation costs one differential order for every visible independent
character, not for every displayed coordinate.

The first-order-faithful case is the full-rank specialization:

```text
partial B/partial X_i evaluated at X=0 !=0
for every i.                                               (3)
```

Then `c_(e_i)!=0` for every coordinate vector `e_i`, so `L_B=Z^k`, `r_B=k`, and `(5a)` becomes

```text
ap_C(f_B)=k.                                               (5)
```

Thus rational scalar observation does not compress independent exponential-state dimension.

The separated-source form is the important additive specialization. Let `R_i in C(X)` be regular
at `X=0` and satisfy

```text
R_i(0)=0,
R_i'(0)!=0.                                               (6)
```

On a right half-plane on which the summands are holomorphic, set

```text
f(s)=sum_(i=1)^k R_i(x_i(s)).                             (7a)
```

Then `B(X)=sum_i R_i(X_i)` satisfies `(3)`, so

```text
ap_C(f)=k.                                                 (7)
```

This is a positive additivity theorem: every rationally independent exponential coordinate costs
exactly one unit of scalar autonomous differential order.

## 2. Algebraic independence of the source coordinates

The evaluation map

```text
ev:C(X_1,...,X_k)->Mer(H),
X_i |-> exp(-lambda_i s)                                  (8)
```

is injective. Indeed, a polynomial in the kernel would give a finite identity

```text
sum_alpha c_alpha exp(-(alpha dot lambda)s)=0.             (9)
```

The exponents `alpha dot lambda` are distinct because the `lambda_i` are rationally independent.
Ordering them and letting real `s` tend to positive infinity makes the least exponent dominate;
its coefficient is zero. Iteration kills every coefficient. Clearing denominators proves
injectivity on the rational function field.

Equip `C(X_1,...,X_k)` with the derivation

```text
Delta=-sum_(i=1)^k lambda_i X_i partial_(X_i).            (10)
```

Then `ev` is a differential-field embedding and

```text
D^j f_B=ev(Delta^j B).                                    (11)
```

## 3. The observability determinant

For `j=0,...,k-1`, put `B_j=Delta^j B` and

```text
b_i=partial B/partial X_i evaluated at X=0 !=0.           (12)
```

Since `Delta` acts on the linear coordinate `X_i` by the eigenvalue `-lambda_i`,

```text
partial B_j/partial X_i evaluated at X=0
  =b_i(-lambda_i)^j.                                      (13)
```

Therefore the Jacobian determinant of `(B_0,...,B_(k-1))` at the origin is

```text
det J
 =product_i b_i
   product_(1<=i<j<=k)((-lambda_j)-(-lambda_i)) !=0.       (14)
```

The characteristic-zero Jacobian criterion gives

```text
B_0,...,B_(k-1) algebraically independent over C.         (15)
```

Injectivity of `ev` transfers `(15)` to

```text
f_B,Df_B,...,D^(k-1)f_B algebraically independent over C. (16)
```

Hence `ap_C(f_B)>=k`.

Conversely, all `B_j` lie in `C(X_1,...,X_k)`, a field of transcendence degree `k`. The `k+1`
elements

```text
B_0,...,B_k                                               (17)
```

are algebraically dependent. Applying `ev` supplies a nonzero autonomous ADE for `f_B` of order at
most `k`. Together with `(16)`, this proves `(5)` and hence the separated form `(7)`.

The proof does more than count Bohr-hull real dimension: it identifies a nonsingular complex
observability determinant and therefore obtains one full order per source coordinate, rather than
the weaker half-rank floor.

## 3a. Full character-lattice classification

The Jacobian argument proves the important full-rank case directly. The general equality `(5a)`
has a complementary support-and-symmetry proof.

Under the differential embedding `ev`, the Taylor series `(3a)` becomes the generalized Dirichlet
series

```text
f_B(s)=sum_alpha c_alpha exp(-(alpha dot lambda)s).        (17a)
```

Rational independence of the `lambda_i` makes distinct Taylor characters have distinct exponents,
and identifies the rational rank of the exponent support with `r_B`. The Cano--Fortuny Ayuso
support-rank theorem says that a generalized power-series solution of a constant-coefficient ADE
of order `n` has support rank at most `n`. Therefore

```text
ap_C(f_B)>=r_B.                                           (17b)
```

For the reverse inequality, let

```text
H_B={t in (C^x)^k:t^alpha=1 for every alpha in L_B}.       (17c)
```

This algebraic subgroup has dimension `k-r_B`. Every `t in H_B` fixes the Taylor expansion of `B`
at the origin, so `B(tX)=B(X)` as a rational-function identity. Hence

```text
B in C(X_1,...,X_k)^(H_B).                                (17d)
```

The diagonal derivation `Delta` commutes with the coordinate torus and preserves this invariant
field. The invariant field is the function field of the quotient torus and has transcendence
degree `r_B`. Thus

```text
B,Delta B,...,Delta^(r_B)B
```

are algebraically dependent. Applying `ev` gives `ap_C(f_B)<=r_B`, proving `(5a)`.

Equivalently,

```text
ap_C(f_B)<k
  iff dim H_B>0
  iff B factors rationally through a quotient torus of dimension <k.         (17e)
```

> **Rational compression classification.** Every scalar differential order saved by a rational
> readout is paid for by an exact algebraic subtorus of source phases that the readout identifies.
> A rational readout with no positive-dimensional phase blindness has full aperture, even when all
> of its first derivatives at the origin vanish.

## 4. Exact finite-Euler law

Let `S` be a nonempty finite set of primes and put

```text
E_S(s)=-D log product_(p in S)(1-p^(-s))^(-1)
      =sum_(p in S) (log p)p^(-s)/(1-p^(-s)).             (18)
```

Take

```text
lambda_p=log p,
R_p(X)=(log p)X/(1-X).                                   (19)
```

Unique factorization makes the `log p`, `p in S`, rationally independent, and
`R_p'(0)=log p!=0`. Equation `(5)` gives

```text
ap_C(E_S)=#S.                                             (20)
```

More generally, nonzero degree-one Euler parameters

```text
E_(S,a)(s)=sum_(p in S) (log p)a_p p^(-s)/(1-a_p p^(-s)),
a_p!=0,                                                   (21)
```

obey the same exact law, since the new local derivative at zero is `(log p)a_p`.

For the canonical cutoff `S_N={p prime:p<=N}`,

```text
ap_C(E_(S_N))=pi(N).                                     (22)
```

The same exact aperture holds for the finite Euler product and its inverse anchor:

```text
Z_S(s)=product_(p in S)(1-p^(-s))^(-1),
A_S(s)=product_(p in S)(1-p^(-s)),

ap_C(Z_S)=ap_C(A_S)=#S.                                  (23)
```

Indeed, the rational readouts `product_i(1-X_i)^(-1)` and `product_i(1-X_i)` have partial
derivatives `1` and `-1`, respectively, at the origin. Any finite diagonal determinant realizing
`A_S` is therefore subject to the same exact aperture: determinant formation packages the source
coordinates multiplicatively but does not reduce their scalar differential order.

## 5. Gamma-relative noncompression

Let

```text
K_Gamma=C(s)<Gamma>.                                     (24)
```

The Gamma projective-boundary theorem says that every finite nonzero coefficient tuple in
`K_Gamma` has a nonzero constant projective limit under upper vertical translation. This implies

```text
ap_(K_Gamma)(f_B)=ap_C(f_B)=r_B.                         (25)
```

for every rational readout `(4)`.

### Proof

The inequality `ap_(K_Gamma)(f_B)<=r_B` follows from the constant-coefficient relation already
constructed in Section 3a. Suppose conversely that a relation of order `n<r_B` exists:

```text
sum_alpha A_alpha(s)
  product_(j=0)^n (D^j f_B(s))^(alpha_j)=0,
A_alpha in K_Gamma,                                      (26)
```

with a nonzero finite coefficient tuple.

The finite quasiperiodic readout `f_B` has return times `T_l->+infinity` such that

```text
D^j f_B(s+iT_l)->D^j f_B(s),
j=0,...,n,                                                (27)
```

locally uniformly on every right vertical strip avoiding the poles. Translate `(26)` by `iT_l`.
The one-point projective-boundary theorem supplies an index `beta` for which

```text
A_alpha(s+iT_l)/A_beta(s+iT_l)->d_alpha in C              (28)
```

locally uniformly, with `(d_alpha)` nonzero. Divide the translated relation by `A_beta` and pass
to the limit using `(27)`--`(28)`. This gives the nonzero constant-coefficient relation

```text
sum_alpha d_alpha
  product_(j=0)^n (D^j f_B(s))^(alpha_j)=0,               (29)
```

contradicting `(5a)` because `n<r_B`. Thus `(25)` holds. In particular,

```text
ap_(C(s)<Gamma>)(E_S)
 =ap_(C(s)<Gamma>)(Z_S)
 =ap_(C(s)<Gamma>)(A_S)=#S.                              (30)
```

The archimedean Gamma field contributes substantial hypertranscendental and asymptotic structure,
but it contributes no compression of the finite Euler differential aperture.

## 6. Constraint-order recession

For a nested cofinal prime exhaustion `S_N`, equation `(30)` gives

```text
ap_(C(s)<Gamma>)(E_(S_N))=pi(N)->infinity.               (31)
```

The infinite Euler logarithmic source

```text
E(s)=-zeta'(s)/zeta(s)
    =sum_(p,m>=1)(log p)p^(-ms),
Re s>1,                                                   (32)
```

has infinite prime-log support rank and is hypertranscendental over `C(s)<Gamma>`. Thus `(31)` is
the exact finite-level approach to the infinite statement:

> **Constraint-order recession law.** The Euler source reaches hypertranscendence through the
> divergence of an exact finite differential aperture. Each new independent prime raises the
> least possible scalar ADE order by one; the cofinal limit has no finite algebraic-differential
> handle.

This is a quantitative landscape description of how DA finite Euler objects converge toward an HT
source. It does not infer zero locations from hypertranscendence.

## 7. Positive consequences for RH implementations

Every concrete implementation that claims to compress the finite Euler logarithmic source into a
scalar ADE over the Gamma completion must expose the exact resource

```text
differential order through N >= pi(N).                    (33)
```

Accordingly:

1. **Hilbert--Polya and Connes.** A bounded-order scalar source equation cannot be the arithmetic
   generator. A viable construction places at least `pi(N)` source coordinates in its operator
   domain, resolvent algebra, trace, determinant, or another growing state carrier.
2. **de Branges.** If the Hermite--Biehler phase or canonical Hamiltonian is claimed to generate the
   Euler source through a scalar Gamma-coefficient ADE, its order must grow by one per retained
   prime. Otherwise the nested spaces or Hamiltonian measure must carry those coordinates.
3. **Nyman--Beurling.** A scalar differential closure of the finite dilation source has exact order
   cost `pi(N)` when it faithfully retains the prime exponent module. A viable route keeps the
   growing approximation space as the carrier.
4. **Weil positivity.** A scalar ADE parametrization cannot compress the complete finite-prime
   response below order `pi(N)`; the test-function/distribution pairing must retain the missing
   source coordinates.
5. **Li's criterion.** A bounded-order scalar generator cannot faithfully encode the cofinal prime
   contribution to the Li hierarchy. The coefficient hierarchy, divisor measure, or an
   infinite-dimensional generator must carry the order recession.

These are implementation laws, not categorical rejections of the exact RH-equivalent criteria.
Their positive common form is

```text
k independent prime coordinates
  => a rational scalar readout has aperture equal to its visible character rank;
     full source faithfulness costs k, while every saved order is an exact
     subtorus of phase blindness.                                             (34)
```

## 8. Attacks and boundaries

1. **Frequency independence is load-bearing.** Resonant `lambda_i` can belong to a smaller
   exponential field. The natural cost is the rational rank of the exponent group, not the number
   of displayed summands.
2. **First-order visibility is not the categorical boundary.** Condition `(3)` is load-bearing only
   for the short Jacobian proof. The character-lattice theorem `(5a)` covers tangent-blind rational
   readouts as well. Full aperture fails only through an actual positive-dimensional subtorus
   symmetry.
3. **Arbitrary coefficient enrichment can compress the order.** If the coefficient field already
   contains some `x_i`, the corresponding source coordinate can disappear from the relative cost.
   Equation `(25)` is special to coefficient fields with a constant projective return boundary.
4. **Gamma completion is not declared simple.** `K_Gamma` is itself hypertranscendental and
   noncompact. The theorem says only that its one-point projective boundary prevents it from
   absorbing recurrent prime coordinates.
5. **Finite Euler factors are DA.** Hypertranscendence occurs only at the cofinal infinite-rank
   limit. Calling every finite cutoff HT would reverse the theorem.
6. **No zero theorem follows.** Exact differential order measures source-state complexity, not
   divisor position, self-adjointness, or positivity.

## 9. Parent and novelty verdict

`[SEARCH] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.

Two recent parent results make the constant-coefficient order law a direct bridge:

1. J. Cano and P. Fortuny Ayuso, *The rational rank of the support of generalized power series
   solutions of differential and q-difference equations*, Indagationes Mathematicae (2026),
   Theorem 1, prove that support rank modulo coefficient support is at most differential order.
   Applied to `(18)`, this gives `#S<=ap_C(E_S)`.
2. B. Teguia Tabuguia, *Arithmetic of D-Algebraic Functions*, Journal of Symbolic Computation 126
   (2025), proves the sum-of-input-orders upper bound for rational expressions of DA functions.
   Each local Euler coordinate is first-order, giving `ap_C(E_S)<=#S`.

Sections 2--3 provide a short self-contained Jacobian proof in the first-order-faithful class.
Section 3a combines the published support-rank theorem with standard algebraic-torus invariant
fields to classify every rational readout. The Gamma-relative equality uses the separately proved one-point projective
boundary of `C(s)<Gamma>`. This exact synthesis is operationally stronger than the earlier
half-prime-count hull bound, but it introduces no mechanism beyond the parent support-rank,
D-algebraic arithmetic, and projective-boundary theorems. It therefore fails the scientific-novelty
gate.

Primary sources:

- `https://doi.org/10.1016/j.indag.2026.04.001`
- `https://arxiv.org/abs/2305.00702`

## 10. Lean status

`[FORMALIZED]` Complete unconditional Lean 4 formalization.

Primary capstones:

- `HTGeometry/RationalPhaseCharacterRankAperture.lean` proves existence of a rank-order
  autonomous relation for every analytic rational presentation, exact minimal order equal to the
  active character-lattice rank, and equivalence of order compression with a
  positive-dimensional character stabilizer. Here `activeSupport` is the Cauchy/Fourier
  realization of visible Taylor characters on a sufficiently far-right phase torus.
- `HTGeometry/FiniteEulerExactDifferentialOrderApertureLaw.lean` packages exact constant-field
  orders of finite Euler anchor, product, logarithmic flux, and diagonal characteristic
  determinant; exact Gamma-field orders of anchor, product, and flux; canonical cutoff equality
  with `Nat.primeCounting N`; recession to infinity; and Gamma-hypertranscendence of the concrete
  infinite source `-ζ′/ζ`.
- Supporting modules `RationalDiagonalDerivation.lean`,
  `RationalDiagonalJetDependence.lean`, `LocalizationDerivationMap.lean`,
  `AnalyticRationalCharacterStabilizer.lean`, `FiniteEulerApertureCompletion.lean`, and
  `FiniteEulerGammaMeroAperture.lean` supply quotient-rule transport, torus-invariant state-field
  rank, analytic realization, finite specializations, and Gamma-relative lower bounds.

Both new capstone modules pass direct `lake env lean` checks and targeted `lake build` audits.
`#print axioms` reports only Lean baseline principles `propext`, `Classical.choice`, and
`Quot.sound` for every new endpoint; no project axiom or unproved declaration is used.

## Gates

- [x] differential aperture defined
- [x] exponential-coordinate field embedded faithfully
- [x] full observability determinant proved nonzero
- [x] exact arbitrary rational-readout character-lattice order proved
- [x] compression classified exactly by positive-dimensional subtorus blindness
- [x] exact finite-Euler specialization proved
- [x] product, inverse-anchor, and determinant noncompression proved
- [x] Gamma-relative noncompression proved
- [x] cofinal constraint-order recession proved
- [x] route consequences stated positively
- [x] exact parent literature located and novelty rejected
- [x] complete unconditional Lean formalization

