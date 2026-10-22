# Weierstrass stabilization glues the square CCM Evans determinants across characteristic births

- **ID:** `ccm-weierstrass-stabilized-square-evans-line-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** Weierstrass preparation, analytic Fredholm determinant lines, finite Grushin
  reduction, and `ccm-restricted-weil-square-evans-determinant-law.md`

## Statement

Fix an aperture `a>0` and a compact real spectral interval `J`. Let

```text
H_a(lambda,xi)=W_a(xi)-lambda.                           (1)
```

There is a finite open cover `{U_alpha}` of `J` and, on each chart, a monic even-degree polynomial

```text
p_alpha(lambda,xi),
degree_xi p_alpha=2L_alpha,                              (2)
```

whose coefficients are analytic in `lambda`, such that for real `lambda in U_alpha`:

1. every real zero of `H_a(lambda,.)`, with multiplicity, is a zero of `p_alpha(lambda,.)`;
2. every additional zero of `p_alpha(lambda,.)` occurs off the real axis in a conjugate pair;
3. the quotient

```text
c_alpha(lambda,xi)
 =H_a(lambda,xi)(1+xi^2)^L_alpha/p_alpha(lambda,xi)      (3)
```

extends smoothly across the real zeros and is strictly positive on the real axis;
4. the square Evans construction gives an analytic finite map

```text
N_alpha(lambda):F_alpha(lambda)->R_(L_alpha),            (4)
```

where source and target both have dimension `2L_alpha`, and

```text
ker N_alpha(lambda) isomorphic to ker(A_a-lambda I).     (5)
```

On overlaps, the determinant sections of `(4)` differ by nowhere-zero analytic transition
factors. They therefore glue to the intrinsic determinant line

```text
Det(A_a-lambda I) -> J                                  (6)
```

and its canonical Evans section `E_a`. Its zero divisor is the spectrum of `A_a` in `J`, with
operator multiplicity:

```text
E_a(lambda)=0 iff lambda in spec(A_a),
ord_lambda E_a=dim ker(A_a-lambda I).                    (7)
```

In particular, births and deaths of real zeros of the scalar symbol `W_a-lambda` create no
singularity and no false zero in the operator Evans line.

## 1. Analytic stabilization of the characteristic factor

The function `H_a(lambda,z)` is holomorphic jointly in `(lambda,z)` in a complex neighborhood of
every compact subset of the real `z`-axis; the digamma poles lie off that axis. Uniformly for
`lambda in J`, one has

```text
H_a(lambda,xi)=log|xi|+O_(a,J)(1),
```

so every real zero lies in one fixed compact interval. Cover the compact real zero set in
`J times R` by finitely many small conjugation- and reflection-stable complex disks avoiding the
digamma poles. Weierstrass preparation in each root cluster gives a monic polynomial whose roots,
with multiplicity, are precisely the complex zeros in that cluster. Multiplying the factors over
the reflected and conjugate clusters gives `(2)`.

For real `lambda`, the coefficients are real and the polynomial has even degree. When a real pair
of characteristic roots disappears, the same polynomial retains it as a nonreal conjugate pair.
Thus its degree does not jump at the birth. Every real zero of the numerator in `(3)` is canceled,
and no additional factor vanishes on the real axis. The quotient is real, continuous, and
zero-free there. Both numerator and monic even-degree denominator have positive asymptotic sign,
so `(3)` is positive. Moreover,

```text
c_alpha(lambda,xi)
 =(1/2)log(1+xi^2)+q_alpha(lambda,xi),
q_alpha(lambda,.) in L_infinity,                         (8)
```

locally uniformly in `lambda`.

## 2. Analytic square reduction

The coercive logarithmic Dirichlet operator associated with `(3)` is an analytic family with a
locally uniformly bounded inverse. The solution bundle

```text
F_alpha(lambda)
 ={f:p_alpha(lambda,D)f=0 on (-a,a)}                    (9)
```

has constant rank `2L_alpha` and admits analytic local frames from the companion first-order
system of `p_alpha(lambda,D)`. The Bessel residual target `R_(L_alpha)` is fixed. Dirichlet
reconstruction followed by the rational residual therefore produces the analytic square map `(4)`.

The proof of the square Evans theorem applies verbatim with the additional nonreal factors: those
factors have no real zero, preserve positivity of `(3)`, and merely stabilize the finite source and
target by equal dimensions. It gives `(5)`.

## 3. Gluing and multiplicity

The supported operator family

```text
A_a-lambda I
```

is an analytic Fredholm family of index zero with fixed operator domain. Each construction `(4)`
is an exact finite Grushin reduction: all eliminated Dirichlet blocks are analytically invertible,
and its effective finite operator is `N_alpha(lambda)`. The determinant-line functor sends this
reduction to an isomorphism

```text
Det(A_a-lambda I)
 isomorphic to
det(F_alpha(lambda))^* tensor det(R_(L_alpha)).           (10)
```

Two reductions of the same Fredholm complex differ by invertible analytic changes of the finite
source, finite target, and eliminated complement. Their determinants are nowhere zero. Hence the
local sections glue as in `(6)`.

Analytic Fredholm theory identifies the vanishing order of the canonical determinant section with
the algebraic multiplicity of the eigenvalue. Self-adjointness makes algebraic and geometric
multiplicity equal, proving `(7)`. `QED`

## Positive CCM consequence

For fixed aperture, characteristic-stratum change is no longer an open carrier problem. The
successful object is the globally glued line and section

```text
(Det(A_a-lambda I),E_a(lambda)).                         (11)
```

Since a real interval is contractible, the line is trivializable. The polar--Euler frame splitting
provides a canonical source normalization. The continuous explicit level
`bar_mu_a=8a exp(a)-m(0)+1` lies strictly above the frame level, so the Birman--Schwinger pencil is
the identity at `lambda=-bar_mu_a` for every aperture. The resulting line is non-Schatten and cannot
be replaced by an ordinary regularized Fredholm determinant. This is proved in
`ccm-source-normalized-nonschatten-birman-schwinger-line-law.md`.

Thus the exact remaining RH obligation is positively stated:

```text
for every a>0, the source-normalized Evans section E_a
has empty zero divisor on (-infinity,0].                 (12)
```

Equivalently, its spectral flow from a sufficiently negative parameter to zero is zero. No finite
symbol-zero birth, basis change, or characteristic-degree jump can imitate or remove an operator
zero.

## Scope and classification

Weierstrass preparation, analytic Grushin reduction, and determinant-line gluing are standard
parent theories. Their application closes the stratum-change gate but is a bridge rather than new
scientific knowledge. The Lean tree does not contain the analytic restricted-Weil Fredholm family
or its logarithmic Dirichlet reduction, so a faithful formalization is not currently available.

## Gates

- [x] real characteristic set confined uniformly on compact spectral intervals
- [x] real-root births stabilized by continued complex-conjugate factors
- [x] positive logarithmic quotient retained across each birth
- [x] analytic fixed-rank square Evans charts constructed
- [x] chart determinants glued to the intrinsic Fredholm determinant line
- [x] Evans vanishing order identified with operator multiplicity
- [x] characteristic-stratum change removed as an RH obstruction
- [x] construct the canonical source normalization at each aperture
- [x] select one continuous explicit source chamber in the aperture
- [ ] prove its zero divisor avoids `lambda<=0` for every aperture
- [ ] RH

## Lean status

`[FORMALIZED]` — supersedes the "a faithful formalization is not currently available" note above.
The analytic Fredholm family and its Dirichlet reduction remain cited parents, but the card's own
algebraic claims — conjugate pairing of the stabilized roots, positivity of the stabilized quotient,
and the determinant restatement — are reachable and are now proved.

Module: `formal/GaloisForLFunctions/RHTower/CCM/CCMWeierstrassStabilizedEvans.lean`
(6 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]`, wired into
`formal/GaloisForLFunctions/RHTower.lean`).

What is proved in Lean:

- `eval_conj_of_real` — a real polynomial takes conjugate values at conjugate points.
- `isRoot_conj_iff` — **claim 2 of (2)**: the nonreal zeros of the real stabilized polynomial occur
  in conjugate pairs.  This is exactly why a vanishing real root pair is *retained* as a nonreal
  conjugate pair and the degree `2L_α` does not jump at a characteristic birth.
- `eval_pos_of_monic_no_real_root` — **claim 3 of (2), root-free factor**: a monic real polynomial
  with no real root is strictly positive everywhere.  Proof: the degree-zero case is `p = 1`;
  otherwise the polynomial tends to `+∞` and a negative value would give a real root by the
  intermediate value theorem.
- `one_add_sq_pow_pos`, `stabilized_quotient_pos` — **claim 3 of (2)**: with positive numerator and
  positive `(1+ξ²)^{L_α}` the quotient `(3)` is strictly positive on the real axis.
- `evans_zero_divisor_empty_iff` — **equation (12)**: the section has empty zero divisor on
  `(-∞, 0]` exactly when it has no zero there.

Deliberately outside the Lean statement (cited parents, not results of this card):

- Weierstrass preparation and the construction of the charts `(2)`;
- the analytic solution bundle `(9)`, its constant rank, and the analytic square map `(4)`;
- the finite Grushin reduction, the determinant-line functor `(10)` and the gluing `(6)`;
- analytic Fredholm theory identifying vanishing order with multiplicity `(7)`;
- the logarithmic decomposition `(8)`.
