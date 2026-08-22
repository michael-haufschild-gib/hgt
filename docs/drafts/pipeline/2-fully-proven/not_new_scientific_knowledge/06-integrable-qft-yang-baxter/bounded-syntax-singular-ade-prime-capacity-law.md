# Bounded ADE syntax has a universal prime-frequency capacity

- **ID:** `bounded-syntax-singular-ade-prime-capacity-law`
- **Stage:** 2-fully-proven / paper proof complete
- **Type:** THEOREM (paper) / POSITIVE COMPLEXITY LAW / GENERAL HT LANDSCAPE
- **Scientific status:** `[PROVED] [SEARCH] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** For every differential-order bound `n` and polynomial-degree bound `d`, there is
  a finite number `B(n,d)`, independent of all complex coefficients, such that every holomorphic
  Bohr-almost-periodic solution of a nonzero scalar autonomous ADE of order at most `n` and degree
  at most `d` carries rational Bohr-frequency rank at most `2B(n,d)`. Consequently every cofinal
  finite-prime realization in this category must grow differential order or polynomial degree.

## 1. Positive law

Let

```text
C{Y}=C[Y_0,Y_1,Y_2,...],
delta(Y_j)=Y_(j+1).                                       (1)
```

For a nonzero differential polynomial

```text
P in C{Y},
ord(P)<=n,
deg(P)<=d,                                                 (2)
```

let

```text
I_P=sqrt[delta]((P)),
V_(P,m)=Z(I_P intersection C[Y_0,...,Y_m]),
kappa(P)=sup_m dim_C V_(P,m).                              (3)
```

Matthew Harrison-Trainor, Jack Klys, and Rahim Moosa prove the following uniform
characteristic-set theorem. For every common degree/order bound `D`, fixed number `u` of
differential indeterminates, and fixed number `q` of commuting derivations, there is

```text
r(D,u,q)<infinity                                          (4)
```

such that every minimal prime differential ideal over a finite system of degree and order at most
`D` has a characteristic set whose degree and order are at most `r(D,u,q)`.

Choose one such bound and put

```text
B(n,d)=r(max(n,d),1,1).                                    (5)
```

`[PROVED]` Every proper `I_P` in `(3)` satisfies

```text
kappa(P)<=B(n,d).                                         (6)
```

Thus bounded differential syntax possesses a universal finite jet capacity. This is a positive
resource attached to the syntax class, not merely a statement that one proposed equation fails.

## 2. Proof of the uniform jet-capacity bound

Put `D=max(n,d)` and `R=r(D,1,1)`. Ritt--Raudenbush decomposition gives finitely many minimal prime
differential ideals

```text
I_P=q_1 intersection ... intersection q_t.                (7)
```

Each `q_a` is a minimal prime differential ideal containing the singleton system `{P}`. By the
uniform theorem, it has a characteristic set of order and degree at most `R`.

Use an orderly ranking. An autoreduced set in one ordinary differential indeterminate contains at
most one polynomial: the leaders of two nonconstant differential polynomials in `Y` would be
derivatives of the same indeterminate and hence one would be a derivative of the other, contrary
to autoreduction. The characteristic set is nonempty because `q_a` contains the nonzero polynomial
`P`. Write it as

```text
{A_a},
h_a=ord(A_a)<=R.                                          (8)
```

Let `y_j` be the image of `Y_j` in `Frac(C{Y}/q_a)`. The initial and separant of `A_a` are nonzero
modulo the prime ideal. Hence

```text
A_a(y_0,...,y_(h_a))=0                                    (9)
```

makes `y_(h_a)` algebraic over `C(y_0,...,y_(h_a-1))`. Differentiating `(9)` gives

```text
Sep(A_a)(y_0,...,y_(h_a)) y_(h_a+1)
  + a rational expression in y_0,...,y_(h_a)=0.           (10)
```

Since the separant is nonzero in the fraction field, `(10)` solves for `y_(h_a+1)`. Repeated
differentiation solves recursively for every higher `y_j`. Therefore

```text
trdeg_C C(y_0,...,y_m)<=h_a<=R                            (11)
```

for every `m`. The left side is the algebraic dimension of the truncation belonging to `q_a`.
Moreover, intersection with `C[Y_0,...,Y_m]` commutes with the finite intersection `(7)`, so

```text
V_(P,m)
 = union_(a=1)^t Z(q_a intersection C[Y_0,...,Y_m]).       (12)
```

The dimension of a finite union is the maximum of the component dimensions. Equations
`(11)`--`(12)` give `dim_C V_(P,m)<=R` for every `m`, proving `(6)`.

The proof includes reducible equations, singular components, and nonunique analytic branches. It
does not invert one globally chosen separant or replace the relation by a vector field.

## 3. Bounded-syntax frequency theorem

Let `f` be holomorphic and uniformly Bohr almost periodic on a horizontal strip and suppose

```text
P(f,f',...,f^(n))=0                                      (13)
```

for a nonzero autonomous `P` satisfying `(2)`. The singular autonomous ADE
Kolchin-frequency theorem gives

```text
rank_Q Gamma(f)=dim_cover X_f<=2kappa(P).                 (14)
```

The same upper bound holds for the frequency group of every continuous translation-equivariant
compact observable of the hull, including the zero-divisor carrier. Combining `(6)` and `(14)`
proves

```text
rank_Q Gamma(f)<=2B(n,d),
rank_Q Gamma(O(f))<=2B(n,d).                              (15)
```

> **Bounded-syntax prime-capacity law.** A scalar autonomous ADE with bounded order and degree has
> a universal finite budget for independent recurrent phases. Coefficients, singularities, and
> branching may choose how that budget is used, but cannot increase it.

## 4. Cofinal prime-growth theorem

For primes at cutoff `N`, put

```text
V_N=span_Q{log p:p<=N},
dim_Q V_N=pi(N).                                          (16)
```

Let `f_N` satisfy a nonzero scalar autonomous ADE `P_N=0`, and suppose `f_N` or a continuous
translation-equivariant compact observable retains `V_N`. If

```text
n_N=ord(P_N),
d_N=deg(P_N),                                             (17)
```

then `(15)` and rational independence of prime logarithms imply

```text
pi(N)<=2B(n_N,d_N).                                       (18)
```

`[PROVED]` Along any cofinal prime exhaustion,

```text
max(n_N,d_N) -> infinity.                                 (19)
```

Indeed, fix `D`. If `n_N,d_N<=D`, apply the uniform theorem directly with the syntax bound `D` to
obtain `pi(N)<=2r(D,1,1)`. For all sufficiently large `N` this is false. Hence eventually
`max(n_N,d_N)>D`. Since `D` was arbitrary, `(19)` follows.

The theorem is qualitative because the parent characteristic-set theorem supplies an existence
bound rather than a useful numerical formula. Its force is uniformity: no bounded-syntax family,
even with coefficients varying arbitrarily with `N`, can absorb a cofinal prime module.

## 5. Positive carrier alternatives

Equation `(19)` says exactly what a successful construction in or near this category must possess.

1. **Growing scalar syntax.** Its differential order or polynomial degree tends to infinity.
2. **Growing state arity.** If order and degree stay bounded, the number of differential unknowns
   must grow; the theorem fixes that number at one.
3. **Coefficient-side arithmetic.** A nonautonomous coefficient hull explicitly carries the missing
   prime-frequency module, subject to the coefficient--state conservation law.
4. **Infinite-dimensional state.** An operator domain, Hilbert/Krein space, determinant class, or
   test-function space carries the unbounded arithmetic rank.
5. **Global constraint.** The construction uses an exact trace, boundary, incidence, or positivity
   constraint without asserting bounded algebraic-differential closure.
6. **Noncompact carrier.** If Bohr compactness is abandoned, a separate faithful cofinal carrier
   theorem must replace the compact-hull argument.

These are exhaustive only relative to the stated scalar autonomous Bohr-almost-periodic category;
they are positive architectural obligations, not claims that the named RH criteria are impossible.

## 6. Consequences for classical RH implementations

The law classifies concrete implementations by where they place the growing resource.

1. **Hilbert--Polya and Connes.** A scalar autonomous spectral surrogate retaining all cutoff prime
   phases must grow order or degree. If its syntax remains bounded, the operator domain, spectral
   measure, trace formula, determinant, or quotient algebra must be the prime carrier.
2. **de Branges.** A bounded-syntax ADE for a Hermite--Biehler phase or canonical Hamiltonian cannot
   carry a cofinal prime module. The nested spaces, Hamiltonian measure, or coefficient data must
   acquire the unbounded capacity.
3. **Nyman--Beurling.** A bounded-syntax scalar closure of the dilation orbit cannot retain all
   cutoff prime directions. The growing approximation space or its nonautonomous dilation data must
   carry them.
4. **Weil positivity.** A bounded-syntax parametrization of the explicit-formula response cannot
   contain the complete prime test module. The full test-function/distribution pairing must remain
   an infinite-dimensional carrier.
5. **Li's criterion.** A bounded-syntax autonomous generator cannot compress the cofinal Li hierarchy
   while faithfully retaining its prime-frequency content. The coefficient sequence, divisor
   measure, or an unbounded-state generator must pay the capacity cost.

Thus the route consequence has the positive form

```text
cofinal faithful prime transport
  => unbounded syntax, unbounded arity, coefficient rank,
     infinite-dimensional state, or a genuinely global constraint.          (20)
```

## 7. Attacks and boundaries

1. **Arbitrary coefficients do not evade the law.** The parent bound is uniform over every
   differential field and all coefficients; coefficient height and transcendence are irrelevant in
   the autonomous constant-coefficient setting.
2. **Singular multiplicity does not evade the law.** All minimal prime components receive the same
   characteristic-set bound, and a finite union cannot raise algebraic dimension above their
   maximum.
3. **A zero relation is not a carrier.** `P=0` is excluded. If a purported specialized equation
   vanishes identically, it supplies no differential constraint and belongs to the unconstrained
   channel.
4. **Large degree is a real resource.** The theorem does not say that fixed order alone bounds
   capacity. Increasing degree is one of the positive escape mechanisms and is intentionally
   counted.
5. **Growing systems are a real resource.** Harrison-Trainor--Klys--Moosa fix the number of
   differential indeterminates. A family with increasing state arity is outside the scalar bound
   and has explicitly exposed its growing carrier.
6. **Nonautonomous coefficients are counted elsewhere.** An almost-periodic coefficient field may
   import prime directions, but the coefficient--state exact sequence records each such direction
   on the coefficient side rather than allowing it to disappear.
7. **No quantitative syntax rate is claimed.** The existential bound proves `(19)` but does not give
   an effective lower bound for `n_N` or `d_N` as a function of `N`.

## 8. Parent and novelty verdict

`[SEARCH] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.

The uniform characteristic-set input is Theorem 6.1 of:

- M. Harrison-Trainor, J. Klys, and R. Moosa, *Nonstandard methods for bounds in differential
  polynomial rings*, arXiv:1105.0600.

The passage from a one-variable characteristic set of order `h` to differential transcendence
degree at most `h` is standard characteristic-set theory. The frequency inequality `(14)` is the
separate singular Kolchin-frequency theorem already proved in this pipeline. Their composition is
useful because it turns the vague escape word “singular” into a concrete positive resource law, but
it is a direct parent-theory bridge and fails the scientific-novelty gate.

## 9. Lean status

The current Lean tree has no characteristic-set theory for differential polynomial ideals, minimal
prime differential decomposition, Kolchin jet dimension, Bohr hull, covering dimension, or
Pontryagin duality sufficient to formalize `(15)`. Adding a theorem-shaped wrapper around the
numerical implication `(18)` would not formalize this claim. The complete unconditional paper proof
belongs in stage 2; movement to stage 3 requires a full unconditional Lean formalization.

## Gates

- [x] positive bounded-syntax capacity defined
- [x] uniform characteristic-set bound transferred to every singular component
- [x] universal Kolchin jet-capacity theorem proved
- [x] universal Bohr-frequency capacity theorem proved
- [x] cofinal prime-growth consequence proved
- [x] singular, coefficient, arity, and degenerate boundaries attacked
- [x] exact parent theorem located and novelty rejected
- [ ] complete unconditional Lean formalization
