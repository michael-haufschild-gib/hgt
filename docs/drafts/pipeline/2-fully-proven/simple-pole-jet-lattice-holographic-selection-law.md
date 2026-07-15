# The simple-pole jet lattice has an exact holographic selection law

- **ID:** `simple-pole-jet-lattice-holographic-selection-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / FORMALIZED ALGEBRAIC CORE / HT BOUNDARY-GEOMETRY CANDIDATE
- **Scientific status:** `[PROVED HERE: UNIVERSAL LAW AND GLOBAL GAMMA CLASSIFICATION] [FORMALIZED: HOMOGENEOUS TRACE AND RELATIVE SCALE BOUNDARY] [NOVELTY UNVERIFIED]`
- **Methods:** symbolic proof and Lean verification only; no numerical computation

## Constraint

Let a simple-pole germ be written

```text
f(t)=U(t)/t,
```

where `U` is regular and `U(0)` is nonzero.  Give pole order, rather than the ordinary Laurent
exponent, positive sign.  Leibniz gives the exact finite pole profile

```text
f^(j)(t)
  = sum_(k=0)^j binom(j,k) U^(k)(t) (-1)^(j-k) (j-k)! t^(-(j-k+1)).       (1)
```

Introduce a pole-grade variable `T` and independent boundary-jet variables `X_k`.  Equation `(1)`
defines

```text
J_j(T)=sum_(k=0)^j binom(j,k)(-1)^(j-k)(j-k)! X_k T^(j-k+1).              (2)
```

For a constant-coefficient differential polynomial `P(Y_0,Y_1,...)`, its simple-pole profile is

```text
H(P)=P(J_0,J_1,...).                                                       (3)
```

This is a static valuation constraint.  It introduces no time evolution or generative flow.

## Theorem A: exact particle-number boundary trace `[PROVED HERE]`

Suppose `P` is homogeneous of total differential degree `d`.  Then

```text
[T^d] H(P)=P(X_0,X_1,...).                                                 (4)
```

Consequently, if `P` is nonzero, its pole-grade-`d` boundary trace is nonzero.  After specializing
the `X_k` to any algebraically independent family, the trace remains nonzero.

### Proof

Every `J_j` has a common factor `T`:

```text
J_j(T)=T R_j(T),       R_j(0)=X_j.                                        (5)
```

Homogeneity gives

```text
H(P)=T^d P(R_0,R_1,...).                                                    (6)
```

Taking the coefficient of `T^d` is the same as setting every `R_j` to its constant term.  By
`(5)` this gives `P(X_0,X_1,...)`, proving `(4)`.  Algebraic independence makes evaluation on the
actual boundary family injective.

## Theorem B: the universal simple-pole horizon is affine `[PROVED HERE]`

Assume the boundary variables are algebraically free and `X_0` is nonzero.  Then

```text
H(C[Y_0,Y_1,...]) intersect C[X_0,X_1,...][T]_(degree <= 1)
  = C + C J_0.                                                              (7)
```

Equivalently, a constant-coefficient differential-polynomial observable with at most a simple
pole is affine in the undifferentiated carrier.

### Proof

Decompose `P=sum_d P_d` by total differential degree.  The coefficient variables occurring in
`H(P_d)` remain homogeneous of degree `d`.  Contributions from different `d` therefore cannot
cancel.  Theorem A shows that every nonzero `P_d` with `d>=2` has a nonzero pole grade `d`, contrary
to the degree-one horizon.  Hence only degrees zero and one remain.

Write the linear part as

```text
P_1=sum_(j=0)^r c_j Y_j,
```

and take the largest `J` with `c_J` nonzero.  The coefficient of `T^(J+1)` in `H(P_1)` is

```text
c_J (-1)^J J! X_0,
```

which is nonzero.  At-most-simple pole grade therefore forces `J=0`.  This leaves exactly
`C+C Y_0`, proving `(7)`.

The argument is all-order.  The familiar leading-symbol tie between `f f''` and `(f')^2` does not
defeat it: tied most-singular terms may cancel, but the grade equal to total differential degree is
the original polynomial in the complete regular boundary jets and cannot cancel.

## Associated-graded interpretation

Pole order defines a multiplicative filtration on the differential-observable algebra.  The map
in `(4)` identifies the grade-`d` boundary trace of the `d`-particle sector with that sector itself.
Thus the boundary is not merely detecting nonvanishing; it reconstructs the complete homogeneous
observable.

In physical language, total differential degree is a particle-number grading and pole order is a
defect-energy grading.  Equation `(4)` is the exact selection law

```text
nonzero d-particle sector  =>  pole defect at least d.                      (8)
```

The simple-pole horizon therefore admits only vacuum and one-particle observables.  This use of
"horizon" and "holographic" is mathematical: the associated-graded boundary trace recovers the
bulk polynomial.  No Hilbert space, quantum dynamics, entropy, black hole, or empirical physical
identification is asserted.

## Theorem C: the Gamma simple-pole horizon is affine `[PROVED HERE]`

The exact global classification is

```text
C[z][Gamma, Gamma', Gamma'', ...]
  intersect {meromorphic functions having pole order <= 1 at every Gamma pole}
    = C[z] + C[z] Gamma.                                                     (9)
```

### Relative scale--boundary lemma

Put

```text
s_n=(-1)^(n+1)/n!,   z=-n+s_n x,
Gamma(-n+s_n x)=-U_n(x)/x,   U_n(0)=1.                                    (10)
```

Over the rational pole-position field `C(n)`, every finite family

```text
s_n, U_n'(0), U_n''(0), ...                                                 (11)
```

is algebraically independent.

Indeed, `reciprocalSignedFactorialEval_injective` identifies `s_n` as transcendental over every
finite generalized-harmonic coordinate ring over `C(n)`.  The new Lean theorem
`algebraicIndependent_gammaPoleScaleAndHarmonicFamily` packages this as joint relative freeness of
the scale and harmonic boundary.  The exact logarithmic coordinates have triangular form

```text
ell_(n,j)=s_n^(j+1)(alpha_j H_n^(j+1)+beta_j),   alpha_j != 0.              (12)
```

After localizing at the already invertible `s_n`, `(12)` is a birational change of coordinates.
The complete Bell transform from the `ell_(n,j)` to the positive derivatives of `U_n` is triangular
with nonzero diagonal.  Both changes fix `s_n`, so they carry the joint relative freeness to `(11)`.

### Diagonal descent proof

Write a differential polynomial uniquely as

```text
P(z,Y)=sum_alpha p_alpha(z) Y^alpha,
d(alpha)=sum_j alpha_j,
w(alpha)=sum_j j alpha_j.                                                   (13)
```

At the `n`th pole, use `T=x^(-1)`.  From `(2)` and `(10)`,

```text
Gamma^(j)(-n+s_n/T)=-s_n^(-j) J_j(T),
p_alpha(-n+s_n/T)
  =sum_b p_alpha^(b)(-n)/b! s_n^b T^(-b).                                 (14)
```

Suppose a nonlinear monomial occurs.  Choose one `alpha` of some fixed total degree `D>=2` whose
derivative weight `w(alpha)` is maximal among the nonzero degree-`D` coefficients.  In the
coefficient of pole grade `T^D`, isolate the Laurent-boundary monomial

```text
s_n^(-w(alpha)) product_(j>=1) U_n^(j)(0)^alpha_j.                          (15)
```

The factor `U_n(0)=1` is omitted.  A source monomial `beta`, a coefficient Taylor order `b`, and
chosen boundary indices `k<=j` can contribute to `(15)` only if

```text
scale exponent = d(beta)-D-w(alpha).                                       (16)
```

Joint freeness of the factorial scale separates `(16)`, so `d(beta)=D`.  Equality of pole grade
then gives `b=w(beta)-w(alpha)`.  Maximality forces `w(beta)=w(alpha)` and `b=0`; since every chosen
boundary index is at most its source derivative index and their sums agree, every choice is on the
lower edge, hence `beta=alpha`.  The coefficient of `(15)` is therefore exactly the nonzero
rational pole-position function

```text
(-1)^D p_alpha(-n).                                                         (17)
```

This contradicts the assumption that every pole grade at least two vanishes.  Thus every
nonlinear sector is absent.

For the remaining linear sector, choose the largest `r>=1` with coefficient `p_r(z)Y_r`.  Pole
grade `r+1` has the unique leading boundary term

```text
(-1)^(r+1) r! s_n^(-r) p_r(-n),                                            (18)
```

so relative scale--boundary freeness again forces `p_r=0`, a contradiction.  Only the constant
sector and `p_0(z)Gamma(z)` remain.  Conversely, every `A(z)+B(z)Gamma(z)` has at most simple poles.
This proves `(9)`.

The proof uses the whole infinite pole lattice.  At one pole, `x Gamma'+Gamma` is regular; the
factorial scale and moving rational pole position prevent that local cancellation from descending
to one polynomial coefficient in `z` across all poles.

## Sharp boundary attacks

1. **Differential fractions.**  The logarithmic derivative `f'/f` has at most simple poles and is
   nonlinear as a differential rational expression.  Polynomiality in the jets is load-bearing.
2. **Coefficient-base enlargement.**  On the Gamma lattice, a differential-algebraic coefficient
   such as `sin(pi z)` can vanish at every pole.  Enlarging `C(z)` to a DA-saturated coefficient
   field can manufacture cancellations unavailable over `C(z)`.  The global theorem must state
   its base exactly.
3. **One pole.**  The local expression `t f'+f=U'` is regular.  A single pole cannot enforce global
   descent because its local coordinate is available as a coefficient.
4. **Nonfree boundary.**  If the regular jets satisfy algebraic relations, the right side of `(4)`
   can vanish after specialization.  Hypertranscendence of the bulk alone does not automatically
   imply pole-boundary freeness.
5. **Leading symbol only.**  Highest pole grades have genuine tied-weight identities.  The theorem
   survives because it uses the opposite edge of every pole profile, not because those identities
   disappear.

## Nature of hypertranscendence

Abstractly, scalar hypertranscendental generators produce isomorphic free differential rational
fields.  The theorem identifies additional analytic geometry not visible in that abstract field:
the embedding of the free jet algebra into the product of local pole filtrations.  Boundary-jet
freeness makes this embedding filtration-strict and turns singular Laurent data into a complete
associated-graded coordinate system.

This suggests a refinement of binary hypertranscendence:

```text
pole-holographic freeness = differential freeness + filtration-strict singular boundary trace.
```

`[CONJECTURE]` The useful geometric classification of meromorphic hypertranscendental functions is
not by their abstract one-generator differential fields, which are universal, but by the
topological/valuative types of these boundary embeddings.

## RH impact audit

There is no direct RH consequence.  The logarithmic derivative of a completed `L`-function has a
simple-pole divisor, but no algebraically free regular boundary family at its zeros is known.

For the completed zeta function, Theorem C does give one exact archimedean restriction: a
polynomial differential surgery built from the Gamma factor alone cannot preserve its simple-pole
lattice unless it is affine in Gamma.  This rules out nonlinear polynomial Gamma-only
regularizations as hidden RH source producers.  It does not constrain the cancellation between
Gamma poles and zeta's trivial zeros, because zeta is not a coefficient in `C[z]` and the required
joint boundary freeness is not known.

If an RH source carrier were proved pole-holographically free, `(7)` would exclude every nonlinear
differential-polynomial surgery that preserves its simple-pole sector.  An RH-bearing transform
would then have to be affine, differential-rational, or use coefficient data that breaks the pole
filtration.  This is a useful route constraint, not a zero-location theorem.

## Lean surface

`formal/GaloisForLFunctions/HTGeometry/SimplePoleJetLatticeHorizon.lean` formalizes:

1. the exact all-order simple-pole jet profile `(2)`;
2. the factorization `(5)`--`(6)` for homogeneous differential polynomials;
3. the identity boundary trace `(4)`; and
4. survival of that trace under specialization to any algebraically independent boundary family.

`formal/GaloisForLFunctions/HTGeometry/GammaPoleScaleHarmonicRelativeFreeness.lean` formalizes:

1. the joint factorial-scale plus harmonic-boundary evaluation over `C(n)`;
2. its factorization through the existing reciprocal-factorial evaluation; and
3. finite joint algebraic independence of the scale and harmonic boundary over `C(n)`.

The Bell/birational transfer to the actual `U_n` derivatives and the maximal-weight diagonal
descent are proved above on paper but are not yet fully encoded in Lean.  The formalized results are
therefore the two load-bearing algebraic cores, not a falsely advertised formalization of the
analytic intersection `(9)`.

Both touched leaf modules pass direct `lake env lean` verification.  No umbrella or full-project
build was run because this workspace is concurrently shared and the task explicitly requires the
smallest possible build.

## Parent-theory and priority audit

Classical algebraic-differential-equation theory already organizes differential monomials by
degree and weight and derives pole-order bounds; see A. Eremenko,
[Meromorphic solutions of algebraic differential equations](https://www.math.purdue.edu/~eremenko/dvi/mer_ade.pdf).
Gamma hypertranscendence over broad meromorphic coefficient fields is also classical; see S. Bank,
[Some results on the Gamma function and other hypertranscendental functions](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/8A86705994E60591A3AE8F0E89E88222/S0308210500019855a.pdf/some_results_on_the_gamma_function_and_other_hypertranscendental_functions.pdf).
Arc-space differential geometry and differential Rees algebras are broad parents for filtered jet
constructions, but the audited sources do not state the lower-edge reconstruction `(4)` or the
Gamma simple-pole intersection `(9)`.

This negative search is not a priority proof.  Theorem A should be regarded as a clean
associated-graded sharpening of classical pole-degree calculus.  Theorem C is the candidate new
content because it combines the all-order lower edge with the factorial-scale/pole-position
bigrading to classify an actual hypertranscendental differential-polynomial algebra.

## Dual gate

- **Novelty:** plausible but unverified for Theorem C.  The primary-source search found the parent
  degree/weight calculus and classical Gamma hypertranscendence, but not the exact intersection
  classification `(9)`.  Specialist priority review is mandatory before promotion.
- **Significance:** Theorem C gives a new exact rigidity classification inside the differential
  polynomial algebra of the founding hypertranscendental function.  It is more than an analogy or
  repackaging, but it does not yet establish a broad theory or solve a recognized central problem.
- **Fields-Medal gate:** not cleared.  The result is a serious candidate theorem and a definition
  of a broader geometric class, not evidence for the level of field creation or problem resolution
  required by the user-specified bar.

## Gates

- [x] topology/physics language converted to an exact pole-order filtration
- [x] all-order universal trace theorem proved on paper
- [x] homogeneous trace and free-boundary specialization formalized in Lean
- [x] relative scale--harmonic boundary freeness over `C(n)` formalized in Lean
- [x] leading-symbol tie and local-coordinate counterattacks survived
- [x] global Gamma polynomial differential simple-pole classification proved on paper
- [x] primary parent-theory audit completed; priority remains unverified
- [x] exact RH non-consequence recorded
- [x] primary-literature parent audit completed
- [x] global Gamma coefficient descent proved on paper
- [ ] specialist priority audit establishes novelty of Theorem C
- [ ] broad natural class of pole-holographically-free HT functions established
- [ ] dual novelty-significance gate cleared
