# The simple-pole jet lattice has an exact holographic selection law

- **ID:** `simple-pole-jet-lattice-holographic-selection-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM (universal/profile parts) / CONJECTURE (native global Gamma intersection) / HT BOUNDARY-GEOMETRY CANDIDATE
- **Scientific status:** `[PROVED AND FORMALIZED: UNIVERSAL LAW, CONSTANT-COEFFICIENT HORIZON, C(n)-RELATIVE SCALE/DERIVATIVE FREEDOM, MOVING C[z] TAYLOR REFLECTION, FAITHFUL TWO-STAGE LAURENT PROFILE, CONSERVED TRI-GRADING, NONLINEAR MAXIMAL-WEIGHT REFLECTION, FULL SYMBOLIC/ACTUAL MOVING-POLE JET INJECTIVITY, EXACT MOVING-COEFFICIENT AFFINE PROFILE HORIZON, DYNAMIC COVARIANT GAMMA VALUE REALIZATION, AND FIRST/SECOND-SUBPRINCIPAL REFLECTION] [OPEN: NATIVE MEROMORPHIC-ORDER TO FROZEN-PROFILE DESCENT] [GLOBAL GAMMA INTERSECTION IS A CANDIDATE, NOT YET A THEOREM] [NOVELTY UNVERIFIED]`
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

## Candidate C: the native Gamma simple-pole horizon is affine `[OPEN ANALYTIC DESCENT]`

The proposed global classification is

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

At the `n`th pole, use `T=x^(-1)`.  The exact running-point law is

```text
J_(n,j)(x,T)
  =sum_(k=0)^j binom(j,k)(-1)^(j-k)(j-k)! U_n^(k)(x) T^(j-k+1),
Gamma^(j)(-n+s_n x)=-s_n^(-j) J_(n,j)(x,x^(-1)),
p_alpha(-n+s_n/T)
  =sum_b p_alpha^(b)(-n)/b! s_n^b T^(-b).                                 (14)
```

The variables in the universal profile therefore represent the **dynamic** regular jets
`U_n^(k)(x)` before the boundary is frozen.  Replacing them pointwise by `U_n^(k)(0)` in the first
line is invalid: Taylor variation of the regular jets can cancel lower displayed pole grades.  The
frozen profile is the boundary value of this covariant law, not the native Laurent expansion by
definition.  This distinction was missed in the earlier version of the card.

The repaired analytic interface is the ring-homomorphism value relation

```text
gammaPolyJetEval(-n+s_n x,P)
  = gammaPoleCovariantPolynomialJetEval(n,x,P)                             (14a)
```

on a deleted neighborhood of `x=0`.  It follows from the exact Leibniz law for `U/x`, the affine
chain rule, and the now hypothesis-free deleted-neighborhood identity
`Gamma(-n+s_n x)=-U_n(x)/x`.  Consequently the two sides of `(14a)` have the same native
`meromorphicOrderAt` at zero.

What remains is a triangular freezing theorem: native order at least `-1` must force the forbidden
frozen profile coefficients to vanish after all Taylor contributions from the dynamic
`U_n^(k)(x)` have been accounted for.  Boundary freeness alone does not prove this implication.
Until that descent is paper-proved and formalized, the global equality `(9)` is a conjectural
endpoint; the diagonal argument below proves the classification only after the frozen profile
cutoff has been obtained.

### Reciprocal-Bell compression of the analytic descent

There is a sharper way to organize the Taylor terms.  Put

```text
S_n(x)=1/Gamma(-n+s_n x),   F_n(x)=S_n(x)^(-1).
```

Thus `S_n` is the normalized reciprocal-Gamma simple-zero section and `F_n` is the normalized
Gamma pole.  Let `P(Y_0,...,Y_(r+1))` be nonzero and homogeneous of particle degree `D`.  First
dehomogenize the pole factor,

```text
H(Z_0,...,Z_r)=P(1,Z_0,...,Z_r).
```

Homogeneity makes this dehomogenization faithful.  Let `B` be the finite complete-Bell
automorphism and let `sigma` negate every raw logarithmic jet.  Define

```text
Q = B^(-1) sigma B(H),      E = totalDegree(Q).                            (14b)
```

The generic Bell identity for an inverse section gives the exact punctured-neighborhood value
law

```text
P(F_n,F_n',...,F_n^(r+1))
  = F_n^D Q(S_n'/S_n,S_n''/S_n,...,S_n^(r+1)/S_n).                         (14c)
```

No frozen coefficient is used in `(14c)`.  The first `B` expresses the normalized derivatives
`F_n^(j)/F_n` in the raw logarithmic jets of `F_n`; `sigma` uses
`(log F_n)'=-(log S_n)'`; and `B^(-1)` passes to the simple-zero covariant jets.  Every map in
`(14b)` is injective on the stated homogeneous sector, so `Q != 0`.

The already formalized reciprocal-Gamma simple-zero horizon detects every nonzero `Q` cofinally
with exact order `-E`.  Since `F_n` has exact order `-1`, multiplication in `(14c)` gives the
cofinal native order law

```text
ord_0 P(F_n,F_n',...,F_n^(r+1)) = -(D+E)                                  (14d)
```

on arbitrarily remote branches.  This compresses all successive Taylor cancellations inside one
homogeneous local-coordinate sector into the single polynomial invariant `Q`; for example the
leading cancellation in `F F''-2(F')^2` becomes the nonzero covariant coordinate `-S''/S`, so
the surviving order is `-3`, not an ad hoc next-coefficient calculation.

Equation `(14d)` is dependency-closed on paper from the generic Bell identity, homogeneous
dehomogenization, the polynomial Bell automorphism, the reciprocal-Gamma covariant order theorem,
and meromorphic-order additivity.  `GammaPoleReciprocalBellOrder.lean` formalizes the generic
value law `(14c)`, proves that `Q` is nonzero, reflects the inverse-section model to the genuine
factorial Gamma zoom, and proves both the cofinal exact order `(14d)` and the complete homogeneous
cutoff law

```text
forall n, ord_0 P(F_n,F_n',...) >= -r  <->  D+E <= r.                      (14e)
```

For a bihomogeneous constant-coefficient sector of derivative weight `W`, the affine chain rule
gives a single common factor

```text
P(F_n,F_n',...) = s_n^W P(Gamma,Gamma',...) .                             (14f)
```

Since `s_n != 0`, native `z`-derivatives have the same exact cutoff `D+E`; their normalized top
residue is the residue in `(14d)` multiplied by `s_n^(-W)`.  Thus the native-coordinate problem
is completely closed inside every bihomogeneous sector.  In source form, a nonzero homogeneous
sector lies at the at-most-simple horizon iff it is a scalar or a scalar multiple of the
undifferentiated Gamma carrier; the derivative-weight hypothesis needed for native coordinates
does not enlarge that class.

There is also a faithful cross-particle completion.  Introduce a polynomial variable `A` and set

```text
R_P(A)=sum_D A^D B^(-1) sigma B(P_D(1,Z_0,...,Z_r)),                      (14g)
```

where `P_D` is the particle-degree-`D` homogeneous component.  The map `P |-> R_P` is an injective
ring homomorphism, and every finite inverse-section jet polynomial satisfies the single value law

```text
P(F_n,F_n',...) = R_P(F_n; S_n'/S_n,S_n''/S_n,...).
```

This subsumes `(14c)` and retains all cross-particle addition and multiplication data that
dehomogenization alone forgets.  The remaining global step is now narrower: after decomposing
`R_P` by derivative weight, prove that the explicit factors `s_n^(-W)` prevent cancellation among
the maximal surviving `D+E` residues, and then incorporate moving polynomial coefficients.  This
is an order-level scale-separation problem, not the former uncontrolled freezing of all regular
jets.

The scale-separation invariant is now dependency-closed.  Give the covariant coordinate `A_j`
weight `j+1`.  Complete Bell substitution, sign reflection, inverse Bell substitution, and
homogeneous dehomogenization all preserve derivative weight, so a bihomogeneous source sector
`P_(D,W)` has reciprocal-Bell transform `Q_(D,W)` of covariant weight `W`.  If
`E=totalDegree(Q_(D,W))`, then fixing the universal first residue in the top ordinary-homogeneous
part leaves the exact residual grading

```text
weight_tail(dehom(homogeneous_E(Q_(D,W)))) = W-E.                         (14h)
```

This is the missing hostile-test invariant.  At a fixed maximal native pole order `M=D+E`, two
different particle degrees have different `E`; at a fixed derivative weight `W`, equation `(14h)`
puts their top residues in different residual-weight summands.  They therefore cannot cancel.
Terms with different `W` carry different Laurent powers `s_n^(-W)` and are separated by joint
freeness of the factorial scale and the reciprocal-unit coefficients.  Since homogeneous
dehomogenization is faithful, every nonzero top sector contributes a nonzero symbolic residue;
the joint Laurent value-reflection theorem makes its pole-index germ nonzero and hence nonzero on
arbitrarily remote branches.  Thus a nonzero constant-coefficient packet realizes the maximal
`D+E` of its bihomogeneous sectors cofinally.  In particular the full native constant-coefficient
at-most-simple intersection is affine in undifferentiated Gamma.  Lean now formalizes the grading
and residual-weight part `(14h)`; the finite maximal-residue sum and its cofinal analytic
reflection remain to be encoded before this constant-coefficient conclusion is marked formalized.

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
This proves the frozen-profile analogue of `(9)`.  The native meromorphic conclusion still needs
the dynamic-to-frozen descent stated after `(14a)`.

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

The diagonal proof gives a nonempty general class, not only a Gamma example.  Let `f` have
infinitely many distinct simple poles `a_n`; normalize by each nonzero residue scale `s_n` so that

```text
f(a_n+s_n x)=U_n(x)/x,   U_n(0)=1.                                        (19)
```

Call this pole tower **boundary scale-separated pole-holographically free** if every finite family

```text
s_n, U_n'(0), U_n''(0), ...                                                (20)
```

is algebraically independent over the rational pole-position germ field `C(a_n)`.  The diagonal
proof gives the following frozen-profile preimage law; obtaining the native meromorphic statement
also requires a dynamic-freezing hypothesis:

```text
{P in C[z][Y_0,Y_1,...] : P(z,f,f',...) has pole order <= 1 on the tower}
  = C[z]+C[z]Y_0.                                                          (21)
```

Under that additional analytic hypothesis, the image intersection would be `C[z]+C[z]f`, and the
preimage statement would also prove hypertranscendence.  Boundary-value freeness alone does not
currently justify those native conclusions.

Thus hypertranscendence is not only the absence of a finite flow.  For this class it is positively
encoded by a static boundary embedding with two independent valuations: differential particle
number is read by pole grade, while residue-scale exponent keeps the particle sectors separated
after normalization.  Gamma is the first carrier with the full frozen boundary algebra and the
exact dynamic covariant value realization, but its native affine intersection remains open.

`[CONJECTURE]` The useful geometric classification of meromorphic hypertranscendental functions is
by the topological/valuative type and rank of these boundary embeddings, not by their abstract
one-generator differential fields, which are universal.

## RH impact audit

There is no direct RH consequence.  The logarithmic derivative of a completed `L`-function has a
simple-pole divisor, but no algebraically free regular boundary family at its zeros is known.

For the completed zeta function, the proved frozen-profile theorem gives an archimedean route
constraint: a nonlinear Gamma-only polynomial surgery cannot remain inside the frozen simple-pole
profile.  Turning that into a native simple-pole statement requires Candidate C.  Neither form
constrains cancellation between Gamma poles and zeta's trivial zeros, because zeta is not a
coefficient in `C[z]` and the required joint boundary control is not known.

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

`formal/GaloisForLFunctions/HTGeometry/SimplePoleJetLatticeAffineHorizon.lean` now formalizes
Theorem B for every finite jet order:

1. flattening the pole variable and regular-boundary variables into one weighted polynomial ring;
2. preservation of boundary homogeneous degree in every pole-grade coefficient;
3. separation of the top homogeneous source sector for an arbitrary differential polynomial;
4. the exact diagonal law by which the `X_0` coefficient at pole grade `j+1` reads the linear
   `j`th-jet coefficient; and
5. the unconditional equivalence
   `pole degree <= 1 <-> P = a + b Y_0`.

`formal/GaloisForLFunctions/HTGeometry/MvPolynomialHomogeneousDehomogenization.lean` extracts the
general algebraic interface behind the specialization arguments.  For an arbitrary nontrivial
commutative semiring and arbitrary tail-variable type, it proves that the coefficient of the head
variable in `optionEquivLeft` retains the residual homogeneous or weighted-homogeneous degree, and
that setting the head coordinate to one cannot kill a nonzero homogeneous polynomial.  This
removes the former finite-index hypothesis from the Bell-profile use of the law.

`MvPolynomialTopHomogeneousComponent.lean` now extracts the other shared source-side interface:
over an arbitrary commutative semiring and arbitrary index type, the homogeneous component at total
degree of a nonzero multivariate polynomial is nonzero.  The former finite Bell and general
simple-pole copies have been replaced by this one law, so the two horizon theories can be imported
and composed in the same module.

`SimplePoleJetScaleSeparatedHorizon.lean` and
`SimplePoleJetScaleSeparatedReesGrading.lean` formalize the independent moving scale `S`, its
retraction to the universal boundary, the exact coefficient/particle trace, the universal affine
horizon after adjoining `S`, and the conserved scale--pole--boundary grading.

`formal/GaloisForLFunctions/HTGeometry/GammaPoleScaleHarmonicRelativeFreeness.lean` formalizes:

1. the joint factorial-scale plus harmonic-boundary evaluation over `C(n)`;
2. its factorization through the existing reciprocal-factorial evaluation; and
3. finite joint algebraic independence of the scale and harmonic boundary over `C(n)`.

`GammaPoleAnalyticCoefficientFreeness.lean` identifies the actual analytic `U_n` derivatives with
the Bell-transformed logarithmic coordinates, while `GammaInversePoleBranchScaleFreeness.lean`
proves joint freeness of the factorial scale and the positive regular-unit coefficients.  These
close the Bell/birational boundary transfer that was open in the original version of this card.

`MvPolynomialAlgHomBaseChange.lean`, `BellCoefficientScalarExtension.lean`,
`GammaPoleUnitRelativeFreeness.lean`, and `GammaPoleScaleUnitRelativeFreeness.lean` now carry that
transfer over the actual rational pole-position field `C(n)`.  In particular, the factorial scale
and every actual positive derivative of the regular Gamma unit are jointly algebraically
independent over `C(n)`, not merely over `C`.

`GammaPoleScaleSeparatedTrace.lean` now dehomogenizes `U_0=1`, converts positive Taylor
coefficients to actual derivatives by the nonzero factorial diagonal, proves injectivity of the
resulting actual Gamma value evaluation, and proves survival of every nonzero homogeneous particle
trace.  Its constant-coefficient map interfaces are explicit simp laws.

`GammaPoleScaleSeparatedAffineHorizon.lean` closes the finite constant-coefficient value-reflection
problem.  Its exact Rees law is

```text
source degree d, pole grade q  =>  residual weight (n+1)d-q,               (22)
```

where the pole variable and moving scale have weight one and the `k`th positive unit derivative
has weight `k+1`.  For `n>=1`, `(22)` isolates the highest source-particle sector, reduces an
arbitrary source to degrees zero and one, and prevents any forbidden linear pole coefficient from
vanishing when `U_0` is set to one.  At `n=0`, the profile is the canonical one-variable polynomial
isomorphism followed by the injective constant-germ embedding.  Hence Lean proves unconditionally,
for every finite jet ceiling `n`,

```text
degree_T(actual_Gamma_profile_n(P)) <= 1
  <-> exists a b, P = a + b Y_0.                                         (23)
```

The polynomial-coefficient interface is no longer wholly open.  `PolynomialMovingPoleTaylor.lean`
proves the general faithful substitution `p(a+s/T)` and its exact Hasse coefficient law.
`GammaPoleMovingCoefficientLaurent.lean` identifies `a=1-n` and the physical factorial scale as
actual pole-index germs, proves the exact coefficient reflection, and proves the entire moving
coefficient transform injective.  `GammaPoleMovingJetLaurent.lean` composes that transform with the
actual Gamma derivative profiles as one ring homomorphism.

`GammaPoleScaleDerivativeLaurentFreeness.lean` proves the general localization law that an
injective polynomial evaluation at a unit remains injective on Laurent polynomials, then applies it
to the Gamma factorial scale and actual unit derivatives over `C(n)`.  Thus negative scale powers
cannot hide a relation even though the target germ ring is not assumed to be a domain.
`GammaPoleSymbolicMovingJetLaurent.lean` uses this to factor every actual polynomial-coefficient
Gamma jet profile through the faithful two-stage symbolic ring

```text
C(n)[U_1,U_2,...][S,S^(-1)][T,T^(-1)].                                  (24)
```

Actual equality is equivalent to symbolic equality in `(24)`.  The same module proves the exact
linear top edge from `(18)`: for the `j`th derivative, outer pole grade `j+1`, scale grade `-j`, and
boundary-constant monomial have coefficient exactly `-j!`.

`GammaPoleSymbolicTriGrading.lean` now formalizes the conserved law behind the nonlinear diagonal:

```text
outer pole exponent + signed scale exponent + boundary derivative weight
  = source particle degree.                                               (25)
```

The law holds coefficientwise for every homogeneous polynomial-coefficient source sector.  The
same leaf proves the opposite generator edge to the former linear top edge: at outer grade one,
scale grade `-j`, and maximal boundary monomial `U_j`, the `j`th derivative has exact coefficient
`-(-1)^j`.  It also extracts a general weighted substitution theorem and the exact sector
factorization

```text
degree D and derivative weight W
  => (-1)^D (-S^(-1))^W * universal simple-pole profile.                  (26)
```

For constant coefficients, the pole-grade-`D` coefficient is now formally identified with the
universal boundary trace times the explicit factor in `(26)`.  For polynomial coefficients, the
center-frozen value sector satisfies the same bigraded factorization, and the zero Taylor
coefficient is formally the injective rational pole-position value.

`GammaPoleCenterFrozenDiagonal.lean` proves that dehomogenizing the finite head variable remains
injective over `C(n)` and computes the center-frozen nonlinear diagonal exactly.  For a nonzero
source sector of particle degree `D` and derivative weight `W`, the coefficient at outer grade
`D` and scale grade `-W` is the nonzero signed dehomogenized boundary polynomial.

`GammaPoleMovingMaximalWeightReflection.lean` closes the full moving-coefficient assembly.  Its
boundary-weight filtration is stable under sums, products, powers, and weighted substitution; the
`j`th symbolic Gamma derivative is both filtered by derivative weight `j` and pure of signed scale
degree `-j`.  Inner scale degree zero of every moving polynomial coefficient is exactly its
center-frozen value.  Hence every bihomogeneous source satisfies the exact moving-center law

```text
[outer D, scale -W] full_moving_profile(P)
  = (-1)^(D+W) center_boundary_dehomogenization(P).                       (27)
```

In particular, `(27)` is nonzero for every nonzero bihomogeneous source.  Weighted homogeneous
decomposition then selects the maximal derivative-weight sector of an arbitrary nonzero
particle-homogeneous source.  A second decomposition by ordinary degree selects the top particle
sector of an arbitrary nonzero source; the conserved tri-grading prevents all lower sectors from
contributing to the selected boundary monomial.  Lean consequently proves unconditional
injectivity of both

```text
C[z][Y_0,...,Y_n] -> C(n)[U_1,U_2,...][S,S^(-1)][T,T^(-1)]
C[z][Y_0,...,Y_n] -> NatGerm[T,T^(-1)]                                   (28)
```

under the symbolic and actual moving-pole Gamma jet substitutions.  This is stronger than the
previously open unique-contribution step `(15)`--`(17)`.

`GammaPoleMovingAffineProfileHorizon.lean` now closes the algebraic classification itself.  It
first proves that the `j`th derivative profile has outer degree at most `j+1`, while moving
polynomial coefficients have nonpositive outer degree and nonnegative signed-scale degree.  For a
linear source, choose its largest active derivative index `J`.  At outer grade `J+1`, scale grade
`-J`, and boundary monomial one, lower derivative indices are excluded by scale purity and higher
indices vanish by maximality.  The surviving coefficient is exactly

```text
gammaPoleCenterRationalEval(p_J) * (-J!).                                 (29)
```

Center-value injectivity makes `(29)` nonzero.  Combined with the maximal-weight reflection for
the top nonlinear particle sector, Lean first proves the arbitrary-cutoff filtration law

```text
symbolic_profile_n(P) has outer cutoff r  =>  totalDegree(P) <= r,
actual_Gamma_profile_n(P) has outer cutoff r  =>  totalDegree(P) <= r.     (30)
```

The cutoff predicate is formalized as a genuine multiplicative filtration: it is monotone, stable
under addition, and sends cutoffs `r,s` to cutoff `r+s` under multiplication (and to `e*r` under
the `e`th power).

At cutoff zero the converse is exact: the symbolic and actual profiles have no positive outer
grade exactly when `P` is a polynomial coefficient with no Gamma-jet variables.  At cutoff one,
the triangular linear reflection `(29)` sharpens `(30)` to the unconditional symbolic and actual
profile laws

```text
all q>1, symbolic_profile_n(P)[q]=0
  <-> exists a b in C[z], P = a + b Y_0,
all q>1, actual_Gamma_profile_n(P)[q]=0
  <-> exists a b in C[z], P = a + b Y_0.                                 (31)
```

The second equivalence uses a coefficientwise symbolic-to-actual value relation and injectivity of
the scale/derivative boundary evaluation, so downstream users no longer need to discharge a
symbolic Prop.  Equations `(29)`--`(31)` discharge every algebraic Laurent interface **after** a
native analytic hypothesis has been reflected to the frozen profile.

`GammaPoleCovariantJetRealization.lean` supplies the missing first analytic layer.  It proves the
general pointwise law that evaluation of the universal simple-pole profile on the running jets
`U^(k)(x)` is exactly the `j`th derivative of `U(x)/x`.  For Gamma it discharges the three local
source hypotheses (`x != 0`, shifted argument off the Gamma poles, and normalized product
nonzero) into one deleted-neighborhood equality.  It then proves `(14a)` for every finite
polynomial-coefficient jet packet and reflects that value relation through `meromorphicOrderAt`.

The former dynamic-to-frozen problem now splits into two exact layers.  The reciprocal-Bell law
`(14b)`--`(14e)` closes the complete Taylor descent and the Prop cutoff interface inside each
homogeneous normalized-coordinate sector.  Equation `(14f)` restores native `z`-derivatives and
proves the same exact cutoff for each bihomogeneous sector, while `(14g)` supplies the faithful
general value law across all particle sectors.  The sole remaining core for Candidate C is the
order-level noncancellation theorem for sums of distinct bihomogeneous sectors, followed by the
moving-polynomial-coefficient Taylor layer.  The full native analytic intersection `(9)` is not
yet proved or formalized.

All new leaves pass direct `lake env lean` verification.  Exact module builds of
`GammaPoleSymbolicTriGrading`, `GammaPoleCenterFrozenDiagonal`, and
`GammaPoleMovingMaximalWeightReflection` succeed through their dependency chains.  The final exact
build of `GammaPoleMovingAffineProfileHorizon` also succeeds; no umbrella build was run.  A
scratch-file `#print axioms` audit of the shared top-homogeneous law,
generic Laurent-localization injectivity, relative Gamma Laurent reflection, symbolic-to-actual
injectivity and equality reflection, moving-coefficient Hasse law, joint `C(n)` freeness, both
Gamma generator edges, the conserved tri-grading, the full moving-center reflection, the maximal
weight diagonal, both final jet-evaluation injectivity theorems, the moving linear maximal
diagonal, the multiplicative cutoff filtration, the arbitrary-cutoff particle bounds, both exact
vacuum horizons, the symbolic and actual at-most-simple Prop reflection, and both affine-profile
horizon theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.  No umbrella or
full-project build was run.

## Parent-theory and priority audit

Classical algebraic-differential-equation theory already organizes differential monomials by
degree and weight and derives pole-order bounds; see A. Eremenko,
[Meromorphic solutions of algebraic differential equations](https://www.math.purdue.edu/~eremenko/dvi/mer_ade.pdf).
Gamma hypertranscendence over broad meromorphic coefficient fields is also classical; see S. Bank,
[Some results on the Gamma function and other hypertranscendental functions](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/8A86705994E60591A3AE8F0E89E88222/S0308210500019855a.pdf/some_results_on_the_gamma_function_and_other_hypertranscendental_functions.pdf).
The closest primary predecessor is Bank's 1983
[A Note on Zeros of Differential Polynomials in the Gamma Function](https://doi.org/10.14992/00010149).
For a homogeneous differential polynomial, Bank extracts the most singular coefficient at every
Gamma pole (his equation (22)); he then states explicitly that when this coefficient vanishes, the
pole sequence becomes complicated and requires successive coefficients of the regular factors.
That cancellation regime is exactly the dynamic-to-frozen open core isolated above.  The current
profile laws refine Bank's top coefficient algebraically, but they do not by themselves solve his
analytic successive-coefficient problem.
Arc-space differential geometry and differential Rees algebras are broad parents for filtered jet
constructions, but the audited sources do not state the lower-edge reconstruction `(4)` or the
Gamma simple-pole intersection `(9)`.

This negative search is not a priority proof.  Theorem A should be regarded as a clean
associated-graded sharpening of classical pole-degree calculus.  Candidate C is the possible new
content because it combines the all-order lower edge with the factorial-scale/pole-position
bigrading to classify an actual hypertranscendental differential-polynomial algebra.

## Dual gate

- **Novelty:** plausible but unverified for Candidate C.  The primary-source search found the parent
  degree/weight calculus and classical Gamma hypertranscendence, but not the exact intersection
  classification `(9)`.  Specialist priority review is mandatory before promotion.
- **Significance:** If Candidate C is completed, it gives a new exact rigidity classification
  inside the differential-polynomial algebra of the founding hypertranscendental function.  The
  present unconditional contribution is the faithful algebraic profile plus its exact dynamic
  covariant value realization; the native intersection is not yet available.
- **Fields-Medal gate:** not cleared.  The result is a serious candidate theorem with one proved
  natural example, not evidence for the level of field creation or problem resolution required by
  the user-specified bar.

## Gates

- [x] topology/physics language converted to an exact pole-order filtration
- [x] all-order universal trace theorem proved on paper
- [x] homogeneous trace and free-boundary specialization formalized in Lean
- [x] arbitrary-sector universal affine horizon `(7)` formalized in Lean
- [x] finite actual Gamma constant-coefficient affine horizon `(23)` formalized in Lean
- [x] relative scale--harmonic boundary freeness over `C(n)` formalized in Lean
- [x] Bell/birational transfer to the actual regular Gamma boundary formalized in Lean
- [x] joint scale and actual positive-unit-derivative freeness over `C(n)` formalized in Lean
- [x] faithful moving-pole `C[z]` Taylor transform and exact Hasse reflection formalized in Lean
- [x] Laurent localization of scale--derivative value reflection formalized in Lean
- [x] faithful two-stage symbolic-to-actual Gamma jet profile formalized in Lean
- [x] exact linear top-edge coefficient `(18)` formalized in Lean
- [x] conserved pole--scale--boundary tri-grading `(25)` formalized in Lean
- [x] exact nonlinear lower-edge generator coefficient formalized in Lean
- [x] constant-coefficient bigraded sector factorization and particle trace `(26)` formalized in Lean
- [x] polynomial-coefficient center-frozen bigraded factorization formalized in Lean
- [x] nonlinear maximal derivative-weight unique-contribution law `(15)`--`(17)` formalized in Lean
- [x] full symbolic moving-pole polynomial jet substitution proved injective in Lean
- [x] actual Gamma germ Laurent polynomial jet substitution proved injective in Lean
- [x] arbitrary symbolic and actual outer-cutoff particle bound `(30)` formalized in Lean
- [x] exact symbolic and actual cutoff-zero vacuum horizon formalized in Lean
- [x] moving polynomial-coefficient symbolic affine profile horizon `(31)` formalized in Lean
- [x] actual-profile at-most-simple Prop reflected to the symbolic interface and classified in Lean
- [x] universal dynamic covariant profile evaluated exactly as the derivative of `U/x` in Lean
- [x] Gamma source hypotheses discharged on a deleted neighborhood in Lean
- [x] arbitrary polynomial-coefficient native Gamma jet values reflected to the covariant profile in Lean
- [x] native/covariant `meromorphicOrderAt` value reflection formalized in Lean
- [x] homogeneous reciprocal-Bell compression of all dynamic Taylor contributions proved on paper
- [x] homogeneous reciprocal-Bell value and cofinal exact-order laws formalized in Lean
- [x] homogeneous factorial Gamma tower cutoff Prop classified exactly by `D+E` in Lean
- [x] native bihomogeneous Gamma tower cutoff Prop classified exactly by `D+E` in Lean
- [x] factorial and native bihomogeneous top-residue value reflections formalized in Lean
- [x] faithful all-particle reciprocal-Bell Fock transform and general value law formalized in Lean
- [x] homogeneous factorial/native at-most-simple Props classified at source level in Lean
- [ ] cross-sector native-coordinate factorial-scale order separation proved on paper
- [ ] final analytic meromorphic-order intersection `(9)` formalized in Lean
- [x] leading-symbol tie and local-coordinate counterattacks survived
- [ ] global Gamma polynomial differential simple-pole classification proved on paper
- [x] primary parent-theory audit completed; priority remains unverified
- [x] exact RH non-consequence recorded
- [ ] specialist priority audit establishes novelty of Candidate C
- [ ] abstract scale-separated pole-holographically-free native affine-horizon theorem repaired with dynamic freezing
- [ ] dual novelty-significance gate cleared

## 2026-07-21 reciprocal-Bell all-sector closure audit

The stale statements above that the finite maximal-residue sum and its cofinal analytic reflection
remain open are superseded for **constant coefficients**.  The dependency-closed paper law is now
formalized in `GammaPoleReciprocalBellGrading.lean`.

For each source polynomial `P`, define its canonical bidegree component

```text
P_(D,W) = weightedComponent_W(homogeneousComponent_D(P)),
```

let `S(P)` be the finite set of its nonzero components, and define

```text
mu(P) = max_(D,W in S(P)) (D + totalDegree(RB(P_(D,W)))),                 (32)
```

where `RB` is reciprocal-Bell covariant compression.  The Lean development proves all of the
following without a nonvanishing, homogeneity, derivative-weight, meromorphicity, or symbolic
reflection hypothesis at the public interface:

1. `P = sum_(D,W in S(P)) P_(D,W)` and `S(P)` is nonempty when `P != 0`.
2. Every component is simultaneously homogeneous of particle degree `D` and weighted homogeneous
   of derivative weight `W`.
3. The factorial Laurent exponent `-W` and residual covariant weight `W-E` make the finite sum of
   all distinct top residues with common `D+E` nonzero.
4. That symbolic sum is exactly the germ of the genuine native Gamma top-residue values, so it is
   nonzero on arbitrarily remote pole branches.
5. For every branch, multiplication by `x^mu(P)` kills every lower sector and converges to the
   summed top residue.  Thus `-mu(P)` is a uniform lower bound for meromorphic order and is attained
   cofinally when `P != 0`.
6. The complete arbitrary-source filtration is

```text
forall branch, ord_0 P(Gamma,Gamma',...) >= -r  <->  mu(P) <= r.          (33)
```

7. At the simple-pole horizon the source classification is unconditional, including the zero
   source:

```text
forall branch, ord_0 P(Gamma,Gamma',...) >= -1
  <-> exists a b in C, P = a + b X_0.                                    (34)
```

Equation `(34)` is the full native **constant-coefficient** intersection promised after `(14h)`.
It strictly subsumes the earlier sectorwise alternatives `P=c` or `P=c X_0`: sums of the two
particle sectors are now admitted and proved exhaustive.  The general meromorphicity Prop for
`gammaAffineJetEval`, the finite-sum meromorphicity interface, and closure of the tower cutoff
under source addition are also discharged.

The exact named capstones are:

- `finset_sum_reciprocalBellNativeTopResidueSymbol_ne_zero`;
- `reciprocalBellNativeTopResidueGerm_eq_sequence`;
- `exists_cofinal_finset_sum_reciprocalBellNativeTopResidueValue_ne_zero`;
- `exists_cofinal_meromorphicOrderAt_finset_sum_gammaAffineJetEval`;
- `sum_reciprocalBellBihomogeneousComponent_support`;
- `tendsto_pow_reciprocalBellNativePoleDegree_mul_gammaAffineJetEval`;
- `exists_cofinal_meromorphicOrderAt_gammaAffineJetEval`;
- `gammaAffineJetTowerPoleCutoff_iff_reciprocalBellNativePoleDegree`;
- `gammaAffineJetTowerAtMostSimple_iff_affine_undifferentiated`.

Direct `lake env lean` verification of the exact leaf succeeds.  The exact-module final build and
axiom print are intentionally deferred to the final audit.  No umbrella build is authorized or
needed.

This does **not** close the polynomial-coefficient moving-center intersection `(9)`: Taylor
coefficients depending on the native variable can mix pole-center and factorial scales and still
require the separate moving-coefficient descent.  Priority also remains unverified.  Bank's 1983
paper is the closest audited predecessor, but the canonical all-sector maximum `(32)`, joint
residual-weight noncancellation, and exhaustive affine source law `(34)` still require specialist
novelty review before promotion.

### 2026-07-21 exact Lean audit

Final verification used only the exact leaf command

```text
lake build GaloisForLFunctions.HTGeometry.GammaPoleReciprocalBellGrading
```

and completed successfully at `8710/8710`.  No umbrella build was run.  The messages replayed by
the build were pre-existing dependency lint suggestions; the new leaf itself passes direct
`lake env lean GaloisForLFunctions/HTGeometry/GammaPoleReciprocalBellGrading.lean` with no output.
A scratch `#print axioms` audit of the eleven capstones listed above reports only `propext`,
`Classical.choice`, and `Quot.sound`.  The scratch sources and literature-extraction temporaries
were moved to Trash after the audit, and no owned Lean process was left running.

### 2026-07-21 moving-center coefficient and value interfaces

The first moving-coefficient gap after the constant-coefficient classification is now closed at
the algebraic coefficient-field level.  The new module
`GaloisForLFunctions.HTGeometry.GammaPoleReciprocalRelativeFreeness` extends formal unit inversion
from `C` to the rational pole-position field `C(N)`, proves the extended inversion involutive and
injective, and transports the existing factorial-scale/unit-coefficient freeness through both
unit inversion and the nonzero factorial diagonal.  Consequently:

- the factorial scale together with every reciprocal regular-unit coefficient is algebraically
  independent over `C(N)`;
- the factorial scale together with every covariant simple-zero residue is algebraically
  independent over `C(N)`;
- polynomial and Laurent evaluation in that scale/residue family are injective over `C(N)`.

The capstone
`gammaPoleScaleAndCovariantResidueRationalLaurentEval_injective` is the exact moving-center value
reflection: a nonzero finite Laurent relation cannot be made to vanish by allowing rational
functions of the pole index as coefficients.

The existing `PolynomialMovingPoleTaylor` module now also contains the generic value law

```text
eval_u(movingPoleTaylorLaurent(a,s,p)) = p(a + s*u^(-1)),
```

with its field-coordinate form.  Thus the Laurent encoding, moving substitution, and rational
coefficient field are no longer missing interfaces.  What remains is genuinely analytic: the
running regular-unit Taylor variation must still be descended to the frozen profile without
assuming away possible lower-grade cancellation.  These results do not claim that final
polynomial-coefficient intersection and do not prove RH.

Final verification used only

```text
lake build GaloisForLFunctions.HTGeometry.GammaPoleReciprocalRelativeFreeness
```

and completed successfully at `8711/8711`; the build also rebuilt the changed exact dependency
`PolynomialMovingPoleTaylor`.  Direct `lake env lean` checks of both changed leaves were clean.
A scratch axiom audit of the algebraic-independence capstone, Laurent reflection, and moving Taylor
value law reports only `propext`, `Classical.choice`, and `Quot.sound`.

### 2026-07-21 analytic weighted reflection and running-to-frozen descent

The first analytic layer of the moving-coefficient descent is now formalized in
`GaloisForLFunctions.HTGeometry.GammaPoleWeightedCovariantAsymptotic`.  Its general weighted
boundary-value law allows both the pole-scaled coordinates and the coefficient ring homomorphism
to vary.  For any finite multivariate polynomial, maximal-weight normalization selects exactly
the evaluation of its maximal weighted-homogeneous component at the limiting coefficients and
coordinate residues.  This strictly subsumes the previous weight-one, fixed-coefficient
`pow_totalDegree_mul_eval` law.

The Gamma specialization uses the new exact dynamic residue theorem in
`GammaPoleCovariantJetRealization`:

```text
x^(j+1) D^j Gamma(-branch + scale*x)
  -> -scale^(-j) (-1)^j j!.
```

Consequently every running polynomial-coefficient Gamma packet has an explicit maximal
Bell-weight boundary value: coefficient polynomials are evaluated at the pole center, and the
Gamma variables are evaluated on the exact factorial top-residue frame.  The same value is the
maximal boundary of the center-frozen packet.  Their difference therefore has meromorphic order
*strictly greater* than the negative maximal Bell weight, both for the covariant realization and
for the native Gamma packet.  This is the unconditional running-to-frozen top-layer descent:
Taylor motion cannot affect the leading pole layer.

Two general meromorphic interfaces were promoted to
`MeromorphicSimplePoleDifferentialOperator`:

- a finite normalized pole limit has exact order `-k` iff its limiting value is nonzero;
- a zero normalized limit forces strict order improvement above `-k`.

The named Gamma capstones are:

- `tendsto_pow_succ_mul_simplePoleCovariantJetValue`;
- `tendsto_pow_succ_mul_gammaPoleCovariantJetValue`;
- `meromorphicOrderAt_gammaPoleJet_affine`;
- `tendsto_pow_weightedTotalDegree_mul_eval₂`;
- `tendsto_pow_weightedTotalDegree_mul_gammaPoleCovariantPolynomialJetEval`;
- `neg_weightedTotalDegree_lt_meromorphicOrderAt_gammaPoleCovariant_sub_centerFrozen`;
- `neg_weightedTotalDegree_lt_meromorphicOrderAt_gammaPolyJetEval_affine_sub_centerFrozen`;
- `meromorphicOrderAt_gammaPoleCovariantPolynomialJetEval_eq_iff`;
- `meromorphicOrderAt_gammaPolyJetEval_affine_eq_iff`.

Final verification used only

```text
lake build GaloisForLFunctions.HTGeometry.GammaPoleWeightedCovariantAsymptotic
```

and completed successfully at `8715/8715`, rebuilding only the required changed dependency chain.
Focused `lake env lean` checks of the changed base, realization, and leaf files passed.  Formal
source lint passed with only the repository's existing large-file warnings.  A scratch axiom audit
of the new general and Gamma capstones reports only `propext`, `Classical.choice`, and `Quot.sound`.

This closes the leading analytic running/frozen gap but not the full polynomial-coefficient
intersection.  A nonzero source can still have a zero reflected top value through cancellation
among equal-weight monomials or vanishing pole-center coefficients; the exact iff theorem records
that boundary honestly and sends such sources to lower layers.  A complete result now requires an
iterated lower-grade descent/noncancellation argument.  No RH claim is made, and priority remains
unverified pending specialist review.

### 2026-07-21 complete principal-remainder jet and relative finite-part freeness

The lower analytic layer below the maximal pole boundary is now identified exactly.  For every
function `U` analytic at zero, the `j`th derivative of `U(x)/x` has only its residue pole monomial;
after that monomial is subtracted, the complete remainder is the analytic divided-difference jet
`iteratedDeriv j (dslope U 0)`.  The new all-order value reflection is

```text
D^m (D^j (dslope U 0))(0) = U^(j+m+1)(0) / (j+m+1).
```

Thus the earlier removable-singularity statement is no longer merely existential or limited to the
first regular value.  Every Taylor coefficient of every differential principal remainder is
explicit, unconditional, and carried by a shifted numerator jet.

`GammaPoleCovariantJetRealization` now names the canonical analytic witness
`gammaPoleJetRegularRemainder`.  It proves its analyticity, its complete shifted-unit jet formula,
and its exact Bell-coordinate reflection through the factorial scale, harmonic jet sequence, and
Gamma logarithmic constants.  The existing covariant and native affine principal-part theorems use
this named witness, so their existential `Prop` interfaces now expose a reusable analytic object.

The new module `GammaPolePrincipalRemainderFreeness` connects that analytic witness to the existing
relative coefficient theory.  For Gamma itself (`j=0`), the `m`th finite-part jet across pole labels
is exactly

```text
gammaPoleFinitePartJetGerm m
  = complexNatGerm (-m!) * gammaPoleUnitPositiveCoefficientGerm m.
```

Because the diagonal factor is nonzero, the complete finite-part jet family remains algebraically
independent over the full rational pole-position field `C(N)`.  Equivalently, the new ring
interface `gammaPoleFinitePartJetRationalEval` is injective.  Principal-part subtraction therefore
does not collapse the analytically free Gamma information below the pole boundary, even when
rational functions of the moving pole label are admitted as coefficients.

The principal capstones are:

- `iteratedDeriv_iteratedDeriv_dslope_zero_eq`;
- `iteratedDeriv_div_id_sub_principal_eventuallyEq`;
- `gammaPoleJetRegularRemainder` and `analyticAt_gammaPoleJetRegularRemainder`;
- `iteratedDeriv_gammaPoleJetRegularRemainder_zero`;
- `iteratedDeriv_gammaPoleJetRegularRemainder_zero_eq_sequenceBell`;
- `algebraicIndependent_gammaPoleFinitePartJetGerm_over_ratFunc`;
- `gammaPoleFinitePartJetRationalEval_injective`.

Focused source checks passed.  Final verification used only the exact changed dependency chain:

```text
lake build GaloisForLFunctions.HTGeometry.MeromorphicSimplePoleDifferentialOperator
lake build GaloisForLFunctions.HTGeometry.GammaPoleCovariantJetRealization
lake build GaloisForLFunctions.HTGeometry.GammaPolePrincipalRemainderFreeness
```

They completed successfully at `8510/8510`, `8685/8685`, and `8701/8701`; no umbrella build was
run.  Formal source lint passed with only existing large-file warnings.  A scratch axiom audit of
the general remainder law, Gamma/Bell reflections, native affine interface, relative-freeness
capstone, and injective evaluation reports only `propext`, `Classical.choice`, and `Quot.sound`.

This is a genuine lower-layer noncollapse theorem, but it is not yet the full moving
polynomial-coefficient intersection.  Products of several jet generators and Taylor-moving
coefficient polynomials can mix distinct lower grades after the top reflected value cancels.  A
complete result still requires a packet-wide iterated graded descent separating those mixtures.
No RH claim is made, and priority remains unverified pending specialist review.

### 2026-07-21 binomial cancellation and universal first-subprincipal reflection

The first pole layer below a canceled maximal Bell weight is now identified exactly.  The explicit
binomial module `GammaPoleBinomialSubprincipalDescent` starts from the divided-power defect

```text
J_0 J_(j+k) - choose(j+k,j) J_j J_k,
```

whose nominal order is `-(j+k+2)`.  The simple-pole principal coefficients satisfy the exact
binomial identity

```text
C_0 C_(j+k) = choose(j+k,j) C_j C_k,
```

so that layer cancels.  For positive `j,k`, the next normalized value is

```text
x^(j+k+1) defect(x) -> C_(j+k) R_0(0).
```

The relative finite-part theory proves `R_0(0) != 0` on arbitrarily remote Gamma branches.  Since
`C_(j+k)` is nonzero, this discharges both factors jointly for the binomial family and yields exact
order `-(j+k+1)` cofinally, for both covariant and native affine Gamma packets.  In particular,
`Gamma * Gamma'' - 2 * (Gamma')^2` has exact local order `-3` on cofinally many Gamma poles.

The general module `SimplePoleWeightedFirstSubprincipal` subsumes this mechanism.  Let `P` be
weighted homogeneous of positive Bell weight `W`, with coordinate weight `weight(X_q)=q+1`.  For
normalized simple-pole coordinates

```text
g_q(x) = C_q + x^(q+1) R_q(x),
```

one has `g'_0(0)=R_0(0)` and `g'_q(0)=0` for every `q>0`.  Therefore, whenever the principal
reflection cancels,

```text
eval(C,P) = 0,
```

the complete first-subprincipal value reflection is

```text
x^(W-1) eval(J(x),P)
  -> eval(C, pderiv X_0 P) * R_0(0).
```

Only the weight-one coordinate can move one grade below the maximal boundary.  If both reflected
factors are nonzero, the packet has exact meromorphic order `-(W-1)`.  The theorem is formalized as
an abstract normalized-extension law, a general analytic simple-pole law, a Gamma covariant law,
and a native affine Gamma law connected by the exact eventual value relation.  For the binomial
polynomial, `pderiv X_0 P = X_(j+k)`, recovering the explicit boundary above.

Focused source checks and exact-module final builds passed:

```text
lake build GaloisForLFunctions.HTGeometry.GammaPoleBinomialSubprincipalDescent
  8702/8702
lake build GaloisForLFunctions.HTGeometry.SimplePoleWeightedFirstSubprincipal
  8722/8722
```

The six general/Gamma first-subprincipal capstones report exactly `propext`, `Classical.choice`, and
`Quot.sound` under scratch `#print axioms`.  Combined formal lint passes with only pre-existing
large-file warnings, and `git diff --check` passes.

The broad Gamma exact-order theorem still assumes branchwise nonvanishing of
`eval(principalFrame, pderiv X_0 P)` and `gammaPoleJetRegularRemainder branch 0 0`.  Existing
finite-part freeness discharges the second factor cofinally, but a general theorem needs a single
joint branch-germ injection proving both factors nonzero at the same cofinal branch.  Separate
cofinal statements are insufficient.  This joint nonvanishing problem remains the exact open core.

Status: **[EXTERNAL NOVELTY UNVERIFIED]**.  These are unconditional HTGeometry theorems, not a
polynomial-coefficient packet intersection theorem and not RH progress.

### 2026-07-21 joint cofinal first-subprincipal discharge

**[BRIDGE] [LEAN-PROVED].**  The two branchwise nonvanishing hypotheses above are now discharged
simultaneously under an exact symbolic criterion.  The new leaf
`GammaPoleWeightedFirstSubprincipalCofinal` packages every Gamma principal jet coefficient as the
highest-pole coefficient of its existing symbolic factorial-scale Laurent profile.  For a fixed
packet `P`, this gives the principal-reflection symbol

```text
gammaPolePrincipalReflectionSymbol n P.
```

Its actual pole-index germ is exactly the branch sequence

```text
N |-> eval(gamma principal frame at N-1, P).
```

The first-subprincipal product is represented by one source element in the already faithful joint
scale/unit-derivative Laurent algebra:

```text
gammaPolePrincipalReflectionSymbol n (pderiv X_0 P)
  * (-C(X_0)).
```

The second factor evaluates to `gammaPoleFinitePartJetGerm 0`.  If the symbolic partial reflection
is nonzero, the source product is nonzero and joint Laurent injectivity keeps its actual germ
nonzero.  If the symbolic principal reflection of `P` is zero, principal cancellation holds on an
eventual branch tail.  Nonzero-germ detection beyond that tail therefore produces, for every bound
`B`, one branch `branch >= B` where all three required facts hold together:

```text
eval(principalFrame branch, P) = 0,
eval(principalFrame branch, pderiv X_0 P) != 0,
gammaPoleJetRegularRemainder branch 0 0 != 0.
```

Applying the existing analytic first-subprincipal theorem gives exact order `-(W-1)` on that same
branch for both the covariant packet and the native affine Gamma packet.  The capstones are:

- `gammaPolePrincipalReflectionGerm_eq_sequence`;
- `gammaPoleFirstSubprincipalJointGerm_ne_zero`;
- `exists_cofinal_gammaPoleFirstSubprincipalFactors`;
- `exists_cofinal_meromorphicOrderAt_gammaWeightedJetEval_of_firstSubprincipal`.

Verification passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/GammaPoleWeightedFirstSubprincipalCofinal.lean
lake build GaloisForLFunctions.HTGeometry.GammaPoleWeightedFirstSubprincipalCofinal
  8723/8723
```

A scratch axiom audit of the coordinate reflection, full reflection, joint-germ nonvanishing,
cofinal factor theorem, and simultaneous order capstone reports exactly `propext`,
`Classical.choice`, and `Quot.sound`.

This closes the named common-branch open core without adding a new freeness axiom or analytic
hypothesis.  It is a connector theorem, not a claim of external novelty.  Packets whose symbolic
principal reflection and first partial both vanish remain below the first-subprincipal layer; their
next honest boundary is the second derivative of the normalized analytic coordinate curve.  The
full moving polynomial-coefficient intersection and RH status remain unchanged.

### 2026-07-21 exact second-subprincipal paper identity

**[PAPER-PROVED] [BRIDGE] [LEAN-PROVED].**  Let `P` be a polynomial in finitely many variables and
let `g_i` be analytic curves with

```text
C_i = g_i(0),       a_i = g_i'(0),       b_i = g_i''(0)/2.
```

Write `F(x)=P(g(x))`.  If the principal and first directional boundaries cancel,

```text
P(C) = 0,
sum_i (partial_i P)(C) a_i = 0,
```

then the exact second quotient limit is

```text
F(x)/x^2 ->
  sum_i (partial_i P)(C) b_i
    + (1/2) sum_i sum_j (partial_j partial_i P)(C) a_j a_i.               (10)
```

Proof: the first polynomial chain rule gives

```text
F'(x) = sum_i (partial_i P)(g(x)) g_i'(x).
```

Differentiating once more and evaluating at zero gives

```text
F''(0) =
  sum_i (partial_i P)(C) g_i''(0)
    + sum_i sum_j (partial_j partial_i P)(C) a_j a_i.
```

Because `F(0)=F'(0)=0`, applying the removable divided-difference law twice gives
`F(x)/x^2 -> F''(0)/2`, which is `(10)`.  This proof uses only finite polynomial chain and product
rules plus analyticity of the divided difference; it has no genericity or hidden nonvanishing
hypothesis.

For the honest normalized simple-pole coordinates

```text
g_q(x) = C_q + x^(q+1) R_q(x),
```

the only nonzero first tangent is `a_0=R_0(0)`, while

```text
b_0 = R_0'(0),       b_1 = R_1(0),       b_q = 0 for q >= 2.
```

Consequently the complete second-subprincipal boundary is the three-term invariant

```text
(partial_0 P)(C) R_0'(0)
  + (partial_1 P)(C) R_1(0)
  + (1/2) (partial_0 partial_0 P)(C) R_0(0)^2.                            (11)
```

Hostile review rules out dropping the first term under the weaker first-boundary condition
`(partial_0 P)(C) R_0(0)=0`: that product can vanish because `R_0(0)=0` while
`(partial_0 P)(C) R_0'(0)` survives.  The canonical two-term corollary therefore requires the
stronger symbolic cancellation `(partial_0 P)(C)=0` itself.

If `P` is Bell-weight homogeneous of weight `W >= 2`, weighted scaling converts `(10)` into

```text
x^(W-2) eval(J(x),P) -> the boundary in (11).
```

Nonvanishing of `(11)` then gives exact meromorphic order `-(W-2)`.  This is the strongest honest
second-layer statement supported by the normalized analytic curve.  It includes the extra base
remainder derivative that a frozen Laurent profile misses.

External parent-theory audit classifies `(10)` as classical multivariate Taylor/Faa di Bruno
calculus, not a novelty claim: see Johnston--Prochno, arXiv:1911.07458, and Leipnik--Pearce,
*The multivariate Faa di Bruno formula and multivariate Taylor expansions with explicit integral
remainder term*.  The local simple-pole specialization `(11)` is therefore recorded as a theorem-
graph bridge.  It does not prove the global moving polynomial-coefficient intersection and does not
change RH status.

The identity and its exact-order consequences are now formalized in
`SimplePoleWeightedSecondSubprincipal.lean`.  The leaf proves the full multivariate second chain
rule, the twice-divided quotient limit, a reusable weighted normalized-extension theorem, the
three-term general simple-pole boundary, Gamma covariant specialization, and native affine Gamma
transfer.  The principal capstones are:

- `HTGeometry.tendsto_inv_sq_mul_mvPolynomial_eval_curve`;
- `tendsto_pow_sub_two_mul_weightedJetEval_of_normalizedExtension`;
- `simplePoleSecondSubprincipalBoundary`;
- `meromorphicOrderAt_simplePoleWeightedJetEval_of_secondSubprincipal`;
- `gammaPoleSecondSubprincipalBoundary`;
- `meromorphicOrderAt_gammaAffineWeightedJetEval_of_secondSubprincipal`.

Focused verification passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/SimplePoleWeightedSecondSubprincipal.lean
lake build GaloisForLFunctions.HTGeometry.SimplePoleWeightedSecondSubprincipal
  8723/8723
```

The seven audited general/simple/Gamma capstones use exactly `propext`, `Classical.choice`, and
`Quot.sound`.  This remains a classical-calculus connector, not an external novelty or RH result.

### 2026-07-21 cofinal Gamma second-subprincipal discharge

**[BRIDGE] [LEAN-PROVED].**  The complete second boundary `(11)` is now represented inside the
existing faithful Laurent algebra for the physical factorial scale and positive derivatives of the
regular Gamma pole unit.  The two new remainder symbols are

```text
R_0'(0)  <->  -(1/2) C(X_1),
R_1(0)   <->   T^(-1) (1/2) C(X_1),
```

where Laurent evaluation sends `T` to the reciprocal signed-factorial germ.  Together with the
existing finite-part symbol `R_0(0) <-> -C(X_0)`, the exact source is

```text
principalReflection(pderiv X_0 P) * R_0'(0)
  + principalReflection(pderiv X_1 P) * R_1(0)
  + (1/2) * principalReflection(pderiv X_0 (pderiv X_0 P)) * R_0(0)^2.
```

The evaluation theorem identifies this source with the germ of the actual branchwise
`gammaPoleSecondSubprincipalBoundary`.  Joint Laurent injectivity therefore turns source
nonvanishing into nonvanishing of the complete boundary germ; it does not separately choose
branches for the three summands.

Assume the symbolic principal reflection of `P` and of `pderiv X_0 P` both vanish, while the full
second-boundary symbol is nonzero.  The first two equations hold on eventual branch tails.  For
every bound `B`, nonzero-germ detection beyond the intersection of those tails supplies one common
`branch >= B` where both cancellations and the nonzero complete second boundary hold.  For a
Bell-weight homogeneous packet of weight `W >= 2`, the analytic theorem then gives simultaneously

```text
meromorphicOrderAt(covariant packet, 0) = -(W-2),
meromorphicOrderAt(native affine Gamma packet, 0) = -(W-2).
```

The formal leaf is
`GammaPoleWeightedSecondSubprincipalCofinal.lean`.  Principal capstones are:

- `eval_baseRemainderDerivativeSymbol`;
- `eval_firstJetRemainderSymbol`;
- `gammaPoleSecondSubprincipalBoundaryGerm_eq_sequence`;
- `gammaPoleSecondSubprincipalBoundaryGerm_ne_zero`;
- `exists_cofinal_gammaPoleSecondSubprincipalBoundary`;
- `exists_cofinal_meromorphicOrderAt_gammaWeightedJetEval_of_secondSubprincipal`.

Focused verification passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/GammaPoleWeightedSecondSubprincipalCofinal.lean
lake build GaloisForLFunctions.HTGeometry.GammaPoleWeightedSecondSubprincipalCofinal
  8725/8725
```

All six audited declarations use exactly `propext`, `Classical.choice`, and `Quot.sound`.  This
closes the named second-layer common-branch gap without new hypotheses or computations.  It is a
theorem-graph connector, not external novelty or RH progress.  Packets whose complete symbolic
second boundary also vanishes require a higher-order classification; no such claim is made here.

### 2026-07-21 exact two-channel nonvanishing classification

**[BRIDGE] [LEAN-PROVED].**  The abstract hypothesis that the complete second-boundary symbol is
nonzero has now been eliminated.  Principal reflections contain only the Laurent scale and no
positive unit-derivative variables.  Consequently every specialization of those derivative
variables has a left inverse on principal reflections and preserves their nonvanishing.

Two exact specializations separate the complete boundary:

- `X_1 = 1` and all other `X_k = 0` isolates the `pderiv X_1 P` first-jet channel after
  `pderiv X_0 P` cancels;
- `X_0 = 1` and all other `X_k = 0` isolates the repeated-base Hessian channel.

The nonzero scalar `1/2` and Laurent unit `T^(-1)` cannot kill either isolated channel.  Conversely,
if both reflections vanish, direct substitution in the three-term symbol makes the whole boundary
zero.  Hence, under first-partial cancellation, Lean proves the exact equivalence

```text
complete second-boundary symbol != 0
  <-> principalReflection(pderiv X_1 P) != 0
       or principalReflection(pderiv X_0 (pderiv X_0 P)) != 0.
```

The theorem is
`gammaPoleSecondSubprincipalBoundarySymbol_ne_zero_iff_channels`.  The strengthened capstone
`exists_cofinal_meromorphicOrderAt_gammaWeightedJetEval_of_secondSubprincipal_channels` takes this
explicit disjunction directly and produces the same common remote branch and exact order
`-(W-2)` for covariant and native affine packets.  This is a sharp hypothesis discharge inside the
existing Laurent algebra, not a new analytic assumption, computation, novelty claim, or RH claim.

The exact module rebuild again passed `8725/8725`.  A scratch axiom audit of both specializations,
the left-inverse/nonvanishing transport, exact iff, cofinal boundary theorem, and strengthened order
capstone reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
