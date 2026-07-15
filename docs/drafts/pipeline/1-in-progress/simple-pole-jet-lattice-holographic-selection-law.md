# The simple-pole jet lattice has an exact holographic selection law

- **ID:** `simple-pole-jet-lattice-holographic-selection-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / FORMALIZED ALGEBRAIC CORE / HT BOUNDARY-GEOMETRY CANDIDATE
- **Scientific status:** `[PROVED HERE: UNIVERSAL CONSTANT-COEFFICIENT LAW] [FORMALIZED: HOMOGENEOUS TRACE] [CONJECTURE: GLOBAL GAMMA DESCENT] [NOVELTY UNVERIFIED]`
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

## Gamma globalization `[CONJECTURE]`

For the factorially rescaled Gamma pole family, the existing Lean theorem
`algebraicIndependent_actualGammaPoleRegularCoefficientGerm` proves that the complete positive
regular Laurent-coefficient family is algebraically independent.  This supplies the free boundary
tail required by Theorem A after the explicit nonzero factorial coordinate scaling.

The global target is

```text
C[z][Gamma, Gamma', Gamma'', ...]
  intersect {meromorphic functions having pole order <= 1 at every Gamma pole}
    = C[z] + C[z] Gamma.                                                     (9)
```

The remaining descent is coefficient-sensitive.  At the pole `z=-n`, the local coordinate is
`t=z+n`; a local cancellation such as `t f' + f` uses the pole index `n` and need not descend to a
single coefficient in `C[z]`.  A proof of `(9)` must combine:

1. the simple-pole jet-lattice trace `(4)`;
2. algebraic independence of the actual Gamma regular boundary coefficients over the rational
   pole-index field `C(n)`; and
3. descent from `C(n)[t]` along the diagonal embedding `z -> t-n` back to `C[z]`.

The repository currently has relative `C(n)` freeness for the logarithmic Gamma boundary jets and
absolute freeness for the regular coefficients.  The relative regular-coefficient transfer and
the diagonal descent are the named open core.  They are not assumed.

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

The touched module passes direct `lake env lean` verification.  No umbrella or full-project build
was run because this workspace is concurrently shared and the task explicitly requires the
smallest possible build.

## Dual gate

- **Novelty:** unverified.  The natural parent theories are pole-order filtrations for meromorphic
  connections and `D`-modules, Rees algebras, arc spaces, and differential-algebraic singularity
  theory.  The exact nonlinear boundary-trace identity and Gamma descent must be checked against
  them before promotion.
- **Significance:** Theorem A is a reusable all-order structural law and bypasses the known
  higher-order leading-symbol degeneracy.  Its significance becomes substantial only if the
  Gamma descent `(9)` or a broad pole-holographically-free class is proved.
- **Fields-Medal gate:** not cleared.  The universal trace is a real theorem, but the current result
  does not establish a new major theory or solve a central open problem.

## Gates

- [x] topology/physics language converted to an exact pole-order filtration
- [x] all-order universal trace theorem proved on paper
- [x] homogeneous trace and free-boundary specialization formalized in Lean
- [x] leading-symbol tie and local-coordinate counterattacks survived
- [x] exact RH non-consequence recorded
- [ ] primary-literature parent and novelty audit completed
- [ ] global Gamma coefficient descent proved or falsified
- [ ] broad natural class of pole-holographically-free HT functions established
- [ ] dual novelty-significance gate cleared
