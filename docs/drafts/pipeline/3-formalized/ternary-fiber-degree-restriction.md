# Degree restriction for the three labeled rational fibers

- **ID:** RH-TFDR-20261007
- **Stage:** 3-formalized; complete necessary rational degree law and F_3 converse
- **Parent:** `../1-in-progress/xi-marked-joint-monodromy.md`, finite rational test
- **Scope:** close the recorded necessary degree law for rational normalized
  parameters. No claim about transcendental parameters or the actual Xi lift.

## Exact statements and competing possibilities

Let V be a nonconstant rational map of degree N. Suppose V(infinity) is not a
cube root of unity, and every point in the complete fiber over omega^j is an
integer congruent to j modulo three, for j=0,1,2. Multiplicities are retained.
The parent paper predicts N=3^e. A counterexample at any other degree would
refute its reduction argument. Existing degree-three examples already refute
degree-one rigidity; occurrence of every degree 3^e is not asserted.

The algebraic core has an exact converse: for positive N, the three polynomials
X^N, (X-1)^N, (X+1)^N over F_3 are linearly dependent if and only if N is a
power of three. This is a finite characteristic-three classification, not a
converse existence theorem for rational maps over C.

## Dependency-closed paper proof

For each fiber form its monic root polynomial A_j, counting multiplicity. Each
A_j lies in Z[X], has degree N, and reduces to (X-j)^N modulo three. Writing
V=P/Q shows that these three polynomials are nonzero scalar multiples of
P-omega^j Q, so they are linearly dependent over C. The coefficient matrix has
rational entries. Its rank over Q equals its rank over C, since ranks are
detected by nonzero minors. Its rational kernel is therefore nonzero. Clear
denominators and divide the coefficient gcd to obtain a primitive nonzero
integer relation c_0 A_0+c_1 A_1+c_2 A_2=0.

Reduction modulo three leaves a nonzero coefficient vector. Evaluating the
reduced relation at 0,1,-1 proves that N is odd: if N is even, each pair of
coefficients sums to zero, hence all vanish since 2 is invertible in F_3.
For odd N the same evaluations make all three coefficients equal and nonzero.
Divide by their common value to obtain

    X^N+(X-1)^N+(X+1)^N=0  in F_3[X].

For each positive even j<N, the coefficient of X^(N-j) is
2*binom(N,j), so it vanishes modulo three. For each odd interior j, use the
even index N-j and binomial symmetry. Thus every interior binomial coefficient
is divisible by three. The Lucas prime-power criterion gives
N=3^(multiplicity(3,N)). Conversely, if N=3^e, Frobenius gives the displayed
polynomial identity directly. This closes the finite-field classification and
the necessary rational degree restriction.

The condition at infinity prevents a fiber from losing degree. Omitting it,
discarding multiple roots, assuming primitive coefficients without descent,
or asserting the rational existence converse would change the theorem.

## Corpus and parent audit

The exact documented lexical search for
`eq_pow_multiplicity_of_choose_modEq_zero_nat` returned no hits; this is not an
absence certificate. Direct local source verification found the theorem in
mathlib `Data/Nat/Choose/Lucas.lean`, namespace `Choose`, with `[Fact (Nat.Prime p)]`
and all interior binomial congruences as inputs. Scratch verification against
this toolchain remains required before use. Focused source/card searches found
the parent paper statement and the existing degree-three family, but no
formalization of this degree restriction.

[Granville's generating-function proof](https://www.cecm.sfu.ca/organics/papers/granville/paper/binomial/html/node7.html)
and the [mathlib Lucas documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Choose/Lucas.html)
identify the classical arithmetic parent. This is provisionally a **BRIDGE**;
there is no certified novelty claim. The new obligation is exact transport from
the labeled rational fibers through the primitive integer relation, not a new
Lucas theorem.

### Elementary descent used in the formal proof

For three integer polynomials sharing coefficient one at degree N, take a
complex relation with nonzero third coefficient. If the first two polynomials
coincide, their difference is already an integer relation. Otherwise choose a
coefficient k where their difference d is nonzero, and let e be the corresponding
difference between the third and first polynomial. Subtract the common leading
coefficient relation and eliminate the second complex coefficient using k.
Cancellation of the third coefficient gives the exact integer relation

    (e-d) A_0 - e A_1 + d A_2 = 0.

It is nonzero because d is nonzero. This replaces rank descent with an explicit
coefficient argument; primitive normalization and the mod-three proof are
unchanged. For three distinct pencil targets, the third complex coefficient is
the nonzero difference of the first two targets times the third leading
coefficient, so its required nonvanishing is derived from the actual pencil.

### Exact pencil and rational-function interface

The same argument applies to arbitrary complex target values t_0,t_1,t_2
with t_0 distinct from t_1, provided their complete finite fibers lie in the
three prescribed residue classes. Put N=max(deg P,deg Q). The precise condition
excluding infinity from target t_j is P_N-t_j Q_N nonzero. It implies that
P-t_j Q has degree N and nonzero leading coefficient l_j. Their normalized
integer root polynomials satisfy the complex relation with coefficients
(t_1-t_2)l_0, (t_2-t_0)l_1, (t_0-t_1)l_2. The last is nonzero, as required by
the explicit descent. No assumption of integral or rational pencil coefficients
is made. Taking P,Q to be the canonical coprime numerator and denominator of
an actual rational function gives its projective map degree N. Specializing
the targets to 1,omega,omega^2 gives the original statement. This generality is
already forced by the same paper proof; it is not a new novelty claim.

## Verification plan

- [x] Verify APIs and the complete F_3 linear-dependence classification in Lean.
- [x] Formalize primitive integer descent and the fiber-polynomial reduction.
- [x] Formalize the exact rational-map wrapper, including infinity and multiplicity.
- [x] Targeted builds, actual-source checks, public axiom audit, wiring and lint run.
- [x] Record precisely what remains open for transcendental parameters and Xi.

## Log

- 2026-10-07 — Existing paper survivor selected for further audit while the
  independent paired-reflection completion finishes verification. No Lean code
  for this card has been written. The general monodromy conjectures remain open.
- API preparation located `Finset.extract_gcd` in the local GCD finset library.
  Applied to a nonzero integer coefficient vector, it gives an exact common
  factor and a primitive quotient vector without a hand-built division argument.
  Cancel the nonzero common factor from the polynomial relation; its quotient
  coefficients cannot all vanish modulo three because their gcd is one.
  The separate `/tmp/rh-ternary-fiber-degree-api.lean` name-verification file is
  prepared but has not run. No proof module for this card exists yet.
- The API file now passes after assigning explicit universe levels to generic
  name checks. A scratch for the characteristic-three power-sum criterion is
  prepared and under verification. It derives odd parity, vanishing of every
  interior binomial coefficient, and the exact Frobenius converse. The primitive
  relation and actual rational-fiber transport remain outstanding.
- The complete characteristic-three relation classifier now passes scratch,
  including zero coefficients. For positive N the kernel is zero unless N is a
  power of three, when it is exactly the line of equal coefficient triples.
  This is the full coefficient conclusion already obtained by the paper's
  three evaluations. No rational realization converse is inferred. Primitive
  integer relation and reduction scratches are now prepared, not yet verified.
- Primitive integer normalization and nonzero reduction modulo three now pass
  scratch. Both generic leaves are promoted and wired; their targeted build is
  running. Actual complex descent and root-multiplicity transport remain open.
- All six proof leaves now pass scratch, including the actual `RatFunc ℂ`
  wrapper. The root-multiset and polynomial-degree leaves also pass targeted
  builds. The final pencil leaf is promoted and wired; its targeted build,
  complete public axiom audit and all actual-source checks remain pending.
- Final verification complete: all six targeted leaves build, all six actual
  source files pass `lake env lean` with empty logs, and all 15 named public
  declarations have transitive axiom closures contained in propext,
  Classical.choice and Quot.sound. All six umbrella imports occur exactly once.
  Evidence: `/tmp/rh-ternary-final-build.log`, `/tmp/rh-ternary-axioms.log`,
  `/tmp/rh-ternary-audit-names.txt`, and the six
  `/tmp/rh-<Leaf>-ternary-final-20261007.log` files.
- Index refresh passes. Authoritative lint reports seven unrelated unwired
  leaves: WeilConeBoundaryMobiusAveraging, WeilConeBoundaryMobiusRigidity,
  ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation,
  ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No owned ternary leaf is
  named and no global lint pass is claimed. Log:
  `/tmp/rh-ternary-lint-20261007.log`.

## Formal output and scientific limit

HTGeometry leaves: TernaryTranslatedPowers,
IntegerPolynomialRelationReduction, IntegerComplexThreeRelation,
IntegerFiberRoots, TernaryPolynomialDegree, TernaryPencilDegree.
The last leaf proves `ternary_labeled_rational_degree` on actual `RatFunc ℂ`.
Its input conditions are the stated geometric fiber conditions, positive map
degree and avoidance of infinity; no primitive relation is assumed.

This completes an existing paper survivor, using classical Lucas arithmetic.
No new scientific novelty or RH premise discharge is claimed. Occurrence of
every degree 3^e, extension to transcendental parameters, and actual Xi cubic
no-lift are not consequences. The next cycle addresses the last problem via
actual strip decay and finite-order rigidity on
`../1-in-progress/xi-cubic-lift-strip-decay.md`.
