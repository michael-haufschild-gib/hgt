# Hedenmalm--Weil source-to-operator capstone

- **ID:** `hedenmalm-weil-source-to-operator-capstone`
- **Stage:** 3-formalized
- **Type:** THEOREM PACKAGE / DIRECT HILBERT--POLYA COMPLETION
- **Scientific status:** `[FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY AUDIT OPEN]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/XiHedenmalmFourierEquation.lean`,
  `formal/GaloisForLFunctions/RHTower/XiHedenmalmEigenbasis.lean`,
  `formal/GaloisForLFunctions/RHTower/XiHedenmalmReciprocalOperator.lean`, and
  `formal/GaloisForLFunctions/RHTower/XiHedenmalmSourceCapstone.lean`.

## Closed theorem surface

Let `XiZeroCopy` be the actual centered Xi divisor with one coordinate for every analytic
multiplicity copy. Let `E_alpha` be the divisor evaluation vector of Hedenmalm's removable theta
eigenfunction quotient at the zero `alpha`. Let `H_Xi=ell^2(XiZeroCopy)` and let `R_Xi` be the
diagonal reciprocal-divisor operator

```text
(R_Xi v)(q)=xiSpectralPoint(q)^(-1) v(q).
```

The formal tree proves the following assumption-free equivalences and concrete operator facts.

### 1. Exact eigenfunction completeness law

For every centered Xi zero `alpha`, the transformed theta-source equation

```text
(alpha-z) U(z) = -I XiC(z)                                (1a)
```

has exactly one continuous solution on the complex plane: the removable entire quotient

```text
U_alpha(z)=I dslope(XiC,alpha)(z).
```

On the real axis the forcing term in `(1a)` is exactly `-I` times the Fourier transform of the
concrete theta-cusp Schwartz source. Thus the vectors below are the unique regular solutions of
the transformed Hedenmalm equation.

Without any simplicity assumption, their algebraic span satisfies the sharper exact defect law

```text
span{E_alpha:Xi(alpha)=0}
  = span{e_q:Xi'(xiSpectralPoint(q))!=0}.                  (1b)
```

Every multiple-zero fiber is therefore deleted in full, whereas every simple-zero coordinate is
present. After Hilbert completion the two closures remain equal. In particular,

```text
closure span{E_alpha:Xi(alpha)=0}=H_Xi
  iff every Xi zero is simple.                              (1)
```

The forward direction is substantive. If `Xi'(alpha)=0`, every theta eigenfunction evaluation
lies in the closed coordinate hyperplane that vanishes at any multiplicity copy over `alpha`, so
the span cannot be dense. Conversely, under simplicity each divisor fiber has exactly one copy and

```text
E_alpha = I Xi'(alpha) e_alpha,                             (2)
```

a nonzero multiple of the canonical `ell^2` basis vector.

Declarations:

- `xiThetaEigenFourier_equation`;
- `xiThetaFourierSolutionSet_eq_singleton`;
- `xiThetaEigenFourier_real_source_equation`;
- `xiDivisorMultiplicity_eq_one_of_simple`;
- `xiSpectralPoint_injective_of_simple`;
- `xiThetaEigenEvaluationLp_eq_smul_single`;
- `xiThetaEigenEvaluationLp_eq_zero_of_deriv_eq_zero`;
- `xiThetaEigenAlgebraicSubspace_eq_simpleCoordinateSubspace`;
- `xiThetaEigenHilbertClosure_eq_simpleCoordinateClosure`;
- `xiThetaEigenAlgebraicSubspace_dense_of_simple`;
- `XiZerosSimple_of_xiThetaEigenAlgebraicSubspace_dense`;
- `xiThetaEigenAlgebraicSubspace_dense_iff_simple`.

### 2. Exact conservative-metric law

For a positive atomic metric supported on the real centered Xi divisor, conservativity means that
every actual theta eigenfunction has strictly positive norm. The tree proves

```text
there exists a conservative divisor-supported theta metric
  iff RH and every Xi zero is simple.                       (3)
```

The reverse implication constructs the unit multiplicity weight explicitly. The forward
implication uses the exact eigenfunction norm: nonreal zeros and multiple real zeros are null.

Declarations:

- `xiUnitRealDivisorWeight`;
- `xiRealDivisorMass_unit`;
- `xiUnitRealDivisorWeight_conservative_of_simple`;
- `exists_conservative_xiThetaMetric_iff_rh_and_simple`.

### 3. Compact reciprocal Xi operator

The reciprocal coordinates are square summable, hence `R_Xi` is Hilbert--Schmidt and compact
without RH. Its diagonal retains the complete analytic multiplicity. The formal determinant is
the multiplicity-exact canonical Xi product on the determinant convergence disk:

```text
det_2(1-z R_Xi)=xiCanonicalProduct(z).                      (4)
```

Moreover,

```text
R_Xi is self-adjoint iff RH.                                (5)
```

Under simplicity every `E_alpha` is an eigenvector with eigenvalue `alpha^(-1)`, and `(1)` makes
this eigenfamily complete.

Declarations:

- `isHS_xiReciprocalDiagonalKernel`;
- `xiReciprocalOperator_isCompact`;
- `xiReciprocalOperator_isSelfAdjoint_iff_rh`;
- `xiReciprocalOperator_thetaEigen`;
- `fredholmDet_xiReciprocalDiagonalKernel_eq_xiCanonicalProduct`.

### 4. Source-to-Hilbert capstone

The already formalized continued prime--Gamma one-Cauchy diagonal sign is equivalent to RH. It is
now coupled to `(1)` without any added interface:

```text
continued prime--Gamma one-Cauchy sign
  + complete actual theta eigenfamily

iff RH + simplicity

iff existence of a conservative Hedenmalm metric

iff R_Xi self-adjoint + complete actual theta eigenfamily.  (6)
```

Declarations:

- `continuedPrimeArchUpperCauchyFormula_iff_riemannHypothesis`;
- `continuedPrimeArchFormula_and_thetaComplete_iff_rh_and_simple`;
- `continuedPrimeArch_and_thetaComplete_iff_rh_and_simple`;
- `continuedPrimeArch_and_thetaComplete_iff_exists_conservative_metric`;
- `continuedPrimeArch_and_thetaComplete_iff_selfAdjoint_and_eigenComplete`;
- `exists_conservative_xiThetaMetric_iff_selfAdjoint_and_eigenComplete`.

## What is and is not source-derived

The prime--Gamma sign in `(6)` is source-defined through the continued von-Mangoldt plus
archimedean relative-resolvent formula. The reciprocal operator `R_Xi` is divisor-indexed. It is
therefore the exact terminal operator a successful source construction must reach, not itself a
proof of RH.

The new positive obligation is exact:

```text
construct the conservative metric from the completed source
  while preserving theta-eigenfunction completeness.       (7)
```

A semidefinite metric supported only on already-real zeros fails `(7)`. A target-fed diagonal
operator satisfies the terminal determinant but does not establish the source sign. Equation `(6)`
shows that both defects are visible in one closed chain.

## Formal verification

- targeted builds of all three modules pass;
- the modules are imported by `GaloisForLFunctions.RHTower`;
- no `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration occurs;
- every headline theorem prints only the standard kernel foundations
  `propext`, `Classical.choice`, and `Quot.sound`.

## Novelty and significance boundary

The reciprocal diagonal model and the individual implications `real divisor <-> self-adjoint
diagonal` are classical bridge material. Candidate novelty attaches to the exact theorem package
for Hedenmalm's June 2026 theta pair:

1. uniqueness of the removable entire solution of the transformed theta-source equation;
2. the exact simple-support defect law `(1b)` and the if-and-only-if completeness law `(1)`,
   including analytic multiplicity copies;
3. the conservative-metric existence law `(3)`;
4. the source-sign/completeness/operator capstone `(6)`;
5. the identification of multiplicity as the precise obstruction separating the source Cauchy
   Hilbert carrier from the one-eigenfunction-per-zero theta family.

No RH proof is claimed. Independent operator-theory and contemporaneous-literature review remains
required before assigning the requested publication significance score.

## Gates

- [x] simple zero gives exactly one divisor copy
- [x] removable quotient is the unique continuous solution of the transformed theta equation
- [x] real-axis forcing is the Fourier transform of the concrete theta-cusp source
- [x] exact eigen-span equals the algebraic simple-coordinate span
- [x] evaluated theta eigenfunction is a basis coordinate under simplicity
- [x] eigenfunction completeness implies simplicity
- [x] eigenfunction completeness iff simplicity
- [x] conservative metric existence iff RH plus simplicity
- [x] reciprocal operator Hilbert--Schmidt and compact unconditionally
- [x] reciprocal operator self-adjoint iff RH
- [x] reciprocal determinant equals the Xi canonical product on its convergence disk
- [x] continued prime--Gamma source sign coupled to theta completeness
- [x] exact module builds
- [x] axiom audit
- [ ] full literature audit
- [ ] standalone paper with no formal-verification references
