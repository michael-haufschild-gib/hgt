# All-level generator approximation at every real lag

## Theorem and actual source

Let U be the proved whole-line logarithmic-cell isometry and P_A the cutoff
retaining the root and all labels a<A at every level. The physical high-tail
projection is R_A=U(1-P_A)U*. Every compact real BV profile has

norm(R_A f)^2<=32 Gamma(f)/(1+log A), A>=1.

Removing this high tail changes every real-lag correlation by at most
96 Gamma(f)/(1+log A). The full critical Euler correlation for a fixed finite
prime set P has error at most96 C_P Gamma(f)/(1+log A), where
C_P=sum_(p in P) 2 log(p)/(sqrt(p)-1). For finite
original cell sources, f-R_A f=U P_A U* f, so this is approximation by
finitely many complete generator families.

## Mathematical mechanism

Orthogonality gives inner(R_A f,g)=inner(R_A f,R_A g). Cauchy–Schwarz and
the two original-source tail bounds pay this pairing by
16*(Gamma(f)+Gamma(g))/(1+log A). Translate the original profile, retaining
its Gamma energy, to get both mixed translated-tail bounds with cost
32 Gamma(f)/(1+log A). Shift isometry pays tail–tail correlation by the same
cost. The exact head subtraction therefore has cost96 Gamma(f)/(1+log A),
uniform in the real translation lag.

For each prime p, the literal critical coefficient sum is
C_p=2 log(p)/(sqrt(p)-1). Each Euler series is absolutely convergent for
every whole-line L2 vector, before any head subtraction. Its terms equal
the original profile correlation integrals on compact real BV sources.
For a fixed finite prime set, sum C_p once. Choosing
A>exp(96 C_P/delta) makes the error at most delta times original Gamma,
uniformly in the source and horizon. All prime powers remain in the sum.

## Formalization and boundary

Lean modules:
`SignedArithmeticHodgeTheory/EveryTranslationHasAnAllLevelGammaTailBound.lean`
and `SignedArithmeticHodgeTheory/FiniteEulerFactorsHaveAllLevelGeneratorApproximation.lean`.
Capstones: `inner_wholeLineGeneratorTail_eq_tail`,
`norm_inner_generatorTail_sources_le`,
`abs_allLevel_translation_head_error_le`,
`abs_wholeCell_allLag_head_error_le`,
`summable_norm_wholeLinePrimeEuler`,
`summable_norm_original_primeEuler_integrals`,
`wholeLineFiniteEulerCorrelation_realSource`,
`abs_wholeCell_finiteEuler_head_error_le`,
`exists_finiteEuler_allLevel_generator_approximation`.
Both individual no-olean checks pass. Printed transitive capstone dependencies
contain only `propext`, `Classical.choice`, `Quot.sound`.
Exact odd-prime commutation is neither asserted nor needed.

No Gamma contraction under projection is assumed. The whole-line complement
of the cell space is retained for general profiles; only actual cell sources
have the finite-generator interpretation. Finite-prime bounds do not give a
summable allocation over all primes. Continuous Gamma/pole interactions and
the retained-orbit sign remain full-Weil research obligations.
