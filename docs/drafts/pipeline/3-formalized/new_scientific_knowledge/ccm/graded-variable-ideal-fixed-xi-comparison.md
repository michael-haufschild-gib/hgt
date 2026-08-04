# Graded variable-ideal comparison to fixed physical Xi quotient

- **ID:** `graded-variable-ideal-fixed-xi-comparison`
- **Stage:** 3 — formalized
- **Type:** THEOREM (Lean)
- **Status:** `[PROVED HERE] [FORMALIZED UNCONDITIONALLY] [AXIOM-AUDITED] [NO COMPUTATION] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeFirstTraceGradedVariableIdealFixedXiComparison.lean`
- **Parent:** `../../../1-in-progress/route-r-graded-variable-ideal-fixed-xi-comparison.md`

## Theorem

Let `I` be the fixed complex `ell1` ideal on ordinary-prime sequences and

```text
C_t(a)(p)=p^(-2t)a(p),
J_t=C_t^(-1)(I).
```

Then:

1. `C_(-t) C_t=id` and `C_t(F_t)=F_(-t)`;
2. `C_t` induces a complex-linear equivalence `S/J_t ~= S/I` for every real `t`;
3. the full complex resolved coefficient line at grade `t` lands on `[F_(-t)]`;
4. in `|t|<1`, this coefficient landing is injective exactly when `t<=0`;
5. both reflected orientations are injective exactly when `t=0`;
6. the actual rational-adelic period-one Stokes regulator gives a resolved-frame map sending the
   retained prime-isotropy class to `(0, XiC^(m_rho)(rho))`, which is nonzero;
7. its coefficient reporter equals the second-coordinate reporter of the existing strict
   prime-localized positive-resolved Xi boundary;
8. fixed physical specialization factors through this resolved frame and lands on
   `XiC^(m_rho)(rho) [F_(-t_rho)]`;
9. the Gamma-reflected specialization lands on `XiC^(m_rho)(rho) [F_(t_rho)]`;
10. simultaneous physical nonerasure at one divisor copy is equivalent to
    `Re(rho)=1/2`, and global simultaneous nonerasure is equivalent to RH.

No coefficient-faithfulness or critical-line premise is assumed.  Resolved coefficient
faithfulness is constructed unconditionally; physical nonerasure is classified.

## Main Lean declarations

- `primeReflectedCharacterMultiplier_involution`
- `primeVariableIdealFixedComparisonEquiv`
- `primeVariableIdealFixedComparison_coefficientClass`
- `primeVariableIdealResolvedCoefficientLanding_injective_iff`
- `ccmRationalAdelicPrimeXiVariableIdealStokesComparison_resolvedBoundary`
- `ccmRationalAdelicPrimeXiResolvedFrameComparison_class_ne_zero`
- `ccmRationalAdelicPrimeXiResolvedFrameCoefficient_eq_resolvedBoundary`
- `ccmRationalAdelicPrimeFixedXiStokesComparison_factorization`
- `ccmRationalAdelicPrimeReflectedFixedXiStokesComparisons_class_ne_zero_iff`
- `ccmRationalAdelicPrimeFixedXiStokesComparisonsCoefficientFaithful_iff_riemannHypothesis`

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/PrimeFirstTraceGradedVariableIdealFixedXiComparison.lean
lake build GaloisForLFunctions.RHTower.PrimeFirstTraceGradedVariableIdealFixedXiComparison
```

Both pass.  `#print axioms` for all load-bearing declarations reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Exact remaining frontier

The raw singular comparison, actual source map, coefficient-faithful resolved frame, leading Xi
reporter square, fixed physical map, and reflected physical map now exist.  Remaining Route-R
theorem is source-derived global nonerasure of both physical images.  The formal classification
proves that asserting this property is exactly RH; it must come from new pre-divisor arithmetic
structure and fail in off-line generalized-prime carriers.

## Novelty boundary

Pullback submodules and quotient equivalences are parent algebra.  Candidate new content is their
exact synthesis with activation-Fisher trace grade, retained rational-adelic prime-isotropy `H1`,
period-one bilateral Stokes regulator, multiplicity-leading strict resolved Xi boundary, and the
two-orientation physical nonerasure classification.  No priority claim is made without broader
ancestry audit and independent expert review.

## Log

- 2026-08-04 — Paper proof completed, full complex Lean construction added, source/resolved/physical
  factorization proved, targeted module build passed, axioms audited, umbrella wired.
