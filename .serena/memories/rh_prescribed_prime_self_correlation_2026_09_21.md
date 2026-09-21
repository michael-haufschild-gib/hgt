# RH prescribed-prime self-correlation and direct simultaneous debt descent
Paid exhaustive continuation and RH remain unproved. Own fact log: docs/drafts/pipeline/1-in-progress/rh-exhaustive-clock-continuation-facts.md. Do not modify other agents' logs.

## Closed new source producers
formal/GaloisForLFunctions/RHTower/MobiusDivisorPrescribedPrimeSelfCorrelation.lean:
- exists_mobiusDivisorDilationMean_uniform_plus_gap: a single c>0 before every finite prime core P and A>=1 satisfies c<=D_P(1)+D_P(A)/A.
- exists_mobiusDivisor_uniform_prescribed_prime_correlation_drop: c*rho(P)*r*sqrt(r)/(r+1)<=rho(P)*D_P(r)-rho(P+r)*D_(P+r)(r), every missing actual prime r. Exact squarefree Euler density rho retained, never drop it.
- exists_mobiusDivisorDirectPrescribedDebtReduction: any nonempty prime core, missing prime r, helper lower bound B admit actual fresh p<q and d>0 with relative full logarithmic clock debt reduced by d*M^2*(1+log M) on a common eventual integer-cutoff tail. Baseline before all helpers, no preliminary insertion.

formal/GaloisForLFunctions/RHTower/MobiusDivisorDirectPrescribedDebtDescent.lean:
- exists_mobiusDivisorDirectPrescribedDebtDescent: either prescribed-prime limiting coefficient debt <=0, or every B admits fresh actual p<q and d>0 giving simultaneous eventual drops of d*M^2*(1+log M) in old-core W, 2*d*M^2*(1+log M) in prescribed-prime-core W, and d*M^2*(1+log M) in their relative debt. No assumed payment/energy/sign bound. First disjunct is a coefficient statement, NOT finite-clock payment. The source weights and density are literal.

Mechanism: positive uniform inverse-cube signed moment; completing square for H(x)+A H(x/A); exact prime renewal at ratio r; positive debt forces D_P(r)<0 via exact release; common continuity interval; two-prime ratio profile; PNT actual primes; fixed-core full logarithmic counting limit.

## Remaining hard obstacle
Local descent does not prove full debt repayment, uniformly bounded prefixes, or control while moving cutoffs. Windows and onset thresholds depend on growing core.
Specific witness iteration chooses p>sup(P), q>r*p. For same r this is geometric helper growth. Certified d<=a/(2p), a=c*rho(P)*r*sqrt(r)/(4*(r+1)*U^2), U>=r; rho decreases. Guaranteed coefficient-normalized payments can sum arbitrarily small when first helper is far out. This is a failure of the inference from strict local descent to full payment, not an upper bound on actual payments or a disproof of other constructions. Next work must attack cumulative mixed correlations of batches at usable clock scales, not just sharpen isolated pair estimates.

Paper-only unformalized Gram feedback: K=rho*D_P(1), delta=K(P+r)-K(P), G=rho*D_P(r)-rho(P+r)*D_(P+r)(r) obey 2*K*G>=sqrt(r)*(r+1)*delta^2 via three-shift Gram inequality. Alone does not fix the geometric scale / moving-onset obstacle.

## Audits
Both scratch checks and both named leaf builds passed, no new-leaf warnings; four public theorem axioms only propext, Classical.choice, Quot.sound. Both leaves imported in RHTower.lean. No full/umbrella build. Index refresh passed. Final formal lint only four unrelated unreachable modules: ThetaCuspHawkingBMLiteralCyclicPeierlsLowerWeylRadialDetector, ThetaCuspHawkingBMLiteralCyclicPeierlsSelfInverseSquarePhysical, ThetaCuspHawkingBMLiteralCyclicPeierlsSelfMixedCuspFlux, XiHeatCassiniWoldJointDepthMöbiusSourceTransport.
All owned processes collected; scratch proof/probe/fragments removed; audit logs /tmp/hgt-self-debt* and /tmp/hgt-direct-debt-descent*. Preserve concurrent work. Goal remains active.
