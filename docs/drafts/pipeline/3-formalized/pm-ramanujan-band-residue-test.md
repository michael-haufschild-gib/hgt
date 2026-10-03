# Route PM: a positive compact test of the complete critical residue numerator

- **ID:** pm-ramanujan-band-residue-test
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Continuation:** `../1-in-progress/pm-ramanujan-band-spectral-escape.md`.

## Exact statement

For epsilon>0 and an actual critical zeta zero rho=1/2+i*gamma, put s(tau)=1/2+i*tau, r(tau)=epsilon+s(tau)-rho and retain the entire actual cleared numerator

    A(tau)=alpha_epsilon*zeta(s(tau))/s(tau)
      *(1-2^(-r(tau)))/r(tau)
      *zeta(1+rho-s(tau))*H_epsilon(rho,s(tau)).

There is a nondegenerate compact interval I strictly to the right of gamma on which A is continuous and nowhere zero. The literal test h=indicator(I)*A belongs to L2, its support stays a positive distance from gamma, its pairing with A is integrable, and

    integral conjugate(h(tau))*A(tau) d(tau)
      = integral_I |A(tau)|^2 d(tau) > 0.

The equality views the positive real integral inside the complex numbers. No simplicity or zero-multiplicity assumption is needed. The actual critical zero is the parameter of this intermediate theorem; the final escape theorem must instantiate it with the corpus's unconditional critical-zero existence theorem.

## Dependency-closed paper proof — [PROVED HERE]

The actual zeta-zero set is discrete, so an open neighborhood U of rho contains no other zeta zero. The already audited joint Euler-correction theorem gives a neighborhood of (rho,rho) on which H is nonzero. Pull both neighborhoods back along tau -> s(tau). A sufficiently short interval gamma<tau<gamma+R then has both zeta(s(tau)) and H_epsilon(rho,s(tau)) nonzero.

The density alpha_epsilon has strictly positive real part. The critical point s(tau) has real part1/2 and is nonzero. The real part of r(tau) is epsilon>0, so r(tau) is nonzero and |2^(-r(tau))|=2^(-epsilon)<1. Thus the complete dyadic factor is nonzero. Finally, 1+rho-s(tau) has real part1, where the actual zeta function is nonzero. Every literal factor of A is therefore nonzero on the punctured interval.

Away from tau=gamma, all zeta arguments avoid their possible pole. Complex powers with the fixed nonzero base2 are continuous, r stays nonzero, and the Euler correction is jointly continuous on its audited domain. Hence A is continuous there. Take I=[gamma+R/4,gamma+R/2]. It has positive length, remains inside the punctured interval, and stays distance at least R/4 from gamma.

Continuity on I gives integrability of |A|^2 and hence L2 admission of the indicator test. Its literal product with A is indicator(I)*|A|^2. This product is integrable; its integral is strictly positive because the integrand is positive at every point of I and I has positive measure. This retains all arithmetic factors and their complex phases until the explicit conjugate test is applied.

## Contribution and remaining hard problem

The construction rules out cancellation of the complete boundary numerator under a bounded frequency test. It supplies the positive side of the proposed cleared-identity contradiction. The actual tested scale transform still needs analytic continuation, and the norm-null variable-profile remainder still needs its Abel limit. No spectral-escape, small-damping energy upper bound or RH conclusion follows from this construction alone.

## Verification status

The complete extended scratch passed foreground Lean with exit0 and no diagnostics: numerator nonvanishing and continuity, compact-test L2 admission, literal pairing integrability and identity, and an actual L2 witness with positive frequency gap and strictly positive complete-numerator pairing. The nine-export leaf `PMRamanujanBandResidueTest.lean` is now promoted and wired once. Targeted `lake --old build GaloisForLFunctions.RHTower.PMRamanujanBandResidueTest` passed (only the new leaf built, 172 seconds). Mandatory `lake env lean GaloisForLFunctions/RHTower/PMRamanujanBandResidueTest.lean` passed with no diagnostics. All nine exports were queried from a separate /tmp scratch file and depend only on propext, Classical.choice and Quot.sound. Lint reports eleven unrelated unreachable modules; no own finding. No heartbeat increase or umbrella build.
