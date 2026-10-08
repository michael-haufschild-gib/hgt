# Critical-width odd source: next constructive audit

Status: OPEN AUDIT. Conjectured while completing cycle 15; not yet a theorem or formal implementation target. Mandatory fresh corpus/novelty audit and complete paper proof precede Lean.

The strict-width obstruction suggests retaining the actual endpoint shifts +/-1. A new derivative is unnecessary to reverse the outer covariance sign. Instead take an odd four-point filter of the actual Riemann kernel Phi:

    g_c(t)=q1*[Phi(t-1)-Phi(t+1)
                  -(sinh(1/2)/sinh(c/2))*(Phi(t-c)-Phi(t+c))],
    0<c<1, q1=polarWeight(1).

Exact translation laws predict both half-poles vanish; oddness relates the two, and the displayed hyperbolic ratio cancels either one. Every actual Weil zero evaluation vanishes since all terms are translates of Phi. This is an untruncated source, with no compact admissibility claim.

Conjectured positive survivor: at c=1/2, its full symmetrized atom trace equals -exposingWeight(n) plus a strictly faster exponential remainder. Specifically, for every r strictly between 2*pi*exp(-2) and 2*pi*exp(-3/2), some C satisfies

    |atomCoeff(g_(1/2),n)+exposingWeight(n)| <= C exp(-r*n), n>=1.

Reason requiring audit: g's outer covariance at lag 2 is -q1²*K(y-2); exposingWeight has +2*q1²*K(log n-2), including the two symmetric samples. All remaining shifts of g have size <=3/2; the exposing mixture rows k>=1 have outer shifts <=1. Exact infinite-mixture summability must be retained. This should give atomCoeff(g,n)/exposingWeight(n)->-1 and a genuinely matched opposite tail, rather than only equal logarithmic decay.

[OPEN CORE] This still does not match the finite head, produce compact polar tests, or pay the literal signed archimedean budget -E+tau_N. A fixed head repair cost is not absorbable into tau_N. Tail sign/proportion must not be reported as an opposite-ray realization or RH proof. Before adopting, audit existing odd-shift filters and whether an existing identity already gives this result.

## Exact shortening identity to audit next

The half-step case has more structure than a tail estimate. Let h=cosh(1/4), d=cosh(1/2)=2h²-1, T_s f(t)=f(t-s), and P_s=1-(T_s+T_-s)/(2cosh(s/2)). Define

    G=(1/(2d))*[T_1-T_-1-2h(T_(1/2)-T_(-1/2))]Phi,
    H=(2h/d)*(h+T_(1/2))*P_(1/2)Phi.

For real frequency tau, writing x=cos(tau/2), the multipliers give

    |P_1|² + |G/Phi|²
      = (4/d²)*(h-x)²*((h+x)²+sin(tau/2)²)
      = (4/d²)*(h-x)²*(h²+2hx+1)
      = |H/Phi|².

Here G/Phi and H/Phi mean filter multipliers, not division by the transform at zeros. Consequently the candidate exact identity is corr(P_1Phi)+corr(G)=corr(H), at every physical lag, and the analogous exact archimedean-energy identity whenever integrable. H uses translation positions [-1/2,1], width3/2, while G and P_1 use [-1,1]. Both G and H are polar: G is a scalar multiple of (T_(1/2)-T_(-1/2))*P_(1/2)Phi, and H visibly contains the same polar factor.

This symbolic identity also applies to the actual truncated Phi source and retains compactness/poles, if established from existing operator identities. It is not yet a Lean theorem. A corpus search is still needed specifically for this shortening identity; the odd-source search did not establish its absence. The signed energy of the residual H is not known here. Iterating the half-step identity appears to leave a nonzero differential residual, so no convergence-to-zero conclusion is licensed.

Fresh odd-source search was partial (`query:autocorrelation shift`, `semantic_retrieval` unfinished). Relevant inspected hits were polar_expand, polarExposingKernel_eq_corr, ordinary logShiftRiemannDifference and its Fourier law; ConstrainedWeilTwistedOddTest concerns a different zero-mean cos-modulated profile, not this four-shift exposing coefficient. Treat this as a candidate, not a novelty verdict.

The more specific documented deep query `polar half shift cosh squared norm autocorrelation shortening positive residual identity` completed non-partially. Candidate/source/idea/ingredient sections were inspected. Relevant recoveries were generic polar-shift bounds, the compact shift-pair autocorrelation formula, the normalized polar Green representation, and existing local energy coercivity; none of the inspected results supplied the displayed half-step shortening identity. Compiler/source refresh still reported a concurrently running background indexer. This is a scoped retrieval verdict, not proof of corpus-wide absence. The next turn should audit the exact coefficient identity on paper, then formalize its positive residual and actual compact/polar source consequences before claiming a new producer.

## Reuse of the new width law

The broader Phi-derivative version of cycle 15 is useful constructively here. H is a finite order-zero Phi packet of radius3/4 after recentering. Its trace therefore decays at every rate below 2*pi*exp(-3/2). Every exposing row k>=1 is an order-zero three-shift packet with radius<=1/2 and coefficient mass 1+2*polarWeight(c)<=2. The uniform width bound, together with the summable dyadic weights, should bound the entire infinite remainder after the k=0 exposing row at every rate below 2*pi*exp(-1). Thus the exact shortening identity would reduce the critical opposite-tail proportion theorem to already established uniform packet envelopes. This is why extending the width law to Phi itself, retaining constants uniform in translation positions and coefficients, matters. It is still necessary to verify exact actual-source and normalization identities in Lean.

## Cycle 16 paper gate

Exact source definitions, polarity factorization, all-lag covariance identity, compact admission, signed energy identity and strict faster opposite-tail remainder are now audited on paper in CRITICAL-WIDTH-ODD-PROOF.md. The finite covariance identity is valid for any real common profile with integrable translated products; parity gives an alternative explanation for even Phi. Adopt this combined source/proportion target for Lean. Do not stop at the elementary filter identity alone.

Fresh cycle16 source search was partial at `query:autocorrelation odd step` and `reranking`; inspected candidate/source/idea/ingredient sections recovered existing actual polar-shift/pole/source identities and conditional positivity receivers, not a checked opposite-tail producer. Direct rg found no matching autocorrelation even/odd decomposition among the targeted corpus names. Primary external search/open compared Csordas2014's kernel/Laguerre framework again; a more recent theta-growth paper could not be opened and supplies no evidence. No global novelty or search-completeness claim.

### Cycle16 follow-up search: do not infer vanishing from iteration

The deep half-step/dyadic/Green query completed with partial coverage (68,536 inventoried/indexed files; predominantly pending or stale compiler metadata; background refresh incomplete). It timed out in semantic retrieval and two query refinements. Candidate and source-argument sections recovered short-source coercivity, exact arithmetic-symbol pairings, and conditional ground-energy/Weil-positivity receivers; none inspected supplies an unconditional elimination of this residual. A lexical OR follow-up on polarShift/normalizedPolar/greenIntegral recovered the existing normalized positive Green representation and polar-shift rigidity; its output does not include compiler-freshness metadata. Do not interpret this as a completeness or novelty certificate.

Utility audit: oddFilter has zero transform at frequency zero, while H=E-G preserves E's zero-frequency value. Repeated shortening therefore cannot be assumed to erase the residual. This is an elementary diagnostic visible in the current multiplier, not a new scientific theorem or a reason to retire the full opposite-ray route. Any iteration proposal must identify its nonzero limit or pay the resulting finite-head and signed-energy obligations. The next useful step must address those obligations or the universal lower estimate, not formalize another isolated filter identity.

### Cycle16 universal receiver audit

The zero-trace follow-up query completed partially (68,540 files inventoried/indexed; background compiler/source enrichment incomplete; unfinished finite-measure query and semantic retrieval after a Qdrant deadline). All20 candidate statements, all20 source-argument statements and the proposed ingredient set were inspected. The relevant exact existing notion is PrimeBlindPositive, not a new lemma to manufacture: WeilPositivityPrimeBlindDuality.lean defines it at292 and proves at558 that existence of a Weil-positive weight system is equivalent to prime-blind positivity at every aperture. It is precisely the t=0 obligation. It must not be assumed while claiming the WP02 universal bound.

The search's zeroTerm_nonneg hit is also not an unconditional positivity proof for the actual Weil sum. Its definition in WeilConditionalConstantSignRigidity.lean:285 evaluates the transform on the real imaginary-coordinate axis; Wsummand_eq_zeroTerm at291 requires RH to identify it with the actual summand. The proposed repair/variance ingredient set does not discharge prime-blind positivity or the opposite source's finite-head energy cost. Direct verification of these definitions prevents a circular use of a superficially unconditional theorem name.

Next WP02 gate remains the full opposite-ray head/energy problem already recorded in OPPOSITE-RAY-CONJECTURE.md. The new critical source isolates a faster complete residual and preserves compact polarity, but supplies neither the missing prime-blind bound nor an arbitrary-mixture lower bound. Avoid duplicating the existing prime-blind equivalence as supposed new research.
