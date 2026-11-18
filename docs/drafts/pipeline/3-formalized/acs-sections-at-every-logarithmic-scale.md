# Prime-pair sections at every logarithmic scale

For every δ < 1 and C ≥ 0, every sufficiently large real T has a set of more than C exp(δT) primes in |log p − T| ≤ 32 log(T+2) for which the full contact moduli of m(e₁ + eₚ) fit strictly inside the original radius. One multiplicity threshold works for the entire set. [eventually_many_prime_moduli_fit_at_every_scale](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/SmallSectionsAtEveryLogarithmicScale.lean#L142)

**Proof.** It suffices to take 0 ≤ δ < 1. Choose δ < γ < β < 1 with β > 7/12. After deleting at most C exp(δT) primes, each u in the inner half-window still has an undeleted prime with 0 ≤ u − log p ≤ 2 exp((β−1)u) in the outer window. Indeed δT ≤ γu throughout the inner window at large T. [Short-interval prime avoidance](../../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/FinitePrimeAvoidance.lean#L118)

Under RH, every prime pair has positive degree. Otherwise let w > 0 be the zero width and put a = max(0,w+β−1) < w. In every sufficiently late inner window the trace 2 Re S(u) exceeds B exp(au) somewhere, for any fixed B. Moving to the undeleted prime costs at most L exp(au) by the width-w derivative estimate. Take B = L + |2 Re S(0)|. The prime pair then has strictly positive degree. [Upper trace peaks](../../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/UpperLogarithmicWindows.lean#L101) · [Width derivative bound](../../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/TheGapMethodIterates.lean#L96)

The positive-degree primes escape every allowed deletion, so their number exceeds C exp(δT). The signed-degree Tate limit puts each of their generators strictly inside its ball for all sufficiently large m. Intersecting these finitely many tails gives the common threshold.

**Open.** Cofinal effectivity for each prescribed prime. [All-prime receiver](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/SectionHeightsAndThePickIndex.lean#L115)
