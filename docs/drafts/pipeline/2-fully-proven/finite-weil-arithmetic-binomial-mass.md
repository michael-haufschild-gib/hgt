# Exact binomial value of arithmetic reference mass

Status: dependency-closed paper argument; Lean API audit and implementation next.
Date: 2026-10-10.
Scope: local Lean corpus and installed Lean dependencies only. No web, external papers, numerical experiment, or external novelty claim.

Target: identify the arithmetic-node reference G_r exactly, then substitute this closed expression into the proved log-grid comparison and actual-reader cost receiver.

Let n=r+1 and b_i=(-1)^(n-i) choose(n,i), for i in Fin(n+1). Let C=choose(n,n/2). Claim: the canonical arithmetic dual is b/C and G_r=2^n/C.

Paper proof:
1. The existing local `fwdDiff_iter_eq_sum_shift` writes the nth forward difference as the signed binomial combination of shifted values. `fwdDiff_iter_pow_eq_zero_of_lt` makes it zero on every power of degree below n. At shift one and base zero this gives sum b_i i^p=0 for p<n.
2. Absolute coefficients equal choose(n,i). `Nat.choose_le_middle` bounds every coefficient by C, and the middle index attains C. Hence ||b||_infinity=C. The final coefficient equals one, so the norm is positive.
3. The broader corpus search exposed a stronger direct producer: `GaloisForLFunctions.HTGeometry.alternating_binomial_sum_pow_eq_zero` and `alternating_binomial_sum_pow_eq_factorial` in `MicroSpectrumMomentCollapse.lean`. The existing barycentric span therefore gives b=n! W for the arithmetic nodes. Since n!>0, W=b/n!, and normalization cancels this positive scalar to give beta=b/C. This also identifies the raw arithmetic nodal weights exactly.
4. `Nat.sum_range_choose` gives sum|b_i|=2^n. Therefore the canonical arithmetic mass is 2^n/C.
5. Substitute this exact formula into both sides of `finiteWeilCanonicalCluster_arithmetic_mass_comparison`. Substitute it into `exists_finiteWeilGram_arithmetic_coordinate_cost`; that producer already gives fixed constants, actual-reader existence, and all-reader cost control. No new analytic premise is introduced.

Local sources inspected: `Mathlib/Algebra/Group/ForwardDiff.lean` lines147,237,252; `Mathlib/Data/Nat/Choose/Sum.lean` line94; `Mathlib/Data/Nat/Choose/Basic.lean` line333; current barycentric span. Initial `binomial moment annihilator` query had no hits. Broader `binomial finite difference` query found the polynomial coefficient extractor in `ThetaCuspHawkingParikhWilczekFinitePolynomialGradeNoGo.lean`, whose lighter dependency `HTGeometry/MicroSpectrumMomentCollapse.lean` provides exactly the two raw-power identities needed (lines68 and82). Reuse those existing corpus producers. Other hits concerned row transforms and jet multiplication. No mathematical evaluation by computation.

Planned leaves: `WeilLogShiftArithmeticBinomial.lean` and `WeilLogShiftBinomialCost.lean`. Native leaf builds, complete public-declaration axiom audit, verified imported API terms, source/direct-dependency freshness, umbrella imports, local index, and formal lint. One owned Lean process at a time. No full build or heartbeat increase.

Expected insight: the formerly abstract arithmetic reference becomes an explicit central-binomial ratio. This does not by itself prove an asymptotic growth rate or uniform distortion for clusters at only linear distance; those remain separate questions.
