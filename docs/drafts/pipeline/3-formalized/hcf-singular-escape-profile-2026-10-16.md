# HCF: resolve the polynomial packet hidden at infinity

Status: formalized; all focused builds, direct source audits, and API/axiom checks passed.

## Starting frontier

Actual normal blocks, inertia/census, Toda multiplicities, and projective admission continuation are already proved. The previous continuation contracts degree n+k to the regular-head polynomial P_n and therefore loses k roots at infinity. The new task is to recover that missing polynomial packet structurally, without RH or positivity assumptions.

## Conjecture loop

1. Full matrix singular unfolding: determinant multiplicity alone does not identify individual eigenvalue orders. A proposed partial-multiplicity ladder needs new matrix-germ arguments; do not infer it from determinant order.
2. Exact local signature pattern: negative double-pole Toda connection should force alternating adjacent pivots near a normal block. This suggests looking at the entire polynomial flow, not stopping at a sign-count formula.
3. Weighted admission blow-up: for k<d, epsilon^(n+k) P_(n+k)(a+epsilon,z/epsilon) should continue analytically to z^n Q_(d,k)(z), where coefficient z^(k-l) of Q is choose(k,l) * (d-k).ascFactorial(l). This determines the entire escaped packet, rather than only its projective contraction.

## Paper mechanism under investigation

The corpus heat connection gives P_N'=(logDeriv Delta_N)' P_(N-1). Exact determinant order M_k=k(d-k) forces the rescaled connection value -M_k. For a coefficient with deficit l>0, meromorphic primitive cancellation gives C_(k,l)=M_k/l * C_(k-1,l-1). Its solution is choose(k,l)*(d-k).ascFactorial(l). Lower coefficients vanish at the larger blow-up scales; the leading coefficient remains one.

Search the corpus for positive rising-factorial moment representations to characterize real versus nonreal zeros of the universal packet. No numerical experiments, web, novelty audit, old research markdown, extra axioms, or heartbeat increases.

## Positive structural result

The whole weighted profile is proved in Lean (first focused build passed).
The coefficient at X^j is choose(k,j)*(d-1-j).descFactorial(k-j), equivalent to the proposed rising-factorial expression. Lower coefficients vanish at the larger scale. Thus no root degree is lost in the weighted compactification.

The corpus search found NewtonInequalities.lean: the normalized top coefficients of a real-rooted polynomial obey Newton's inequality. For the escape polynomial they are exactly 1,b,b(b+1), b=d-k>0, contradicting the first Newton inequality when k>=2. Consequently every packet of degree at least two has a nonreal root. Closedness of real-rooted bounded-degree coefficient limits transfers this to actual admissions in a full punctured neighborhood of the contact. The final actual capstone has only positive-time/rank inputs and states the offset<=1/nonreal-neighborhood dichotomy.

This bypasses the integral/Gamma representation proposed above and makes no unsupported claim that all roots lie in any half-plane. The exact number of real roots is not needed or asserted.

## Dependency-closed paper proof

1. Use the actual canonical regular-head cover at positive time a. In its block n,n+d, the already proved Toda law gives determinant order k(d-k). Hence (t-a)^2 times the logarithmic-derivative curvature extends analytically with value -k(d-k).
2. The actual heat connection differentiates each coefficient of P_(n+k) into that curvature times the same coefficient of P_(n+k-1). For the coefficient at n+j, j<k, the meromorphic primitive lemma forces cancellation exponent k-j and leading coefficient C_(k,j)=k(d-k)/(k-j)*C_(k-1,j). The top coefficient is one.
3. The binomial identity and descending-factorial recursion solve this exactly: C_(k,j)=choose(k,j)*(d-1-j).descFactorial(k-j). Deficit indexing l=k-j gives choose(k,l)*(d-k).ascFactorial(l).
4. Below n, the existing order-k cancellation multiplied by the extra positive power n-i has value zero. Assemble the finitely many analytic extensions into one analytic vector. Its value is the coefficient vector of X^n Q_(d,k). Q is monic of degree k, and its constant coefficient is strictly positive for k<d.
5. For k>=2 set b=d-k>0. The first three Newton-normalized coefficients of Q are 1,b,b(b+1). If Q split over the reals, the corpus Newton theorem would imply b(b+1)<=b^2, contradicting b>0. Thus Q has a nonreal root.
6. X^n Q also fails to split. If real-rooted weighted admissions occurred arbitrarily near a, extract a sequence converging to the punctured neighborhood filter. The corpus bounded-degree coefficient-limit theorem would force X^n Q to split. This contradiction gives a whole punctured neighborhood of nonsplitting admissions. Nonzero real dilation and multiplication preserve splitting, so the actual unscaled admissions also fail to split there. The corpus complex-root characterization turns this into an explicit existential nonreal complex root.

Every actual-source input in these steps is discharged by existing unconditional heat theorems. The final capstones take only positive time and rank. Generic helper premises describe a block, bounded degree, or a convergent family; none is left as an assumption in the actual capstones.

## Completion requirements

Only intrinsic positive-time/rank inputs in actual-source capstones. Focused foreground builds, one at a time; direct lake env lean audits; umbrella wiring; axiom/lint checks; cleanup. Complete source sign remains a separate open obstacle.

## Audit record

- Focused foreground `lake --old build +Module:olean` passed for all three new modules; final builds have no warnings from these modules. No full or umbrella build was run.
- `lake env lean GaloisForLFunctions/RHTower/XiGaussianHeatAdmissionEscape.lean` passed with no output.
- `lake env lean GaloisForLFunctions/HTGeometry/HankelHeatEscapePolynomial.lean` and `lake env lean GaloisForLFunctions/HTGeometry/HeatEscapeNonreal.lean` passed with no output.
- A `/tmp` scratch audit verified 27 mathlib API names and printed the axioms of 11 central theorems, including both actual-source capstones. Every axiom list is exactly `[propext, Classical.choice, Quot.sound]`. No additional axioms or deferred proofs; no heartbeat or recursion-limit changes.
- New modules are wired into HTGeometry and RHTower umbrellas. The HCF frontier paragraph now records the escape profile and actual nonreal-root neighborhood theorem.
- `scripts/formal_tools.py lint` ran after wiring. No errors concern this contribution. Global exit 1 reports six unrelated concurrent RHTower umbrella omissions: CHMDArchimedeanDomain, CHMDBoundedPrimeGenerator, CHMDPrimeDomain, CHMDPrimeOperatorDomain, CHMDPrimeRowBound, CHMDThetaHarmonicIdentity. These files are outside this task's write scope.
- Task-owned scratch files and logs were removed after the audit. No task-owned build/search process remains. No commit or push was made.

## Formal artifacts

- `formal/GaloisForLFunctions/HTGeometry/HankelHeatEscapePolynomial.lean`: analytic-germ raising, exact escape coefficient recurrence, rising-factorial form, nonvanishing constant coefficient.
- `formal/GaloisForLFunctions/HTGeometry/HeatEscapeNonreal.lean`: degree/monicity, explicit quadratic, Newton obstruction for every k>=2, coefficient-limit transfer, weighted-polynomial dilation.
- `formal/GaloisForLFunctions/RHTower/XiGaussianHeatAdmissionEscape.lean`: actual upper-coefficient ladder, full analytic weighted profile, punctured-neighborhood nonsplitting, unconditional positive-time/rank nonreal-root dichotomy.

## Remaining frontier

The full escaping polynomial has replaced the degree loss at a singular contact. Its nonreal roots cannot be removed by a real-rooted local continuation. This does not establish that an actual long singular gap occurs, does not count all real roots of the packet, and does not select the global no-transition/source-positive branch. Those claims are neither assumed nor advertised as proved.
