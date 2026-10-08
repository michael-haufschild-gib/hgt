# Exact tail repair for the exposing ray

Main WP02 inequality remains OPEN.

## Audited conjectures

1. **Ground-state identity alone supplies a positive residual.** Verdict: REDISCOVERED for the identity; no sign proof. `RiemannKernelGroundStateZeroIdentity` already provides the zero-side transform. Its complex exponential kernel has no established sign. This route has not been disproved; it has not supplied the required inequality.
2. **Exposing trace tails admit positive-mixture repair with precisely their box-tail cost.** Verdict: BRIDGE. The two-point construction is already inside the corpus linear-duality proof; the explicit tail certificate and its cofinal transport quantify the missing extension step. No claim of new scientific knowledge beyond the parent duality theory.

## Dependency-closed paper proof of the repair certificate

Write w(n)=exposingWeight(n), b(n)=(log n+C0)|w(n)| for n>=2 and b(n)=0 otherwise. Put tau(N)=sum_{n>N} b(n). The corpus proves b>=0 and sum b<infinity.

For arbitrary natural N,M, index a finite family by S={n: max(2,N+1)<=n<=M}. At n in S let s_n=1 if w(n)>=0 and s_n=-1 otherwise. Take the existing polar two-point resonator r_n=twoPointResonator(n,s_n), at atomLevel(n), with positive bump mass m_n. Give it coefficient alpha_n=|w(n)|/(4*pi*m_n)>=0. The existing exact atom formula gives

    2*pi*alpha_n*atomCoeff(r_n,j) = w(n) if j=n, 0 otherwise (j>=2).

Consequently this family realizes the tail trace w(j) 1_{N<j<=M} at every integer j>=2, including every omitted coefficient. Its total archimedean energy is at most

    sum_{n in S} (log n+C0)|w(n)| = sum_{N<n<=M} b(n).

For N<=M this equals tau(N)-tau(M), by absolute convergence. In all cases it is at most tau(N), which tends to zero as N tends to infinity, uniformly in M. The functions are smooth compactly supported polar tests; the mixture has nonnegative coefficients even when w(n)<0. No numerical computation and no positivity hypothesis for an unknown Weil producer enters.

If M<=floor(exp(2B)), the corpus `atomLevel_le` places all repair tests at level B+1. Therefore appending the family (scaled by t>=0) to any family matched to t*w_N produces a family matched to t*w_M, at level max(A,B+1), and raises its energy by at most t*(tau(N)-tau(M)).

## Cofinal implication and remaining estimate

Suppose a future proof supplies dual bounds at cutoffs M_j tending to infinity and levels C_j tending to infinity, with every repair test for n<=M_j admitted at C_j, and lower bounds E-tau(M_j)-epsilon_j where epsilon_j tends to zero. Append the repair certificate to a fixed original family at cutoff N and aperture A. For all sufficiently large j, M_j>=N and C_j>=A. Subtracting the repair upper bound gives original energy >=t*(E-tau(N)-epsilon_j). Passing to the real limit proves the exact desired bound. This step includes t=0 and arbitrary finite complex test families.

[OPEN CORE] Prove those diagonal dual lower bounds from the actual archimedean source, uniformly over the full matched-test cone. The repair theorem proves no such lower bound.


## Earlier conjecture: logarithmic cost of independent repair

For s in {-1,1}, conjecture

    archEnergy(twoPointResonator(n,s)) / (4*pi*resonatorMass(n)*log(n)) -> 1

as n tends to infinity, uniformly over these two signs. The existing corpus gives the upper bound with log(n)+C0. The proposed lower mechanism is support-measure uncertainty: a normalized Fourier density of a function supported on total measure L is bounded above by L/(2*pi), forcing its logarithmic frequency moment above log(pi/L)-1. Combine this with a uniform logarithmic lower bound for the actual digamma symbol and the exact disjoint-bump mass. Here L is of order 1/n.

[OPEN CORE] Verify all constants, Fourier conventions, support measure and logarithmic integrability, and complete the source lower bound. No theorem claimed. This would establish a sharp limitation of independent atom repair, not WP02 positivity. Its general parent is logarithmic uncertainty / the Dirichlet logarithmic Laplacian, so a routine specialization would fail the scientific-novelty gate. Seek a collective matched-trace result if that audit kills the candidate.


## Cycle 3 update

`PACKET-PROOF.md` closes the stronger, coefficient-uniform finite-size lower bound on paper and in Lean. It retains every Fourier cross term and avoids separate logarithmic integrability. The independent logarithmic cost mechanism was therefore not pursued as a separate scientific-novelty claim. No Lean limit theorem for the normalized two-point ratio is claimed here; the formal deliverable is the stronger finite-N coercivity inequality itself.


## Cycle 5: sharp literal tail

TAIL-SIGN-PROOF.md contains the complete theta-envelope and outermost-shift argument. The new source module proves eventual positive coefficients, exact logarithmic rate `-2*pi*exp(-2)`, subcritical exponential bounds for the existing box tail, and strict tail positivity at every finite cutoff. Full scratch and final installed leaf checks passed without warnings. All eight audited capstones use only propext, Classical.choice and Quot.sound. These estimates improve the previously formalized repair budget without supplying the universal energy lower bound.

## Cycle 6: uniform truncation and exact source realization

`UNIFORM-TRUNCATION-PROOF.md` contains the dependency-closed proof of uniform double-exponential polar autocorrelation and actual archimedean energy errors. `REALIZATION-PROOF.md` gives the full paper construction of finite exact matched families at natural aperture with energy <=E+(1+epsilon)*tau_N. The former passed final leaf and standard-axiom audits; the latter is not yet formalized. Neither is a lower-bound producer.

## Cycle 7: full finite assembly

REALIZATION-PROOF.md is now implemented in the complete finite-realization scratch, including exact repair at every residual integer, nonnegative coefficients, aperture overhead, finite shift truncation, and the eventual comparison against the literal positive tail. All three public capstones pass the standard-three-axiom audit. Final installed leaf check passed without warnings. The resulting bound is existential and upper; universal WP02 positivity remains open.

## Far-polar repair budget

See POLAR-LEAKAGE-PROOF.md for the dependency-closed proof of the sharp scale X exp(X), uniform smallness of the actual traces, persistent negative energy, and the uniform exposing-target residual lower bound. Formal source: `WeilWorkExposingRayPolarLeakage.lean`.

The opposite-ray uniqueness reduction was audited against prior work and classified REDISCOVERED. It supplies no missing lower estimate. The far-polar estimate instead diagnoses an actual source failure and isolates the cost incurred by the omitted second correlation window. Arbitrary coherent corrections remain outside this obstruction.

## Cycle 10 source theorem

POLAR-UNIFORM-TAIL-PROOF.md supplies the dependency-closed proof of a common positive tail for every actual polar shift 0<c<=1, strengthened to a D*c^4*exp(-C*exp(y)) lower bound. The proof keeps the full theta derivative series, estimates all negative parts of the signed autocorrelation, and uses the exact finite-interval Green identity. The normalized Green weights cancel before the envelope comparison. This source theorem does not discharge the universal matched-cone energy lower inequality stated above.

## Cycle 11: exact geometric completion floor

COHERENT-GAP-PROOF.md supplies the dependency-closed proof and its stronger refinement-invariant version. Literal compact C2 sources enter the exact weighted CCM form domain, preserving both polar moments and the 2*pi Fourier normalization. The existing one-tenth ground gap yields the actual-source bound. A fixed plateau gives E(f_s)>=(3*pi/25)*(1-c_s)^2, and the finite geometric multiplier at zero gives M*(1-c_s)=1-c_(Ns). Together these give total completion energy >=(3*pi/25)*(1-c_(Ns))^2, uniformly under arbitrary short-step refinement. The C2/short-source leaf and complete geometric capstones pass full scratch, standard-axiom and final installed-leaf audits. The universal lower inequality remains OPEN.

## Cycle 12: local-seed capacity, literal Riemann source

LOCAL-SEED-CAPACITY-PROOF.md closes the full unequal-seed finite variance identity, the exact C2 short-window Fourier evaluation cost, and a cutoff-independent positive zero-frequency mass for the actual unit-shift Riemann source. These now compile in WeilWorkExposingRayLocalCapacity.lean. The whole finite exposing mixture pays at least riemannCapacity/(2*pi), allowing independently varying finite seed types, coefficients, profiles and positions at every k. This is an exact positive survivor for that representation class, not an energy premise or an estimate for arbitrary repairs. Universal WP02 remains OPEN.

## Cycle 13: exact sampled mass and stability

LATTICE-REPAIR-PROOF.md is formalized in WeilWorkExposingRayLatticeMass.lean. Every rounded sample isolates one actual Fejer covariance coefficient. The retained pole product gives exact mass recovery; only one actual half-pole is needed. Its stability bound controls coefficient mass by the complete cosh-weighted absolute sampled trace, and sampled nonnegativity classifies precisely zero active rows. All seven public capstones pass scratch/axiom and final installed source audits. This positive conservation/stability survivor does not supply the universal signed energy lower bound.

## Cycle14: all-order polar differential tail sign

Dependency-closed proof is in DIFFERENTIAL-PARITY-PROOF.md. The signed source polynomial has degree k+4 and positive leading coefficient 4*pi^2*(2*pi)^(k+2). Its full theta series supplies a positive right-tail lower envelope and a two-sided double-exponential upper envelope. In the convolution, any adverse product places one argument below the fixed cusp threshold and the other beyond y-R, costing exp(-a*exp(2(y-R))). The central interval contributes twice exp(-2*pi*exp(2)*exp(y)); the adverse integral is eventually at most half that contribution. Exact parity then converts convolution to (-1)^k times autocorrelation. This proves the sign law without dropping a signed region. All-order Fourier linearity proves actual polar/radical zeros separately.

The complete scratch proof and final installed leaf/cache audit pass without warnings, with ten public scratch axiom audits using only the standard three axioms. This is not compact-support admissibility or an energy bound. The next compact correction and the actual exposing-rate comparison are explicitly OPEN in COMPACT-ODD-SOURCE-CONJECTURE.md.

## Cycle 15: strict translation-width boundary

See DIFFERENTIAL-WIDTH-PROOF.md for the dependency-closed proof. A fixed cusp polynomial is absorbed into every subcritical theta exponent; exact parity supplies the second tail. Complex finite synthesis has a uniform envelope with coefficient l1 mass, and the full autocorrelation has an integrable norm majorant. The literal lower exposing-weight envelope then yields uniform exponential separation, homogeneous finite-mixture amplification, fixed-mixture nonproportionality, and invariance under independent recentering. The final formal packet uses all actual derivatives Phi^(k), so finite polar differential filters and order-zero translation filters are included. No spectral or energy sign is inferred.


## Cycle16 proof chain: actual opposite proportion

The complete paper argument is [CRITICAL-WIDTH-ODD-PROOF.md](CRITICAL-WIDTH-ODD-PROOF.md). The checked source leaf expands the finite real covariance at all25 pairs, pays integrability for every translated full or truncated profile, and transports the identity to the actual complex Weil autocorrelation. Its entire Fourier multiplier proves both poles and all actual zero evaluations; compact C² admission and signed-energy integration retain every residual.

The checked tail leaf identifies H with an order-zero Phi packet and recenters its translation window to radius3/4. The uniform cycle15 packet estimate also controls every remaining polar row because its shift is at most1/2 and coefficient norm sum at most2. Dyadic summability therefore bounds the complete infinite remainder. Combining this with the already proved literal lower envelope at rate2*pi*exp(-2) gives exponential relative error, ratio minus one, and strict negative tail. No positivity or spectral hypothesis enters these actual-source statements.

The remaining core is unchanged. Full G is noncompact; compact G_L has exact poles but not exact negative exposing trace. The faster residual is not zero at the finite head, and the exact signed energy identity does not pay that head's correction cost. The zero-trace lower condition is the existing PrimeBlindPositive condition, not a premise established by this construction. See CRITICAL-HEAD-COST-CONJECTURE.md for the next hostile paper audit.

## Cycle17: exact matched-ray mass and zero-margin boundary

MATCHED-MASS-MARGIN-PROOF.md gives the dependency-closed argument. The complete complex correlation is bounded by physical mass using 2ab<=a²+b² and translation invariance. One actual positive exposing atom then bounds the mass of EVERY matching nonnegative mixture below, with the exact 4*pi normalization. Combine this with natural-aperture finite realization and the literal tail envelope to obtain the exponentially small normalized excess upper bound and strict failure of every positive mass margin. No energy lower hypothesis occurs. The complete scratch and final installed leaf/cache audits pass; no global positivity conclusion is drawn.

The stronger opposite-ray head-cost route is DEFERRED, not disproved: its weak-duality consequence is full cone uniqueness. Single-source exposure, ordinary near-radical approximation and scalar factorization do not supply the missing endpoint. The next spectral-density conjecture concerns the actual retained source plus positive repairs, with an explicit novelty/utility gate before implementation.


## Cycle18 — primitive loss and optimized survivor

PRIMITIVE-SHARPNESS-PROOF.md closes the full argument. The old scalar logarithmic inequality discarded -1 in log x<=x-1; restoring it gives B_b(f)+M(f)/4<=E(f) for all compact complex C2 sources. The bounded inverse multiplier gives 0<=P<=16*M. For M>0, P>0 follows from varying b; b=log(M/P)/4 yields E>=(log(M/P)/4-C)*M. The zero-mass case follows from P<=16*M and is included without a nonzero-mass premise. An exact multiplier identity identifies P with the original smooth compact primitive's Fourier mass.

Cosine inversion at zero gives M=2*pi*physicalMass. Apply cycle17's actual exact-ray counterexamples with physical-mass debit pi/2 and sum the restored inequality against arbitrary nonnegative coefficients. The SAME family makes every row-dependent old surrogate smaller than T-c*tau_N, for every fixed real c. No sign of E-T is inferred. Both final installed source audits pass; axiom audit is tracked in EVIDENCE.md.

[OPEN CORE] VANISHING-MASS-DEFECT-CONJECTURE.md asks for a universal lower bound with negative mass error K/(1+log N) on the cofinal diagonal. Canonical repair mass is uniformly bounded on paper, permitting that error to vanish for each fixed original family. The producer estimate remains completely unpaid; a conditional reduction alone is not another research contribution.
