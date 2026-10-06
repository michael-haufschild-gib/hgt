# BAG complete allowed prime collision cancellation

2026-10-06,02az/03az. CLOSED on paper and in Lean.
ChiCubicAllowedPrimeCollision: 540 lines, API2 at480/519.

The literal sharp-band Gaussian cubic allows p=q!=r. Its ENTIRE such sector
has complex norm o(N/log²N). This is a signed saving beyond its critical-size
counting estimate. Both original contraction exclusions remain respected;
the physical W window and actual V factors are retained without hypotheses.

Paper proof: embed the prime masks in coefficients of the complete integer
matrix exp(2pi*i*p²/r), N<=p,r<=2N. For r!=s the column correlation has
quadratic curvature2|r-s|/(rs). The source second-derivative theorem gives
96N/sqrt|r-s|. Schur, Cauchy and the source harmonic separated-row estimate
give Gram budget B_N=(N+1)+96N*sqrt(N+1)*sqrt(2*(1+log(N+1))).

The actual physical logarithmic Schwartz multiplier preserves this matrix
bound. Its exact identity physicalLogWindow(logx)=sqrt(x)*W(x) makes each
original entry equal (2pi/N)*c_r*d_p*K(p,r)*physicalLogWindow(2logp-logr-logN),
where c_r=1_prime*(sqrtN/sqrtr)*conj(V(r/N)) and
 d_p=1_prime*(N/p)*V(p/N)^2.
Both coefficient norms are<=1. The full double sum is bounded by
4pi*physicalLogWindowFourierBudget*sqrt(B_N). Removing the all-equal diagonal
costs<=16 using the actual entry and prime-band bounds. Finally
(log²N/N)*sqrt(B_N)->0, proved by the squared majorant600log^5N/sqrtN.
Every intermediate analytic estimate is proved; no budget premise remains.

Final production81595, /tmp/bag-collision-production-01az.log: terminal0,
empty PASS, lake --old env lean on the leaf with explicit olean. Imported
axiom54541, /tmp/bag-collision-axioms-01az.log: terminal0, both API declarations
use only propext, Classical.choice, Quot.sound. Scratch07 audit91148 checked
five private/public stages with the same standard axioms. No admissions,
new axioms, heartbeat or recursion increases. RHT umbrella import once;
no full or umbrella build. Index16094 PASS; both declarations indexed.

Authoritative lint26717 terminal1:367 warnings, two unrelated unreachable
modules, no owned finding. Global lint is NOT clean. Exact errors:
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.XiStripEdgeSquaredWeightSum
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.HalfShiftHarmonicEulerBound

The remaining pairwise-distinct cubic/global defect is not estimated here.
Growing mixed moments/cofactors, deterministic common-height self-return,
and RH remain open. This closes a source sector, not the BAG route.
