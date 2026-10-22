# BAG full allowed first/second-prime collision cancellation

2026-10-06,02az/03az. CLOSED; final audits in matching P2/P3 cards.
Target: the ENTIRE allowed p=q!=r sector of the original sharp Gaussian
prime cubic has complexnorm o(N/log²N). This sector is retained by both
original exclusions and breaks the proposed p/r permutation. Its trivial
counting bound reaches the target scale, so it needs signed cancellation.
Do not confuse it with either excluded p=r or q=r contraction.

Corpus basis: literal ChiPrimeGaussianCubicMain entry and mask; corpus
SecondDerivativeTest.second_derivative_test'; AlmostOrthogonality Schur;
ChiPhysicalMatrixMultiplier actual physicalLogWindowSchwartz, its finite
Fourier budget, and norm_schwartz_weighted_matrix_form_le. Research searches
allowed-collision-quadratic andcollision-quadratic-gram02az running before
any new Lean. Existing fixed root matrix is a DIFFERENT phase.

New paper proof mechanism avoids a prime-specific quadratic Vaughan bound:
build complete integer matrix K(p,r)=exp(2pi*i*p²/r) on[N,2N]. Prime masks
are coefficients, not deleted samples in a cancellation theorem. Correlation
of columns r!=s is a complete quadratic integer sum, curvature2|r-s|/(rs).
Choose lambda=|r-s|/(4N²), hgrow8. The corpus second-derivative bound gives
at most96N/sqrt|r-s|. Diagonal isN+1. Cauchy with the existing harmonic
separated-row bound gives Gram budget

 B_N=(N+1)+96N*sqrt(N+1)*sqrt(2*(1+log(N+1))).

Schur then gives matrix norm at mostsqrt(B_N)=O(N^(3/4)*log(N)^(1/4)).
No coefficient randomness or prime-distribution premise is used.

The actual W(p²/(rN)) weight is paid by the existing logarithmic Schwartz
multiplier, not bounded entry by entry. Since physicalLogWindow(logx)=
sqrt(x)*W(x), the original entry equals2pi*sqrtN times the weighted matrix
with c_p=1_prime*V(p/N)^2/p and d_r=1_prime*conj(V(r/N))/sqrt(r), and window
argument2logp-logr-logN. Their energy product isO(N^(-1/2)), cancelling
the outer sqrtN. Thus the whole p=q double sum isO(sqrt(B_N)). The p=r
all-equal diagonal removed from this double sum isO(1), so normalized norm
vanishes. Actual smooth edge masks can be included in these coefficients.

This would remove a genuine critical-size allowed source sector, not solve
the entire pairwise-distinct cubic or RH. The remaining joint signed real
carrier, growing moments/cofactors and common-height return stay open.
No conditional receiver theorem, new axiom or numerical experiment planned.

Scratch04 audit88851 terminal1: the complete quadratic correlation and Gram
row theorem now print only standard3. Matrix operator and weighted window
form elaborate. Remaining errors: cast/instance transport of scalar log
limit and missing open namespace for the actual height window. Physical
entry identity and final norm closure not yet audited. Fixed namespace and
explicit convert!-then-definitional equality; appended full sharp action,
actual coefficient norms, exact window/scalar identity, diagonal removal,
and final unconditional norm limit for the fifth audit. No productionleaf
or claimed collision closure yet. First three failures were derivative
instance/scalar normalization and elementary inequality rewrite issues;
no mathematical counterexample found.

Searchaudit: allowed-collision-quadratic02az partialdeadline,index1258549
coveragepending; all20candidate+20source inspected. Quadratic-gram02az
partialinterruptedretrieval,66969/66969indexed,noinventoryerrors,
index1258549coverage/current1258553,compilerpending/stale,refreshincomplete;
all20+20 andingredienttext inspected. Exact SecondDerivativeTest' found
and used directly; no prime-specific quadratic theorem was assumed.

Scratch07 audit91148 terminal0: all five checked declarations, including
exact physical entry and unconditional complete collision norm limit, use
only propext, Classical.choice, Quot.sound. The sixth audit exposed that
field_simp had already cancelled the common exponential and 2pi, so the
remaining square-root identity needed only its reduced coefficient. No
mathematical premise changed. Removed the final unnecessary sequence-focus
warning in the production copy. Leaf ChiCubicAllowedPrimeCollision created
and wired once; production and imported axiom audits pending.

Final audit closure03az: production81595 terminal0 empty PASS; imported
axiom54541 terminal0 all API2 standard3. Index16094 PASS/API2; umbrella wired
once, no umbrella build. Lint26717 terminal1 with367 warnings and two unrelated
unreachable modules (XiStripEdgeSquaredWeightSum, HalfShiftHarmonicEulerBound),
no owned finding. P2/P3 record the exact result and remaining hard frontier.
