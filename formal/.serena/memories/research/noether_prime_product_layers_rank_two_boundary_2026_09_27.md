# Product layers, rank-two boundary, and Euler curvature of the actual deficit (2026-09-27)

## Goal status
RH is NOT proved or falsified. Full signed square-root bound for D remains unproved. Goal remains active. Previous turn was progress (44 checked theorems); this turn adds 5 modules / 26 public theorems, all checked. Difficulty is not a blocker and no narrowed success condition was substituted.

Repo /Users/michael/Documents/code/hgt/formal. Earlier state in research/noether_prime_pair_flux_and_diagonal_control_2026_09_27 and research/noether_prime_deficit_critical_work_and_scale_descent_2026_09_27.
Use corpus search formal_tools.py research plus direct Lean; no cards. No subagents/commits. One own foreground Lean process at a time, lake --old env lean leaf audits, no full/umbrella builds.

D(T)=ccmLogChebyshevDeficitPrimitive T.
E(T)=exp(-T)D(T)^2.
N=floor(exp T).
S(T)=ccmPrimeEntryPrefix N T.
P(T)=psi(exp T).
Earlier exact centered energy: integral E=B-2M+Pair, with B=expT-exp(-T)-2T and M=ccmPrimeEntryBackgroundPrefix T N.
Earlier Diag<=T^2+78T+50, and integral E=Diag+CenteredOff. Fixed upper budget for CenteredOff is still unproved.

## Five new modules

### CCMPrimeEntryProductKernel.lean — 7 theorems
Exact reconstructed ratio kernel:
ccmPrimeEntryProductKernel T R s =
 K_T((log R+s)/2,(log R-s)/2).
No artificial cutoff is postulated; the original finite integral enforces it.
- K_T(a,b)=0 if T>=0 and either a>=T or b>=T.
- Product kernel even, nonnegative for T>=0.
- For positive naturals n,m:
 W(T,nm,log n-log m)=K_T(log n,log m).
- W(T,R,s)=0 when T>=0 and |s|>=2T-log R, including equality.
- For R>0 and |s|<=2T-log R:
 W=exp(-logR/2)*ratioKernel(s)
   -exp(-T)*[(T-logR/2)^2-s^2/4+2(T-logR/2)+2].
This preserves the product-dependent ratio aperture AND the finite boundary correction.

### CCMPrimeEntryProductLocalization.lean — 3 theorems
Private exact finite-square regrouping by product uses Finset.sum_fiberwise_of_maps_to.
For T>=0:
 Pair(T,N)=sum_{1<=R<=N*N} localizedVonMangoldtPair (W(T,R)) R.
The explicit square-cutoff indicator disappears because W vanishes if either factor exceeds N.
Full energy equals B-2M plus this complete product-layer sum.
For distinct primes p,q, positive exponents a,b:
 localizedPair W (p^a*q^b)
 =2 log p log q * W(a log p-b log q).
Thus the two orientations reinforce, not cancel.

### CCMPrimeEntryPairBoundary.lean — 3 theorems
ccmPrimeEntryPairLimit N =double sum Lambda(n)Lambda(m)K_infinity(log n,log m).
ccmPrimeEntryPairBoundary T =
 exp(-T)*[(S(T)+P(T))^2+P(T)^2].
Boundary nonnegative for every real T.
EXACT for every real T:
 Pair(T,N)=PairLimit(N)-Boundary(T).
The entire omitted tail is a sum of squares of TWO terminal arithmetic charges.
Underlying rank-two identity:
 (T-a)(T-b)+2T-a-b+2=(T-a+1)(T-b+1)+1.
For T>=0:
 integral E=B-2M+PairLimit-Boundary.
Dropping Boundary is not justified.

### CCMPrimeEntryBoundaryScale.lean — 6 theorems
All unconditional from PNT and earlier D/exp ->0:
- exp(-T)*S(T)->1.
- exp(-T)*integral_0^T E ->0.
- exp(-T)*Boundary(T)->5.
Define UncorrectedEnergy=B-2M+PairLimit (the proposed shortcut replacing finite overlap by infinite overlap).
- UncorrectedEnergy=integral E+Boundary for T>=0.
- exp(-T)*UncorrectedEnergy->5.
- Eventually exp(T)<=UncorrectedEnergy.
This rigorously REFUTES the shortcut: it inserts a spurious 5 exp(T) growth term into the actual arithmetic source, independently of RH.
Finite Pair/exp ->1 and PairLimit/exp ->6 are plausible follow-ons but NOT formalized here. Do not report them as proved.

### CCMPrimeEntryEulerCurvature.lean — 7 theorems
Imports actual LocalizedHalfDensityGerm, whose halfDensityCoeff sigma * halfDensityCoeff(-sigma)=1 is already proved.
Define
 Curv(T,R)=Re[(1/2)*iteratedDeriv 2 (halfDensityFibre (W(T,R)) R) 0].
For R !=0:
 Curv(T,R)=localizedPair(W(T,R),R)
   -(Lambda*Lambda)(R)*K_T(log R,0).
Every Curv(T,R)>=0 for T>=0, R!=0.
Key unconditional overlap inequality:
 K_T(a+b,0)<=K_T(a,b), for a,b,T>=0.
Proof is pointwise tent inequality, using (t-a)(t-b)-t(t-a-b)=ab when t>=a+b.
Also K_T(a,b)>0 if 0<=max(a,b)<T.
For ANY distinct primes p,q:
 Curv(log(pq),pq)>0.
At that time the endpoint K_T(log(pq),0)=0 but both prime-entry tents have a strictly positive overlap. This disproves the candidate that the exact Euler inverse law annihilates localized curvature.
Exact full pair:
 Pair(T,N)=sum_{R<=N*N}[Curv(T,R)+(Lambda*Lambda)(R)*K_T(log R,0)].
Exact full centered E integral has B-2M plus that sum.

## What was learned / remaining actual estimate
- The old constant-weight inverse charge does not survive localization as zero work. The newly formalized actual two-prime source has strict positive curvature.
- Positivity of Curv provides a LOWER estimate. It cannot be advertised as the missing upper bound.
- The exact rank-two boundary counterterm must stay: omitting it causes a provable 5 exp(T) error.
- Product-only untruncated Selberg convolution estimates lose the ratio aperture, also essential.
- The next target is an ACTUAL upper estimate for
 B(T)-2M(T)+sum_R[Curv(T,R)+(Lambda*Lambda)(R)*K_T(logR,0)]-Diag(T),
 i.e. the unchanged CenteredOff(T). No conjectural upper estimate was assumed/proved.
- Polynomial integrated E could feed Laplace continuation; that receiver for this D still not formalized in these batches. Do not substitute a conditional criterion for proving the arithmetic estimate.

Possible later direction (unimplemented):
Construct chronological signed-work identity for the normalized two-state residual r=exp(-t/2)D, q=exp(-t/2)(exp t-psi(exp t)).
Storage L=(r+q)^2+q^2 has between-prime derivative -r^2+2exp(t/2)(r+2q), and a prime jump q->q-Lambda(n)/sqrt(n) contributes -2lambda(r+2q^-)+2lambda^2.
This suggests an exact diagonal variance budget 2*sum Lambda(n)^2/n plus explicit compensated signed work. It is NOT yet a proved upper bound; generic passivity only gives a lower work estimate.

## Validation / cleanup
All 5 new leaf modules audited with plain lake --old env lean FILE -o matching .olean; fresh objects verified. All 26 public theorem axiom reports standard propext, Classical.choice, Quot.sound only. No sorry/new axioms/native_decide/#eval/heartbeat changes. No numerical experiments. All five imported exactly once into RHTower.lean. No umbrella/full builds.
Scratch axiom importers and logs removed. No live own Lean/index processes remain at batch end.
git diff --check for umbrella passed.
Index refreshed after final additions, exit0.
Last global lint FAILED on unrelated concurrent work:
unwired MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, RiemannKernelWeilRadical, SelbergCuspMellinResidues, SelbergStripPolynomialGrowth, SelbergThetaMellinBarnes, XiGaussianPolarAnnihilator, XiGaussianPolarSourceCancellation, ZetaZeroDensityPowerSaving, HTGeometry.FinitePoleVerticalContourShift, HTGeometry.GammaHalfIntegerLineBound.
Also unrelated temporary sorry in SelbergCuspMellinResidues.lean:187 (ExtendedSelbergClass.analyticOnNhd_cuspPolarPart), plus generated metadata races. The index was regenerated AFTER that lint. Do not claim global lint passed; preserve other agents' work.

## Lean details
- In finite product reindexing, simp only [S,...] where S is a let-bound Finset product reduced membership to Quot.lift and prevented mem_product rewriting. Keep S abstract and use Finset.mem_product.mp/mpr explicitly after mem_filter.
- Product layer log reconstruction uses Nat.cast_mul then Real.log_mul.
- No identifier add_neg_eq_sub here: use sub_eq_add_neg, neg_neg.
- Pair boundary summation factors through sum Lambda(n)*(T-logn+1) and sum Lambda(n), so sum of squares is simpler than four separately expanded mixed sums.
