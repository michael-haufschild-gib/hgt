# Natural-aperture exact realization: paper proof

Status: dependency-closed paper proof; complete Lean scratch and three-capstone axiom audits passed. Final installed leaf audit passed without warnings. The exact statement strengthens the earlier constant-K bound.

There is a fixed real C such that for every epsilon>0 and every sufficiently large integer N, there is a finite nonnegative mixture of actual complex C2 polar tests, each at aperture at most (log N)/2+C, whose complete integer atom trace is exactly exposingWeightTrunc N with multiplier t=1 and whose total archimedean energy is at most E+(1+epsilon)*tau_N. Constants C and the source construction do not depend on epsilon; the sufficient lower bound on N may depend on epsilon.

Here E=archimedeanExposingThreshold and tau_N=exposingTail N. This is an existential UPPER bound. It is not the universal lower inequality required by WP02.

## Fixed constants and source

Let rho=exposingWeightDecayRate>0 and choose r=rho+1. The proved eventual coefficient lower bound supplies D>0 and n0 with w(n)>=D exp(-r n) for n>=n0. Since boxConst>=0, for N>=max(n0,2), the (N+1)-st term alone gives

tau_N >= d exp(-r N), d=(log 2)*D*exp(-r)>0.

This uses nonnegativity and summability of the literal box majorant, and eventual strict positivity of w; no estimate of numerical constants.

Choose s>r with s>1, set B=1+(log s)/2, and let L_N=(log N)/2+B. Then exp(2(L_N-1))=sN exactly, so q(L_N)=exp(-sN). In particular q(L_N)/tau_N<=(1/d)exp(-(s-r)N), which tends to zero.

Let c_k=1/(k+1) and f_k=P_{c_k}(Phi*chi_L). Each f_k is smooth, has the exact two pole zeros, and is supported in [-L-1,L+1] for L>=0. For a finite J, assign alpha_k=2^(-k)/(2*pi), k<J. Its normalized trace is

v_{J,L}(n)=sum_{k<J} 2^(-k) atomCoeff(f_k,n).

All terms outside M=floor(exp(2(L+1))) vanish exactly by compact support. For the above B>1, M>=N.

## Uniform full trace error

The polar autocorrelation theorem and the identity between real-test autocorrelation and atomCoeff give, for n>=2,

|atomCoeff(f_k,n)-[K_{c_k}(log n)+K_{c_k}(-log n)]| <= 2 C_corr q(L)/n^2,

uniformly in k. Summing k<J uses sum 2^(-k)<=2. The existing literal exposing-kernel envelope |K_{c_k}(y)|<=D0 exp(-2|y|) bounds the omitted geometric tail by 4 D0*2^(-J)/n^2. Thus

|v_{J,L}(n)-w(n)| <= (4 C_corr q(L)+4 D0*2^(-J))/n^2.

The box-weighted majorant S=sum_{n>=2}(log n+boxConst)/n^2 is finite. For instance use the existing summability theorem for (2 log n+boxConst)/n^2 and comparison; all terms are nonnegative. Hence every finite sum of weighted trace errors is <= S(4 C_corr q(L)+4 D0*2^(-J)). This covers all residual integer coefficients, not a selected prime subset.

## Uniform energy error

The uniform energy theorem gives

|archEnergy(f_k)/(2*pi)-atomPairing(Lambda,K_{c_k})| <= C_energy q(L)

for all large L, uniformly in k. The existing polar exposing-kernel envelope and summability of Lambda(n)/n^2 uniformly bound the absolute limiting pairing by H=2 D0 sum_n Lambda(n)/n^2. Therefore the finite source mixture has total energy at most

E+2 C_energy q(L)+2 H*2^(-J).

This uses the existing identity expressing E as the infinite geometrically weighted sum of the limiting pairings. No sign of any individual energy is assumed.

## Exact repair and aperture

For each n in [2,M], put r_n=w_N(n)-v_{J,L}(n). Choose sigma_n=1 if r_n>=0 and -1 otherwise. Add twoPointResonator(n,sigma_n) with nonnegative coefficient |r_n|/(4*pi*resonatorMass(n)). Its normalized atom vector is exactly r_n at n and zero at every other integer m>=2. Its energy is at most (log n+boxConst)|r_n|. The repair test aperture is at most (L+1)+1=L+2 by the existing atomLevel bound. The source tests have aperture L+1, so the entire finite disjoint-union family lies at aperture L+2=(log N)/2+(B+2).

For n<=N, |r_n|=|w(n)-v(n)|. For N<n<=M, |r_n|=|v(n)|<=|w(n)|+|v(n)-w(n)|. Consequently total repair energy is at most

tau_N+S(4 C_corr q(L)+4 D0*2^(-J)).

Exact matching holds at ALL integers: inside [2,M] by one-atom cancellation, outside it both source trace and target vanish. The coefficient sum is finite, nonnegative, and no cross terms occur because this is a mixture, not a sum of tests inside one quadratic form.

## Choosing the finite shift cutoff

For each large N choose finite J with 2^(-J)<=q(L_N), using convergence of the geometric sequence. The preceding source and repair estimates give

energy <= E+tau_N+K q(L_N)

for one fixed K>=0. Since q(L_N)/tau_N tends to zero, for each epsilon>0 choose N large enough that K q(L_N)<=epsilon*tau_N, L_N is in the uniform-energy range, and the coefficient lower bound holds. This proves the exact stated theorem with C=B+2.

## Attack and remaining work

Verdict BRIDGE. Exact source construction and its natural aperture/tail rate survive the paper attack. Generic duality gives only unquantified approximate feasibility; it does not provide this rate. Scientific novelty beyond this literal corpus construction remains unestablished. This result cannot exclude a different matched family with lower energy, including a negative multiplier-zero family. No RH proof follows from this upper construction. Next formalization must preserve every normalization, every integer coefficient, and the uniform aperture bound.
