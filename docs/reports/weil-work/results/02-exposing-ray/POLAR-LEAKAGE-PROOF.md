# Far polar correction: pointwise-small trace, divergent repair budget

Status: dependency-closed paper proof and complete Lean formalization; final leaf and standard-axiom audits passed. This tests a concrete source mechanism, not the full opposite-ray conjecture.

## Statement

Use the corpus's actual flat-top Fejer test psi, supported in [-17/50,17/50], its autocorrelation R, and its far polar correction

f_X(u)=psi(u)-c_X(psi(u-X)+psi(u+X))/2, c_X=1/cosh(X/2).

Set M_X=floor(exp(2(X+17/50))) and

B_X=sum_{2<=n<=M_X}(log n+boxConst)*|atomCoeff(f_X,n)|.

For X>=4,

X exp(X)/32 <= B_X <= 6 exp(1)(3+boxConst) X exp(X).

Nevertheless the complete atom trace tends uniformly to zero, and the actual polar archimedean energy stays strictly negative for all sufficiently large X. Thus pointwise or uniform convergence of integer traces is inadequate for the existing independent-atom repair construction: its weighted absolute-error budget diverges at the sharp scale X exp(X).

This is a statement about that repair budget, NOT a lower bound for the energy of every possible coherent repair. Opposite-ray production remains open.

## Exact trace and elementary estimates

The existing cosine-moment identity and Plancherel cosine identity give, for n>=2,

a_X(n)=c_X^2 R(log n-2X)/2-2c_X R(log n-X).

The corpus proves 0<=R<=1, R(y)=0 for |y|>=17/25, R(0)>=323/500, and R(0)-R(y)<=y for y>=0. In particular R(y)>=1/4 for 0<=y<=1/4. Also

exp(-X/2)<=c_X<=2exp(-X/2) (X>=0).

Hence |a_X(n)|<=2c_X+c_X^2/2 uniformly. The right side tends to zero. The existing energy estimate is E(f_X)<=E(psi)+(2c_X+c_X^2)Eabs(psi), with E(psi)<0; its error tends to zero. All these are estimates for actual complex C2 polar tests with aperture X+17/50.

## Lower budget

Put t=exp(2X), and take integers in Ioc(floor t,floor(5t/4)). Their number is at least t/4-1>=t/8, since X>=4 gives t>=9 via exp(2X)>=1+2X. Each satisfies

2X<log n<=2X+1/4,

using 5/4<=exp(1/4), and lies below M_X. On this window R(log n-X)=0, while R(log n-2X)>=1/4. Thus a_X(n)>=exp(-X)/8. Since log n+boxConst>=2X, summing gives

B_X >= (t/8)(2X)(exp(-X)/8)=X exp(X)/32.

All omitted terms are nonnegative. No sampling or replacement of the full trace is used.

## Upper budget

For every Y>=0 and every finite cutoff M,

sum_{n=2}^M (log n+boxConst) R(log n-Y)
 <= (Y+1+boxConst) exp(Y+1).

Indeed a nonzero summand has log n<Y+17/25<Y+1, hence n<=floor(exp(Y+1)); there are at most exp(Y+1) such integers, R<=1, and each weight is at most Y+1+boxConst. The exact trace identity and triangle inequality therefore give, writing H=2X+1+boxConst,

B_X <= 4 exp(-X/2) H exp(X+1)+2 exp(-X) H exp(2X+1)
 <=6 exp(1) H exp(X)
 <=6 exp(1)(3+boxConst) X exp(X).

## Novelty and attack audit

The far polar source, negative limiting energy, exact two-window trace formula, and sparse-weight obstruction are already formalized in `WeilPositivitySparseWeightsObstruction`. Those are reused, not claimed as new. New candidate is the sharp scale of the literal full box-repair budget, including the dominant second window near exp(2X). The first window alone only costs O(X exp(X/2)); discarding the second window misses the obstruction.

This is an analytic route diagnostic, not scientific novelty established against all literature. Internal search results and the external comparison are recorded in EVIDENCE.md. No computations or numerical tests were used.

## Literal exposing targets

Let K=sum_n exposingMajorant(n), finite by the existing summability theorem, and sum the complete matching error up to max(N,M_X). The triangle inequality gives

sum(log n+boxConst)|2*pi*a_X(n)-exposingWeightTrunc(N,n)|
 >=2*pi*B_X-K >=pi*X*exp(X)/16-K,

uniformly in N. Thus selecting a faster or slower exposing cutoff cannot rescue this particular independent-atom repair strategy. Proof uses the complete source trace and the exact existing exposing weights; the target's weighted norm is at most K.
