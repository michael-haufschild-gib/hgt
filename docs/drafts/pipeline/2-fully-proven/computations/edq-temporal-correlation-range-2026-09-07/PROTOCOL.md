# EDQ full covariance: direct estimate and correlation-range discriminator

Stage: 1-in-progress. Primary target remains an unconditional proof or falsification of RH through EDQ.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.

## Hard target and work constraint

Prove an actual cofinal subpower ceiling in the preserved inner cutoff X for
the complete averaged current, or for a full compensated arithmetic energy
that supplies it. This card does not replace that target with another receiver.
The proposed additional Hardy-transfer module is not being written. Further
formal infrastructure must follow a successful attack on the missing bound,
not serve as the main output while that bound remains untouched.

## Direct proof attempt: Graham followed by Cauchy

Use the actual error increments c(k)=[k=1]-g(k)+H, with
g(k)=(b_M(k)-b_X(k))/(log M-log X). Their cumulative sum is the literal
target error. Cauchy gives

`E_T <= sum_(j<=T)c(j)^2 * sum_(n=j..T)1/(n+1)`.

Thus even a mean-square bound `sum_(j<=t)c(j)^2<=A*t+B` supplies a term of
order A*T after summation, as well as a boundary/error cost. The simpler
bound by `(1+log(T+1))*sum_(j<=T)c(j)^2` already makes the loss explicit.
For T>=M the inspected Graham theorem supplies
`sum g(k)^2 <= 2*(B(M,T)+B(X,T))/L^2`, with
`B(Y,T)=4*C^2*T*(1+log Y)+(Y*log Y)^2` and L=log M-log X.
Including the actual compensation gives
`sum c(k)^2 <= 3+3*T*H^2+3*sum g(k)^2`.
The complete tail also retains its bound `(M+1)^2/(T+1)`.
These estimates do not yield the required subpower inner-scale ceiling.
The failed step is replacing the signed cumulative correlations by individual
squares. This rejects this direct estimate as a proof, not the arithmetic
source, Graham's theorem, or the possibility of a stronger use of it.

## Frozen experiment: where does the cancellation occur?

Question: can temporal correlations of range at most sqrt(X) approximate the
actual finite compensated covariance, or does even range X miss substantial
signed mass? This tests whether short-interval estimates are a plausible next
producer. Earlier experiments measured full error and cutoff-averaging gains;
they did not measure the correlation range.

For X=2^k, k=10,...,16, use T=256X and two actual sources: raw cutoff X,
and the logarithmic average over [X,4X). Keep their literal compensators.
Let c denote their full error increments and S their cumulative sums.
The exact finite energy is
`E=sum_(n<=T) S(n)^2/[n(n+1)]`.
For each range h, record the signed band covariance
`D+2*sum_(k<=T)c(k)*(1/k-1/(T+1))*sum_(max(1,k-h)<=j<k)c(j)`,
where `D=sum_(k<=T)c(k)^2*(1/k-1/(T+1))`.
Ranges: 1, floor(sqrt(X)), X/16, X/4, X, 4X, 16X, 64X, T.
Also record the signed omitted covariance and its absolute size divided by E.
The band-restricted kernel need not be positive: negative values must be
reported as signed covariances, never called negative physical energy.

Predeclared primary classification uses only the averaged source, evaluated in the listed order:

- Local: all seven relative discrepancies at h=floor(sqrt(X)) are <=1/4.
- Nonlocal: at least four relative discrepancies at h=X exceed 1.
- Otherwise: mixed.

No threshold or range will change after data. This finite comparison does not
prove a uniform asymptotic estimate or a full-tail bound. It can change which
correlation estimate is worth attempting next.

## Validation and execution controls

Run only on the authorized RunPod, seven independent scale workers, BLAS
threads one, and a 180-second external deadline. Validate Möbius values against
direct factorization; averaged coefficients against suffix sums of the actual
cutoff probability; fixed coordinates against direct divisor/floor sums;
initial prefix identities; and the full h=T covariance against E computed
independently from cumulative errors. Download the script, protocol, complete
results, log, report and hashes to the computations directory. No numerical
result enters Lean. No experiment has yet been executed for this question.
