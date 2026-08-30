# T1 minimum-log ordinary Abel transform

## Claim and RH proof chain

Route T1: smooth AFE / Barban--Vehov producer -> exact finite-head long-detector energy -> coefficient-faithful affine mean-square/core-current landing -> eventual bounded fixed critical half-density Weil-source pairing -> RH.

Exact burden attacked: determine the full leading term of the sole tuned minimum-log Gram remainder, hence the actual included long-detector energy at `L=N^100`, `M=N^49`, `lambda=1/log L`. This is the surviving analytic burden exposed by `DifferentiatedBarbanVehovTunedMinLogGram`.

## Frontier audit

- `[CORPUS]` `selbergOriginalTunedMinLogRemainder_eq_integral_totient_sq` gives an exact positive Gram integral, but no growth law.
- `[CORPUS]` `tendsto_selbergOriginalLogMonomial_div_log_pow` proves every ordinary positive-power Selberg monomial asymptotic.
- `[CORPUS]` `abs_levinsonCriticalDetectorLongEnergy_fortyNine_sub_polynomialMain_le` reduces the actual finite-head energy to its included polynomial main with vanishing error.
- `[LOCAL-RESEARCH]` the frontier map leaves detector-moving signed cancellation and coefficient-faithful landing open. It is read-only for this work.
- `[LITERATURE]` Graham/Jutila and modern Barban--Vehov work control ordinary logarithmic sieve quadratic forms. The checked primary literature does not state the detector-coupled minimum-log combination below, its ordinary Abel-transform identity, or its leading coefficient.

## Conjecture loop

1. `[FALSIFIED C1]` Reciprocal tuning makes the positive remainder lower order: `R(M)=o(log(M)^4)`.
   Killing mechanism: the exact ordinary Abel transform below has a strictly positive fourth-log beta moment `7/12`.
2. `[PAPER-PROVED C2]` Exact ordinary Abel transform:
   `R(M)=integral_0^H [L22(exp u)+2(H-u)L12(exp u)+(H-u)^2 L11(exp u)] du`, where `H=log M` and `Lij` is the real-cutoff original Selberg log monomial.
3. `[PAPER-PROVED C3]` Fourth-log law:
   `R(M)/log(M)^4 -> 7/12`.
   Ordinary coefficients `4/3,1,1` and beta moments `1/4,1/12,1/12` force `1/3+1/6+1/12=7/12`.
4. `[PAPER-PROVED C4]` Detector consequence at reciprocal forty-nine scale:
   the actual included long energy tends to `(1/12)*(49/100)^2`, exactly one eighth of the already-formal full-energy limit `(2/3)*(49/100)^2`.

## Hostile checks and open core

- Real cutoff must be treated coefficient-faithfully; replacing `exp u` by its floor without proving endpoint-shift control is invalid.
- The change of variables must retain both endpoints and interval orientation.
- No pointwise positivity may replace the signed ordinary monomial asymptotics.
- C3 needs a genuine Abelian convolution theorem with enough domination near `u=0` and `u=H`; fixed-ray convergence alone is insufficient.
- C4 must use the exact included polynomial and its already-proved approximation to actual energy; it may not substitute full energy or discard interference.

## Paper proof

Write `c(m,n)=mu(m)mu(n)gcd(m,n)/(mn)` and, for real `x>=1`,
`Lij(x)=sum_{m,n<=x} c(m,n) log(x/m)^i log(x/n)^j`.

1. In the Gram identity for `R(M)`, put `H=log M` and `Y=M exp(-t)`. A tent factor is zero unless `m<=Y`; on that support
   `log(M/m)(log(M/m)-t)=log(Y/m)^2+t log(Y/m)`.
   Expanding the square and substituting `u=H-t` gives C2 exactly. Equality at a moving endpoint causes no term because `log(Y/m)=0` there.
2. For `N=floor x` and `delta=log(x/N)`, binomial expansion expresses `Lij(x)` as `Lij(N)` plus terms carrying a positive power of `delta`. Gauss's identity gives
   `sum_{m,n<=N}|c(m,n)| <= sum_{d<=N} phi(d)/d^2 * H_(N/d)^2 <= H_N^3`.
   Hence every endpoint-shift error is bounded by a fixed polynomial in `1+log N` times `delta`. Since `delta<=1/N`, it is exponentially small for `x=exp u`. Therefore corpus's natural-cutoff laws transfer to
   `L11(exp u)/u -> 1`, `L12(exp u)/u^2 -> 1`, and `L22(exp u)/u^3 -> 4/3`.
3. If `F(u)/u^p -> c`, eventual convergence plus boundedness on compact intervals gives `|F(u)|<=C(1+u)^p`. Substitution `u=Hx` and dominated convergence prove
   `H^(-(p+q+1)) integral_0^H (H-u)^q F(u) du -> c integral_0^1 x^p(1-x)^q dx`.
   Apply this with `(F,p,q,c)=(L22,3,0,4/3),(L12,2,1,1),(L11,1,2,1)`. The three limits are `1/3`, `1/6`, and `1/12`, proving C3.
4. In the exact included polynomial, reciprocal forty-nine tuning has `rho=log M/log L=49/100`. Corpus's ordinary monomial limits give ordinary-sector limit `-rho^2/2`; C3 gives Gram contribution `7rho^2/12`. Their sum is `rho^2/12`. The corpus's vanishing included-polynomial approximation error transfers this limit to the actual finite-head long energy. The formal full-energy limit is `2rho^2/3`, so the ratio is exactly `1/8`.

Every step is unconditional. No prime-distribution hypothesis, RH consequence, numerical experiment, or unproved uniform moving-modulus estimate is used.

## Status

`[PAPER-PROVED]` Stage 2. Dependency-closed proof survives endpoint, sign, floor, domination, and scale audits. Exact Lean formalization of C2--C4 is next.
