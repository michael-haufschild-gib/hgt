# Finite prime-sieve phases: numerical rejection of two sign laws

These are exploratory numerical results, not interval certificates or Lean proofs. Their location under `computations` does not make the numerical conclusions formal theorems. All mathematical evaluation ran on the specified Runpod; results were downloaded here. No output is used as a Lean proof input.

## Question and definitions

With `u=conjugate(s)`, `D=u(u+1)`, define the ordinary remainder

`R_s(n)=sum_(1<=j<=n)j^(-s)-zeta(s)-n^(1-s)/(1-s)-n^(-s)/2`.

Let `W_d=d^(1-s)sum_(n>=1)n^(-s)conjugate(R_s(dn))`. For the product `M_k` of the first `k` primes (`M_0=1`), evaluate

`U_k=sum_(d|M_k)mu(d)W_d/(dD)=sum_(n>=1,gcd(n,M_k)=1)n^(-s)conjugate(R_s(n))/D`.

Frozen conjecture J asserted `Im(U_k)<=0` for every cutoff at every positive-height strip zero. Frozen conjecture K asserted that every prime-insertion step increases or preserves `Im(U_k)`. The unknown small-index signs, which are not determined by the established asymptotic coefficient, motivated the experiment.

## Method

`scan.py` evaluates 96 critical-line zero approximations and horizontal nonzero controls at real parts 0.45 and 0.55, through the first ten primes (ending at 29). Eight worker processes each use one BLAS thread. Zero ordinates are calculated at 55 digits; the main scan uses complex float64 sums. Two configurations use direct heads `ceil(4|t|)+512` and `ceil(7|t|)+512`, with 8 and 12 Euler–Maclaurin terms respectively. Tail coefficients are summed over rough integers using finite divisor inclusion-exclusion and Hurwitz tails starting beyond the head. This avoids subtraction of nearly equal full zeta and head values at large exponents.

`verify.py` independently evaluates three selected violations at 90 digits, on three workers, using the finite divisor formula. Each `W_d` uses Hurwitz evaluation of the ordinary remainder and a tail expansion. Configurations use head factors 4 and 7 with 16 and 24 correction terms. Both configurations check each reported starting phase; the next phase in the K example uses the second configuration. Runtime/library metadata and complete outputs are in the accompanying JSON files.

## Results

Among 1,056 zero/cutoff pairs, 213 had imaginary phase above `1e-9`. Among 960 insertion steps, 341 decreased by more than `1e-9`. The two scan configurations differed by at most `7.81e-17` on the critical-line sample.

| Independent verification | Result |
|---|---:|
| Ninth zero, no primes removed: `Im(U_0)` | `+0.00040293988155473538625` |
| Nineteenth zero, prime 2 removed: `Im(U_1)` | `+0.00012646848923231505577` |
| Fourth zero, inserting prime 3 after 2: `Im(U_2-U_1)` | `-0.00036887122296423429497` |

The starting-phase configuration differences were between `1.50e-52` and `4.19e-50`; evaluated zeta residuals were below `2.06e-90`. Agreement is a stability check, not a proved error bound or a proof of existence of an exact zero in a certified interval.

All 96 sampled phases were negative after removing primes through 29. This does **not** establish a universal cutoff of 29, an all-height sign theorem, or RH.

## Interpretation

J and K are numerically rejected in their frozen all-cutoff forms, including for nonempty prime prefixes. These results cannot support a formal impossibility theorem about every possible arithmetic identity.

The surviving paper mechanism concerns sufficiently late cutoffs. The actual normalized summand times `n^(2 Re(s)+1)` tends to `-1/[12(conjugate(s)+1)]`, with negative imaginary part whenever `Re(s)>0` and `Im(s)>0`. Removing the finite exceptional head therefore leaves a negative imaginary tail. Subsequent prime deletion increases the phase strictly toward the unit-term limit. This mechanism does not need a zero equation and supplies no sign bound on the limit itself. It must not be presented as a recovered proof of J, K, or RH.

Reproduction on Runpod: run `python3 scan.py`, then `python3 verify.py` in one directory. The scripts enforce one BLAS thread per worker. No exploratory mathematical computation was run locally.
