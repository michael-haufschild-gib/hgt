# Logarithmic phase blocks: numerical findings

These are exploratory evaluations, not interval certificates or Lean premises. Placement in the computations directory does not certify the tested conjectures.

## Questions and definitions

For `b(x)=(fract(x)^2-fract(x))/2`, `s=sigma+i*t`, `u=conjugate(s)`, integer `n>=1`, and `a_k=n*exp(2*pi*k/t)`, evaluate

`B_k=Im[n^(-s)*integral_(a_k..a_(k+1)) b(x)x^(-u-2) dx]`

and `P_K=sum_(k<K)B_k`. Every recorded number is multiplied by the positive factor `n^(2*sigma+2)`. The conjectures were frozen in [the research card](../../../1-in-progress/arithmetic-log-phase-blocks.md) before each scan.

## Results

The main scan has 64 parameter triples and 504 complete turns: `sigma={0.05,0.5,2,8}`, `n={1,4,16,64}`, `t/(2*pi*n)={0.3,0.7,0.95,0.9999}`. Up to eight turns were tested, with `log(a_K/n)<=20`.

- **43 individual turns were positive**, in 21 parameter triples. Thus B1 has strong numerical counterevidence even strictly below the proposed threshold.
- **All 504 cumulative prefixes were negative.** B2 survives this scan; it remains unproved.
- Example: `sigma=0.05`, `n=16`, ratio `0.7`, second turn `k=1`: normalized `B_1=+0.00896930216808625646616752164325`. Its prefix remains negative: normalized `P_2=-0.0106569736460393874263396891297`.

A separate finite-cell scan tested 882 prefixes: `sigma={-1,-0.5,0,0.001,0.5,8}`, `n={1,16,256,4096}`, ratios `{0.25,0.5,0.75,0.99,0.9999}`, first through eighth turns. Prefixes crossing more than 3,000 integer cells were omitted explicitly by the script, leaving 147 evaluations per real part. **All 882 were negative.** Of these, 441 have `sigma>0` and test B2; the `sigma=-1` cases test the separately frozen undamped clock conjecture C. These are not zero-selected data.

Near an arithmetic coincidence, `sigma=-1`, `n=4096`, ratio `0.5`, `K=1` gives normalized prefix `-0.00000738870395901927843539171793820`. Small margins near these endpoints require care; no positive uniform margin was inferred.

## Methods and verification

`scan.py` evaluates real-cutoff tails using Hurwitz zeta at the next integer plus the exact polynomial-power primitive on the remaining cell. Precision grows from 100 decimal digits with real part and endpoint size. An initial accelerated integer-sum run terminated with `BrokenProcessPool` before producing results. Its worker termination was not diagnosed. The successful script disables that accelerator and uses mpmath's direct finite-sum fallback; no installed library file was changed.

`boundary.py` uses only finite-cell polynomial-power primitives at 110 digits, with no infinite-tail evaluation. Its x-integrand after positive normalization is

`b(x)*(n/x)^(sigma+2)*sin(t*log(x/n))`.

`verify.py` independently integrates that real integrand, splitting at every integer, at 150 digits for eight selected blocks/prefixes. Differences from the Hurwitz-tail method are below `9e-144`. `verify_boundary.py` independently checks four small-margin or undamped boundary cases at 150 digits; differences from finite primitives are below `4e-144`. These comparisons check numerical consistency, not certified errors or every recorded sign.

All numerical work ran on the authorized Runpod in `/root/rh-log-phase-blocks-20260906`, with Python 3.8.10 and mpmath 1.3.0, up to eight worker processes, and BLAS/OpenMP threads limited to one per worker. Scripts and every result table are retained here: `results.json`, `verification.json`, `boundary.json`, and `boundary-verification.json`.

## Mathematical consequence and remaining gap

Positive turns can coexist with negative prefixes. This suggested a separately proved constant-speed model: for `0<lambda<2*pi`, every prefix of `b(x)sin(lambda*x)` is nonpositive. At complete turns, it is zero exactly at integer endpoints. The second turn at `lambda=4*pi/3` is positive. These symbolic theorems are formalized in `ArithmeticLinearPhasePrefix`; they do not depend on this data.

Neither the constant-speed proof nor these computations establish the logarithmic prefix law B2, the clock law C, the whole-tail conjecture R, or the sign at the exceptional unit head required for RH. The phase change and its arithmetic endpoint effects remain the mathematical issue.
