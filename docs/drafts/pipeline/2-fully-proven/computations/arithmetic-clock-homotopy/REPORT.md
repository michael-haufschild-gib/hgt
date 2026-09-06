# Arithmetic clock transfer: diagnostic results

These are exploratory numerical results, not proofs. Their location in the computations directory does not certify their signs. No output is used in Lean. The [research card](../../../1-in-progress/arithmetic-clock-homotopy.md) contains the frozen conjectures and their role in the RH dependency chain.

## Question and definitions

For `b(y)=(fract(y)^2-fract(y))/2` and `q_h(v)=(exp(h*v)-1)/h`, evaluate

`F(h,lambda,V)=integral_(0..V)b(q_h(v))*sin(lambda*v) dv`

at complete turns `V=2*pi*K/lambda`. D1 predicts nonpositivity for `0<h<=1` and `0<lambda<2*pi`; Dall predicts it for every `h>0`. When `h=1/n`, integer n, D1 specializes to the arithmetic logarithmic-clock conjecture C by an exact change of variables. Neither conjecture is an RH proof: the independent constraint at the unit remainder remains missing.

A separate test examines the stronger layer conjecture E:

`integral_(0..V)1_[delta<=fract(n*exp(v))<=1-delta]*sin(t*v) dv >= 0`

for `n>=1`, `0<t<2*pi*n`, `0<=delta<1/2`. Integrating these indicators with weight `1/2-delta` recovers `-b`. E was frozen before the scan; it does not replace C.

## Outcome

| Diagnostic | Evaluations | Outcome |
|---|---:|---|
| Initial clock grid | 96 | Every evaluated prefix negative |
| Additional nonreciprocal scales in `(0,1)` | 48 | Every evaluated prefix negative |
| Combined D1 range | 108 | No positive value |
| Fast clocks `h=16,64,256,1024` | 8 | Seven positive, one negative |
| Layer grid | 290 of 320 planned | 232 nonzero-layer tests with no negative value; 58 zero-layer controls |

Initial scales were `{.01,.1,.25,.5,1,2,4,8}`, ratios `lambda/(2*pi)` were `{.25,.5,.75,.99}`, and K was `{1,2,4}`. Additional scales were `{.37,.63,.83,.97}` at the same ratios and K. Fast clocks used ratios `{.5,.99}` and K=1. At h=16 the ratio .5 was negative and .99 positive; the other six fast-clock values were positive.

The layer grid used `n={1,4,16,128}`, ratios `t/(2*pi*n)={.25,.5,.75,.99}`, `delta={0,.05,.25,.45,.499}`, and `K={1,2,4,8}`. Thirty cases exceeded the 3,000-cell cap and were explicitly skipped. Delta=0 supplies an exact-zero control at complete turns. The numerical negative threshold was `-1e-70`, at 100 decimal digits. This finite grid supplies no uniform bound or exhaustive coverage of E.

Independent checks of fast-clock positives used 512 explicit cells and a bound on the remaining centered quadratic:

| h | ratio | Finite cells plus exact remaining mean | Analytic truncation bound |
|---:|---:|---:|---:|
| 16 | .99 | `1.22323325656e-5` | `5.27104862852e-6` |
| 64 | .5 | `5.86029108649e-5` | `1.27229244917e-6` |
| 1024 | .5 | `1.96994638947e-6` | `7.94728951249e-8` |

Each displayed center exceeds its truncation bound. These are **not certified interval enclosures**: floating-point roundoff was not enclosed. They are strong independently checked counterevidence to Dall, not a Lean refutation. D1, C, and E remain open.

## Methods and reproducibility

All mathematical computations ran on the authorized Runpod, in `/root/rh-clock-homotopy-20260906`, using Python 3.8.10 and mpmath 1.3.0. The scripts use process pools with at most eight workers and set OpenMP, OpenBLAS, and MKL to one thread. The verification script uses six workers. Scripts and complete results were downloaded here. All owned Runpod jobs completed; the final process check found none still running.

Write `a=1/h`, `t=lambda/h`, and `x=a*exp(h*v)`. The transformed integrand is

`a*b(x-a)*sin(t*log(x/a))/x`.

The shift by a is essential when a is not integer. Each cell `[a+m,a+m+1]` has an elementary polynomial-power primitive. The broad scan uses its endpoint differences and a shifted Hurwitz representation evaluated directly by Euler--Maclaurin. It explicitly bypasses the zeta finite-sum accelerator and does not use a reflection formula. At `u=-1-i*t`, individual infinite quadratic integrals do not converge; the endpoint expression is a regularized representation of the **finite difference**, not a claimed convergent tail. Precision grows with endpoint size.

For enormous complete-turn endpoints, `extend.py` keeps the quadratic's mean explicitly and uses its centered periodic primitive to bound the endpoint error. `verify.py` makes no Hurwitz-zeta calls: it sums 512 explicit cells and completes the mean contribution to the requested endpoint. For the centered part,

`P(r)=r*(1-r)*(1-2*r)/12`, `|P(r)|<=1/48`, and `P'=b+1/12` within each cell.

Integration by parts bounds the remaining contribution after `X=a+512` by `a*(1+abs(1-i*t))/(48*X)`. This bound covers the requested finite endpoint. The JSON fields `lower` and `upper` subtract/add this analytic truncation bound only; they do not include certified rounding errors.

Three smaller cases (`h=.37, ratio=.99`; `h=.83, ratio=.5`; `h=1, ratio=.99`) were independently evaluated by both finite-cell primitives and direct cellwise quadrature at 150 digits. Differences were at most `1.06e-150`. Comparisons with the stored broad-scan results differed by at most `1.22e-83`, consistent with their stored precision. This checks selected implementations, not every numerical sign.

`layers.py` sums cosine differences at the exact layer endpoints, at 100 digits. No separate quadrature validation of the full layer grid is claimed.

Files:

- `scan.py`, `results.json`: initial clock grid.
- `extend.py`, `extended.json`: additional and fast scales.
- `layers.py`, `layers.json`: layer tests and skips.
- `verify.py`, `verification.json`: independent finite-cell checks.
- `audit.json`: counts and selected method comparisons.

Run the scripts in this order on Runpod with `python3 scan.py`, `python3 extend.py`, `python3 layers.py`, and `python3 verify.py`. The extension imports the scan helpers. The initially attempted context-method call for the direct Hurwitz evaluator was unavailable in this mpmath version; the saved implementation imports the module function `_hurwitz_em` explicitly. All listed data come from completed runs of the corrected scripts.

## Consequences for the proof search

Unrestricted acceleration is not supported by the arithmetic data. Do not treat a constant-speed sign theorem as a sign-preserving law for arbitrary exponential clocks. The restricted range and layer formulation survived these tests and still need proofs or counterexamples. Tests at complete turns do not by themselves prove statements for every endpoint.

The separate source-scaling theorem transfers fixed finite segments to the constant-speed model as the integer cutoff grows while the height grows proportionally. Its proofs use no numerical results. It can establish eventual signs where the model has a strict margin; integer endpoint coincidences have zero margin and require a separate argument. None of these computations establishes a constraint at a zeta zero.
