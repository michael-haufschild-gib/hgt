# Positive periodic Poisson sources: period 41

Question: do positive periodic arithmetic coefficients with finite Fourier self-duality, fixed cusp residue and two unchanged source moments permit prescribed nonreal double zeros inside the critical strip? This is an arithmetic specificity control. It does not compute the original HB source or causal action.

For real even period-q coefficients a, require normalized DFT(a)=a and a_r>0. The baseline is a_r=1+sqrt(q) if r=0 and a_r=1 otherwise. Define theta_a(y)=sum over integer n of a_(n mod q) exp(−pi n² y/q), Lambda_a(s)=(q/pi)^(s/2) Gamma(s/2) sum a_n n^(−s), and X_a(t)=s(s−1)Lambda_a(s)/2 with s=1/2+i t. DFT invariance supplies theta inversion; fixed a0 retains the pole residues. The two center constraints are X_a(0) and X_a''(0), fixed to their baseline values. Positivity of these Dirichlet coefficients is distinct from positivity of the differentiated Xi cosine kernel.

| Target Re t | Im t | Both moments fixed | Both moments omitted |
|---|---|---|---|
| 20 | 0.125 | False | True |
| 20 | 0.25 | False | True |
| 40 | 0.125 | False | True |
| 40 | 0.25 | False | True |
| 80 | 0.125 | False | False |
| 80 | 0.25 | False | False |

True denotes a floating-point feasible LP followed by high-precision equality correction, not an exact certificate. False denotes numerical infeasibility in the frozen box 0.05 a_baseline ≤ a ≤ 4 a_baseline. It is not an infeasibility theorem beyond that box. The finite DFT-fixed even subspace has dimension 11. A zero objective asks feasibility; no constants are optimized.

Four candidates survive in the moment-relaxed control, at t=20+i/8, 20+i/4, 40+i/8 and 40+i/4. Their 100/160-digit coefficient vectors agree within 4.39e-98; all have nonzero second derivative and positive coefficients. Equality correction moves some coefficients below the nominal lower bound by less than 2.8e−14, so exact membership in the originally specified closed box is not certified. Strict positivity, with every coefficient ratio above 0.049999, survives comfortably.

The original adaptive source-check pool terminated abruptly. Its summary incorrectly counted four returned error records as four completed checks; the actual number is zero. Raw errors are preserved and analysis.json corrects that accounting. Cause of worker termination is not established. The separately timed independent challenge replaces adaptive quadrature with two fixed high-precision Gauss-Legendre rules and retains the explicit pole term. All four candidates pass; fine-rule scaled F/F_t residuals are below 3.17e-146, and nearby nonzero anchors agree with Hurwitz continuation within 3.17e-146. Working precision is190 digits; achieved source agreement is about145 digits at worst, not190. These are numerical witnesses without interval existence certification.

Consequence: positive periodic Dirichlet coefficients, Poisson inversion and fixed residues alone permit inside-strip nonreal double-zero candidates. Retaining the two specified moments blocks these prescribed targets in this coefficient box. The subsequent singleton-moment experiment distinguishes this constraint dependence. No conclusion about an Euler product, full PSL2Z HB source, all zeros of this completion, or RH follows.

One original guard took 41.792s; recorded completed worker tasks total 48.567s. The failed source pool's unreported worker time is not included, so worker accounting underestimates that run. Discovery and later independent validation are separately timed, not represented as one uninterrupted run. Exact environments, source files and remote checksums are retained. No builds.
