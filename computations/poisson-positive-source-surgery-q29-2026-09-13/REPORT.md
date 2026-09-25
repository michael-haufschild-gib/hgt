# Positive periodic Poisson sources: period 29

Question: do positive periodic arithmetic coefficients with finite Fourier self-duality, fixed cusp residue and two unchanged source moments permit prescribed nonreal double zeros inside the critical strip? This is an arithmetic specificity control. It does not compute the original HB source or causal action.

For real even period-q coefficients a, require normalized DFT(a)=a and a_r>0. The baseline is a_r=1+sqrt(q) if r=0 and a_r=1 otherwise. Define theta_a(y)=sum over integer n of a_(n mod q) exp(−pi n² y/q), Lambda_a(s)=(q/pi)^(s/2) Gamma(s/2) sum a_n n^(−s), and X_a(t)=s(s−1)Lambda_a(s)/2 with s=1/2+i t. DFT invariance supplies theta inversion; fixed a0 retains the pole residues. The two center constraints are X_a(0) and X_a''(0), fixed to their baseline values. Positivity of these Dirichlet coefficients is distinct from positivity of the differentiated Xi cosine kernel.

| Target Re t | Im t | Both moments fixed | Both moments omitted |
|---|---|---|---|
| 20 | 0.125 | False | False |
| 20 | 0.25 | False | False |
| 40 | 0.125 | False | False |
| 40 | 0.25 | False | False |
| 80 | 0.125 | False | False |
| 80 | 0.25 | False | False |

True denotes a floating-point feasible LP followed by high-precision equality correction, not an exact certificate. False denotes numerical infeasibility in the frozen box 0.05 a_baseline ≤ a ≤ 4 a_baseline. It is not an infeasibility theorem beyond that box. The finite DFT-fixed even subspace has dimension 8. A zero objective asks feasibility; no constants are optimized.

All twelve LP problems were infeasible. No accepted source or source-integral validation exists. Positive salvage is this scoped finite obstruction and the stronger period-41 control, not a claim that Poisson symmetry excludes nonreal zeros.

One original guard took 2.690s; recorded completed worker tasks total 6.374s. No source-check workers were needed because no coefficient vector was accepted. Exact environments, source files and remote checksums are retained. No builds.
