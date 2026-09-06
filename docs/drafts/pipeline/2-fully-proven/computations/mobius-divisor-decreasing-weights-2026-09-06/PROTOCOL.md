# Frozen decreasing-weight source attack

## DW1 [BRIDGE]

For every integer M>=2 and real weights w_1>=...>=w_(M-1)>=0, set
`C_d(w)=mu(d) sum_(k=d)^(M-1) w_k D(floor(k/d))`, with the literal
`D(q)=log(q!)-sum_(n<=q)tau(n)+2 gamma q`.
The frozen proposal is `(sum_d C_d(w))^2<=sum_d C_d(w)^2`.

Physical content: ordinary monotone time smoothing supplies the missing signed cancellation.
Motivation: the square-root Abel kernel is in this class and its complete-source inequality
survives the preceding exhaustive finite scan. This is a proof-directed stronger bridge, not
an inferred theorem, primary universal conjecture, or novelty claim. A failure does not refute
the square-root statement SD1. Do not replace DW1 with a smaller cone after seeing data.

## Whole-cone experiment

Every such w is a nonnegative mixture of prefix indicators, with mixture coefficients
`a_t=w_t-w_(t+1)` and terminal w_M=0. Form the full matrix V whose t-th column is the actual
channel vector for the flat prefix through t. The optimal source-to-diagonal ratio on this
cone equals the larger squared norm of the Euclidean projections of +1 and -1 onto cone(V).
Compute those projections by nonnegative least squares, scaling columns only by positive
numbers. Record primal coefficients, residual/KKT diagnostics and the ratio of the resulting
explicit witness. Numerical optimization is not used as proof of a global maximum.

Initial endpoints M=16,32,64,128,256,512, at most eight independent workers, BLAS1. Each remote
batch has a120-second cap. If a failure appears, use its finite embedding in larger endpoints
to bracket the earliest failure, and inspect whether two prefix indicators already suffice.
Preserve raw witnesses and failed solves. Validate every reported counterexample with the
original double sum at60 and100 digits and fixed decimal or rational coefficients. No
numerical value enters Lean.

The source archive from the earlier complete-dilation experiment is reused. All arithmetic,
optimization, and high-precision audits run on the Runpod. Download all artifacts and a
compact report. Extract the exact algebraic obstruction after rejection, and distinguish
that proof from the numerical rejection of the literal-source conjecture.
