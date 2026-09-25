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

## GH1 [BRIDGE], independently frozen follow-up

Keep SD1 unchanged. For the actual square-root channel vector C and source S, propose
`B_M(q)=sum_d C_d C_d(q)-S sum_d C_d(q)>=0` for every M>=2 and 0<q<1,
where `C_d(q)=mu(d)sum_(k=d)^(M-1)q^k D(floor(k/d))`. The square-root kernel is a positive
Laplace mixture of geometric kernels, so this mixed sign would produce SD1 after a justified
finite-sum integral interchange. It tests whether one-sided half-order smoothing repairs the
failed unsmoothed cone. No such sign or integral proof is assumed.

First test all M=2,...,512 with q=exp(-u/M), u on a fixed logarithmic grid 1e-3,...,1e4;
use eight workers and a120-second cap. Report normalized signed mixed margins and preserve
failures. Audit the worst finite witness at60/100 digits using the original source. If it
fails, retain the signed mixed kernel explicitly; do not call generic Laplace positivity a
remaining solution. This is a fresh claim, not a range change to DW1.

## PH1 [BRIDGE], independently frozen after the GH1 grid passes

For each actual half-order channel vector C(M), test every flat-prefix channel vector F(t),
1<=t<M: `sum_d C_d(M) F_d(t) - S(M) sum_d F_d(t)>=0`.
This is membership of the half-order residual in the dual of the decreasing-weight cone;
it does not assert the false DW1 self-pairing inequality for that cone. Exact finite Abel
prefix decomposition would turn PH1 into SD1. PH1 also implies GH1 at finite M.

Test every M=2,...,512 and every prefix t. If it survives, test every prefix at larger fixed
endpoints 1024,2048,4096,8192,16384,32768,65536 using literal quotient blocks and the existing
complete source archive. Keep all failures and distinguish endpoint selection from an
exhaustive large-M test. Do not extrapolate finite dual-cone membership to all scales.

## GH1 scale stress test (same frozen inequality)

After PH1 fails, GH1 remains unchanged. Use exact quotient-block channel formulas and
product-event accumulation to test the same geometric pairing at fixed larger endpoints
1024,...,1048576 and the previously recorded SD1 late maximum M=1865411. The kernel grid
is the same 113 logarithmic u values. Separately test its necessary fast-kernel coefficient
D(1)*(C_1(M)-S(M)) at every available integer endpoint through2097152. A negative value
would reject GH1 by q tending to zero; retain all such endpoints. Audit the smallest
nondegenerate small-grid margin and any first failure independently at60/100 digits.
