# Prime-block feedback experiment

Status: exploratory numerical science, not a proof certificate. No computation is an input to Lean.

## Scientific question and RH chain

The closed quartic block comparison retains the count and total logarithm of the primes in each block. Its correction converges; cancellation in the retained statistics remains unproved. Does chronological coupling between those two statistics reveal a restoring mechanism across scales, beyond the information in earlier counts alone?

This is a search for evidence from which to form a mathematical conjecture, not a claim that a predictor proves RH. A useful prediction would still need an exact arithmetic explanation and control of accumulated innovations on every scale. A numerical failure retires only the tested predictor/mechanism, not arithmetic RH or all possible nonlinear laws.

## Data and coordinates

Use all ordinary primes below `90^4=65,610,000`. For each `k=4,...,89`, subdivide `[k^4,(k+1)^4)` into `r=1,4,16` equal physical-width intervals, with integer endpoints. There is no prime selection by signs or fitted outcomes.

In a cell `[a,b)`, set `L=integral_a^b dx/log x`, `ell=L^(-1) integral_a^b log(x/mid) dx/log x`, and `V=integral_a^b (log(x/mid)-ell)^2 dx/log x`. Observations are

`A=(prime_count-L)/sqrt(L)`,

`B=sum_(a<=p<b) (log(p/mid)-ell)/sqrt(V)`.

These are precisely two coordinates of the retained source. The normalization is a diagnostic baseline, not an assumed stochastic model of primes. Numerical quadrature uses 32-point Gauss–Legendre and is checked against 64 points before interpretations. Small systematic biases in the chosen smooth baseline are retained and reported; predictors include a constant intercept.

## Separation of discovery and validation

Discovery training: `k=4,...,23`. Discovery screening: `k=24,...,31`. Locked validation: `k=32,...,63`. Final separate scale range: `k=64,...,89`. Only the discovery ranges are inspected before a candidate is frozen. The script may construct later raw rows, but its discovery output must omit their statistics and predictions.

Predeclared predictor family: ridge linear prediction of `A_j` from the previous eight `A` values; compare with the previous eight `A` and `B` values. Ridge coefficient is `10^-3`, predictors standardized on training data only, intercept unpenalized. Fit each resolution separately. Diagnostics include lag correlations through eight cells and forward/backward prediction to detect whether a proposed effect is merely symmetric correlation.

A candidate may advance only if the added `B` features improve discovery-screen mean squared error by at least 5% over the count-only fit, and the complete predictor improves at least 5% over the training-mean baseline at resolution 16. Freeze its statement and coefficients before inspecting later ranges. Survival then requires the same two improvements on both held-out ranges at resolution 16; report other resolutions without selecting whichever works.

Controls, if a candidate advances: keep actual count history fixed and randomize the standardized `B` observations within each sixteen-cell group; separately keep paired observations fixed and shuffle their chronological order in the same groups. Use 128 fixed-seed replicates. These are statistical controls that deliberately break chronology, not ordinary prime systems or RH countermodels. They do not establish that a general source perturbation preserves the zeta zeros.

## Execution

Run only on the authorized Runpod. Segmented prime sieve uses up to eight worker processes; each worker runs one task at a time. Cap BLAS/OpenMP threads at one. Each command has a 120-second cap. Download script, raw rows, fitted models, and result summaries. Do not run a computation whose conclusion already follows from the block-compression identity. Report failed predictions and actual limitations, without turning an observed finite fit into an all-scale law.

## Corpus seeds

`PrimeLogBlockCompression`: exact two-moment cancellation and the complete arithmetic comparison; `LiouvillePrimeErrorDivisorAudit`: information-preservation audit; `XiPhysicalPrimeApertureMertensCoboundary`: cumulative discrepancies versus interval differences; `ConstitutiveSplitFormationParallax`: distinction between what an observation retains and what its residual carries. Searches are mechanism discovery, not claims that these modules contain the missing RH estimate.
