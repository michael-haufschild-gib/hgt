# Signed arithmetic Hodge theory with source-compatible renormalization

## Objective

Develop source-faithful signed block, residual and renormalization estimates on the actual Weil
source. Complete signed complement, growing modal complement and critical-energy upper control
are research endpoints; no positive interface may assume them.

## Objects

Actual real Weil tests and their source-graph completion; proved positive arithmetic sections
and Weil projections; full mixed pairing and both poles; Ramanujan prime modes; canonical critical
source energy. Programme: formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/.

## Certified section removal

The actual unbounded fixed-log-cell carrier has exact trial-energy minimization,
quadratic stationarity error bounds, one operator budget for a whole coefficient
family, and exact retention of the full Weil radical. Modules 1–3 formalize
these statements. Small stationarity on an exhaustive arithmetic family and
nonnegativity of the residual remain separate research problems.

## Method and proof obligations

Search the existing corpus for variational and nested projection results. Read exact source
statements. Prove only genuinely missing statements with all arithmetic inputs supplied.
Formalize each dependency-closed proof directly; audit using foreground Lean and #print axioms.
Do not turn residual positivity, growing-source bounds or critical-energy upper estimates into
assumptions.

## Research record

Foundational exposition: programme README.md.
Working evidence and continuation state: logs/signed-arithmetic-hodge-research.log.
No proof is classified as complete until formalized.

## Source-compatible scaling boundary

Every nonzero compact source has graph growth at every exponential rate under
translation, while its full Weil value stays fixed. Modules 4–5 prove this
boundary and its positive replacement: uniform two-sided graph comparisons on
explicitly bounded source windows and translation ranges.
No blanket claim of unboundedness of each fixed translation is made without proof.

## Scalar renormalization boundary

For every nonzero compact source f, module 4 proves the bound, uniform in
every scalar amplitude a,

c exp(B |t|) |W(a tau_t f)| <= |W(f)| ||a tau_t f||_graph^2.

This measures the exact loss of signed energy under any graph-bounded scalar
renormalization, rather than only ruling out fixed exponential amplitudes.
A positive replacement uses two-sided comparisons on explicitly bounded source
windows and bounded translation ranges. It does not assert a global bounded
action of every fixed translation on the complete graph.

## Completed aperture transport

Module 6 uses the existing CHMD apertureGraphCore and apertureGraphCompletion
to extend literal compact-source translation to an injective bounded linear map
from completed aperture a into completed aperture a+|t|. It preserves the full
mixed Weil form and transports all strip Fourier readouts, including both pole
coordinates with their exact exponential factors. Constants depend on source
aperture and translation range.

Do not identify the signed-source radical with the full Weil radical. The
CHMDQuotientWeilForm two-pole classification remains part of the source data.

## Quantitative growing-mode Gram budget

For the actual normalized Ramanujan pole profiles v_m, the formalized uniform finite
family estimate is

|sum_(n=1)^N (sum_(m in S) c_m v_m(n))^2
  - log N * sum_(m in S) c_m^2|
 <= (1+2*sum_(m in S) m^2) * sum_(m in S) c_m^2,

for every finite positive-conductor set and every natural horizon N.
GrowingRamanujanFamiliesHaveAUniformGramBudget proves it by complete-period
orthogonality, Abel summation and finite Cauchy–Schwarz. The exact harmonic
normalizer has constant 2*sum_m m^2. This controls the Gram part of growing-mode
transfer only.
Prime-matrix residual, modal complement and Gamma/pole comparison remain distinct.

## Conductor-explicit prime residual budget

Module 8 proves that the reciprocal Mangoldt mass on p-powers beyond y>=1
is at most 2 log(p)/y. Subtracting the first floor(log_p y) powers from the
complete geometric bound proves this directly. Summing conductor primes gives
the formalized normalized correction bound

4 sqrt(phi(m)) log(m) / y. The squarefree conductor part divides m,
so sum_(p|m) log(p)<=log(m).

With e(y)=MertensSum(y)-log(y)+EulerGamma and
f(y)=|e(y)|+1/y, module 9 proves the literal normalized Ramanujan row residual bound

|residual_m(N,n)| <= sqrt(phi(m)) (1+4 log(m)) f(floor(N/n))/sqrt(n).

For arbitrary real coefficients a_m, it proves
sum_n (sum_m a_m residual_m(N,n))^2
<= (sum_m a_m^2) * (sum_m phi(m)(1+4 log(m))^2)
  * sum_(n<=N) f(floor(N/n))^2/n.
The harmonic-quotient theorem proves the final arithmetic factor is o(log N).
The input contains only finite prime arithmetic and the proved Mertens remainder;
no conductor-uniform convergence or complement sign is assumed. Module 9,
OneArithmeticRemainderControlsEveryRamanujanResidual, passes its final audit
and has standard transitive axioms. The bounds do not identify a complete modal
source or transfer Gamma and both poles.

## Horizon-uniform arithmetic error

Module 10, TheArithmeticResidualBudgetIsUniformInTheHorizon, proves an absolute
bound B_N<=B at every natural horizon. The global Mertens decay gives
f(y)<=C/(1+log y). Exact floor roundoff compares its square with twice the
summable Wiener logarithmic kernel, whose mass is at most 1+2*pi^2.
Thus B=2C^2*(1+2*pi^2) pays all horizons.

For every finite family and all coefficients, the squared residual is at most
B*(sum_m phi(m)*(1+4log m)^2)*(sum_m a_m^2).
The final individual Lean audit passes, with standard transitive axioms.
Distinct eigenvalue labels still require energy separation. These estimates
control prime-matrix approximation, not the full-Weil complement or continuous
Gamma and pole transfer.

## Local source-capture target

The exact totient bound suggests
sum_(n<=L) |sum_(m in S) a_m v_m(n)|^2
<=H_L*(sum_(m in S) phi(m))*(sum_(m in S) a_m^2).
Combined with the proved global Gram lower estimate, this measures the fraction
of normalized modal mass in each fixed integer window. Extract the positive
readout bound and approximation cost before any route-retirement claim.
The topology here is the literal prime-matrix l2 normalization; no claim about
every full-Weil completion follows.

## Actual bounded-energy source capture

The existing TheRenormalizedPrimeEnergyControlsTheDefect proves uniform finite
Ramanujan approximation on every bounded actual renormalized-prime-energy
sublevel. Combine this with local-modal mass control and the Gram lower bound
to determine whether unit vectors in each such sublevel lose all mass on every
fixed integer window. This is a source-transfer boundary in the literal
integer-coordinate norm. Retain its quantitative local readout and approximation
costs; it does not determine Gamma, both poles or the full Weil sign.
