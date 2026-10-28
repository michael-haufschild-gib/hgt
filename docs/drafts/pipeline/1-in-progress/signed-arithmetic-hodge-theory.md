# Signed arithmetic Hodge theory with source-compatible renormalization

## Objective

Develop source-faithful signed block, residual and renormalization estimates on the actual Weil
source. Complete signed complement, growing modal complement and critical-energy upper control
are research endpoints; no positive interface may assume them.

## Objects

Actual real Weil tests and their source-graph completion; proved positive arithmetic sections
and Weil projections; full mixed pairing and both poles; Ramanujan prime modes; canonical critical
source energy. Programme: formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/.

## First research question

Determine the exact optimal energy after correction by an arithmetic positive section.
Extract quantitative distance, mixed-charge and nested-removal laws. Instantiate them on the
actual unbounded fixed-log-cell carrier, preserving its residual radical.

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

## Source-compatible scaling question

Determine how exact Weil translation isometry interacts with the complete source graph norm.
The source mass weight is cosh(u/2)/Phi(u), so compact-source translations may retain their
Weil value while their graph size diverges. Seek a quantitative escape theorem for every
nonzero compact test, with exact pole scaling and a positive aperture-dependent comparison.
This tests whether dyadic coarse renormalization can use a single uniform graph topology.
No blanket claim of unboundedness of each fixed translation is made without proof.

## Scalar renormalization question

For a nonzero compact source f, combine full-Weil translation invariance and
all-rate source-graph escape. Seek a bound, uniform in every scalar amplitude a,

c exp(B |t|) |W(a tau_t f)| <= |W(f)| ||a tau_t f||_graph^2.

This measures the exact loss of signed energy under any graph-bounded scalar
renormalization, rather than only ruling out fixed exponential amplitudes.
A positive replacement uses two-sided comparisons on explicitly bounded source
windows and bounded translation ranges. It does not assert a global bounded
action of every fixed translation on the complete graph.

## Completed aperture transport target

Use the existing CHMD apertureGraphCore and apertureGraphCompletion. The proved
bounded-window estimate should extend literal compact-source translation to a
bounded linear map from the completed aperture a into the completed aperture
 a+|t|. On smooth representatives the map must be the original translated test;
on the completion it must preserve the full mixed Weil form and transport both
pole coordinates by their exact exponential factors. Constants remain dependent
on the source aperture and translation range.

Do not identify the signed-source radical with the full Weil radical. The
CHMDQuotientWeilForm two-pole classification remains part of the source data.

## Quantitative growing-mode Gram target

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

## Conductor-explicit prime residual target

For a prime p and horizon y>=1, the reciprocal Mangoldt mass on p-powers
beyond y should be bounded by 2 log(p)/y. Complete geometric mass minus the
first floor(log_p y) powers proves this directly. Summing only over conductor
primes gives the proposed normalized correction bound

4 sqrt(phi(m)) log(m) / y. The squarefree conductor part divides m,
so sum_(p|m) log(p)<=log(m).

With e(y)=MertensSum(y)-log(y)+EulerGamma and
f(y)=|e(y)|+1/y, the literal normalized Ramanujan row residual should satisfy

|residual_m(N,n)| <= sqrt(phi(m)) (1+4 log(m)) f(floor(N/n))/sqrt(n).

This would give one explicit finite-family squared residual budget
(sum_m phi(m)(1+4 log(m))^2) * sum_(n<=N) f(floor(N/n))^2/n.
The harmonic-quotient theorem proves the second factor is o(log N).
The input contains only finite prime arithmetic and the proved Mertens remainder;
no conductor-uniform convergence or complement sign is assumed. These estimates
remain research targets until formalized. They do not identify a complete modal
source or transfer Gamma and both poles.

## Horizon-uniform arithmetic error target

Seek an absolute bound on
B_N=sum_(n<=N) (|MertensSum(floor(N/n))-log(floor(N/n))+gamma|
+1/floor(N/n))^2/n.

The existing Chebyshev error bound and its explicit inverse-log-square
majorant imply a candidate Mertens remainder bound C/log(y). The exact Euler
integral identifies the tail constant. A finite positive-integer head then gives
f(y)^2<=D/(1+log(y)^2). Floor roundoff compares this profile with the summable
Wiener Lorentzian kernel. The existing bound_sum_log' applied to the constant
arithmetic sequence should yield B_N<=3D*(1+2*pi^2).

This would give an absolute residual budget for growing conductor families.
Distinct eigenvalue labels still require energy separation; a wider-window
spectral count could use dimension instead. Neither conclusion supplies the
modal complement or continuous Gamma and pole transfer.

## Local source-capture target

The exact totient bound suggests
sum_(n<=L) |sum_(m in S) a_m v_m(n)|^2
<=H_L*(sum_(m in S) phi(m))*(sum_(m in S) a_m^2).
Combined with the proved global Gram lower estimate, this measures the fraction
of normalized modal mass in each fixed integer window. Extract the positive
readout bound and approximation cost before any route-retirement claim.
The topology here is the literal prime-matrix l2 normalization; no claim about
every full-Weil completion follows.
