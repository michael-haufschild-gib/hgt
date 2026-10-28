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

## Local source capture

RamanujanFamiliesHaveAnExplicitLocalCaptureCost proves
sum_(n<=L) |sum_(m in S) a_m v_m(n)|^2
<=H_L*(sum_(m in S) phi(m))*(sum_(m in S) a_m^2).
Combined with the global Gram lower estimate, this gives local/global mass ratio
at most H_L*sum_(m in S) phi(m)/(log N-1-2*sum_(m in S) m^2), whenever
the denominator is positive. Each fixed finite modal span loses normalized mass
on every fixed integer window, uniformly over all coefficients. The final
individual Lean audit passes, with standard transitive axioms.
The topology here is the literal prime-matrix l2 normalization; no claim about
every full-Weil completion follows.

## Actual bounded-energy source capture

The existing TheRenormalizedPrimeEnergyControlsTheDefect proves uniform finite
Ramanujan approximation on every bounded actual renormalized-prime-energy
sublevel. BoundedPrimeEnergyEscapesEveryFixedIntegerWindow combines this with
local-modal capture: for every fixed T,L and epsilon>0, all sufficiently large
horizons have local mass <=epsilon for every unit vector of renormalized prime
energy <=T. The explicit transfer inequality is
mass_L(x)<=2*norm(x-v)^2+2*mass_L(v). The final individual Lean audit passes,
with standard transitive axioms. This is a boundary in the literal integer-coordinate
norm; it does not determine Gamma, both poles or the full Weil sign.

## Complete dyadic coordinates

Target the actual logarithmic-cell isometry W_2 and its cell embedding U,
which satisfy T_(log 2) U=U W_2. Identify the wandering space as cell 1 plus
balanced adjacent Haar vectors, prove purity by integer support growth, and
obtain complete orthogonal dyadic coordinates. Prime two then acts along
nearest-neighbour chains at fixed Haar index. This supplies exact multiscale
source coordinates before any sign assertion.

A separate Gamma square-function estimate must pay all levels from one reserve.
The candidate mechanism assigns each pair of points to its least common
ancestor in the actual logarithmic-cell tree and uses the existing two-interval
mean/variance inequality. Summing per-level Gamma bounds is not a proof of this
joint estimate. All-prime couplings and the selective generator-orbit sign are
further obligations.

### Completed logarithmic-cell clock

TheLogCellClockHasACompleteWanderingDecomposition proves the completed weighted
statement on H=l2(N+;C), with actual W=logCellShift 2 and K=(range W)^perp. W^j annihilates coordinates below 2^j,
so the intersection of its iterated ranges is zero. Distinct translates W^j K
are orthogonal, and their closed linear span is H. The proof of completeness
pulls a vector orthogonal to every W^j K back through the closed isometric range
at every depth, then uses the support cutoff. Literal compatibility with the cell embedding U is also proved. Its final
individual no-olean audit passes with standard axioms only. Exact finite
Pythagoras and identification of K with cell 1 plus balanced weighted Haar
details are further coordinate theorems.

The existing finite unweighted average/difference expansion is already proved
in TheCompleteSourceIsADyadicMultiresolution. The new target is the Hilbert
orthogonal decomposition and completion of the actual weighted clock. Its
completion is the logarithmic-cell subspace, not the entire continuous Weil
graph. No full-form positivity follows from Hilbert orthogonality alone.

### Explicit balanced wandering coordinates

For each positive a, set alpha_a=sqrt(ell_(2a)/ell_a) and
beta_a=sqrt(ell_(2a+1)/ell_a). The target generator is
beta_a*e_(2a)-alpha_a*e_(2a+1), together with e_1.
BalancedCellDetailsFormTheWanderingBasis proves orthonormality and completeness
in K from the exact two-coordinate rotation and alpha_a^2+beta_a^2=1.
EveryFiniteCellSourceHasFiniteDyadicCoordinates constructs the complete orbit
Hilbert basis and literal coordinate isometry indexed by N x (Option N+).
Both modules pass final no-olean audits with standard axioms only. Pay the embedding-to-balanced-Haar
normalization explicitly before invoking Gamma estimates for those atoms.

### Arithmetic action in complete levels

Because W_p W_2=W_2 W_p, the actual arithmetic action should have the exact
level matrix law

inner(W_2^j u,W_p W_2^k v)=0 if j<k,
inner(W_2^j u,W_p W_2^k v)=inner(W_2^(j-k) u,W_p v) if k<=j,

for u,v in K and p>=2. Prime two is the one-step shift. This is a candidate
analytic operator-valued Toeplitz representation of the actual arithmetic
semigroup. Its coefficients must be derived from the original source maps.
It supplies no selective sign or joint Gamma cost without additional proofs.

### Finite source exhaustion before form limits

EveryFiniteCellSourceHasFiniteDyadicCoordinates proves
e_(2a)=alpha_a W e_a+beta_a d_a and
e_(2a+1)=beta_a W e_a-alpha_a d_a. The algebraic span of all W^j generators
is W-invariant. Strong induction in the integer coordinate places every
standard cell vector, hence every finite compact cell profile, in this
algebraic span. This is stronger domain information than Hilbert density:
Gamma and the full Weil form can be evaluated on exact finite expansions
without an unproved passage through infinite sums.

### Physical balanced-Haar normalization

Prove sqrt(haarMass a)*U(d_a)=haarAtom a using the existing physical Haar
source and its mass. The scalar square-root identities follow from positive
cell widths and the exact parent-width telescope. Transport this equality
through every literal iterated log2 shift. This is the required comparison
before applying physical Gamma estimates to the new coefficient coordinates.

### One Gamma reserve for the complete tree

The exact target is a single bound on the weighted squared physical detail
readouts over all levels. Existing gamma_twoInterval_mean_variance_ge and
archLevyDensity_ge_inv_two_mul suggest the local estimate
Gamma(sibling rectangle)>=Var(parent)/8, since each actual child has at least
one quarter of its parent's logarithmic width and each parent width is <=log2.
DyadicSiblingPartition supplies uniqueness of the integer sibling rectangle.
Adapt it to the actual physical interval pairs, sum disjoint rectangles once,
and count how many parent variances contain each detail. The resulting weight
should be comparable to 1+log(a). Root cell means remain a distinct sector.
All constants, domain restrictions and the Gamma pair-integral normalization
must be carried in the Lean statements.
