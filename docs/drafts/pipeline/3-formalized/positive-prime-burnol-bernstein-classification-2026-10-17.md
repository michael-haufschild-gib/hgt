# Positive prime-Burnol operators: exact Bernstein mixture classification

- **ID:** positive-prime-burnol-bernstein-classification-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean proofs complete)
- **Source:** whole local Lean corpus; contribution 7, counted once

## Exact structural result

Let H be the literal complex L2 space on (0,infinity), and let T be a bounded
complex-linear operator preserving every actual critical-prime Burnol line.
Say T preserves nonnegativity when every a.e. real nonnegative input has an
a.e. real nonnegative output. This holds exactly when there is a
unique finite positive measure tau carried by [0,infinity) such that

`T f = integral K_h f d tau(h)`,

where `K_h f(t) = t/(t+h) * f(t+h)` is the actual weighted Burnol shift.
The integral is a strong vector integral for each f, not an operator-norm
Bochner integral. The norm equals total mass. Composition corresponds to
convolution of measures. All conclusions count together once.

The same classification has a complete packet test: nonnegativity
preservation is already equivalent to nonnegative output for every packet
`t exp(-lambda*t) * (1-exp(-delta*t))^n`, with lambda,delta>0 and n natural.
A failed finite-difference inequality exposes a literal positive
packet whose image is negative on an initial interval. This separates the
physical positivity criterion from merely nonnegative prime eigenvalues.

## Paper mechanism

1. Contribution 6 forces one bounded holomorphic symbol phi on the complete
   right half-plane and `T e_z = phi(z) e_z` for all complex frequencies.
2. For real lambda,delta>0, the displayed packet is a finite linear
   combination of complex Burnol features and is pointwise nonnegative.
   Its output has continuous representative
   `t exp(-lambda*t) sum_k (-1)^k choose(n,k) phi(lambda+k*delta) exp(-k*delta*t)`.
   Positivity a.e. implies positivity everywhere in t>0 by full support.
   For n=0 the symbol is real and nonnegative. Dividing by the positive
   prefactor and taking t down to zero gives every complete-monotonicity
   finite-difference inequality for the real symbol.
3. The corpus defines complete monotonicity by these finite differences,
   so no unproved differentiation under an L2 point evaluation is needed.
   Holomorphy gives continuity; antitonicity and the operator norm bound
   give a finite right limit at zero. BernsteinWidder then constructs tau.
4. For a finite positive tau, strong continuity and contractivity of K_h
   make every vector orbit integrable. The integral defines a bounded
   nonnegativity-preserving operator. Its actual-prime eigenvalues are the
   Laplace transform of tau. Contribution 6 prime totality identifies it
   with T. Monotone convergence at frequency zero gives norm = total mass.
5. Laplace uniqueness gives uniqueness of tau. Fubini and K_h K_j=K_(h+j)
   give the convolution law. If a finite-difference inequality fails, the
   continuous output polynomial is negative near t=0, giving the packet
   obstruction stated above.

The dependency checks below close this paper proof. Nothing is counted until
the exact classification has passed Lean verification.

## Initial corpus comparison

Whole-corpus hybrid query for positive operators, prime eigenlines, complete
monotonicity and weighted translation mixtures reported partial=false over
73,129 files and 1,082,467 declarations, with mixed/stale compiler coverage.
Candidate and source-argument names and relevant mathematical sources were
inspected. Search results containing old research prose are not mathematical
evidence. A separate completed deep query for positivity-preserving convolution
commutants and Laplace measure representation is recorded below.

- `HTGeometry/BernsteinWidder.lean` supplies a finite positive measure for
  a continuous finite-difference completely monotone function with finite
  right limit at zero, and the converse.
- `HTGeometry/CompletelyMonotoneSampling.lean` supplies nonnegativity and
  antitonicity consequences of the finite-difference definition.
- `RHTower/ThetaRateLaplaceBernstein.lean` gives actual rate-measure uniqueness
  and measure-order recovery from complete monotonicity of Laplace differences.
- `HTGeometry/BurnolHalfLineWeightedShift.lean` and contribution 4 give actual
  weighted shifts, contractivity, eigenfeatures and strong continuity at zero.
- `HTGeometry/QuantileBurnolLanding.lean` concerns positive Gram landings and
  quantile synthesis; its operator positivity is a different property.
- Contribution 6 alone classifies bounded holomorphic symbols, with no
  nonnegativity-preserving or positive-measure characterization. This lead
  must establish that new physical cone, not merely restate symbol existence.

No external novelty claim. Corpus novelty and significance audit below.

## Closed paper proof and dependency audit (2026-10-17)

Use finite positive measures on NNReal, equivalently measures on the real
line carried by [0,infinity). All operator integrals below are vectorwise.

For lambda,delta>0 define the positive packet u_n(t) by the displayed formula.
The binomial theorem writes it as a finite sum of the L2 features
e_(lambda+k*delta), so its membership in H is unconditional. The same finite
sum with coefficients multiplied by phi(lambda+k*delta) is a continuous
representative v_n of T u_n. If packet outputs are nonnegative a.e., continuity
and positivity of Lebesgue measure on every nonempty open subinterval force
v_n(t) to be real nonnegative for every t>0. At n=0, phi(lambda) is therefore
real nonnegative. For general n, divide by t exp(-lambda*t)>0 and let t decrease
to zero. The resulting inequality is exactly
(-1)^n Delta_delta^n (Re phi)(lambda)>=0: this follows either from the binomial
formula for finite differences or induction using Delta f(x)=f(x+delta)-f(x).

H=Re phi is continuous on (0,infinity), completely monotone in the corpus's
finite-difference sense, and bounded between zero and ||T||. The source lemma
completelyMonotoneDiff_antitone makes H antitone. AntitoneOn.tendsto_nhdsGT,
with the bound ||T||, gives its finite right limit L=sSup(H''(0,infinity)).
exists_finiteLaplaceMeasure_of_completelyMonotoneOn therefore supplies a finite
positive real measure nu carried by [0,infinity), with H its Laplace transform.
Push nu forward by Real.toNNReal to obtain tau. The support condition makes
coercion back to the real line equal to the identity nu-a.e., so this pushforward
preserves the Laplace formula and total mass.

Conversely, for any finite tau on NNReal, continuous_burnolWeightedShift_apply
proves continuity of h -> K_h f on the entire closed half-line, not just at zero.
Contractivity bounds its norm by ||f||, giving Bochner integrability and a bounded
complex-linear map B_tau f=integral K_h f with norm at most tau(univ).toReal.
The literal a.e. formula for K_h and quasiMeasurePreserving_add_right_Ioi show
it preserves nonnegativity. Mathlib LpOrder supplies the closed order cone on
complex L2, with ComplexOrder (real comparison and equal imaginary part).
IsOrderedModule.of_smul_nonneg lifts real scalar order through Lp.coeFn_nonneg;
integral_nonneg_of_ae then proves B_tau preserves this same literal cone.

The depth-zero eigenfeature identity gives
B_tau e_lambda=(integral exp(-lambda*h) d tau(h)) e_lambda. Thus the operator
constructed from the preceding Bernstein measure agrees with T on every
actual-prime feature. primeBurnol_operator_ext identifies B_tau=T. The existing
symbol bound, evaluated as lambda decreases to zero, and bounded convergence
of exp(-lambda*h) to 1 give mass(tau)<=||T||; combined with the integral estimate
this is norm equality. This argument covers the zero measure and atoms at zero.

If two such mixtures agree, their positive-integer eigenvalues agree because
e_n is nonzero. LaplaceTomography.measure_eq_of_laplace_eq_succ then proves
equality of the two finite NNReal measures. Define tau*sigma as the pushforward
of tau.prod sigma under addition. The orbit (h,j)->K_(h+j)f is continuous and
bounded by ||f||, hence integrable for the finite product measure. The continuous
linear-map integral identity, Bochner Fubini, and burnolWeightedShift_comp give
B_tau B_sigma=B_(tau*sigma). This also proves the composition assertion without
asserting operator-norm continuity or operator-valued Bochner integrability.

All steps from packet positivity to the measure were proved without assuming
positivity on other inputs. Hence packet positivity alone is equivalent to
positivity preservation. If the symbol is real on positive rates and one
alternating finite difference is negative, the normalized output polynomial
has negative value at zero. Continuity makes the actual output negative on
some interval (0,epsilon). If a positive-rate symbol is nonreal, the n=0 packet
already violates the real nonnegative cone. These are separate cases.

## Corpus comparison and significance

The completed deep query reported partial=false over 73,131 files and 1,082,481
declarations. All 20 candidate names, 20 source-argument names, and the single
ingredient set were inspected. Suggested Volterra/weighted-Laplace identities
are generic convolution identities; they do not classify every positive
operator preserving actual-prime lines. No old research prose is proof evidence.

An exhaustive source-text search for burnolWeightedShift, burnolRateFeature,
and primeLogCriticalLaplaceFeatureL2 found 16 mathematical modules. Relevant
statements were compared. BurnolGraphActionFiltration gives particular shift
actions; RestrictedUnitaryBurnolDefectCovariance concerns positive Gram/adjoint
effects; BurnolWeightedShiftSingularSequence concerns spectra and norm-one
shifts; PrimeLogThetaRealAxisAmbientHilbertObstruction excludes certain ambient
readers. None gives the present physical-cone classification. A cross-filter of
all Bernstein/completely-monotone/Laplace-measure Lean modules against weighted
shift/raw-prime/rate-feature names returned only BurnolHalfLineWeightedShift.
Compiler freshness of search retrieval was mixed; direct sources and scratch
Lean checks are authoritative. Contribution 6 itself is treated as an ingredient,
not evidence of prior novelty.

The new structural conclusion is an exact classification of the physical
nonnegativity-preserving subalgebra, including a complete positive-packet test,
unique measure coordinates, exact mass norm and convolution. This enables
arbitrary positive shift distributions and excludes symbols via explicit
positive inputs. It is not merely existence of a bounded holomorphic symbol,
an estimate, a finite-node interpolation bridge, or an unproved RH receiver.
All related conclusions are one contribution. No claim of external novelty.

## Gates

- [x] 0 -> 1: precise operator class, literal positivity and proposed classification.
- [x] 1 -> 2: source applicability, exhaustive selected-mechanism audit, complete proof.
- [x] 2 -> 3: exact Lean classification, targeted builds, axiom audit and wiring.
- [x] Generated index and global lint executed; unrelated global failure recorded below.

Frontier map remains read only.

## Lean implementation checkpoint

Four new leaves, all compiled and wired once:

- HTGeometry/BurnolPositivePackets.lean: literal cone, packet recursion,
  a.e. positive formula, normalized operator image and zero-limit readout.
- HTGeometry/BurnolPositiveShiftMeasure.lean: vector integrals, positive
  mixtures, rate eigenvalues, uniqueness, convolution and exact mass norm.
- RHTower/PrimeBurnolPositiveSymbol.lean: packet test, complete monotonicity
  and finite NNReal measure representation of the actual operator symbol.
- RHTower/PrimeBurnolPositiveMeasureClassification.lean: complete packet test,
  unique physical measure classification and actual-prime realization.

Only one owned Lean process runs at a time. Scratch API probe passed after
correcting the root name continuous_real_toNNReal and continuous_re composition.
All four leaves compile with empty logs. This includes literal packet readout,
all finite positive mixtures, measure injectivity, convolution, exact mass
norm, complete packet test, unique-measure classification and actual-prime
realization. All 38 explicitly named public declarations were audited from a
/tmp scratch file: every axiom list is exactly propext, Classical.choice and
Quot.sound. Six primary signatures were inspected with no hidden source premise.
Each leaf is wired once and has a fresh .olean.

Index regeneration passed at 03:40 UTC. Global lint --check-generated reported
one error: unrelated concurrent RHTower.WeilConePoleDualityAnatomy was not yet
wired into its umbrella. It reported no generated-file drift or forbidden
declarations; the remaining 381 lines were existing large-file warnings.
All four contribution-7 imports are wired, all 38 axiom audits pass, and source
hashes were rechecked unchanged. No unrelated file was changed to bypass lint.
As with contributions 1 and 2, the external wiring failure is recorded without
misrepresenting global lint as green. This fully formalized result counts once.

SHA256 of the verified sources:

```text
BurnolPositivePackets 10d5f0b4c7fc491d9e83fe91a85c51dbd10aea3ef71118a3d249c7ac21110dcc
BurnolPositiveShiftMeasure 5b363ce183c88ef6c50215118188f0c3dcfc9412fe0a75c8f32ce8cfcdf23673
PrimeBurnolPositiveSymbol d1c2b56dc5387857ccba27c83fdce019fb3388569881ffd4af644aa168557680
PrimeBurnolPositiveMeasureClassification 4506c82cc8996db15fdafe1bcc7fdcdb3b5965ab6adf3feac1e37a89cb961fe8
```
