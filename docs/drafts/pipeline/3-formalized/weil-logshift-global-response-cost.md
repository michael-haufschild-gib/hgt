# One optimal shift and exact global response cost

Status: formalized; direct leaf and axiom audits passed, 2026-10-09.

## Local corpus evidence

`WeilLogShiftSharpDualReceiver` constructs a C₀ map Ψ from shifts into the
dual of the actual regular amplitude subspace, under one normalization.
`WeilLogShiftExactResponseCost` proves exact scalar-functional budget
feasibility and attained minimum cost for an arbitrary finite-dimensional
real normed amplitude space. Local mathlib's `Continuous.exists_forall_ge'`
gives a global maximum when a continuous function is eventually bounded
above by one of its values outside compact sets. Only Lean sources consulted.

## Paper proof

For any nonempty topological X and normed target F, every f:C₀(X,F) attains
its supremum norm. If f=0, any point works. Otherwise pick x₀ with
‖f(x₀)‖>0. Since ‖f(x)‖→0 outside compact sets, eventually
‖f(x)‖≤‖f(x₀)‖. The local extreme-value theorem gives a global maximizer x*.
The supremum norm characterization then identifies ‖f(x*)‖=‖f‖.

Apply this to Ψ:C₀(X,E*) for finite-dimensional real normed E. Write Q=‖Ψ‖.
Choose x* with ‖Ψ(x*)‖=Q, before choosing any target response or budget.
Every x has ‖Ψ(x)‖≤Q. Thus for every real r,A,

    (∃x,a, Ψ(x)(a)=r and ‖a‖≤A) iff 0≤A and |r|≤AQ.

Necessity follows from the operator bound and bounded evaluation. For
sufficiency use the already-proved exact budget theorem at x*.

At this same x*, for every response r feasible anywhere, minimum amplitude
cost is attained and equals |r|/Q. The local cost theorem supplies an attainer
at x*. Every amplitude b at any shift y with response r obeys
|r|≤Q‖b‖, so the attainer is globally minimal. When Q=0, all responses are
zero and the zero amplitude is the minimizer; nonzero responses are impossible.
No uniqueness of the shift or amplitude is asserted.

Specialize to the actual regular paired-kernel receiver. Its existing HasSum
contract and uniqueness of sums identify response equality with convergence
of the literal normalized series to r. The optimal shift is fixed once per
family and normalization, independently of response and budget. Q is the
global norm of the dual-valued receiver (equivalently the supremum of its
pointwise sensitivity). No added analytic premise or preferred amplitude norm.

## Work log

- [x] Local corpus search, predecessor and API source inspection.
- [x] Paper proof recorded before implementation.
- [x] Verify new local mathlib API names in /tmp Lean scratch.
- [x] Formalize C₀ norm attainment and one-point global cost classification.
- [x] Specialize literal paired-kernel series, keeping HasSum and regular domain.
- [x] Direct leaf builds, all-declaration axiom audit, umbrella wiring.
- [x] Index and lint; record exact results and clean owned scratch.

## Formal declarations

`formal/GaloisForLFunctions/RHTower/WeilLogShiftGlobalResponseCost.lean`:

- `exists_c0_norm_attainer`: any C₀ map from a nonempty topological space
  to a normed additive group attains its norm, including the zero map.
- `exists_c0_dual_optimal_response_point`: for a dual-valued C₀ family on
  a finite-dimensional real normed amplitude space, one point attains the
  global sensitivity and globally minimum cost for every feasible response;
  global budget feasibility is exactly 0≤A and |r|≤A‖Ψ‖.

`formal/GaloisForLFunctions/RHTower/WeilLogShiftGlobalResponseReceiver.lean`:

- `exists_weilLogShift_globally_optimal_response_shift`: one common
  normalization, actual dual receiver with HasSum at every shift, and one
  shift y₀ that maximizes evaluation norm and attains globally minimum
  amplitude cost for every feasible response. The explicit global sensitivity
  is Q=‖Ψ(y₀)‖, with ∀y, ‖Ψ(y)‖≤Q. Both global budget feasibility and the
  exact minimum cost |r|/Q include the zero-sensitivity case.

The native statement uses the maximum evaluation norm in place of writing
the C₀ supremum norm. These are equal by the generic theorem. This avoids
a Lean instance-inference failure for `Norm C₀(ℝ,L*)` with the concrete
regular submodule L, confirmed in an isolated /tmp scratch file despite
successful synthesis of the normed group structures on L and L*. No
mathematical conclusion or quantifier was weakened. Replaced deprecated
`push_neg` with `push Not`; no heartbeat or recursion-limit adjustment.

## Verification

Both final `lake --old env lean <leaf> -o <olean>` checks exited 0 without
warnings. All three public theorems passed a /tmp `#print axioms` audit;
each uses exactly `propext`, `Classical.choice`, and `Quot.sound`.
Both umbrella imports occur once; both oleans postdate their sources.
`scripts/formal_tools.py index` exited 0. Module-filtered local search found
all three declarations in their intended modules.

Final `scripts/formal_tools.py lint` exited 1 with exactly two unrelated
unreachable-module errors and no proof-debt errors:

- `HTGeometry.PaperPluckerNormalRowAction`
- `HTGeometry.QKrawtchoukCompanionTriangular`

No external search, numerical experiment, full build, or umbrella build.

## Follow-up: arithmetic-grid premise discharged

Local source inspection found
`GaloisForLFunctions.HTGeometry.linearIndependent_arithmetic_L2_translates`
in `HTGeometry/L2TranslationPolynomialIndependence.lean`: every nonzero
complex L² vector has linearly independent equally spaced translates. Its
proof uses a polynomial Fourier multiplier whose zero set is null.

The arithmetic-grid restriction is now removed in
[arbitrary-l2-translation-independence.md](arbitrary-l2-translation-independence.md).
`HurwitzExp.expLin_linearIndependent` and Bottcher's countable analytic-zero
theorem supply the stronger Fourier multiplier argument. Arbitrary distinct
real shifts are independent for every nonzero complex L² vector; the exact
relation theorem also classifies the zero source. Applying this to the
finite paired-log receiver kernel remains a separate task, including an
L² lift and the repeated logarithmic coordinates at indices 0 and 1.

Other inspected source ingredients: `pairedLogKernel` in
`WeilLogShiftDomainBoundary.lean`; `fourier_riemannAutocorr_eq`,
`integrable_riemannAutocorr_complex`, and `riemannAutocorr_eq_integral`
in `RiemannKernelSpectralLocalization.lean`. No new kernel classification
is claimed. A new working card and dependency-closed paper proof are required
before implementing the next conjecture. Full research goal remains active.
