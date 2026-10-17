# Positive prime-Burnol operators: exact Bernstein mixture classification

- **ID:** positive-prime-burnol-bernstein-classification-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** whole local Lean corpus; prospective candidate 7, uncounted

## Exact proposed structural result

Let H be the literal complex L2 space on (0,infinity), and let T be a bounded
complex-linear operator preserving every actual critical-prime Burnol line.
Say T preserves nonnegativity when every a.e. real nonnegative input has an
a.e. real nonnegative output. Conjecture: this holds exactly when there is a
unique finite positive measure tau carried by [0,infinity) such that

`T f = integral K_h f d tau(h)`,

where `K_h f(t) = t/(t+h) * f(t+h)` is the actual weighted Burnol shift.
The integral is a strong vector integral for each f, not an operator-norm
Bochner integral. The norm should equal total mass. Composition should
correspond to convolution of measures. All conclusions count together once.

Stronger exact test proposed for the same classification: nonnegativity
preservation is already equivalent to nonnegative output for every packet
`t exp(-lambda*t) * (1-exp(-delta*t))^n`, with lambda,delta>0 and n natural.
A failed finite-difference inequality should expose a literal positive
packet whose image is negative on an initial interval. This separates the
physical positivity criterion from merely nonnegative prime eigenvalues.

## Paper mechanism under audit

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

This is not yet a dependency-closed paper proof. Literal L2 cone closure,
full strong continuity, measure uniqueness, and the exact finite-difference
packet identities must be checked against source before promotion or code.

## Initial corpus comparison

Whole-corpus hybrid query for positive operators, prime eigenlines, complete
monotonicity and weighted translation mixtures reported partial=false over
73,129 files and 1,082,467 declarations, with mixed/stale compiler coverage.
Candidate and source-argument names were inspected; selected mathematical
sources are being read. Search results containing old research prose are
not mathematical evidence. A separate deep query for positivity-preserving
convolution commutants and Laplace measure representation is pending.

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

No external novelty claim. Final corpus, significance and paper audits open.

## Gates

- [x] 0 -> 1: precise operator class, literal positivity and proposed classification.
- [ ] 1 -> 2: source applicability, exhaustive selected-mechanism audit, complete proof.
- [ ] 2 -> 3: exact Lean classification, targeted builds, axiom audit, wiring and lint.

Frontier map remains read only. No new Lean source belongs to this candidate yet.
