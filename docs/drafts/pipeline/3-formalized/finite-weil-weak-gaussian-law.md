# Actual finite probability laws converge to the diagonal Gaussian

Status: in progress. Research sources: local Lean corpus and installed Lean dependencies only.
Previous Gaussian characteristic-function increment revalidated with no metadata issues.

Prior search found the reusable `FourierLLogL.Law.atomicProbability` constructor and its
exact real integral formula in `HTGeometry/PaperFourierLawMeasure.lean`. Existing finite
atomic observer laws are restricted to real targets; circle cubature hits address a different
construction. No ProbabilityMeasure/atomicProbability declaration exists in the WeilLogShift
family. Installed Lean's LevyConvergence theorem handles finite-dimensional real inner-product
spaces, so the joint law will live in `EuclideanSpace ℝ (Fin 2)`.

Conjecture: with n=r+1,k=2n²+t(r), the actual finite probability law on points
((i-E)/sqrt(n), n(T_i-Q)/sqrt(n)) with canonical weights m_i converges weakly to
the image of N(0,1/4) under z -> (z,z). Every real linear projection (a,b) therefore
converges to N(0,(a+b)²/4), including the degenerate case a+b=0.

Dependency-closed paper proof:

1. Package the already proved positive weights of total mass one as the existing finite Law.
   Its atomicProbability image is a genuine ProbabilityMeasure on any target. Extend the
   existing finite real integral identity to complex observables, directly from finite Dirac
   integrals. No measurability or integrability assumption on these finite observables is needed.
2. Expand the Euclidean inner product of each joint point against (a,b). The resulting
   characteristic function is exactly the previously verified finite joint phase sum.
3. Push N(0,1/4) along the continuous diagonal embedding. Its characteristic function is
   exp(-(a+b)²/8), by the installed Gaussian formula and change of variables. Its entire
   mass lies on the diagonal.
4. Apply the installed finite-dimensional Levy theorem to the existing unconditional joint
   characteristic-function limit. The weak limit is therefore the actual diagonal Gaussian.
5. Expose convergence of every bounded continuous real observable as exact finite sums.
   For each a,b, define the actual scalar atomic projection law and compute its characteristic
   function using the old joint sum at (u*a,u*b). Levy and the Gaussian formula give the stated
   scalar limit with variance (a+b)²/4. No nondegeneracy premise is required.

Plan: finite observable law and integral formulas; joint Euclidean law; diagonal Gaussian
target and support; joint weak limit and observable receiver; all scalar projected limits.
Build individually with one owned foreground Lean process, audit every public declaration
and new local API, check dependency freshness and all imports, wire each leaf once, index
finished roots, and run formal lint without altering unrelated concurrent work.


## Formal closure — 2026-10-11

Status: FORMALIZED. Local Lean corpus and installed Lean dependencies only; no web, papers, or numerical evidence.

For every offset sequence t : Nat -> Nat, put n = r + 1 and k = 2 n^2 + t(r).
The canonical edge probability law of ((i - E)/sqrt(n), n(T_i - Q)/sqrt(n))
converges weakly to (Z, Z), where Z is Gaussian with mean zero and variance 1/4.
The target has mass one on the diagonal. Every bounded continuous real observable
has convergence of its actual finite weighted expectation. Every projection with
coefficients a,b converges to the real Gaussian with variance (a+b)^2/4; the
anti-diagonal projection (a,-a) converges to the Dirac probability at zero.
No analytic hypotheses remain on these roots; t,a,b and the observable are structural parameters.

The proof packages the already proved joint characteristic sum as the characteristic
function of a genuine finite probability measure. The local atomicProbability
constructor supplies total mass one and integration formulas. A diagonal pushforward
of gaussianReal has exactly the limiting characteristic function. Local finite-dimensional
Levy convergence closes the joint and projected weak limits, including zero variance.

Five leaves under formal/GaloisForLFunctions/RHTower:

- WeilLogShiftObservableLaw.lean: 5 declarations; canonical Law and observable probability law, real/complex integration.
- WeilLogShiftJointProbabilityLaw.lean: 4 declarations; Euclidean fluctuation points and characteristic-function identity.
- WeilLogShiftDiagonalGaussian.lean: 6 declarations; diagonal Gaussian, characteristic function, diagonal full mass.
- WeilLogShiftJointWeakLimit.lean: 2 roots; weak joint convergence and bounded continuous expectations.
- WeilLogShiftProjectedWeakLimit.lean: 6 declarations; scalar laws, Gaussian limits, anti-diagonal collapse.

Verification: all five native leaf builds passed with empty logs; native final audit
passed for all 23 public declarations (8 definitions, 15 theorems), using only
propext, Classical.choice, Quot.sound. The final audit also checked 27 explicit API haves.
Metadata found no issues: all 9 direct dependency records fresh, all 9 incoming imports
audited, one umbrella import per new leaf, no duplicate authored declaration names.
All four public convergence roots appear in the refreshed local search index.
Scoped git diff --check passed. No full umbrella build, heartbeat changes, commits, or pushes.

Artifacts: /tmp/hgt-weak-gaussian-{api.lean,api.log,metadata.py,metadata.json,
declarations.json,incoming-imports.txt,final-audit.lean,final-audit.log,
roots-search.json,lint.log,close.py}; leaf logs /tmp/hgt-WeilLogShift*.log.

Global formal lint: 12 errors, 367 warnings, all outside the five new leaves.
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMPolarOddPrimeJumps
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzCompactCharacter
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzEnergyDomain
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzPowerRegularization
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzSourceIdealBridge
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzWallApproach
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilRegularVariationLockRigidity
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.XiCriticalZeroSeparatedNodes
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.FejerLatticeVanishing
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperDiagonalStrongConvergence
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionTriangular
- error: proof debt: formal/GaloisForLFunctions/RHTower/CCMPolarOddPrimeJumps.lean:104: sorry (theorem ccmPolarOddSource_eq_core_add_atoms)
