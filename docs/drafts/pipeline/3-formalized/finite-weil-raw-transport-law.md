# Finite Weil raw transport law

Status: FORMALIZED. Paper proof and native Lean audit complete.

Only local Lean corpus and installed Lean dependencies. No web, external papers, or numerics.
The refreshed prior residual metadata has no issues. Scoped lexical Wasserstein search
in WeilLogShift has no hits. Existing HTGeometry.KantorovichRubinsteinDuality supplies
IsCoupling, wassersteinOne, lipschitzDual and a coupling upper bound without compactness.
Its compact-space duality theorem is not needed for this finite construction.

Put n=r+1, X_i=i-E, Y_i=n(T_i-Q), and let m_i be canonical edge probabilities.
Define actual probability laws mu=sum m_i delta(X_i), nu=sum m_i delta(Y_i),
and pi=sum m_i delta(X_i,Y_i). Pushforward of finite atomic laws gives the marginals
exactly. Its transport cost is sum m_i |X_i-Y_i|=rawFluctuationGap.
Hence 0 <= wassersteinOne(mu,nu) <= rawFluctuationGap.

For every L-Lipschitz real observable f, finite integration and the triangle inequality give
|integral f dmu-integral f dnu| <= L rawFluctuationGap. No boundedness assumption on f
is needed: both laws have finite support. The unit-Lipschitz class includes zero and its
expectation differences are bounded above by rawFluctuationGap. Thus the corpus
lipschitzDual also lies in [0,rawFluctuationGap], without using noncompact duality.

At k=2n^2+t(r), the previously proved rawFluctuationGap tends to zero for every offset
sequence t:Nat->Nat. Squeeze proves both transport and uniform Lipschitz limits. The
observable estimate also permits an arbitrary r-dependent family with common Lipschitz
constant L; no convergence of the observables is required.

Plan: finite observable pushforward/coupling; actual raw laws and cost; Lipschitz bound
and dual; three unconditional limit receivers; native leaves, native axiom audit,
umbrella wiring, local index, lint. Structural parameters only on final roots.


## Formal closure — 2026-10-11

Status: FORMALIZED. All proposed actual-law and limit statements proved.
For n=r+1,k=2n^2+t(r), arbitrary t:Nat->Nat, the Wasserstein distance between
the actual canonical laws of X_i=i-E and Y_i=n(T_i-Q) tends to zero before
Gaussian normalization. The corpus Lipschitz dual value also tends to zero.
Every rank-dependent family of real observables with a common Lipschitz constant
has vanishing expectation gap; observables need not be bounded or converge.

The finite shared-index probability coupling has exact marginals and exact cost
sum m_i |X_i-Y_i|=rawFluctuationGap. Wasserstein and Lipschitz dual values both lie
between zero and this cost. The individual L-Lipschitz integral gap is bounded
by L times this cost. The existing raw first-moment root therefore closes all three
receivers without any compactness premise or unproved noncompact duality identity.

Files under formal/GaloisForLFunctions/RHTower:

- WeilLogShiftObservableCoupling.lean: generic observable pushforward, finite coupling,
  both marginals, IsCoupling witness and exact metric cost (6 declarations).
- WeilLogShiftRawTransportLaw.lean: raw values and laws, actual coupling and cost,
  Wasserstein value with nonnegativity and upper bound (10 declarations).
- WeilLogShiftRawLipschitzComparison.lean: unbounded observable estimate and bounded
  nonnegative Lipschitz dual value (5 declarations).
- WeilLogShiftRawTransportLimit.lean: three unconditional limit receivers (3 declarations).

Verification: all four final native leaf builds passed with empty logs. Native final
audit checked all 24 public declarations (8 definitions, 16 theorems) and 19 explicit
API haves; axioms are only propext, Classical.choice, Quot.sound. Metadata has no
issues; six direct import records fresh and seven incoming imports audited; one
umbrella import per new leaf and no duplicate authored declaration identifiers.
All three roots appear in refreshed local search. Scoped git diff --check passed.
No full/umbrella builds, heartbeat changes, commits, pushes, external sources, or numerics.
All builds remained sequential.

Lean details: spell the Lipschitz constant type NNReal when its notation scope is
not open. Function subtypes require explicit coercion `(f : Real -> Real)` when
applied; the varying-observable root uses `(f r : Real -> Real)` explicitly.

Artifacts: /tmp/hgt-raw-transport-{api.lean,api.log,metadata.py,metadata.json,
declarations.json,incoming-imports.txt,final-audit.lean,final-audit.log,
roots-search.json,lint.log,close.py,prior-search.json,atomic-search.json}; per-leaf
/tmp/hgt-WeilLogShift*.log.

Global formal lint: 15 errors and 367 warnings, all outside these four leaves.
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMPolarOddPrimeJumps
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzCompactCharacter
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzEnergyDomain
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzPowerRegularization
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzSourceIdealBridge
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzWallApproach
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilLockSpectralIdentity
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.XiCriticalZeroLinearNodes
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.XiGaussianHeatHankelLinearHorizon
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.XiSliceHeatMomentConcentration
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.DanskinPerturbationBound
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.LorentzOrderedSums
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperDiagonalStrongConvergence
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionTriangular
- error: proof debt: formal/GaloisForLFunctions/RHTower/CCM/CCMPolarOddPrimeJumps.lean:104: sorry (theorem ccmPolarOddSource_eq_core_add_atoms)
