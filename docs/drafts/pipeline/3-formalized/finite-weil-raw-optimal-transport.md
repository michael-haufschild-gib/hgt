# Finite Weil raw optimal transport

Status: FORMALIZED — 2026-10-11.

Objective: prove, for every natural r,k, that the existing raw index/correction
coupling attains Wasserstein cost and its raw gap equals the Lipschitz dual.
Use only the local Lean corpus and installed Lean dependencies.

Prior corpus search: `wassersteinOne coupling`, lexical HTGeometry. The local
KantorovichRubinsteinDuality module provides compact-space duality, while its
coupling definitions, marginal integral identities, nonnegative cost, and
coupling upper bound apply on R. The raw law modules already supply the
canonical coupling, its gap cost, dual boundedness, and the two upper bounds.
The new RawOrder module proves that Y and X-Y are increasing in the index.

Dependency-closed paper argument:

1. Let X_i be centered raw index and Y_i centered raw correction. Put
   e_i = X_i-Y_i. Both Y and e increase in i.
2. If some e_i >= 0, choose its first index j and c=Y_j. For e_i>=0,
   c<=Y_i<=X_i. For e_i<0, X_i<Y_i<=c. If no e_i>=0, choose c at the final Y.
   Thus |X_i-c|-|Y_i-c|=|X_i-Y_i| for every i.
3. The globally 1-Lipschitz potential f(x)=|x-c| therefore attains the
   existing raw gap in the actual finite-law integral difference. This
   proves dual=gap from the existing upper bound.
4. For any coupling of the raw laws, pull integrability of the coordinate
   identity and of any Lipschitz test back through its two marginals.
   The distance cost is integrable as |fst-snd|. Integrating the pointwise
   Lipschitz inequality proves dual<=every coupling cost, hence dual<=W1.
5. Existing canonical coupling gives W1<=gap. Therefore W1=dual=gap,
   with explicit attaining primal coupling and dual potential.

No compactness, width, limiting, or additional analytic premise is needed
in the r,k roots. Couplings and test functions appear as structural subtypes
only in supporting lemmas. No claim of global novelty or Gaussian W1
convergence follows from this increment alone.

Plan: verify local APIs; formalize the potential and the finite-marginal
integrability bridge; compose exact primal-dual equality; wire imports;
native audit every public declaration; run formal lint and document scope.


## Verified closure — 2026-10-11

The paper argument above is now fully formalized. For all natural r,k,
raw Wasserstein distance = raw Lipschitz dual = raw fluctuation gap.
The existing canonical probability coupling attains the infimum, and the
constructed globally 1-Lipschitz absolute-distance potential attains the
supremum. Every other coupling has cost at least this gap. Integrability
of every coupling cost follows from the finite marginals, with no
compactness, width, moment, or asymptotic assumption in the r,k roots.

All names below are in namespace `RHTower`; filenames identify modules.

- `WeilLogShiftRawPotential`: existence of a threshold center, center and
  potential definitions, Lipschitz certificate, pointwise calibration,
  and exact integral gap. 6 public declarations (4 theorems, 2 definitions).
- `WeilLogShiftRawCouplingIntegrability`: coupling subtype; integrability
  pulled through both marginals; integrable distance cost; test-function
  and dual lower bounds against every coupling; dual<=Wasserstein.
  7 public declarations (6 theorems, 1 definition).
- `WeilLogShiftRawOptimalTransport`: 6 theorem roots,
  `finiteWeilCanonicalRawLipschitzDual_eq_gap`,
  `finiteWeilCanonicalRawWasserstein_eq_gap`,
  `finiteWeilCanonicalRawWasserstein_eq_lipschitzDual`,
  `finiteWeilCanonicalRawCoupling_optimal`,
  `finiteWeilCanonicalRawPotential_attains_dual`, and
  `finiteWeilCanonicalRawGap_le_coupling_cost`.

Native leaf builds exited 0 with empty logs. Native final audit checked
all 19 declarations and 18 API witnesses, with only propext,
Classical.choice, and Quot.sound. Metadata issues: none; fresh objects,
unique declarations, clean source whitespace, 6 direct imports and
5 incoming import edges. All 3 leaves are wired once into the umbrella.
Scoped git diff --check passed. Local lexical index returned all 6 final
roots, including all 4 specifically requested principal roots.

Global formal lint: 10 errors and 367 warnings outside these
three leaves; global gate remains unclean. Exact diagnostics are saved in
`/tmp/hgt-raw-optimal-lint.log`.

Additional corpus audit found the existing
`WeilLogShiftCanonicalIndexTransport.finiteWeilCanonicalCoupling_index_optimal`.
That theorem concerns positive/negative parity profiles and finite adjacent
index cost 1. The present roots concern the centered raw index/correction
probability measures on R and optimize over all measure couplings.

Lean repair: an explicitly typed intermediate integrable absolute-coordinate
difference resolves a function-expression elaboration mismatch before
rewriting `Real.dist_eq`. No heartbeat changes or extra axioms.

Artifacts: `/tmp/hgt-raw-optimal-{api.lean,api.log,prior-search.json,
metadata.py,metadata.json,declarations.json,incoming-imports.txt,
final-audit.lean,final-audit.log,roots-search.json,lint.log,close.py}`;
one `/tmp/hgt-<Leaf>.log` per native build. Only local Lean sources supplied
mathematical evidence. No web, external papers, or numerical computation.
The overarching research goal remains active. Gaussian Wasserstein
convergence and strict positivity for nonzero rank are separate questions.
