# HCF: resolve individual escaping roots without ramification

Status: formalized; all focused builds, direct source audits and axiom/API audits passed. Repository-wide lint reports unrelated concurrent umbrella omissions, listed below.

## Starting frontier

The previous contribution identifies the complete weighted polynomial X^n Q_(d,k), but gives no individual root branches. A repeated nonzero root would allow fractional-power splitting and obstruct canonical analytic continuation. The task is to remove that obstacle unconditionally for the actual heat family.

## Conjecture loop

1. A determinant multiplicity alone does not determine matrix partial multiplicities; do not infer a full analytic matrix normal form from scalar Toda order.
2. Conjecture: every nonzero root of the escape polynomial is simple. Its coefficients suggest two exact identities: Q_(d+1,k+1)'=(k+1)Q_(d,k), and Q_(d+1,k+1)=(X+d)Q_(d,k)-X Q_(d,k)'. A common root with the derivative would descend inductively to the constant polynomial. The positive constant coefficient excludes zero.
3. Conjecture: these simple roots lift to unique real-analytic scaled root branches of the actual weighted admission. Dividing by t-a gives genuine unramified simple poles, with residues exactly the distinct roots of Q. The full analytic coefficient-vector extension already exists in the corpus.
4. The recurrence and induction proofs passed direct Lean checking. The coefficient-space implicit branch, scalar restriction, punctured-germ uniqueness and exact meromorphic order −1 also passed direct checking. No analytic complex-time extension is assumed.
5. The all-time actual-source construction passed `lake env lean`. The finite residue set has exactly k elements; choosing its branches and intersecting finitely many neighborhoods proves simultaneous actual-root equations and injectivity on one punctured neighborhood. All three focused `lake --old build +Module:olean` builds passed.

## Formal artifacts

- `formal/GaloisForLFunctions/HTGeometry/HeatEscapeSimpleRoots.lean`: derivative/raising recurrences, nonzero simple residues, separability, exact root count, and weighted root transport.
- `formal/GaloisForLFunctions/HTGeometry/AnalyticMonicRootGerm.lean`: coefficient-space implicit branch pulled back to real analytic coefficients, uniqueness against punctured continuous root germs, and exact simple-pole order.
- `formal/GaloisForLFunctions/RHTower/XiGaussianHeatEscapingBranches.lean`: actual-source `HeatAdmissionEscapingBranch`, branch separation, `hcf_heat_admission_unramified_branches`, and simultaneous `hcf_heat_admission_escape_packet`. Both capstones take only positive time and rank.

All three modules are wired into their theorem-area umbrellas. The frontier map records the new unramified-branch result.

## Audit record

All three final source files passed direct audits, each run alone in the foreground:

```text
lake env lean GaloisForLFunctions/HTGeometry/HeatEscapeSimpleRoots.lean
lake env lean GaloisForLFunctions/HTGeometry/AnalyticMonicRootGerm.lean
lake env lean GaloisForLFunctions/RHTower/XiGaussianHeatEscapingBranches.lean
```

Each module also passed its focused `lake --old build +Module:olean`. No full or umbrella build ran. A `/tmp` scratch audit checked 57 mathlib API names and printed axioms for 15 new theorems, including both actual-source capstones. Every axiom list was exactly `[propext, Classical.choice, Quot.sound]`; there were no audit errors or warnings. No numerical experiments, extra axioms, admissions, heartbeat/recursion increases or web/novelty searches were used. Owned scratch sources, search outputs and build logs were removed after recording results.

`scripts/formal_tools.py lint` ran after wiring. No HCF error was reported. The repository-wide gate failed on eight unrelated concurrent RHTower umbrella omissions: `CHMDStationaryGenerators`, `CHMDStationaryGroundDomain`, `CHMDStationaryGroundEquivalence`, `CHMDStationaryGroundGraph`, `CHMDStationaryGroundPotential`, `CHMDStationaryOperatorDomain`, `OddWeilLineKernel`, and `OddWeilSpectralMeasure`. These lie outside this task's write scope.

## Closed paper argument

At a common root of Q_(d+1,k+1) and its derivative, the derivative recurrence forces Q_(d,k)=0. Its constant coefficient excludes the zero root. The raising recurrence then forces Q_(d,k)'=0. Induction on k terminates at Q_(d,0)=1. Thus Q_(d,k) is separable for k<d and has exactly k distinct complex roots, all nonzero.

Write W_t(X)=(t-a)^N P_N(t,X/(t-a)). Its analytic coefficient extension at a is X^n Q_(d,k). Each root z of Q is simple in this whole limit, since z≠0. Apply the holomorphic implicit-function theorem in the space of all monic complex coefficient vectors, then restrict scalars and compose with the actual real-analytic coefficient vector. This gives an analytic scaled root r with r(a)=z. The original admission root is r(t)/(t-a), of exact meromorphic order −1. Local pointwise implicit-function uniqueness pulls back to uniqueness against any continuous scaled admission-root germ. Distinct residues separate the actual branches near the contact.

This resolves ramification and individual root trajectories at infinity. It does not select the global no-transition/source-sign branch.

## Corpus leads

ParametricSpectralBranch supplies an analytic implicit function with germ uniqueness over complex coefficient space. AnalyticAt.restrictScalars composes that universal complex branch with the real-analytic actual coefficient vector. This avoids assuming an analytic complex-time extension or a simple-root hypothesis on actual data.

## Required outcome

An actual-source theorem with only positive time and rank as external inputs, producing the canonical block and a branch for every root of its escape polynomial. Establish nonzero residues, analyticity of the scaled branches, the actual polynomial-root equation on one punctured neighborhood, and uniqueness at the germ level. No estimates, RH receiver, numerical computation, added axiom, heartbeat raise, web search, novelty audit, or old research markdown. Foreground focused builds; direct Lean audits; umbrellas; cleanup.
