# HCF: resolve individual escaping roots without ramification

Status: conjecture and dependency-closed proof investigation.

## Starting frontier

The previous contribution identifies the complete weighted polynomial X^n Q_(d,k), but gives no individual root branches. A repeated nonzero root would allow fractional-power splitting and obstruct canonical analytic continuation. The task is to remove that obstacle unconditionally for the actual heat family.

## Conjecture loop

1. A determinant multiplicity alone does not determine matrix partial multiplicities; do not infer a full analytic matrix normal form from scalar Toda order.
2. Conjecture: every nonzero root of the escape polynomial is simple. Its coefficients suggest two exact identities: Q_(d+1,k+1)'=(k+1)Q_(d,k), and Q_(d+1,k+1)=(X+d)Q_(d,k)-X Q_(d,k)'. A common root with the derivative would descend inductively to the constant polynomial. The positive constant coefficient excludes zero.
3. Conjecture: these simple roots lift to unique real-analytic scaled root branches of the actual weighted admission. Dividing by t-a gives genuine unramified simple poles, with residues exactly the distinct roots of Q. The full analytic coefficient-vector extension already exists in the corpus.

## Corpus leads

ParametricSpectralBranch supplies an analytic implicit function with germ uniqueness over complex coefficient space. AnalyticAt.restrictScalars composes that universal complex branch with the real-analytic actual coefficient vector. This avoids assuming an analytic complex-time extension or a simple-root hypothesis on actual data.

## Required outcome

An actual-source theorem with only positive time and rank as external inputs, producing the canonical block and a branch for every root of its escape polynomial. Establish nonzero residues, analyticity of the scaled branches, the actual polynomial-root equation on one punctured neighborhood, and uniqueness at the germ level. No estimates, RH receiver, numerical computation, added axiom, heartbeat raise, web search, novelty audit, or old research markdown. Foreground focused builds; direct Lean audits; umbrellas; cleanup.
