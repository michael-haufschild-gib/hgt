# Lean frontier tool

`scripts/formal_tools.py brief` computes research frontier from compiled Lean declarations. It does not read pipeline cards, handovers, route taxonomies, embeddings, or model knowledge.

## Commands

Refresh graph after corpus changes:

```bash
scripts/formal_tools.py brief --area RH --refresh --format json
```

Read cached frontier:

```bash
scripts/formal_tools.py brief --area RH --limit 5
```

Cache: `formal/.lake/hgt-research/rh-frontier.json`. Cache invalidates when any `formal/GaloisForLFunctions/**/*.lean` file or exporter changes.

## Corpus and graph semantics

Generated exporter imports every `.lean` module below `formal/GaloisForLFunctions`, including files temporarily missing from an area umbrella. `RiemannHypothesis` is target, not corpus boundary.

- Named `Prop` binder plus theorem result creates checked implication hyperedge.
- `P ↔ Q` creates two edges.
- Theorem with no proposition premise closes its result.
- Closed `¬P` refutes `P` route.
- Target strongly connected component is reported as equivalent criteria, not frontier work.
- Frontier output is ranked subset-minimal unresolved cuts with checked paths to target.
- Proof-body dependencies never create logical edges.
- Exact proposition expressions, including arguments, are graph keys. Declaration names alone are not identities.

Generic unnamed assumptions are skipped rather than invented as research tasks. Research agents should introduce a named Lean `Prop` interface when an open premise must become machine-visible.

Legacy connectors remain live unless corpus proves their negation or their Lean docstring explicitly marks premise nonviable. Tool reports uncertainty instead of inferring viability from external mathematical priors.
