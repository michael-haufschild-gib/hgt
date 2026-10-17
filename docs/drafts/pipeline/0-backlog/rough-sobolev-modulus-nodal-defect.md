# Rough Sobolev modulus realization and exact nodal defect

- **ID:** rough-sobolev-modulus-nodal-defect
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Statement:** Construct an actual L² velocity representing the modulus of every
  logarithmic Sobolev state, then prove exact finite mixed-graph nodal decomposition.

## Candidate

For q in physical L² and F(t)=∫₀ᵗq, construct the actual L² class

    q_abs(t)=sign(c+F(t))q(t).

Conjecture the pointwise identity

    |c| + primitive(q_abs,t) = |c+F(t)|,

and equality of local physical Dirichlet energies for q_abs and q. Consequently
the logarithmic state with inputs (q_abs,|c|) is exactly the modulus of the
state with inputs (q,c), with no abstract closure/admission premise.
For every constructed compact-source mixed graph, conjecture

    J(q) = J(q_abs) + nodalEnergy(q,c),
    sourceMass(q_abs,|c|) = sourceMass(q,c).

The existing nodalEnergy definition already includes four times opposite-sign
pairing. This would realize the contraction inside the actual rough-state domain
and identify the precise energy lost at sign changes, while additive Dirichlet
energy stays unchanged.

## Mechanism and boundary

Use absolute continuity and the one-dimensional modulus chain rule. The subtle
input is the zero-level set: q must vanish almost everywhere where c+F=0, so
squaring the sign factor does not lose physical derivative energy there. Prove
that fact, construct MemLp and its representative, and use the fundamental
theorem of calculus; do not replace these obligations by assumptions.

Corpus query `absolute value Sobolev primitive nodal jump decomposition`,
filtered to BiScaleUncertainty, found the discrete and continuous-velocity nodal
algebra, rough primitive absolute continuity, and current mixed-graph nodal
bounds. It found no actual rough L² modulus realization. The search completed
without errors or partial results; semantic coverage is unmeasured and the
coverage snapshot lags the index. Perform a focused deep corpus/mathlib and
parent-theory audit before implementation. No external novelty claim for the
classical Sobolev chain rule or Beurling–Deny contraction.

Not proved or counted.
