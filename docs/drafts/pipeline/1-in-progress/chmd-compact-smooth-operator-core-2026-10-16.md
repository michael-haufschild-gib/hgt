# CHMD: compact smooth operator core

Status: IN PROGRESS. Unconditional RH remains the goal.

## Verified starting point

The actual arithmetic generator L and stationary pullback generator G are
self-adjoint with the same maximal domain; L-G is bounded. Spatial cutoffs
preserve that domain and give compactly supported graph approximations.
Compact smooth form density alone does not give operator-core density.

## Conjecture

Compact smooth sources form an operator core for both actual generators.
Local regularization after the proved spatial cutoffs should close the missing
weak compact-test domain admission without an additional hypothesis.

## Paper mechanism to audit

Construct the ordinary-volume stationary difference graph for the actual
kernel kappa, and its actual generator A. Translation invariance should make
compact convolution mollifiers commute with A and converge in graph norm.

For compactly supported u in Dom(G), put f=Theta*u. To prove f in Dom(A),
split every stationary form test q by a smooth cutoff chi=1 near supp(f).
The local test chi*q/Theta belongs to the actual ground graph; G's form
identity supplies its pairing. The complementary separated-support pairing
is an ordinary-L2 bounded functional. Riesz representation then gives the
ordinary operator-domain admission of f.

Mollify f, divide the resulting smooth compact functions by positive Theta,
and transfer convergence to the mass space. The mass convergence is local;
generator-image convergence uses bounded Theta/cosh. Finally diagonalize
with the already-proved spatial operator cutoffs.

Do not identify Dom(G) globally with {u:Theta*u in Dom(A)}. The proposed
ordinary-domain admission is only after compact spatial localization.
The existing Gamma-clock generator uses kappa/t and is not A.

## Work plan

1. Audit corpus support and build the correct stationary operator.
2. Establish compact-source transfer into its maximal domain.
3. Prove actual convolution regularization and transfer back to G and L.
4. Verify every finished leaf, all axioms, umbrella wiring, lint, and cleanup.

## Validation

Pending. No smooth operator-core or RH proof claimed yet.
