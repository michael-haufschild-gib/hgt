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

Let J:u -> Theta*u from the mass Hilbert space to ordinary L2. Let W_n be
the bounded local inverse f -> chi_n*f/Theta. Then J W_n=M_n, and W_n J is
the mass cutoff. The actual first Levy moment supplies the bounded ordinary
commutator C_n=[A,M_n] through endpoint pullbacks and their adjoints.

For compactly supported u in Dom(G), choose n with the mass cutoff fixing u.
Writing f=J u, the complete form identity becomes
E(f,q)=<W_n* G u + C_n f,q>. Thus f belongs to Dom(A), with the displayed
actual generator image. This avoids an independent far-field kernel lemma.
Conversely, f=J u in Dom(A) gives u in Dom(G) and G u=J* A f, by testing
against the complete ground graph and Riesz uniqueness.

Take u_j=W_n S_j f, where S_j is the Bochner mollifier average. Then
J u_j=M_n S_j f is in Dom(A). The exact commutator gives convergence of
A M_n S_j f to A f. Boundedness of W_n and J* gives graph convergence in
the mass space. Each u_j has the compact C2 representative
chi_n * (rho_j*f) / Theta. Finally diagonalize with the already-proved
spatial operator cutoffs. A common support bound for all mollifiers is not
needed because the fixed outer cutoff is part of W_n.

Do not identify Dom(G) globally with {u:Theta*u in Dom(A)}. The proposed
ordinary-domain admission is only after compact spatial localization.
The existing Gamma-clock generator uses kappa/t and is not A.

## Work plan

1. Audit corpus support and build the correct stationary operator.
2. Establish compact-source transfer into its maximal domain.
3. Prove actual convolution regularization and transfer back to G and L.
4. Verify every finished leaf, all axioms, umbrella wiring, lint, and cleanup.

## Validation

Verified targeted builds: correct ordinary-volume generator; translation
covariance of its literal graph and resolvent; strong Bochner mollification
preserving its operator domain and both graph coordinates. Representative
identification needed one missing explicit corpus import; recheck running.
Local inverse and first-moment commutator leaves drafted, not yet verified.
No smooth operator-core or RH proof claimed yet.
