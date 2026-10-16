# CHMD: compact smooth operator core

Status: FORMALISED IN LEAN 4. Unconditional RH remains the goal.

## Verified starting point

The actual arithmetic generator L and stationary pullback generator G are
self-adjoint with the same maximal domain; L-G is bounded. Spatial cutoffs
preserve that domain and give compactly supported graph approximations.
Compact smooth form density alone does not give operator-core density.

## Theorem

Compact C2 sources form an operator core for both actual generators. Every
maximal-domain vector is the limit of compact C2 domain vectors, with their
actual generator images converging as well. Equivalently, each full operator
graph is the closure of its compact C2 part. No extra domain hypothesis is
used in these conclusions.

## Dependency-closed paper proof

Construct the ordinary-volume stationary difference graph for the actual
kernel kappa, and its actual generator A. The source projection is injective
and has dense range, so its product with its adjoint is an injective positive
self-adjoint resolvent. The inverse resolvent minus identity gives A.

Translation preserves the literal source and edge graph, since the edge
measure is the product of kappa(t) dt on t>0 and Lebesgue measure in x.
Riesz uniqueness makes the resolvent commute with translations. Strong
continuity on ordinary L2 makes the Bochner mollifier averages S_j converge
strongly to identity. Passing the bounded resolvent through the integrals
shows S_j Dom(A) lies in Dom(A), with A S_j f=S_j A f. Fubini, dominated by
products of the mollifier and the two input squares, identifies these
averages with literal smooth convolutions for arbitrary L2 inputs.

Let J:u -> Theta*u from the mass Hilbert space to ordinary L2. Let W_n be
the bounded local inverse f -> chi_n*f/Theta. Then J W_n=M_n, and W_n J is
the mass cutoff. The actual first Levy moment supplies the bounded ordinary
commutator C_n=[A,M_n] through endpoint pullbacks and their adjoints.
Specifically, on the first-moment edge space, let E_l,E_r be the bounded
endpoint pullbacks and let B_n multiply by
(chi_n(x)-chi_n(x+t))/t. Then
C_n=E_l* B_n E_r-E_r* B_n E_l, and direct expansion gives
E(M_n f,q)-E(f,M_n q)=<C_n f,q> on the entire closed form domain.

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

Do not identify Dom(G) globally with {u:Theta*u in Dom(A)}. The forward
ordinary-domain admission is proved after compact spatial localization.
The existing Gamma-clock generator uses kappa/t and is not A.

## Completed workflow

1. Audit corpus support and build the correct stationary operator.
2. Establish compact-source transfer into its maximal domain.
3. Prove actual convolution regularization and transfer back to G and L.
4. Verify every finished leaf, all axioms, umbrella wiring, lint, and cleanup.

## Validation

Verified targeted builds: correct ordinary-volume generator; translation
covariance of its literal graph and resolvent; strong Bochner mollification
preserving its operator domain and both graph coordinates; literal smooth
convolution representatives for arbitrary L2 inputs; exact ordinary cutoff
commutator; bounded theta transform and local inverse; complete-form local
operator-domain transfer in both directions; local compact C2 graph-norm
approximation in the actual mass space.

The capstone targeted `lake --old build` passed. Nine new leaves, containing
143 declarations in 1206 lines, are wired once into RHTower. Final
`lake env lean <file>` checks passed with empty logs for all nine new leaves,
both generalized existing helper modules, and the prior compact-support core
(12 files). The all-declaration `#print axioms` audit passed for all 182
declarations in the nine new and two generalized modules; only `propext`,
`Classical.choice`, and `Quot.sound` occur. Mathlib API probes passed.
The checked source hashes were unchanged at the end of the audit. All 28
owned scratch files were removed after the audit process exited successfully.
Global lint exited 1 on five unrelated unwired leaves:
CHMDLevySymbolLowerBound, CHMDWindowFourierTail,
PaperThetaNativeArithmeticResolvent, PaperThetaNativeQuantileDomain,
WeilCutEvenMeanZeroDeficit. No defect was reported in this contribution.
No full or umbrella build, heartbeat increase, web search, numerical
experiment, commit, or push was performed. No RH proof claimed.

## Lean capstone

`formal/GaloisForLFunctions/RHTower/CHMDCompactSmoothOperatorCore.lean`:

- `stationaryGenerator_compact_smooth_graph_closure`
- `stationaryGenerator_compact_smooth_core`
- `arithmeticGenerator_compact_smooth_core`
- `arithmeticGenerator_compact_smooth_graph_closure`

Local domain transfer is in `CHMDStationaryLocalOperatorDomain.lean`, notably
`localized_theta_mem_volume_domain`, `stationary_of_volume_mem_domain`, and
`stationary_of_volume_apply`. Local graph convergence is
`localStationarySmooth_tendsto` in `CHMDStationaryLocalSmoothCore.lean`.

## Exact contribution and frontier

The previous result only gave compactly supported operator approximants.
Compact C2 form density did not imply density in the operator graph norm.
The new local transfer proves the missing maximal-domain compatibility with
ordinary convolution. In particular, theta need not have a bounded global
inverse: local inverses, their adjoints, and the exact bounded commutator
close the argument on the full form domains.

This is an unconditional operator-core theorem for the actual CHMD generators,
not a spectral positivity or RH theorem. The critical signed-form sign and
the primal cardinal synthesis problem are not resolved by this result.
