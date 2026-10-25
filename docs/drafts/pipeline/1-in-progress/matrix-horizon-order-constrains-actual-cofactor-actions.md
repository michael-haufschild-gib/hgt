# Matrix horizon order constrains actual cofactor actions

- **ID:** matrix-horizon-order-constrains-actual-cofactor-actions
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / OPERATOR INVARIANT
- **Parent:** [Q-III](q-iii-escape-state-classification.md)

## Candidate theorem

For every actual common kernel K and positive integers p<=q, the matrix
`p*K(p*j,p*k)-q*K(q*j,q*k)` is positive semidefinite. Equivalently,
`p*D_p^*D_p >= q*D_q^*D_q` as quadratic forms on the actual Hilbert module.
This strengthens numeric antitonicity of `p*K(p,p)`.

## Paper route

For a finite real packet u=sum c_j A(floor(n/j)), the complete-block
identity identifies p times its dilated pronic energy at T with its
energy at floor(T/p), up to a bounded last-fibre error. The error is
bounded by a constant depending only on the packet, so vanishes after
normalization on escape. Integer horizon order compares these packet
energies. Under admission, full pronic pairing limits scale exactly, so
the matrices are equal. Complex packets follow by real and imaginary
parts, and dense packet vectors extend the inequality to the completion.

## Consequences to audit

Every common eigenvector sees a nonnegative, multiplicative, antitone
profile p*|chi(delta_p)|^2. The Archimedean rigidity argument would force
either augmentation modulus or p^(-alpha), alpha>=0. This potentially
classifies the moduli of all finite actual hull characters, not only
rank-one module characters. Establish existence of common eigenvectors
in each nonzero joint generalized eigenspace from the corpus before use.
No phase classification follows: an abstract diagonal unitary action with
arbitrary multiplicative phases still satisfies critical equality.

## Status

Real packet, complex packet and complete-Hilbert operator order passed
canonical checks with standard axioms. The owner
`NumericHorizonOrderControlsTheCofactorAction` is installed and wired;
required olean `68599` and final source-only audit `42266` passed.
Finite-hull consequences still await their own direct verification.

`scaled_packet_antitone` reuses the finite-packet Gram identity.
`scaled_kernelForm_antitone` complexifies it;
`scaled_dilation_norm_sq_antitone` passes to the complete Hilbert module.
All consume the checked mixed horizon error and contracted-pairing limit.
Nearby-dilation continuity is not an assumed analytic input.

## Infinite-dimensional limitation

Do not extend the eigenvector modulus argument to every character of an
infinite module hull. The corpus white-noise shift model has
`p*D_p^*D_p = 1` for every p and still has the whole polydisk as annihilator
hull. Its characters need not be represented by eigenvectors of D_p.
Finite joint generalized eigenspaces supply actual common eigenvectors;
that step is essential and must be proved. Nearby-dilation search found
continuous CCM/log-dilation models but no continuity bridge for actual
Möbius escape modules. Such continuity remains an open input.

## Finite joint-eigenvector bridge

Corpus searches found a two-operator common-eigenvector theorem and joint
generalized eigenspace decomposition, but no arbitrary-family common-vector
lemma. The missing elementary bridge is drafted in
`/tmp/qiii_commuting_family_eigenvector_body.lean`: induct on dimension;
if every operator is scalar, choose any nonzero vector; otherwise restrict
the family to a nonzero proper eigenspace of one nonscalar operator.
Commutativity preserves that space. The bridge is now canonical as
`HTGeometry.exists_common_eigenvector_family` in
`FiniteCommutingFamiliesHaveCommonEigenvectors`. Its required olean and final
source-only audit `15948` passed with standard axioms.

The modulus bridge and finite actual hull application are now drafted in
`/tmp/qiii_eigencharacter_power_body.lean` and
`/tmp/qiii_finite_hull_moduli_body.lean`. The final target is
`finite_moduleHull_modulus_classification`: every finite actual hull point
has augmentation modulus or `|omega(p)|=p^(-alpha)` for one alpha>=0.
No phase claim is included. The operator horizon-order and common-family
eigenvector dependencies are complete. The modulus conclusions remain OPEN
until their own Lean check passes.

The finite-hull scratch now has every required dependency and is under
direct verification. No finite-hull modulus claim is verified yet.
