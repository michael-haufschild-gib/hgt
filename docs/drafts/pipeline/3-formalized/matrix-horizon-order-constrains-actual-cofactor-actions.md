# Matrix horizon order constrains actual cofactor actions

- **ID:** matrix-horizon-order-constrains-actual-cofactor-actions
- **Stage:** 3-formalized
- **Type:** THEOREM / OPERATOR INVARIANT
- **Parent:** [Q-III](../1-in-progress/q-iii-escape-state-classification.md)

## Theorem

For every actual common kernel K and positive integers p<=q, the matrix
`p*K(p*j,p*k)-q*K(q*j,q*k)` is positive semidefinite. Equivalently,
`p*D_p^*D_p >= q*D_q^*D_q` as quadratic forms on the actual Hilbert module.
This strengthens numeric antitonicity of `p*K(p,p)`.

## Proof mechanism

For a finite real packet u=sum c_j A(floor(n/j)), the complete-block
identity identifies p times its dilated pronic energy at T with its
energy at floor(T/p), up to a bounded last-fibre error. The error is
bounded by a constant depending only on the packet, so vanishes after
normalization on escape. Integer horizon order compares these packet
energies. Under admission, full pronic pairing limits scale exactly, so
the matrices are equal. Complex packets follow by real and imaginary
parts, and dense packet vectors extend the inequality to the completion.

## Eigencharacter consequences

Every common eigenvector sees a nonnegative, multiplicative, antitone
profile p*|chi(delta_p)|^2. Archimedean rigidity forces either augmentation
or |chi(delta_p)|=p^(-s), s>=1/2. Every hull character of a finite-dimensional
actual module occurs on a common eigenvector, so its Bohr modulus is
augmentation or |omega(p)|=p^(-alpha), alpha>=0. This classifies these
magnitudes beyond rank-one modules.
No phase classification follows from these modulus statements. The scalar
calibration below retains every multiplicative unit-norm phase while
satisfying critical equality.

## Formal scalar phase calibration

For any multiplicative phase `eta : positive integers -> C` with
`norm(eta(p))=1`, put `chi(p)=eta(p)/sqrt(p)` and `D_p z=chi(p)z`.
Square-root multiplicativity gives `chi(pq)=chi(p)chi(q)`, hence the action
law. Also `sqrt(p)chi(p)=eta(p)` and
`p*norm(D_p z)^2=norm(z)^2`. This is a scalar calibration, not an actual
Möbius escape realization. The canonical module
`HTGeometry/MultiplicativePhasesPreserveCriticalScalarEnergy` constructs
`criticalScalarCharacter` and proves `criticalScalarCharacter_phase`,
`criticalScalarCharacter_action_mul`, and `criticalScalarCharacter_energy`.
Final source-only audit `69412` passed with four reports containing only
`propext`, `Classical.choice`, `Quot.sound`. Its umbrella import is wired;
no olean is needed. The completed audit is tracked in
[the completion ledger](q-iii-existing-findings-lean-completion.md).

## Status

Real packet, complex packet and complete-Hilbert operator order passed
canonical checks with standard axioms. The owner
`NumericHorizonOrderControlsTheCofactorAction` is installed and wired;
required olean `68599` and final source-only audit `42266` passed.
Finite-hull consequences also passed their final canonical checks below.

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
that step is proved in the finite-hull application. Nearby-dilation search found
continuous CCM/log-dilation models but no continuity bridge for actual
Möbius escape modules. Such continuity remains an open input.

## Finite joint-eigenvector bridge

Corpus searches found a two-operator common-eigenvector theorem and joint
generalized eigenspace decomposition, but no arbitrary-family common-vector
lemma. The elementary bridge inducts on dimension:
if every operator is scalar, choose any nonzero vector; otherwise restrict
the family to a nonzero proper eigenspace of one nonscalar operator.
Commutativity preserves that space. The bridge is now canonical as
`HTGeometry.exists_common_eigenvector_family` in
`FiniteCommutingFamiliesHaveCommonEigenvectors`. Its required olean and final
source-only audit `15948` passed with standard axioms.

`MonotoneCriticalCharacterNormsArePowers` and
`CofactorEigencharacterMagnitudesArePowers` passed final source-only audits
`64788` and `82260`. `FiniteCofactorHullsApproachTheHalfPlaneCurve` passed
final audit `82346`, including `finite_moduleHull_modulus_classification`
and the common eigenvector construction. All transitive axiom reports
contain only `propext`, `Classical.choice`, `Quot.sound`; every leaf is
umbrella-wired. The final half-plane approximation and its scope are on
[the finite-hull card](finite-cofactor-hulls-approach-the-half-plane-curve.md).
