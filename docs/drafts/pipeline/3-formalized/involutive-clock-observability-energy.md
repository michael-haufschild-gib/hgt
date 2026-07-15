# Involutive clock observability energy

- **ID:** involutive-clock-observability-energy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [BRIDGE] finite-group twirling, conditional expectations, and Kadison--Schwarz defects
- **Statement:** For an involutive unitary clock, observable twirling is projective pinching, its multiplicativity defect is the master constraint of the erased observable component, the defect vanishes exactly on the clock commutant, and every state reads the defect as one quarter of the squared clock--observable commutator on its clock-shifted vector.

## Goal

Turn the statement that a clock is an observability structure into a positive static value already
native to general HTGeometry. The construction must not introduce a Hamiltonian, evolution
parameter, or zeta-specific carrier.

## Gates

- [x] 0 → 1 in-progress: exact identity, source-pure proof, general consumer identified
- [x] 1 → 2 fully-proven: algebraic proof and Hilbert-space value proof complete
- [x] 2 → 3 formalized: targeted builds, direct checks, and targeted axiom audit are green
- [ ] 3 → 4 publication-ready: standalone theorem note and Lean certificate

## Physics relation

Finite-group twirling is the conditional expectation onto the symmetry commutant. For a
two-element unitary symmetry `U² = 1`, the state average

`P = (1 + U) / 2`

is the invariant-sector projector and `1-P` is the anti-invariant projector. The observable twirl

`Φ_U(X) = (X + U X U) / 2`

is therefore exactly the nonselective two-outcome measurement

`P X P + (1-P) X (1-P)`.

For self-adjoint `X`, its Kadison multiplicativity defect has the state value

`Re <ψ, [Φ_U(X²)-Φ_U(X)²] ψ>
  = ‖(1-P) X P ψ‖² + ‖P X (1-P) ψ‖²`.

The same value is the single disturbance master constraint

`Re <ψ, [Φ_U(X²)-Φ_U(X)²] ψ> = ‖(X-Φ_U(X))ψ‖²`.

The erased component itself is the static operator identity

`X-Φ_U(X) = (1/2) [X,U] U`.

Consequently, for every state `ψ`, not only stationary states,

`Re <ψ, [Φ_U(X²)-Φ_U(X)²] ψ> = (1/4) ‖[X,U](Uψ)‖²`.

If `Uψ=ψ`, then

`Re <ψ, [Φ_U(X²)-Φ_U(X)²] ψ> = (1/4) ‖[X,U]ψ‖²`.

At operator level,

`Φ_U(X²)-Φ_U(X)² = 0  ⟺  U X = X U`.

At state level, the defect value is zero exactly when `[X,U](Uψ)=0`; on a stationary state
this is exactly `[X,U]ψ=0`.

Thus clock observability is exactly cross-sector transition energy, erased-observable energy, and
stationary commutator energy in three interchangeable coordinates. Positivity is automatic.

Primary provenance:

- R. V. Kadison, *A generalized Schwarz inequality and algebraic invariants for operator algebras*, Ann. Math. 56 (1952), 494--503.
- J. Helsen et al., *Real Randomized Benchmarking*, arXiv:1801.06121, for finite-group twirling as the orthogonal projection onto the commutant.
- P. A. Höhn, A. R. H. Smith, and M. P. E. Lock, *The Trinity of Relational Quantum Dynamics*, arXiv:1912.00033, for group-averaged relational observables and physical conditional values.
- A.-C. de la Hamette, S. L. Ludescher, and M. P. Mueller, *Entanglement-asymmetry correspondence for internal quantum reference frames*, arXiv:2112.00046, for observability/asymmetry arising conditionally from a globally invariant state.
- K. Jensen, S. Raju, and A. J. Speranza, *Holographic observers for time-band algebras*, arXiv:2412.21185, for the observer algebra being characterized by a coarse-grained commutant.  The exact defect-to-commutant detector above is a finite involutive bridge, not a claim from that paper.

## Corpus application

General declarations in
`formal/GaloisForLFunctions/HTGeometry/TwoOutcomePinchingKadison.lean`:

- `finiteInvolutiveGaugeAverage_apply`
- `finiteInvolutiveObservableTwirl_eq_symmetrizer`
- `sub_finiteInvolutiveObservableTwirl_eq_half_commutator_mul`
- `twoOutcomePinching_finiteInvolutiveGaugeAverage_eq_observableTwirl`
- `finiteInvolutiveObservableTwirlKadisonDefect`
- `finiteInvolutiveObservableTwirlKadisonDefect_eq_pinching`
- `re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_transitionNormSq_add`
- `sub_twoOutcomePinching_eq_transition_sum`
- `twoOutcomePinchingKadisonDefect_eq_disturbanceMasterProduct`
- `twoOutcomePinchingKadisonDefect_eq_quantumMasterConstraint_disturbance`
- `re_inner_twoOutcomePinchingKadisonDefect_eq_disturbanceNormSq`
- `finiteInvolutiveObservableTwirlKadisonDefect_eq_quantumMasterConstraint_disturbance`
- `finiteInvolutiveObservableTwirlKadisonDefect_eq_zero_iff_commutes`
- `re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_disturbanceNormSq`
- `re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_quarter_commutatorNormSq_shifted`
- `re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_zero_iff_commutator_shifted`
- `re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_quarter_commutatorNormSq_of_fixed`
- `re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_zero_iff_commutator_of_fixed`
- `re_inner_finiteInvolutiveObservableTwirlKadisonDefect_nonneg`

This reuses the existing two-outcome pinching and quantum-master-constraint surfaces instead of
adding an independent positivity theory for clocks.

The direct logarithmic Sonin consumer in
`formal/GaloisForLFunctions/RHTower/SoninLogCoordinateScattering.lean` is:

- `soninLogFourierObservableTwirlKadisonDefect`
- `soninLogFourierObservableTwirlKadisonDefect_eq_zero_iff_commutes`
- `re_inner_soninLogFourierObservableTwirlKadisonDefect_eq_transitionNormSq_add`
- `re_inner_soninLogFourierObservableTwirlKadisonDefect_eq_quarter_commutatorNormSq`
- `re_inner_soninLogFourierObservableTwirlKadisonDefect_eq_zero_iff_commutator`

It identifies the observable content rejected by the Sonin scattering clock with transitions
across the existing physical/nonphysical scattering split.

## Verification boundary

- `lake build +GaloisForLFunctions.HTGeometry.TwoOutcomePinchingKadison` passed.
- `lake build +GaloisForLFunctions.RHTower.SoninLogCoordinateScattering` passed after its cached interface became stale.
- `lake env lean GaloisForLFunctions/HTGeometry/TwoOutcomePinchingKadison.lean` passed.
- `lake env lean GaloisForLFunctions/RHTower/SoninLogCoordinateScattering.lean` passed.
- Targeted `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for the new general and Sonin declarations.
- No full build, concurrent Lean process, numerical experiment, or broad lint was run.
