# Hawking/Teukolsky frequency-lattice critical barycenter (2026-08-24)

Extends `mem:research/hawking_teukolsky_single_sector_frequency_support_no_go_2026_08_24`.

## Exact new laws
Write each positive BM QNM or its real-field partner with imaginary frequency
[
y_j-D_{n_j},qquad D_n=2n+3/2,qquad 0<y_j<1/2
]
at an Xi divisor. A negative-branch target has imaginary frequency (-y_0-D_{n_0}).

### Quadratic all-sector no-go
Frequency matching for any two Xi-sector inputs would imply
[
y_0+y_1+y_2=D_{n_1}+D_{n_2}-D_{n_0}
=3/2+2(n_1+n_2-n_0).
]
Left side is strictly in ((0,3/2)); right side lies in (3/2+2\mathbb Z). Impossible. Therefore full second-order Teukolsky source cannot drive any negative-branch Xi QNM from positive-branch Xi QNMs alone, even with arbitrary sector mixing and either real-field Fourier sign.

### Cubic classification
For three Xi-sector inputs, matching implies
[
y_0+y_1+y_2+y_3=3+2(n_1+n_2+n_3-n_0).
]
Left side lies in ((0,2)), so necessarily
[
n_0=n_1+n_2+n_3+1,qquad y_0+y_1+y_2+y_3=1.
]
Since (y_j=(1-Re\rho_j)/2), cubic branch return forces
[
sum_{j=0}^3Re\rho_j=2.
]
This is a critical-barycenter law. It permits reflection-balanced tilted quartets, so it is not RH by itself; it proves actual nonlinear return must be four-sector balanced rather than sector-local.

## Formalized
Same file:
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskySingleSectorFrequencyNoGo.lean`

New main declarations:
- `d4QuadraticDecayMatch_impossible`
- `d4CubicDecayMatch_classification`
- `d4BMQuadraticOutputFrequency_ne_qnmMinus_xi`
- `d4BMCubicOutputFrequency_eq_qnmMinus_xi_forces_criticalBarycenter`

Verification:
- direct leaf compile passed without warnings;
- new declarations' axioms: only `propext`, `Classical.choice`, `Quot.sound`;
- task-local lint clean and module reachable from `RHTower.lean`;
- global lint still reports unrelated existing unreachable `GaloisForLFunctions.HTGeometry.SecondOrderConstraintDescent`.
- no git; scratch files deleted.

## Interpretation correction
Existing AIME inverse-Jost formula proves meromorphic pole/residue, not Fourier-support incidence from a single seed. Second-order source is ruled out as that incidence. First possible pure-QNM mechanism is cubic balanced quartet with overtone step.