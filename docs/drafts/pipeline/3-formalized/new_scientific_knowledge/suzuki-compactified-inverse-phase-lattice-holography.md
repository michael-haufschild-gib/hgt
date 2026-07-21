# Formal core of Suzuki compactified inverse-phase lattice holography

- **ID:** `suzuki-compactified-inverse-phase-lattice-holography-formal`
- **Status:** formalized and audited
- **Paper theorem:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki-compactified-inverse-phase-lattice-holography.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiCompactifiedPhaseProfile.lean`
- **RH used:** no
- **Computation used:** no

## Formalized content

For a proper normalized phase order isomorphism `phi : R ≃o R`, the module defines

```text
X(y) = phi⁻¹(pi+y),
U(y) = arctan(X(y)),
y_k = (2k-1)pi.
```

It proves:

- exact phase recovery and lossless finite-pole recovery `tan(U(y))=X(y)`;
- strict monotonicity, centering, oddness, and range `U(y) in (-pi/2,pi/2)`;
- the anchored Cayley phase floor
  `q=2/(1+x²)+q_res`, `q_res>=0` implies `q(1+x²)>=2`;
- exact inverse derivatives
  `X'(y)=q(X(y))⁻¹` and `U'(y)=1/[q(X(y))(1+X(y)²)]`;
- the sharp derivative chamber `0<U'(y)<=1/2`;
- exact fixed-lattice holography: each normalized Donoghue atom equals `2U'(y_k)`;
- transfer of probability normalization to the derivative samples
  `HasSum (fun k => 2U'(y_k)) 1`;
- the global sharp compactness input `LipschitzWith (1/2) U`.

## Source-specific capstones

```text
suzukiAnchoredPhaseSpeed_floor
hasDerivAt_suzukiCenteredInversePhase
hasDerivAt_suzukiCompactifiedInversePhase
deriv_suzukiCompactifiedInversePhase_mem
suzukiPhaseProbabilityMass_eq_two_mul_compactifiedDeriv
suzukiCenteredInversePhase_evenLattice
hasSum_two_mul_suzukiCompactifiedDeriv_one
suzukiCompactifiedInversePhase_lipschitz
```

## Boundary of the formal layer

The paper theorem continues from this formal core with Arzela--Ascoli, diagonal extraction of all
lattice derivative samples, weak compactness on the closed projective interval, and a positive
residual-measure decomposition.  Those measure-topology steps remain on paper because the current
Suzuki Lean interface does not yet construct the aperture-indexed concrete Clark probabilities.
No derivative convergence is inferred from locally uniform convergence: derivative samples are
extracted as independent bounded coordinates.

The surviving frontier is not generic compactness.  It is source-specific residual elimination:
choose an intrinsic cofinal Suzuki schedule, prove total fixed-label mass tends to one, and identify
the resulting lattice values and masses with the Xi/de Branges divisor.

## Audit

- [x] direct `lake env lean GaloisForLFunctions/RHTower/SuzukiCompactifiedPhaseProfile.lean`
- [x] exact `lake build GaloisForLFunctions.RHTower.SuzukiCompactifiedPhaseProfile`
- [x] SOTA import source check
- [x] `#print axioms` capstone audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] global formal lint
- [x] `git diff --check`
