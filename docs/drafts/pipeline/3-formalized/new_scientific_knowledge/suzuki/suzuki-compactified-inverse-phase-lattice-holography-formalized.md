# Suzuki compactified inverse-phase lattice holography — Lean certificate

- **ID:** `suzuki-compactified-inverse-phase-lattice-holography-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-compactified-inverse-phase-lattice-holography.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/ClockPotentialAlgebra.lean`
- `formal/GaloisForLFunctions/HTGeometry/LabelledAtomicMeasure.lean`
- `formal/GaloisForLFunctions/HTGeometry/PointwiseLimitClass.lean`
- `formal/GaloisForLFunctions/HTGeometry/ScheffeCounting.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiCayleyPhaseLift.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiCompactifiedPhaseProfile.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiDonoghueHerglotzTransform.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.ClockPotentialAlgebra`:

```text
GaloisForLFunctions.HTGeometry.BoundedC1Potential.sub
```

`GaloisForLFunctions.HTGeometry.LabelledAtomicMeasure`:

```text
GaloisForLFunctions.HTGeometry.coalescence_not_injective
GaloisForLFunctions.HTGeometry.integral_labelledMeasure
GaloisForLFunctions.HTGeometry.labelledMeasure
GaloisForLFunctions.HTGeometry.labelledMeasure_univ
GaloisForLFunctions.HTGeometry.labelled_add_residual
GaloisForLFunctions.HTGeometry.residual_eq_zero_iff
GaloisForLFunctions.HTGeometry.residual_univ_eq
GaloisForLFunctions.HTGeometry.tight_criterion_failure_iff
GaloisForLFunctions.HTGeometry.two_defects_independent
```

`GaloisForLFunctions.HTGeometry.PointwiseLimitClass`:

```text
GaloisForLFunctions.HTGeometry.exists_subseq_tendsto_joint
GaloisForLFunctions.HTGeometry.exists_subseq_tendsto_of_equiLipschitz
GaloisForLFunctions.HTGeometry.exists_subseq_tendsto_of_mem_Icc
GaloisForLFunctions.HTGeometry.limitClass_of_tendsto
GaloisForLFunctions.HTGeometry.lipschitzBound_of_tendsto
GaloisForLFunctions.HTGeometry.mem_Icc_of_tendsto
GaloisForLFunctions.HTGeometry.monotone_of_tendsto
GaloisForLFunctions.HTGeometry.odd_of_tendsto
```

`GaloisForLFunctions.HTGeometry.ScheffeCounting`:

```text
GaloisForLFunctions.HTGeometry.abs_tsum_mul_le
GaloisForLFunctions.HTGeometry.exists_finset_eventually_tsum_compl_lt
GaloisForLFunctions.HTGeometry.exists_finset_tail_bounds
GaloisForLFunctions.HTGeometry.exists_finset_tsum_compl_lt
GaloisForLFunctions.HTGeometry.summable_abs_sub
GaloisForLFunctions.HTGeometry.tendsto_tsum_abs_sub_of_tendsto
GaloisForLFunctions.HTGeometry.tendsto_tsum_mul_comp_of_tendsto
GaloisForLFunctions.HTGeometry.tendsto_tsum_posPart_of_tendsto
```

`GaloisForLFunctions.RHTower.SuzukiCayleyPhaseLift`:

```text
GaloisForLFunctions.RHTower.cayleyPhaseLift_half_sub
GaloisForLFunctions.RHTower.cayleyPhaseLift_reflection_of_odd
GaloisForLFunctions.RHTower.cayleyPhaseLift_zero_of_odd
GaloisForLFunctions.RHTower.neg_cot_half_cayleyPhaseLift
```

`GaloisForLFunctions.RHTower.SuzukiCompactifiedPhaseProfile`:

```text
GaloisForLFunctions.RHTower.hasDerivAt_suzukiCenteredInversePhase
GaloisForLFunctions.RHTower.hasDerivAt_suzukiCompactifiedInversePhase
GaloisForLFunctions.RHTower.hasSum_two_mul_suzukiCompactifiedDeriv_one
GaloisForLFunctions.RHTower.orderIso_zero_of_reflection
GaloisForLFunctions.RHTower.suzukiAnchoredPhaseSpeed_floor
GaloisForLFunctions.RHTower.suzukiCenteredInversePhase
GaloisForLFunctions.RHTower.suzukiCenteredInversePhase_phase
GaloisForLFunctions.RHTower.suzukiCompactifiedInversePhase
GaloisForLFunctions.RHTower.suzukiCompactifiedInversePhase_lipschitz
GaloisForLFunctions.RHTower.suzukiCompactifiedInversePhase_mem_Ioo
GaloisForLFunctions.RHTower.suzukiCompactifiedInversePhase_neg
GaloisForLFunctions.RHTower.suzukiCompactifiedInversePhase_speed_mem
GaloisForLFunctions.RHTower.suzukiCompactifiedInversePhase_zero
GaloisForLFunctions.RHTower.suzukiCompactifiedInversePhase_zero_of_reflection
GaloisForLFunctions.RHTower.suzukiDonoghueAtom_eq
GaloisForLFunctions.RHTower.suzukiPhaseProbabilityMass_eq_two_mul_compactifiedDeriv
GaloisForLFunctions.RHTower.suzukiPhaseProbabilityMass_eq_two_mul_compactifiedDeriv_of_clarkAtom
GaloisForLFunctions.RHTower.tan_suzukiCompactifiedInversePhase
```

`GaloisForLFunctions.RHTower.SuzukiDonoghueHerglotzTransform`:

```text
GaloisForLFunctions.RHTower.cayleyOfHerglotz_I
GaloisForLFunctions.RHTower.cayleyOfHerglotz_herglotzOfCayley
GaloisForLFunctions.RHTower.cayleyOfHerglotz_ne_one
GaloisForLFunctions.RHTower.herglotzOfCayley
GaloisForLFunctions.RHTower.herglotzOfCayley_cayleyOfHerglotz
GaloisForLFunctions.RHTower.herglotzOfCayley_zero
GaloisForLFunctions.RHTower.im_herglotzOfCayley
GaloisForLFunctions.RHTower.im_herglotzOfCayley_pos
GaloisForLFunctions.RHTower.norm_le_norm_cayleyOfHerglotz_of_mapsTo
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 57 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- 3 -> 4 publication-ready: standalone paper, specialist priority review
- source proof that the cofinal residual vanishes
- Xi divisor identification
- RH

These are research frontier items, not formalization debt.

---

## Earlier certificate (merged from the flat stage-3 companion)

# Formal core of Suzuki compactified inverse-phase lattice holography

- **ID:** `suzuki-compactified-inverse-phase-lattice-holography-formal`
- **Status:** formalized and audited
- **Paper theorem:**
  `./suzuki-compactified-inverse-phase-lattice-holography.md`
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
