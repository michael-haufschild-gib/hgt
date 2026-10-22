# Finite-aperture boundary phase locking

- **ID:** `suzuki-finite-aperture-boundary-phase-locking`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED] [UNCONDITIONAL]` for the universal law of Sections 2–5
- **Paper proof:** `./suzuki-finite-aperture-boundary-phase-locking.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiFiniteApertureBoundaryPhaseLocking.lean`
  - `formal/GaloisForLFunctions/HTGeometry/NestedProjectionConvergence.lean`
  - `formal/GaloisForLFunctions/HTGeometry/FiniteRankTransportUnitary.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PolarTransportUnitary.lean`
  - `formal/GaloisForLFunctions/HTGeometry/NestedExhaustionCayleyLimit.lean`
  - `formal/GaloisForLFunctions/HTGeometry/NormalResolventDistance.lean`
  - `formal/GaloisForLFunctions/HTGeometry/StrongResolventSpectralInclusion.lean`

## Formal content

| Card | Lean |
|---|---|
| §3 `(3.1)`, `(3.7)` deficiency-projection convergence | `starProjection_inf_orthogonal_apply`, `starProjection_inf_orthogonal`, `tendsto_deficiency_starProjection` |
| §3 `(3.2)` the projections converge **in operator norm** | `tendsto_opNorm_deficiency_rankOneTransport`, `tendsto_opNorm_comp_of_frame`, `block_eq_comp_of_idempotent`, `norm_sub_le_blocks_of_idempotent` |
| §3 transport at deficiency index one | `lineTransport`, `norm_lineTransport`, `lineTransport_mem_range`, `tendsto_lineTransport`, `rankOneTransport`, `rankOneTransport_self_eq_starProjection`, `tendsto_opNorm_rankOneTransport` |
| §3 general-`k` polar transport | `nearOneWindow`, `spectrum_subset_nearOneWindow`, `invSqrtNearOne`, `isSelfAdjoint_gram`, `norm_gram_sub_one_le`, `polarTransport`, `adjoint_polarTransport_comp_self`, `norm_polarTransport_apply`, `range_polarTransport`, `tendsto_polarTransport`, `tendsto_opNorm_selfComp_sub` |
| §4 embedded Cayley assembly and its convergence | `cayleyAssembly`, `tendsto_cayleyAssembly` |
| §4 base-subtraction converse | `tendsto_boundary_of_tendsto_cayleyAssembly` |
| §4 Cayley resolvent transfer | `cayleyResolvent`, `tendsto_cayleyResolvent` |
| §4 deficiency-one phase-lock equivalence | `tendsto_opNorm_phaseBlock`, `tendsto_phase_of_tendsto_opNorm`, `tendsto_opNorm_apertureBoundaryBlock_iff`, `tendsto_phase_of_tendsto_apertureBoundary` |
| §4 Theorems 4.1 and 4.2 for the aperture chain | `apertureDeficiencyProjection`, `apertureBoundaryBlock`, `globalBoundaryBlock`, `tendsto_apertureTransport`, `tendsto_apertureCayley_of_phaseLock`, `tendsto_apertureResolvent_of_phaseLock` |
| §5 spectral approximation | `isStarNormal_algebraMap_sub`, `norm_inverse_le_of_spectrum_far`, `eventually_norm_sub_smul_lt`, `one_div_lt_norm_resolvent`, `eventually_mem_spectrum_or_norm_resolvent_gt`, `eventually_exists_mem_spectrum_norm_sub_lt` |

## What the equation-level recheck caught

`(3.2)` claims operator-norm convergence of the deficiency projections, not merely norm convergence
of their restrictions to the limit deficiency space.  The first formalization proved only the
weaker statement, and the card's Log records the recheck that found it and the isometry route that
closed it.  The distinction is real: a family of projections whose restrictions converge can still
fail to converge as operators when the ranges move.  `block_eq_comp_of_idempotent` and
`norm_sub_le_blocks_of_idempotent` are the step that upgrades one to the other.

The general-`k` polar factor is the second place where the paper compresses genuine work.  A frame
of approximating vectors need not be orthonormal, so the transport built from it is not unitary; the
fix is the polar correction `G^{-1/2}` where `G` is the Gram operator, whose spectrum lies in a
compact window around `1` once the frame is close enough (`spectrum_subset_nearOneWindow`).  The
inverse square root is then the continuous functional calculus of an explicit function on that
window (`invSqrtNearOne`), and `tendsto_invSqrtNearOne` gives the convergence.

## Hypotheses

A nested exhaustion of closed subspaces of a Hilbert space, a symmetric operator with the stated
deficiency structure, and the convergence hypotheses of §2 — all object data the card quantifies
over.  No hypothesis is a theorem proved elsewhere in the corpus.

No `sorry`, `axiom`, `opaque`, `unsafe`, RH premise, or numerical computation occurs.  Every cited
declaration audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

Section 6 is `[RETRACTED: STABLE DEFICIENCY FAILS]` for the Suzuki source and is in any case
`[PROVED FROM RH]`; it is explicitly out of scope for the Lean gate and is not formalized.  The
card's two remaining unchecked gates — manuscript completion and independent specialist novelty
review — are editorial, not mathematical.
