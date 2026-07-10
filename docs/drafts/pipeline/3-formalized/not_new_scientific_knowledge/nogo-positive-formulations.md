# No-go positive formulations

- **ID:** nogo-positive-formulations
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** `../2-fully-proven/not-new/orthogonality-meta-theorem.md`;
  `../../rh-monodromy-weight-mismatch/105-landau-shadow-no-go.md`;
  `../../rh-monodromy-weight-mismatch/106-joint-reading-no-go.md`
- **Statement:** The Landau, joint-symmetry, and pinned sigma-source no-go theorems can be repackaged as
  positive Lean statements: parity shadows select their involution fixed loci; the RH-bearing shadow is the
  FE critical-line reflection; odd strip zeros activate finite Euler-Maclaurin certificates; and pinned
  prime-local sigma sources are exhausted.

## Goal
This banks the reusable positive interfaces left by the no-go results.  The module does not claim RH, DSS,
or a new native C5 theorem.  It turns route-kill theorems into constructive theorem APIs for later work:
axis selection, FE fixed-locus reading, finite certificate activation, and pinned sigma-source exhaustion.

## Lean Theorems
- `RHTower.involution_fixed_locus_parity`
- `RHTower.landau_shadow_selects_real_axis`
- `RHTower.fe_shadow_selects_critical_line`
- `RHTower.landau_fe_axis_separation`
- `RHTower.xi_landau_shadow_trivial_on_off_real_closed_set`
- `RHTower.xi_landau_order_sum_even_on_off_real_closed_set`
- `RHTower.lineReflection_half_fixed_iff`
- `RHTower.pinned_joint_symmetry_two_torsion`
- `RHTower.pinned_joint_symmetry_order_bounded`
- `RHTower.pinned_joint_symmetry_preserves_three_divisor_readings`
- `RHTower.rh_ladder_one_even_order_positive`
- `RHTower.odd_strip_zero_activates_em_certificate`
- `RHTower.odd_strip_zero_activates_mirror_em_certificates`
- `RHTower.odd_strip_zero_certificate_and_prime_invisibility`
- `RHTower.pinned_sigma_sources_exhausted_positive`
- `RHTower.additive_carrier_multiplicative_source_mismatch_positive`

## Gates
- [x] 0 -> 1  in-progress: building blocks checked in `LandauShadowNoGo`, `MirrorTransport`,
  `JointReadingNoGo`, `CertificateActivation`, `PrimeDivisorAtomsNoGo`, and `SigmaDivisorExhaustion`.
- [x] 1 -> 2  fully-proven: paper content is inherited from the existing no-go and certificate theorems.
- [x] 2 -> 3  formalized: Lean module
  `formal/GaloisForLFunctions/RHTower/NoGoPositiveFormulations.lean`; target build
  `lake build GaloisForLFunctions.RHTower.NoGoPositiveFormulations` passed; representative scratch
  `#print axioms` returned only `[propext, Classical.choice, Quot.sound]`.
- [ ] 3 -> 4  publication-ready: fold into the RHTower narrative as "no-go results as positive theorem APIs";
  next useful theorem is a nonlocal/global seam object escaping finite prime-local pinned exhaustion.

## Door Grade
BRIDGE (substrate).  Door-2 strips each theorem to finite involution parity, FE reflection, finite Euler
unit facts, or the existing Euler-Maclaurin certificate.  The value is interface consolidation: later work
can cite positive APIs instead of reusing the no-go modules by name.

## Log
- 2026-07-09 - Added `NoGoPositiveFormulations.lean`, appended its umbrella import to
  `formal/GaloisForLFunctions/RHTower.lean`, built the new module, and checked representative axioms.
