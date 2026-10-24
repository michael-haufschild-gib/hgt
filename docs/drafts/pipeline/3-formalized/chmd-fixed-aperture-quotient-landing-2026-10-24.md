# CHMD fixed-aperture quotient landing

- **ID:** chmd-fixed-aperture-quotient-landing-2026-10-24
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** At every fixed positive aperture, the real Weil form completion embeds with closed range into the actual CHMD signed-radical quotient, with equivalent norms and exact preservation of the full Weil form.

## Scope and source

The CHMD frontier had left the lower quotient bound and completion landing
open. `CHMDGraphNormIsTheWeilFormNormOnAnAperture` proves equivalence before
quotienting and an upper bound after quotienting. This theorem removes the
remaining completion assumption. It does not prove the signed
form nonnegative, make any constant uniform in aperture, or complete RH.

The preceding conjecture that arbitrary positive shifts would repair the
secondary-ground-state argument is already covered by ACT:
`markovEnergy_phiDoob_shiftedGroundState_eq_twoSided` applies for every positive
shift and retains the full negative prime collar. That conjecture supplies no
missing sign theorem. No external novelty claim or check is made.

## Dependency-closed paper argument

Fix aperture `a>0`. Let `H_a` be the graph-norm closure in the literal CHMD
`SourceGraph` of inverse-Doob lifts of real smooth functions supported strictly
inside `[-a,a]`. Let `K` be `signedRadical`, `P` its graph-orthogonal projection,
and `J` the mass/source coordinate.

1. **Compact mass coordinate on this aperture.** The already proved two-sided
   graph/Weil-form norm comparison identifies `H_a` with the real core closure
   in the CCM archimedean form domain. Its physical L2 embedding is compact by
   `isCompactOperator_ccmArchimedeanFormEmbedding`. On `[-a,a]`, multiplication
   by `1/Theta` from physical L2 to the mass space is bounded: the squared norm
   is `integral |f|^2 cosh(x/2)/Theta(x)`, and its weight has finite maximum on
   that compact interval. Thus `J:H_a -> MassSpace` is compact. The same
   conclusion follows sequentially directly on the smooth core and then on
   its closure; no aperture-uniform compactness is needed.

2. **The critical projection gains the mass norm.** Existing
   `projection_source_orthogonal` and `source_mass_decomposition` give
   `||J Pp|| <= ||Jp||`. Existing `radical_norm_sq` gives
   `||Pp||^2 = 2 ||J Pp||^2 <= 2 ||Jp||^2`. Applied to differences, this shows
   that every sequence whose source coordinates are Cauchy has Cauchy critical
   projections. Hence `P|H_a` is compact.

3. **The compact aperture contains no nonzero full radical.** If `p` lies in
   `H_a cap K`, its physical coordinate `f=Theta*Jp` is an L2 function supported
   in `[-a,a]`. The full radical characterization forces its literal Fourier
   integral to vanish at every Xi zero. The unconditional compact-L2 uniqueness
   theorem `eq_zero_of_supported_fourier_constant_on_xiZeros` gives `f=0`.
   Theta is strictly positive, so `Jp=0`, and injectivity of the graph source
   coordinate gives `p=0`. This is uniqueness for the actual Xi zero set, not
   an RH assumption or a density statement deduced from RH.

4. **Positive angle and lower quotient bound.** If no `c_a>0` satisfies
   `c_a ||p|| <= ||(I-P)p||` on `H_a`, choose unit `p_n` with
   `||(I-P)p_n|| -> 0`. Compactness of `P|H_a` gives a convergent subsequence of
   `Pp_n`; hence the same subsequence of `p_n` converges to a unit `p in H_a`.
   Its reduced component vanishes, so `p in K`, contradicting step 3.
   Since `||[p]||=||(I-P)p||`, this proves the desired lower bound. The upper
   bound is quotient contraction. Combining with the existing core norm
   comparison gives norm equivalence with the real Weil form completion.

5. **Closed landing.** A quotient-Cauchy sequence in the image is graph-Cauchy
   by the lower bound. Completeness of `H_a` supplies a limit in `H_a`, and
   continuity of the quotient map identifies its image with the quotient
   limit. Thus the image is closed and the completion maps onto exactly that
   image with continuous inverse. Density of the original core identifies it
   with the closure of its quotient image.

6. **Preservation of the actual Weil form.** The completed map agrees on the
   common smooth core with the literal inverse-Doob quotient coordinate.
   `suzukiCoreSignedQuotient_weil` identifies its full quotient Weil energy
   with the restricted CCM Weil form, including both polar terms. Both
   quadratic forms are continuous in the norms just compared. Their equality
   therefore extends from the dense real core to every vector of the real
   Weil form completion. Thus the landing preserves the actual signed form,
   rather than merely identifying abstract normed spaces.

All compactness and uniqueness inputs above were located by corpus search and
their statements inspected. Their formal combination and transitive axiom
audit passed. This argument does not bound the whole quotient by a single
aperture or sign its descended Weil form.

## Formal implementation

`formal/GaloisForLFunctions/RHTower/CHMDFixedApertureQuotientLanding.lean`
contains the complete, directly audited proof.

The implementation strengthens step 2 to an exact bounded factorization:
`P = 2 P J* J`, where `J*` is the graph adjoint of the source map. Thus a
convergent source subsequence gives a convergent critical-projection subsequence
directly. A single existing `localThetaInverse N`, with `a <= N+1`, transfers
CCM physical compactness to source compactness. Normalized smooth sources then
give the lower quotient bound, which passes to their graph closure.

The implementation constructs the real form completion explicitly as the closure
of the smooth core in `CCMArchimedeanFormDomain`, and extends the common-core
linear equivalence. Its inverse followed by the actual quotient map is the
claimed completion landing. This is not an assumed completion identification.

Main declarations in namespace `RHTower`:

- `eq_zero_of_signedRadical_of_supported_physicalSource`: no nonzero graph
  radical vector has compactly supported physical source.
- `criticalSourceReconstruction_source`: exact factorization `P = 2 P J* J`.
- `exists_aperture_quotient_lower_bound`: the quotient norm controls the graph
  norm on the entire completed fixed-aperture space.
- `exists_quotient_norm_sq_equiv_weilFormNorm`: two-sided quotient/Weil norm
  comparison on the common real smooth core.
- `apertureGraphWeilEquiv`: canonical continuous linear equivalence of the
  two real core completions, constructed by extension.
- `isClosedEmbedding_apertureWeilSignedQuotient`: actual completed Weil
  domain embeds injectively with closed range in `SignedQuotient`.
- `apertureWeilSignedQuotient_core`: the map is the literal quotient lift
  on the original core.
- `apertureWeilSignedQuotient_weil`: exact full Weil-form preservation on
  the completed domain.

Here the real Weil completion is explicitly the closure of the real Suzuki
core in `CCMArchimedeanFormDomain`. No identification with the stronger
derivative-norm completion is asserted.

Verification:

- The complete `/tmp` proof, including the completed form identity, passed
  `lake --old env lean /tmp/chmd_aperture_proof.lean` with exit 0 and no
  warnings or errors.
- `#print axioms` on physical-source uniqueness, projection factorization,
  quotient/Weil norm comparison, closed completed embedding, exact core
  agreement, and completed Weil-form preservation returned only
  `propext`, `Classical.choice`, and `Quot.sound`.
- The module is imported by `formal/GaloisForLFunctions/RHTower.lean`.
- Final direct repository-leaf check passed with exit 0 and no diagnostics:
  `lake --old env lean GaloisForLFunctions/RHTower/CHMDFixedApertureQuotientLanding.lean`,
  run from `formal/`.
- Scoped whitespace checks passed. No umbrella or full build was run, and
  no olean was produced or replaced.

## Gates

- [x] Exact documented gap and proof mechanism identified.
- [x] Paper argument with all mathematical dependencies identified.
- [x] Lean proof of lower bound, closed completion landing, and full-form preservation.
- [x] Foreground leaf audit and transitive axiom audit.
- [x] Umbrella wiring and accurate frontier update.

## Next conjecture after landing

Use the completed aperture realizations to attack the actual signed form on
increasing apertures. Any continuation estimate must control its negative
part; norm equivalence alone supplies no sign or aperture-uniform estimate.
