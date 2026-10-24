# CHMD fixed-aperture quotient landing

- **ID:** chmd-fixed-aperture-quotient-landing-2026-10-24
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper; formalization pending)
- **Statement:** At every fixed positive aperture, the real Weil form completion embeds with closed range into the actual CHMD signed-radical quotient, with equivalent norms.

## Scope and source

The CHMD frontier explicitly leaves the lower quotient bound and completion
landing open. `CHMDGraphNormIsTheWeilFormNormOnAnAperture` proves equivalence
before quotienting and an upper bound after quotienting. The proposed theorem
removes this remaining completion assumption. It does not prove the signed
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

All compactness and uniqueness inputs above were located by corpus search and
their statements inspected. Their formal combination and transitive axiom
audit remain pending. This argument does not bound the whole quotient by a
single aperture or sign its descended Weil form.

## Gates

- [x] Exact documented gap and proof mechanism identified.
- [x] Paper argument with all mathematical dependencies identified.
- [ ] Lean proof of lower bound and closed completion landing.
- [ ] Foreground leaf audit and transitive axiom audit.
- [ ] Umbrella wiring and accurate frontier update.

## Next conjecture after landing

Use the completed aperture realizations to attack the actual signed form on
increasing apertures. Any continuation estimate must control its negative
part; norm equivalence alone supplies no sign or aperture-uniform estimate.
