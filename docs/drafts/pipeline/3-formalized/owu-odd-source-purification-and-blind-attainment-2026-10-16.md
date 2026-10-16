# OWU: odd source purification and blind attainment

Status: FORMALIZED. Exact odd smooth-source scalarization,
integer samples, all weighted Weil energies, fixed-aperture purification,
energy completion, and blind attainment have passed Lean. All 37 public
declarations pass the axiom audit. Global lint is blocked by unrelated
concurrent work described below. Cut removal is not proved.

## Contribution

The odd source problem has no finite-mixture rank defect and no normalized
finite-energy limit-realization defect at fixed aperture. Every positive finite
smooth odd mixture is one smooth odd autocorrelation in the same interval.
Every pointwise limit of such normalized, energy-budgeted mixtures has one
actual odd source in the complete Weil form domain at that aperture. Every
positive aperture has an actual normalized arithmetic-blind odd minimizer.

This removes a source-realization obstruction rather than adding a positivity
receiver. Feasibility, factorization, support preservation, compactness, and
attainment are proved. No sign of the minimum is assumed or concluded.

## Objective and constraints

Prove one structural result removing a hard OWU obstruction. No improved bound,
new RH equivalence, conditional receiver, numerical experiment, external search,
or external novelty audit. Use the Lean corpus as mathematical evidence. Preserve
pre-existing workspace edits. Final proofs must introduce no unproved premises,
new axioms, computation certificates, or heartbeat increases.

## Plan

1. Inspect OWU's current Lean frontier and search the entire indexed corpus.
2. Form and attack competing structural conjectures; record failures and pivots.
3. Complete a dependency-closed mathematical proof before formalization.
4. Verify new declarations in Lean, wire leaf modules into RHTower, audit axioms,
   run formal lint, and remove owned scratch artifacts. No umbrella/full builds.

`update_plan` and `multi_tool_use.parallel` are unavailable in this session.
Independent tool reads use awaited parallel calls. Serena ignores Lean paths;
the attempted symbol lookup failed, so Lean inspection uses `rg` and bounded reads.

## Verified starting point

- `OddWeilSpectralMeasure`: odd positivity produces a positive Nevanlinna measure
  on critical ordinates and the real cut; the central constant is invisible to
  odd tests. The converse is also proved.
- `WeilCutEvenMeanZeroDeficit`: even mean-zero positivity is equivalent to cut
  removal for an odd-positive weight. This does not produce that positivity.
- `WeilDilationRayCriterion`: the single dilation ray would remove both cut mass
  and the central obstruction, but its all-scale positivity remains an input.
- `OddSectorPoleDensityLaw`: positive pole weight requires nonzero Abel density.
  Tempered pole-free weights cannot supply a positive-pole source.
- `WeilConeUniquenessUnconditional`, `EvenSectorTwistedArcNull`: arithmetic
  blindness of a shifted-Gamma family supplies an independent null identity.
  Its existing parity does not directly exploit odd positivity.

## Conjecture loop

1. Repeated odd spectral tests alone remove the cut: REJECTED. The exact spectral
   weights are nonnegative on the cut. Need arithmetic structure beyond this
   representation.
2. Differentiate the existing blind null family to get an odd blind family:
   UNPROVED. Blindness at log-integer nodes does not imply blindness of the
   second derivative there. This missing cancellation cannot be assumed.
3. Arithmetic rigidity removes the central obstruction once the cut is absent:
   NO CLOSURE OBTAINED. The mean-zero positive cone and its null families did
   not supply central nonnegativity without an extra premise.

## Further conjecture cycles and surviving gaps

4. **Polar-cone closure from the odd Abel law.** The corpus already proves the
   required Abel lower behavior on odd-positive weights. It does not provide the
   even pole-free positivity required by `PolarConeAbelRigidity` and
   `ParitySectorJointRigidity`. This proposed closure is incomplete, not a theorem.

5. **Complementary covariance repair.**
   `WeilWorkExposingRayCriticalOddSource` supplies an exact even-plus-odd equals
   residual autocorrelation identity. Odd positivity gives an upper inequality
   for the even energy; it supplies no lower sign for the residual. It therefore
   does not establish even mean-zero positivity or remove cut mass.
   `WeilPaperPacketCoprimeFibre` uses parity of prime-subset masks, not spatially
   odd tests; these two meanings of parity cannot be interchanged.

6. **Differentiate the twisted-arc null family.** The intended multiplier is
   `r²`, making the individual tests odd when starting with even transforms.
   The corresponding physical operation is a second derivative. Blindness at
   `log n` specifies values, not second derivatives. The existing annihilator
   from `twistedArcMinimumPrinciple_holds` does not prove annihilation of the
   differentiated moments. No preservation of blindness has been established.

7. **Shift the Legendre operator to manufacture the missing zero at the origin.**
   `TwistedArcFamilyN1Reduction` identifies the family `M(M-a)` and spectral
   multiplier `(1/4+r²)(1/4+r²-a)`. At `a=1/4` this formally supplies an `r²`
   factor, but the file's existence theorem assumes an annihilating signed
   density with positive moments. It does not construct that density. The
   existing minimum principle is for `M²`; no minimum principle for the shifted
   family has been proved here. Passing the shift to an annihilating measure
   also introduces boundary terms on the bottom arc. Neither positivity nor
   cancellation of those boundary terms is established.

8. **Remove the central obstruction after removing the cut.** Mean-zero
   positivity cannot be silently promoted to full positivity: the general
   representation retains a term proportional to `-|fhat(0)|²`. The available
   full-cone null-family argument assumes the positivity needed to eliminate
   this term. No independent arithmetic elimination of the central term was
   obtained.

9. **Use a tempered correction of the existing null spectrum.**
   `PrimeBlindCarlsonThreshold` rules out the required nonzero arithmetic-blind
   spectrum at the `Xi²` exponential decay rate, including polynomial and the
   specified subexponential room. This prevents treating a finite polynomial or
   Gaussian correction as an unrestricted source-construction mechanism.
   This is an existing corpus obstruction, not a new result of this session.

The unresolved constructive target is an arithmetic-blind null covariance
realized entirely by odd tests, with enough decay to pass the actual weighted
arithmetic functional to the limit. Another sufficient target is an independent
arithmetic argument eliminating cut mass. Neither target has a dependency-closed
paper proof here. No route is retired and no no-go is claimed as a contribution.

## Constructive candidate: exact scalarization of the odd source cone

**Statement.** For every finite family of smooth compact complex odd functions
`f_j` and nonnegative coefficients `a_j`, there is one smooth compact complex
odd function `f` such that, at every real lag,

`f * f~ = sum_j a_j (f_j * f_j~)`.

Consequently all arithmetic-node cancellations and every linear Weil energy
are preserved exactly. This is a source construction, with no assumption of
RH, odd Weil positivity, or existence of a prime-blind witness. It does not
itself prove positivity of the constructed source.

**Paper proof.** Each odd compact `f_j` has integral zero. Its primitive from
the left of its support is therefore compact, even, and smooth; call it `g_j`.
Form the entire even Hermitian spectrum
`H(z) = sum_j a_j ghat_j(z) conjugate(ghat_j(conjugate z))`.
It is nonnegative on both coordinate axes. The corpus theorem
`EvenHermitianFactor.exists_even_entire_factor_subquadratic` constructs an
entire even factor `q`, including zero functions and all axis/origin zeros.
Its axis norm squared is exactly the corresponding sum of squared norms.
Hence its real restriction has rapid decay, and its imaginary restriction
has finite exponential type. The corpus theorem
`exists_smooth_compact_source` realizes `q` as the Fourier transform of a
smooth compact even `g`. Set `f = g'`. Differentiation makes `f` odd, retains
compact support and smoothness, and multiplies every spectrum by `z²`.
Since `f_j = g_j'`, the resulting spectral identity is exactly the desired
mixture identity. Fourier injectivity gives equality at every lag, not only
almost everywhere. Every ingredient besides the odd specialization is in
the inspected Lean corpus.

**Scope audit.** The earlier corpus construction concerns smooth even
pole-free mixtures. The odd construction removes the mixture obstruction for
smooth odd sources; the extension below also removes aperture and completion
escape and supplies actual blind attainment. No pole-zero constraint is imposed
on the resulting odd domain. The exact objective is the archimedean energy
minus twice the squared positive half-pole moment. This is not a proof of the
minimum's nonnegativity, an odd-positive arithmetic system, real-cut removal,
or the original C² Farkas criterion. Those claims remain open here.

## Successful continuation: purification without aperture escape

**Paper proof.** The primitive of a compact odd source remains inside its
original symmetric interval: outside that interval its derivative vanishes,
so it is constant on each exterior ray, and compact support forces both
constants to be zero. For the even factor `q`, its squared norm on the imaginary
axis is exactly the positive mixture of the squared primitive transforms.
If all inputs have support in `[-a,a]`, this gives the same exponential type
`a` for `q`. `compactInverse_tsupport_subset_axis_window` then puts the even
source in `[-a,a]`; differentiation retains this support. A finite family of
strict interior supports has a common smaller closed interval, so strict
interior support is preserved too.

Thus the fixed-aperture odd autocorrelation image itself is a convex cone.
This removes the finite-mixture rank obstruction while preserving all
arithmetic constraints, normalization, and literal energy. Combined with the
corpus's compact physical energy sublevels, any pointwise limit of normalized
energy-budgeted odd mixtures has one actual odd form-domain source at the
same aperture. Reflection-oddness and mass one are closed physical conditions;
the energy sublevel is closed by the existing lower-semicontinuity theorem.
No phase choices along the sequence, source-positivity premise, or sign of a
minimum is needed. All four leaf modules implementing this argument have now
passed `lake --old env lean`.

**Attainment continuation.** At every positive aperture, differentiate a
nonzero smooth compact even bump supported in a smaller interval of diameter
less than `log 2`. Its derivative is odd and nonzero (a compact function with
zero derivative everywhere would be constant and hence zero). Its
autocorrelation vanishes at every `log n`, `n >= 2`, by support. Normalize its
physical L2 norm to one. This proves feasibility without an existence premise.
The actual blind unit odd domain is closed in physical L2. Intersect its energy
sublevel with that of this feasible source; the resulting nonempty compact set
has a minimum of the existing lower-semicontinuous extended Weil energy. This
is a genuine odd source minimizing over all blind odd form-domain sources and
over the blind slice of every finite-energy mixture completion. The minimum's
sign is deliberately not asserted.

## Formal declarations and verification

All declarations are in `RHTower.OddSector`:

- `OddSectorSmoothSourceScalarization.lean`:
  `exists_smoothOdd_exact_autocorrelation_with_window` and
  `exists_smoothOdd_exact_moments` preserve the whole lag profile, common
  support window, every integer trace, and every weighted Weil functional.
- `OddSectorWindowPurification.lean`: `exists_window_purification`,
  `convex_window_profile_range`, and `exists_interior_window_purification`
  stay inside the original closed or strict interior source domain.
- `OddSectorEnergyCompletion.lean`:
  `closure_nativeEnergyProfiles_subset_completed` and
  `isCompact_closure_nativeEnergyProfiles` prevent rank, mass, and aperture
  escape under normalized finite-energy pointwise completion.
- `OddSectorBlindVariationalAttainment.lean`:
  `nonempty_blindUnitSource`, `sourceQuadratic_blind_eq_gamma_sub_pole`,
  `exists_blind_minimizer`, and
  `exists_blind_minimizer_for_mixture_completion` prove actual blind
  feasibility and attainment, retaining the negative pole direction.

Each of the four exact module files passed a foreground
`lake --old env lean <module> -o <module.olean>` audit. They are imported by
`RHTower.lean`; no full or umbrella build was run. No heartbeat increases,
numerical experiments, computation certificates, web searches, or external
novelty checks were used. A `/tmp` scratch audit of all 37 public declarations
passed: their only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

`scripts/formal_tools.py lint --check-generated` was run after index refresh,
then repeated after the first stale-index failure. The last run exited 1.
No OWU wiring, proof-debt, or heartbeat error was reported. The failures were
13 unrelated modules unreachable from the RHTower umbrella:

```
MobiusDivisorBooleanEnergySpectrum
MobiusDivisorPreparedPrimeCube
MobiusDivisorPrimeClusterSynthesis
MobiusDivisorPrimePhaseGate
PaperThetaEntireNativeMode
PaperThetaNativeAnalyticInverse
PaperThetaNativeCounterSource
PaperThetaNativeEntireRepair
PaperThetaNativeGrushin
PaperThetaNativeGrushinArithmetic
PaperThetaNativeMomentIdentity
PaperThetaNativeResonantSplitting
PaperThetaNativeScalarReduction
```

The run also reported stale `formal/LEAN_API.md` and `formal/LEAN_OVERVIEW.md`
after concurrent source edits; `PaperThetaNativeEntireRepair` appeared between
the two runs. Those unrelated unfinished modules were not changed. Generated
indexes were refreshed again at cleanup; the global lint gate is not claimed
to pass. All four OWU compiled artifacts were checked newer than their source
files. Owned scratch files were removed. No commit or push was performed.

## Next conjecture, not proved here

The attained blind odd minimum is nonnegative at every positive aperture.
The new exact objective identifies the remaining mechanism: arithmetic
orthogonality must control the negative half-pole moment through the
archimedean form. Existence, finite-mixture purification, and fixed-aperture
compactness can no longer be used as missing premises for this problem.
No sign assertion follows from attainment alone.

## Search coverage

Initial whole-corpus hybrid and deep searches reported indexed source coverage,
but older coverage snapshots and unavailable semantic coverage. Deep results
were partial. Candidate applicability is checked against actual Lean sources;
absence from search is not treated as proof of absence.
