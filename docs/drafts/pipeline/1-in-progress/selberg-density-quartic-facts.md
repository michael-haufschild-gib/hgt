# Selberg density-quartic facts

- `SelbergMaassDensityQuartic.density_sq_realLaplacian` is a closed pointwise
  identity for the literal finite congruence-trace density.
- `density_sq_hyperbolic_laplacian` gives
  `-y^2 L(rho^2) = 4 lam rho^2 - 3 y^2(current_1^2 + current_I^2) -
  4 y^2 rho angularEnergy`.
- The identity uses `trace_laplacian` and `density_mul_gradientDensity`; its
  source terms remain defined at density zeros.
- The desired quarter bound on the quadratic route remains equivalent on paper
  to `3 D + 4 A >= R`; neither pointwise identity proves this global inequality.
- Scalar Poincare control of density variation cannot establish the quarter
  target because the positive horizontal density mean survives descent.
- `MaassCuspAutomorphicCorrespondence` identifies Maass forms with spherical
  right-regular automorphic vectors, but does not construct the global L-function,
  functorial lifts, or generic GL(n,R) classification needed for parameter exclusion.
- `GenericUnitaryExponentBounds` proves only finite prescribed rank-one packet
  criteria; it is not a generic-unitary classification theorem.
- Deep corpus search, snapshot generation `916875`, for a coupled phase-stress
  compensation returned no source-attached Selberg core/side/top inequality in
  its ranked candidates.  Its generated Bessel/HTGeometry ingredient set does
  not supply the missing congruence-coefficient premise and is unusable.
- The literal phase record remains `sidePhaseFlux = integral phaseStressXX` and
  `topPhaseFlux = integral (x * phaseStressXY + phaseStressYY)`.  Since the
  latter contains signed off-diagonal Fourier interference, the existing
  positive tail Gram theorem does not imply its sign; this is the precise
  source-level gap in the phase route.
- For `L = N+1`, the existing projector decompositions imply on paper that
  summing `lossEnergy N r s v` over independent residues `r,s` gives
  `(L^2 - 1) * ||v||^2`.  This full average cannot be inserted into the seam
  estimate, whose source identity requires `r = s`; it therefore collapses to
  the already-known full trace identity rather than supplying quarter
  coercivity.
- The diagonal projector-Gram deep search, completed at generation `916900`,
  returned projector identities and generic matrix material but no
  source-attached diagonal spectral gap.  Direct source review identifies the
  diagonal coupling with the already-audited weighted finite-Gram/Kloosterman
  branch, which lacks the needed spectral estimate and is not resumed.
- `source_lower_character` transfers a lower residue at `z` to an upper residue
  at `S⁻¹ • z`; it does not turn the diagonal pair into arbitrary independent
  character pairs while preserving the same core/seam functional.
- The completed deformation/residue search at generation `916911` returned the
  known Maass boundary-trace decomposition and unrelated Xi-residue records,
  not a modular-symbol residue-detection theorem.  The Maass result is only an
  exact Bessel boundary rewrite and has no signed varying-modulus estimate.
- `SelbergScattering*` modules inspected here are built from `XiZeroCopy` and
  have no `MaassCuspEigenform` or congruence-source parameter.  Their residual
  statements do not attach to the target proof chain.
- `SelbergMaassInversionPhaseEnergy.diagonal_transfer_loss_sum_lower` is a
  closed Lean theorem: for the diagonal phase family, `sum_r lossEnergy r r v
  >= (L - 1) * ||v||^2`.  Each transfer loss contains the upper-projector loss,
  whose sum is exactly `||v||^2`; diagonal loss therefore cannot vanish
  simultaneously on a nonzero source.
- This lower bound does not close the phase estimate.  The seam/Rellich Cauchy
  bound uses loss as an *upper* factor, so a lower loss bound has the wrong
  direction for bounding the signed core/side/top stress.  The missing result
  remains a signed coercive comparison, not phase-loss nondegeneracy.
- Broad arXiv screening found Ramaré's May 2026 weighted-large-sieve Parseval
  paper.  Its theorem concerns one trigonometric polynomial with coefficients
  independent of the sampled rational point and a local support condition.  A
  Kloosterman summand has the coefficient `exp(n * inverse(a,c)/c)`, which
  varies with both numerator and denominator.  It is not one such polynomial;
  the paper does not provide the required signed short-modulus sum.
- A fresh deep search for the signed short-modulus target was partial at
  generation `916918`.  Its top Bessel candidate is a generic order-zero
  `J_0` van-der-Corput bound with no Maass/Kloosterman source attachment;
  the other leading candidates are Xi/prime-sampling material.  No returned
  statement binds a signed modulus sum to the actual Maass Bessel test.
- A broad current-arXiv screen on `observability`, `cancellation`, and `boundary`
  returned no January--September 2026 analytic result with a transfer to the
  source-attached Maass boundary form.  The matching results were unrelated
  holography, software observability, and statistical mechanics.  No external
  method is admitted into the proof route without an exact source-level map.
- The source-current modules now prove pair-plus-phase positivity, divergence of
  the total phase current, and its exact modular covariance.  A deep search at
  generation `917049` found no source phase-period vanishing theorem.  The
  nearby current-limit results instead show that a vanishing horizontal current
  limit forces pair/phase vanishing and then a common node with zero horizontal
  derivative energy.  Conservation therefore does not close the signed
  boundary term without a new global period/cancellation input.
- The flat-node unique-continuation experiment was partial at generation
  `917068`.  Its Maass-relevant result is only
  `exceptional_positive_limit_or_flat_node`; no source theorem turns a common
  zero plus one vanishing horizontal derivative into global vanishing.  The
  available unique-continuation hits are unrelated.  This alternative cannot
  be discarded by current corpus facts.
- The completed current-mass search at generation `917082` found the
  source-attached upper bound `periodCurrentLimit_le_accelerationBound`, but
  its right side is a source-dependent horizontal acceleration integral.  It
  provides continuity and compact-band integrability, not a uniform quotient
  comparison that can oppose the positive current-band mass.  Thus the actual
  missing theorem is a global automorphic cancellation/comparison estimate,
  not another local current identity.
- A second broad arXiv screen on `control` and `boundary` produced only
  unrelated holography, stochastic control, and physics/ML results.  It adds
  no theorem with a source-functional map and is rejected.
- Boundary-form search at generation `917095` reached
  `SelbergBesselAdverseModes`: the signed Bessel seam is nonnegative outside
  an exact finite adverse Fourier block, but that block has unbounded size as
  the congruence width grows.  The module explicitly has no Maass compact-core
  response.  This is the previously audited finite-Gram/debt branch; it cannot
  yield a level-uniform quarter bound without new signed arithmetic control.
- For an exceptional source, `SelbergMaassDeckAverage.sum_deck_values_zero`
  proves the pointwise deck sum is zero.  By the definition of the finite
  regular `sourceMean`, this gives `sourceMean N f = 0` identically (an
  immediate unrecorded corollary of existing Lean theorems).  Hence the
  mean-zero block/path identities apply to the actual source.  Their known
  conversion from finite deck displacement to differential path current still
  has level-growing unipotent path lengths, so this correction does not by
  itself yield the required level-uniform quartic inequality.
- The refreshed signed Kloosterman search at generation `917126` again found
  generic Poincare-series and sieve Kloosterman formulas but no theorem
  attaching a signed varying-modulus cancellation estimate to the actual Maass
  Bessel boundary test.  This remains the arithmetic gap.
- The Maass-to-model/Hilbert bridge is no longer the active gap: `MaassQuotientL2`,
  `MaassModelQuotientL2`, `MaassModelHilbertGenerators`,
  `MaassModelHilbertForm`, and `MaassModelHilbertCompletion` already attach every
  hypothetical exceptional Maass source to an injective finite-model map in the
  genuine quotient `L²`, identify all three infinitesimal generators, identify its
  pullback form with the positive complementary form, and extend the normalized
  map isometrically to the canonical completion.  This makes local unitarity a
  receiver: exceptional parameters remain compatible with this source-attached
  unitary realization.  The remaining symmetric-power route gap is the global
  unbounded-degree lift/local-factor producer, not another local-model lemma.
- Summing the character seam mismatch over every residue cancels algebraically:
  `sum_characterProjection` reconstructs both upper and lower source vectors,
  while `radialFlux_seam_identity` expresses the paired current as their
  difference.  This does not create a new Selberg inequality.  Its sum is
  already represented by `SelbergMaassTraceArea.core_cusp_quarter_identity`,
  whose unsolved term is the signed global `coreQuarter + boundarySum` form.
  Formalizing the cancellation alone would duplicate that existing source-free
  trace identity.
- `SelbergBesselAdverseModes` proves the Bessel boundary coefficient is negative
  exactly on an explicit finite integer block and decomposes every finite packet
  into nonnegative square/positive boundary terms minus its adverse debt.  Its
  `integer_width_cutoff_unbounded` theorem proves this block is unbounded with
  congruence width.  Therefore the direct route's precise hard problem remains
  a source-attached, level-uniform comparison that pays this adverse debt from
  original compact-core/gradient response; finite-mode positivity cannot close
  the global quarter bound.
- `SelbergMaassPhaseStress.core_cusp_phase_stress_bound` now reduces the direct
  source route to its exact angular phase energy and side/top phase-stress
  record.  `SelbergMaassKernelWronskian.coefficientWronskian_eq_tail` controls
  the antisymmetric cross-mode combination by the positive tail Gram kernel.
  On paper, pairing the `x * phaseStressXY` Fourier terms for two same-residue
  frequencies instead produces the height derivative of their *symmetric* Gram
  pairing.  It is not the Wronskian.  Thus tail-kernel positivity alone cannot
  replace the weighted top term; a new source-attached derivative or weighted
  Gram comparison is the remaining direct-route target.
- Shifting the dilation origin cannot remove the weighted top obstruction.  The
  horizontal stress row `(phaseStressXX, phaseStressXY)` is conserved, and its
  side flux cancels by the proved unit translation law.  Green's identity then
  identifies its unweighted top flux with the opposite circular-arc flux.
  Replacing the dilation current by that current minus `a` times the horizontal
  row subtracts `a` times the top flux and adds exactly the opposite amount to
  the arc flux.  Thus a shifted multiplier only moves the same signed moment
  between top and core; it cannot supply the missing sign or coercivity.
- The current Bessel response is deliberately the order-zero, critical
  (`lambda = 1/4`) Riccati solution.  Combining its Riccati equation with the
  actual modal ODE shows that `a' + response(k,·) a = 0` for a nonzero
  exceptional mode would force `(1/4-lambda)a/y^2 = 0`, hence is impossible.
  The formal nonnegative `remainder` is therefore the exact exceptional
  parameter defect, not an omitted proof of a coefficient-to-response map.
  The generic Bessel carrier exists, but no source-attached order-dependent
  Maass model is available.  More decisively, the internal two-frequency test
  with the exact decaying Bessel ODE has a negative top-stress determinant at
  frequencies `A = 2*pi*R`, `B = 4*pi*R` for all sufficiently large natural
  `R`.  Thus local ODE/DtN information cannot make the top stress universally
  positive; any survivor must use actual arithmetic coefficient relations or
  compensation by the source core and side terms.
- The completed deep search for a signed dual-mode bridge returned only generic
  `RHTower.Sieve` Kloosterman/Dirichlet carriers and unrelated boundary
  results.  The inspected physical-residue kernel is explicitly a finite
  ordinary Dirichlet bilinear form whose promised spectral saving remains open;
  no map from a `SelbergMaass` source into that carrier was returned or found
  in its source.  It cannot advance the direct Maass route without first
  proving precisely the missing source attachment, so the active target is the
  existing source-only density inequality `3*D + 4*A >= R`.
- The completed global-lift deep search returns only real-quotient/differential
  Maass lifts, local-factor identities, and local packet operations.  None is
  a global automorphic symmetric-power lift attached to the actual Maass
  source, let alone an unbounded compatible family with its archimedean local
  factor.  This confirms the local all-degree implication is a receiver, not
  a global producer; it does not establish nonexistence of such a producer.
- The completed twist/nonvanishing deep search returns Mellin injectivity only
  under line- or strip-wide vanishing and a nonvanishing statement only for
  Dirichlet `L`-functions.  It returns no fixed-Maass twist family, no forced
  value theorem, and no completeness map turning its isolated forced zeros
  into the hypotheses of Mellin injectivity.  The twist route therefore stops
  at the missing source-attached global assertion rather than a formalization
  gap.
- The actual finite Maass-to-model intertwiner is
  `MaassModelIntertwiner.maassDifferentialModelEquiv`.  It is a closed linear
  equivalence from the intrinsic differentiated cyclic space of an exceptional
  Maass source to `SphericalKFiniteModel`; its inverse `modelToMaass` realizes
  each finite model vector by an actual automorphic Maass derivative.  It
  intertwines compact right translation and the three derived directions
  (`E+F`, `i(E-F)`, `iH`).  `MaassModelHilbertGenerators` and
  `MaassModelHilbertCompletion` then give the corresponding three quotient-L2
  derivatives and an isometric completion.  Neither path defines an integrated
  noncompact action on that completion or proves range invariance under the
  quotient `SL(2,ℝ)` action; both completion docstrings identify the missing
  full-group/orbit argument.  This closes the finite differential
  Maass-to-model arrow, but its integration would still not construct the
  separate global unbounded-degree lift/local-factor producer, which remains
  the route-closing target.
- A bounded deep/method query returned `SelbergMaassCuspTransport` as a possible
  direct mechanism.  Its exact every-integral-cusp flux identity has a strictly
  negative exceptional defect times the strictly positive tail mass, but it is
  only the translated version of the existing cusp decomposition and explicitly
  excludes a compact-core estimate.  `SelbergMaassTraceMass.core_boundary_strict_neg`
  already gives the combined consequence: an exceptional source forces
  `coreQuarter + boundarySum < 0`.  Hence cusp flux negativity is compatible
  with ordinary cusp decay and cannot close the route.  The positive survivor
  is the sharp signed target itself: a source-arithmetic lower bound
  `0 ≤ coreQuarter + boundarySum` would immediately exclude the exceptional
  source.  The search had pending index coverage and supplied no such bound.
- A second bounded deep/method query tested whether the actual finite
  Maass-to-model equivalence transfers complementary-series positivity to the
  direct signed form.  Its only Maass hits were the equivalence, its inverse,
  and the complementary inner form; no candidate connected any of them to
  `coreQuarter`, `boundarySum`, or their sum.  Thus current model positivity is
  not a comparison theorem for the direct source functional.  The query also
  had pending coverage; no absence claim beyond the inspected candidates is
  made.
- A third bounded deep/method query tested the only identified arithmetic
  source mechanism: an actual Maass Hecke, normalizer, or deck coefficient
  relation that controls the signed core–boundary form.  Its Maass candidates
  were only the finite model equivalence, Fourier-coefficient definition, and
  quotient translation; it returned no Hecke/normalizer action, no coefficient
  identity, no proof idea, and no ingredient set.  With its pending coverage,
  this records only that no inspected corpus candidate supplies the needed
  source-arithmetic comparison.
- The full local compact-picture principal-series action already exists in
  `RealPrincipalSeriesCompactAction`, and `RealPrincipalSeriesCompactHarishChandra`
  identifies the finite model with its finite compact K-types.  The latter
  proves only K-invariance; `RealPrincipalSeriesCompactUnitarity` proves only
  infinitesimal complementary-form invariance.  No inspected declaration makes
  the full compact action isometric on a complementary Hilbert completion, or
  extends the Maass map equivariantly to it.  This is the exact remaining full
  Maass-to-model bridge.  It is local and does not manufacture the separate
  global lift family, so it cannot by itself close either active Selberg route.
- The current generic-unitary module is exactly a finite rank-one packet
  calculation: `GenericUnitaryExponentBounds` defines packet positivity from
  explicit complementary-series blocks and proves its half-strip criterion.
  Its own scope excludes classification of generic `GL(n,ℝ)` representations.
  The bounded deep/method search and exhaustive module-name/text audit found no
  `GL(n,ℝ)` generic, Whittaker, Langlands, or Maass-to-adelic representation
  object to which a general bound could apply; the only Whittaker files belong
  to a distinct Eisenstein construction.  Thus a general generic-unitary
  exponent theorem is a missing foundational development, not an existing
  source theorem awaiting formal proof.  It cannot advance the actual Maass
  route until a source-attached global lift provides such a representation.
- For every exceptional principal-congruence Maass source, the proved pointwise
  deck cancellation is exactly `sourceMean = 0`. The closed module
  `SelbergMaassExceptionalMeanZero` derives this equality and removes the
  conditional mean-zero premise from the full deck-mixing identity, the
  uniform four-unipotent-block variance bound, and the existing finite-cost
  `S,T` comparison. Thus finite deck algebra is not an open link in the direct
  route; the remaining link is a level-uniform source-energy comparison.
- The fixed-generator experiment has a precise negative result in the inspected
  corpus: no finite-congruence spectral-gap/Poincaré theorem or fixed-`S,T`
  source-to-hyperbolic-energy bridge was retrieved. The existing word-cost
  comparison is formally proved to diverge with level, while the inversion
  seam/phase-stress route retains an unrestricted signed angular/side/top
  boundary functional. Neither proves the needed uniform comparison.
- `SelbergMaassInversionPhaseEnergy.diagonal_transfer_loss_sum_lower` gives
  `(N : ℝ) * ‖v‖² ≤ Σ_r lossEnergy(N,r,r,v)`. The closed
  `SelbergMaassDiagonalLoss` source bridge specializes this to `sourceVector`,
  then combines `density_pos_somewhere` with finite-sum positivity: for every
  positive `N`, an actual Maass source has a point and diagonal channel of
  strictly positive transfer loss. This closes finite source attachment of
  aggregate diagonal loss, but it gives no source-energy-to-core coercivity.
- The phase Rellich core functional integrates `massPhaseDensity` only over the
  circular arc `x ↦ point x (arcHeight x)`. Corpus proof
  `exceptional_density_pos_in_unit_period` supplies a positive source-density
  point on each fixed horizontal slice, not on that circular arc. No inspected
  theorem transfers this positivity to the arc or signs the remaining angular,
  side, and top stress. Therefore strict loss at an arbitrary source point
  cannot yet enter `core_cusp_phase_stress_bound`.
- The current corpus has a concrete analytic Maass-to-automorphic correspondence
  (`MaassCuspAutomorphicCorrespondence`) and a nonzero algebraic cyclic
  right-regular `SL2R` subrepresentation (`MaassCyclicAutomorphicRepresentation`).
  `MaassModelIntertwiner` further identifies the K-finite model image with the
  minimal subspace stable under two noncompact *derivatives*. This advances the
  local source attachment beyond K-covariance, but establishes neither a
  completed unitary right-regular representation nor an adelic/local-factor
  construction.
- `MaassModelQuotientL2` injects every finite model vector into quotient `L2`,
  and `MaassLadderL2` proves first-order L2 admission plus an exact first-ladder
  energy identity. The inspected declarations do not prove a right-regular
  quotient-measure isometry, identify the pulled-back L2 form with the
  complementary-series form, or construct symmetric-power lifts.
  `GenericUnitaryExponentBounds` proves exponent zero only after certificates
  for every positive symmetric-power packet; these certificates are not
  attached to any Maass source. Thus the global route's precise remaining
  mathematical link is source-attached all-degree symmetric-power unitarity,
  not the finite local packet calculation.
- `SelbergMaassExceptionalMeanZero.no_exceptional_level_one` is target-built and axiom-audited
  (only `propext`, `Classical.choice`, and `Quot.sound`): an exceptional source at `N = 0`
  would have a singleton congruence deck, so deck cancellation says its source is zero and
  contradicts Maass nonvanishing. Hence the positive-level restriction in the strict diagonal
  transfer-loss theorem leaves no exceptional source untreated.
- `SymmetricPowerDegreeFamilies` proves an exact necessity result for the global route: every
  finite degree family admits a complementary exponent and an eigenvalue in `(0, 1/4)`, while
  an infinite degree family is precisely what isolates exponent zero. `SelbergExceptionalSphericalModel`
  already turns any exceptional eigenvalue into a nonzero complementary exponent and proves that
  some positive even packet fails its explicit local unitarity test. Therefore the only missing
  global step is an unbounded even-degree, source-attached automorphic unitary lift family.
- `SelbergMaassBoundaryPositivity` is target-built and axiom-audited (only `propext`,
  `Classical.choice`, and `Quot.sound`). The exact Bessel adverse-mode criterion implies
  `boundarySum N f (transitionCutoff N) ≥ 0` for every actual principal-congruence source,
  where `transitionCutoff` places the first Fourier frequency at the Bessel transition. Combining
  this with the exceptional core--cusp identity proves `coreQuarter N f (exp transitionCutoff) < 0`.
  Thus the direct obstruction has been sharpened: any proof of nonnegativity of this one
  source-attached compact-core quarter form would rule out an exceptional source; cusp boundary
  signs are no longer an open part of that implication.
- A bounded deep search for that compact-core inequality returned only the exact existing
  core--cusp/flux identities and generic coercivity APIs. Its inspected candidates contain no
  source-attached compact-core Poincare or inversion-loss-to-core lower bound. This is a
  coverage-qualified no-go for the inspected mechanisms, not an assertion that no such theorem
  can be developed.
- Deck cancellation cannot force the period-current limit to vanish: in
  `SelbergMaassAverageCurrents`, `sourceMean = 0` makes the mean field and its mixed brackets
  vanish, while the original pair and phase currents remain exactly those of the centered family.
  `SelbergMaassPeriodCurrentRigidity` therefore only yields the existing alternative “positive
  current limit or a common first-order-flat node.” This rules out that particular direct bridge.
- Modal Cauchy uniqueness in `SelbergMaassSliceRigidity` excludes a whole zero horizontal slice,
  but its stated scope and the proved period dichotomy leave common value-and-horizontal-derivative
  zeros open. Hence the period-current route cannot presently exclude its flat-node branch.
- A 278-second deep search for a source-attached mean-zero deck-displacement to compact-core
  hyperbolic-gradient/Poincare estimate returned zero matching declarations. Its generic
  coercivity candidates are unrelated operator models; source, compiler, and semantic coverage
  were incomplete. This is a coverage-qualified no-go for an existing bridge, leaving the exact
  open target: an integrated displacement-to-gradient inequality strong enough to dominate
  `density / (4*y^2)` in `coreQuarter`.
- The only existing deck-variance coefficient is formally known to be unsuitable as a uniform
  route ingredient: `SelbergMaassGeneratorCostGrowth.generatorConstant_tendsto_atTop` and
  `not_exists_uniform_generatorConstant_bound` prove divergence of the all-word `S,T`
  comparison constant. This does not rule out a different finite-quotient or source-geometric
  inequality, but it rules out extracting the required level-uniform core estimate from that
  certified word-cost recipe alone.
- The weak-curvature route has an explicit scalar no-go. `SelbergScalarCurvatureFamily` constructs
  smooth positive modular scalar models with positive curvature and the same total curvature
  budget for every positive parameter, and proves `no_scalar_quarter_comparison`. Thus
  nonnegative scalar/amplitude curvature cannot yield Selberg's (1/4) bound; any curvature
  completion must use Maass-specific vector/deck information. The surviving target is again a
  quantitative link from that vector information to the compact-core quarter form.
- Focused deep search `diagonal inversion loss frequency weighted reverse lower horizontal vertical Maass core quarter` (15 Sep 2026; 58,106 source files inventoried; source index incomplete, semantic coverage unavailable) returned no matching declaration. Existing `SelbergMaassInversionPhaseEnergy.transfer_loss_decomposition` and coefficient-residue identities provide exact norm redistribution, while the source comparison remains `weighted_phase_loss_le_horizontal`; no reverse weighted-loss or vertical-ODE-to-core bridge was found. Thus the current character-inversion mechanism does not remove the strip bound's low-frequency factor.
- Deep search `observability unique continuation compact core deck source Maass energy` (15 Sep 2026; source index incomplete, semantic coverage unavailable) had no matching declaration. Returned finite-matrix/other-program spectral-gap candidates only, with no `MaassCuspEigenform` source bridge. The search was partial at its filtering stage, so this is not an exhaustiveness claim; it gives no usable observability theorem for the direct route.
- `HTGeometry.carleman_weighted_estimate` is a compact-support one-dimensional inequality. Applied to a log-height cutoff of an actual Fourier coefficient, its cutoff derivative yields the lower modular-arc endpoint term. The only returned source identity, `SelbergMaassTraceBoundary.arc_current_cancellation`, rewrites that vertical arc current using horizontal arc currents; it supplies no sign. Since the trace density is a deck sum of squared norms, `sourceMean = 0` does not cancel this current. Therefore Carleman plus present arc identities cannot prove the required core-quarter nonnegativity.
- Deep search `congruence deck Cayley spectral gap expansion Maass coercivity` (15 Sep 2026; source index incomplete, semantic coverage unavailable) returned no source-attached expansion or Cayley-gap theorem. Its only Maass candidates were the existing correspondence and trace identities; abstract Cayley/spectral lemmas carried no `MaassCuspEigenform` energy bridge. Thus no corpus theorem currently supplies the direct route's needed level-free deck coercivity.
- Deep search `Maass Hecke adelic automorphic local representation source correspondence` (15 Sep 2026; source index incomplete, semantic coverage unavailable) found `maassCuspToSphericalAutomorphicCorrespondence` and finite differential lifts only. No candidate constructs an adelic completion, a local packet attached to the Maass source, or an all-even-degree unitary lift family. Thus the global route remains blocked at the source-attached completed lifting step.
- `MaassModelHilbertForm` proves the source-attached complementary-series norm identity on every finite K-type. `MaassModelHilbertCompletion` therefore defines `completedModelIsometry : ComplementaryHilbert lam →ₗᵢ Lp` and proves its range is the closure of the normalized finite Maass image. This closes the isometric-completion part of Maass-to-model correspondence. Its stated remaining condition is closed-range invariance and full (SL_2(ℝ))-equivariance; `MaassModelHilbertGenerators` proves only infinitesimal identities on finite vectors.
- `HTGeometry.norm_sub_taylorWithinEval_le_factorial` supplies a Banach-valued Taylor remainder with exact factorial denominator. `sphericalPrincipalE_single` and `sphericalPrincipalF_single` give the required one-step affine K-index recurrence. A focused deep search found no Maass/all-order weighted-shift norm estimate or analytic-vector theorem. Hence completing noncompact intertwining reduces concretely to proving factorial bounds for repeated (E\pm F) in the established complementary norm and matching those iterates to quotient-unitary orbit derivatives.
- The complementary `K`-type recurrence gives exact singleton energies
  `((2m+1)^2-s^2)/4` and `((2m-1)^2-s^2)/4` times the respective diagonal weight
  for `E` and `F`.  This can support analytic-vector completion arguments, but the
  already source-attached complementary Hilbert receiver still cannot produce the
  missing unbounded-degree global lift family or the direct core inequality; it is
  not pursued as a Selberg-closing route.
- The Poincaré/Bessel candidate fails source attachment: `PoincareSeriesBesselCoefficient`
  proves coefficient and Petersson identities for holomorphic level-one cusp forms,
  while the target `MaassCuspEigenform` has no pairing or transfer theorem to that
  space.  Its Kloosterman--Bessel formula therefore cannot control the actual Maass
  adverse packet without a new, independent Maass Poincaré correspondence.
- The refreshed symmetric-power search again finds only the exact local shrinkage theorem
  `genericUnitarySymPower_degree_family_eq_singleton_iff`.  `MaassLadderQuotientL2`
  supplies all compact-weight vectors in the same quotient `L²`; tensoring or multiplying
  them remains diagonal `SL₂` automorphy and has no map to the higher-rank packet required by
  `SymmetricPowerSphericalPacketUnitarizable`.  It cannot serve as the missing lift family.
- The multi-cusp/deck experiment yields no uniform compact-core gap.  The full deck trace
  descends to level one and is already identically zero, whereas every nonzero coordinate or
  character readout remains a level-`N+1` Maass source with its original widening cusp.
  The search returns no theorem aggregating those readouts into a source-attached uniform
  coercive estimate; summing their exact identities returns the audited full trace identity.
- The July 2026 Ginzburg--Landau comparison-field method and the September 2026
  Hardy--Wronskian boundary method do not transfer.  The former needs a unit-modulus
  nonlinear exterior state and Jacobi coercivity, while every cuspidal Maass source decays to
  zero.  The latter needs a Liouville/Robin equation and holomorphic frames.  The actual Maass
  `coefficientWronskian_eq_tail` controls antisymmetric coefficient currents; the unresolved
  top flux contains the symmetric weighted `x * phaseStressXY` term.  Neither supplies the
  missing signed compact-core comparison.

- `RealSphericalComplementaryGeneratorEnergy` now proves, with closed Lean derivations, the exact one-step complementary-form energies of `sphericalPrincipalE` and `sphericalPrincipalF` on every spherical K-type.  Each is the quadratic coefficient `((2m ± 1)^2 - s^2)/4` times the preceding weight.  This supplies the literal recurrence-controlled base case for a finite-support analytic-vector estimate; it does not by itself integrate a noncompact action or produce the independent global higher-rank lift family.
- `RealSphericalComplementaryGeneratorEnergy` now also constructs the finite K-type reflection `R`, proves `R² = 1`, `R E = F R`, `R F = E R`, and proves `R` is an isometry for the complementary Hermitian form.  Transporting the already proved raising estimate through `R` gives the closed finite-support lowering estimate
  `sphericalPrincipalF_complementary_energy_re_le_of_support`, with the same radius factor
  `(2*r+1)^2/4`.  Targeted module build and `#print axioms` audits on 15 Sep 2026 found only
  `propext`, `Classical.choice`, and `Quot.sound`.  Thus two-sided one-step local generator control
  is no longer an obstruction; factorial iteration and noncompact exponentiation remain open.
- `MaassModelHilbertAnalyticVectorBounds` transfers those two one-step bounds to the actual
  source-attached pre-Hilbert model `ComplementaryKFinite`.  For its diagonal noncompact generator
  `D = E + F`, it proves support radius `r+n` after `n` iterations and the closed factorial majorant
  `‖D^[n] v‖ ≤ (2*r+2)^n * n! * ‖v‖`.  Its targeted source check and OLean build, plus theorem-level
  axiom audit on 15 Sep 2026, use only `propext`, `Classical.choice`, and `Quot.sound`.  This is the
  exact local analytic-vector input for the already proved quotient-L² diagonal derivative; the open
  bridge is a Banach Taylor-tail theorem that places the actual quotient orbit in the closed range of
  `completedModelIsometry`.
- `MaassModelHilbertOrbitDerivatives.integralSubgroupUnitary_hasDerivAt_all_times` proves that any
  zero-time derivative of a quotient `L²` orbit along an `SL₂(ℝ)` one-parameter subgroup propagates
  to every real time, with derivative transported by the actual quotient unitary.  The proof uses
  the subgroup law and explicitly restricts the fixed complex unitary to a real continuous linear
  map.  Direct source check, targeted module build, and `#print axioms` audit on 15 Sep 2026 found
  only `propext`, `Classical.choice`, and `Quot.sound`.  This removes all-time differentiation as
  an obstruction to completed-model range invariance; the remaining local obligation is the
  iterated derivative/Taylor-tail closure argument.
- `MaassModelHilbertOrbitDerivatives` now proves a two-sided, source-attached local Taylor theorem: for every finite complementary vector with support radius `r`, its actual quotient diagonal translate lies in `Set.range completedModelIsometry` whenever `|(2*r+2)*t| < 1`.  The proof has exact quotient-orbit iterated derivatives, factorial Taylor remainder, finite-model Taylor polynomials, geometric convergence, and the completion range-closure identity.  Reverse time is proved using Mathlib's `iteratedDeriv_comp_neg`, not a presumed group intertwiner.
- **NO-GO for the naive density lift:** the certified local radius is `(2*r+2)⁻¹` and depends on the finite vector's support radius.  Approximants to an arbitrary completed-model vector need not have bounded support radii, so no fixed nonzero `t` makes the current finite-vector theorem a `MapsTo` statement on the dense normalized finite image.  Continuity plus closed range therefore cannot extend this local result to the whole completion from the present factorial bound alone.  A surviving global bridge must supply support-uniform analytic control, a support-weighted completed topology invariant under the diagonal action, or an independent full group intertwiner.
- Target build of `GaloisForLFunctions.RHTower.MaassModelHilbertOrbitDerivatives` passed on 15 Sep 2026.  Axiom audits of its forward two-sided local range theorem, reverse local range theorem, and normalized-image transport theorem report only `propext`, `Classical.choice`, and `Quot.sound`; source-token scan found no `sorry`, `admit`, added `axiom`, `opaque`, `unsafe`, or heartbeat override.
- Re-inspection of the local packet and Maass correspondence route confirms the exact reduction.  `SelbergExceptionalEigenvalue.exists_nonunitarizable_even_symmetricPower_degree` proves that every exceptional source exponent fails `SymmetricPowerSphericalPacketUnitarizable` in some even degree, while `all_even_degree_symmetricPowerSphericalPacketUnitarizable` proves the converse all-degree local obstruction.  `MaassCuspAutomorphicCorrespondence` gives only the spherical function-space correspondence; its own stated scope omits quotient `L²`, Laplace/Casimir compatibility, adelic factorization, and any symmetric-power lift.  The 15 Sep 2026 deep correspondence search returned no source-attached Maass-to-symmetric-power packet construction (partial, source index incomplete), so this remains the exact global open lift theorem.
- `MaassModelQuotientL2.modelToLp_spherical` now gives exact quotient-`L²` equality between the zero `K`-type finite-model vector and `MaassQuotientL2.sourceLp`.  Together with the previously formalized local orbit derivative identity, this closes the literal source-to-spherical-model dictionary row.
- `MaassModelHilbertOrbitDerivatives` now proves that the completed-model range contains every zero-`K`-type diagonal translate at nonnegative time: `modelToLpComplementarySphericalOrbit_mem_range_completedModelIsometry_of_nonneg`, and therefore the literal Maass source via `sourceLp_diagonal_mem_range_completedModelIsometry_of_nonneg`.  The proof uses closed-range endpoint differentiation, uniform zero-`K` factorial bounds, and a translated Taylor continuation in quarter steps.  This removes the support-radius obstruction only for the one spherical forward orbit; it proves neither negative-time nor full-group invariance and does not attach a global symmetric-power lift.
- Target build and theorem-level axiom audits on 15 Sep 2026 for those results succeeded with only `propext`, `Classical.choice`, and `Quot.sound`; source scan found no `sorry`, `admit`, added `axiom`, `opaque`, `unsafe`, or heartbeat override.  The next bridge test is whether the same closed-range continuation can be generalized to each finite `K`-type vector.  If so, density and continuity yield forward diagonal invariance of the entire completed range; if not, the failure must expose a support-uniformity obstruction or a replacement completed topology.
- `MaassModelHilbertOrbitDerivatives.closedSubmodule_mem_of_iteratedDeriv_factorial_nonneg` now proves the reusable continuation law: a closed real submodule contains a smooth orbit at every nonnegative time when it contains every initial jet and the orbit has a uniform factorial jet bound.  It removes local-radius dependence from the global continuation argument.
- Instantiating that law for both diagonal parameterizations proves global range membership for every fixed finite `K`-type vector in both directions.  `linearIsometryEquiv_mapsTo_completedModelIsometry_range_of_finite` then transports finite-image invariance through the certified completion closure.  Consequently `integralSubgroupUnitary_mapsTo_completedModelIsometry_range` proves two-sided diagonal invariance of the entire completed model range.  This closes the diagonal part of the noncompact intertwining obstacle.  It does not construct compact-`K` invariance, a full `SL₂(ℝ)` action, or a source-attached global symmetric-power lift.
- `MaassModelHilbertOrbitDerivatives.integralSubgroupUnitary_modelToLp_K` proves the exact compact intertwiner
  `U_k (modelToLp v) = modelToLp (sphericalKTypeAction k v)` for every finite complementary vector. Its normalized version and the completed-range closure transfer prove
  `integralSubgroupUnitary_mapsTo_completedModelIsometry_range_K`: the compact stabilizer preserves the whole completed-model range. Together with the prior two-sided diagonal theorem, the remaining local group-theoretic bridge is a formal factorization of arbitrary `SL2R` elements into compact factors and `realPositiveDiagonalBorel` factors.
- Deep corpus search for that `KAK`/Cartan factorization returned no matching declaration; source index is incomplete. Existing `realIwasawaB_mul_realIwasawaK` gives only `g = b(g) k(g)` with an unrestricted upper-Borel factor, so it cannot combine with current range-invariance theorems. The positive survivor is the exact factorization target, not an inferred full-action claim.
- `RealSL2Cartan.realSL2_exists_compact_diagonal_compact` now proves a closed real Cartan factorization
  `g = k₁ · diag(exp t, exp(-t)) · k₂` for every `g : SL2R`, by spectral decomposition of `gᵀg`, positive square roots, and a determinant-`-1` reflection correction. `MaassModelHilbertOrbitDerivatives.integralSubgroupUnitary_mapsTo_completedModelIsometry_range_SL2R` composes this factorization with certified compact and two-sided diagonal range invariance. Therefore the source-attached completed complementary-model range is now invariant under the full real `SL2R` quotient action. Target OLean audits passed on 15 Sep 2026; both new theorems audit to only `propext`, `Classical.choice`, and `Quot.sound`.
- Route consequence: the local Maass-to-complementary Hilbert intertwining obstruction is closed through a genuine full real-group invariant completed image. This does **not** provide the source-attached global symmetric-power/adelic lift: the existing deep corpus evidence still leaves that lift as the central remaining bridge from an exceptional Maass source to an all-even-degree unitarizable packet.
- **NO-GO for the existing finite-deck-to-core composition.** `SelbergMaassExceptionalMeanZero.sourceMean_eq_zero` and `SelbergMaassUnipotentPaths.density_fraction_le_pathCost_of_mean_zero` force a positive-density exceptional source to incur regulated horizontal path cost.  But `SelbergMaassTraceArea.core_quarter_identity` is `coreQuarter = flux + (λ - 1/4) * coreMass`; for an exceptional `λ`, its mass term is negative.  The inspected path theorems compare deck displacement only to path cost, and `SelbergMaassUnipotentPaths` explicitly retains no quotient-area comparison.  The focused deep search `source attached compact core quarter form finite deck mean zero generator energy path cost coercivity proof mechanism` found no source-attached path-cost/generator-energy-to-flux lower bound (index incomplete).  Therefore these certified inequalities cannot produce `0 ≤ coreQuarter` by composition.  Positive survivor: exact mean-zero lower demand on regulated path cost and its exact current-integral identity; the direct bridge target is now a lower flux/physical-gradient comparison for that current.
- **Global-route prerequisite gap.** The corpus definition `MaassCuspEigenform` records only invariance, nonvanishing, the Laplace equation, and integral-cusp decay.  The deep search `Maass Hecke eigen cusp correspondence spectral decomposition` returned zero exact declarations and no Hecke/adelic source construction (index incomplete).  `MaassCyclicAutomorphicRepresentation` constructs a nonzero algebraic cyclic right-`SL2R` subrepresentation and explicitly leaves Hilbert completion, adelization, and local factorization separate.  Hence current full real-group model invariance has no formal arithmetic input from which a symmetric-power packet can be constructed.  Positive survivor: source-attached nonzero cyclic automorphic representation; the first global bridge must add a proved arithmetic spectral/Hecke realization before packet lifting can be stated source-attached.
- `SelbergMaassCuspDecay.flux_nonpos` is now a closed Lean corollary: for every exceptional principal-congruence source and every height at or above `cutoff N`, its actual outgoing slice flux is nonpositive.  It combines the certified convex mass ODE, decay of mass at infinity, and `mass' = 2*flux`; target source check and OLean build pass, and `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.  **Cutoff-flow reframe outcome:** promoting height to a flow coordinate yields one-sided cusp decay/flux control, but this sign is compatible with, rather than opposite to, the already proved negative compact-core quarter form.  It does not supply the missing compact-core coercivity bridge.  Positive survivor: a sharp source-attached terminal flux sign for any later core-to-cusp comparison.
- **NO-GO for present finite-deck comparison mechanisms.** `SelbergMaassGeneratorCostGrowth.generatorConstant_tendsto_atTop` and `not_exists_uniform_generatorConstant_bound` prove that the current all-word `S,T` comparison coefficient diverges with congruence level; `not_exists_uniform_certifiedCost_bound` extends this to every complete choice of literal generator-word representatives in that recipe.  The apparently level-uniform four-block variance inequality does not repair this after geometric realization: `SelbergMaassUnipotentPaths.parameterMoment_eq` gives the exact block path multiplier `N*(2*N+1)/12`, and the two-period density comparison carries the resulting `N*(2*N+1)` factor.  Thus no regrouping of the current word or full-unipotent-block paths can furnish a level-uniform direct coercivity estimate.  Positive survivor: exact finite-deck variance and exact parameter-moment identities; a direct route must introduce a different source-sensitive geometry or a non-word/non-full-block comparison, then still bridge it to `coreQuarter`.

- **Quartic coercivity composition no-go (current corpus, 2026-09-15).** `SelbergMaassDensityQuartic.density_mul_angularEnergy` gives the exact nonnegative pair/phase decomposition of \(\rho\,a\), and `SelbergMaassFullGradient.full_gradient_identity` gives the unweighted identity \(\int e=\lambda\int\rho\). The quartic target instead needs \(D+4A=4\int\rho e\), hence a source-attached bridge from unweighted to density-weighted energy (or directly \(3D+4A\ge R\)). No indexed theorem supplies that bridge; scalar Poincare is inapplicable because \(\rho\) has positive mean. `SelbergThetaCommonForcingPacketMass` concerns a Xi-zero packet rather than a Maass source and cannot supply it. The positive survivor is the exact source-specific pair/phase decomposition and the sharply reduced coercivity target.
- **Positive-mean profile experiment (current corpus, 2026-09-15).** The horizontal mean of the modular density is exactly the finite sum of Maass slice masses (`density_integral_eq_sum_mass`), with first and second height derivatives given by summed flux and summed gradient-minus-potential terms. These identities are linear in \(\rho\). The quartic target contains \(R=\int\rho^2\) and \(\int\rho e\); the inspected slice/flux theorems provide no nonlinear bridge from the mean profile to either quantity. The profile reframe therefore identifies the missing statement as a nonlinear source-attached mean-to-quartic coercivity, rather than another linear cusp ODE.
- **Projective-rigidity experiment (current corpus, 2026-09-15).** Exceptional zero means yield separated normalized deck directions at every height, and negative correlation yields a fixed chord margin at a fixed source pair. Its available conversion to derivative energy is the closed-period path product, carrying an exact level-width factor. The inspected `SelbergMaassReadoutCusp` and character-projection candidates do not prove that vanishing angular energy forces a forbidden deck character or give a quantitative lower bound. Thus projective separation alone does not close \(3D+4A\ge R\); any survivor needs a new source-attached global comparison.
- **Flat-bundle/graph and tensor-square reframes (current corpus, 2026-09-15).** The deep searches found generic weighted-graph spectral-gap and tensor/Cauchy lemmas, but no Maass-source map to a flat bundle or tensor-square quotient representation with a spectral decomposition. The graph theorem requires the desired gap as its hypothesis; the tensor candidates provide only algebraic norm inequalities. Combined with the already-proved level growth of literal generator costs, these are reformulations of the missing global coercivity, not bridges to it.
- **Approach-1 revalidation (current corpus, 2026-09-15).** The source-attached real arrows are now closed through `integralSubgroupUnitary_mapsTo_completedModelIsometry_range_SL2R`. A fresh deep search for the next arrow returned only Maass ladder automorphy, quotient lifts, and the finite rank-one packet criterion. Direct source review confirms that `MaassCyclicAutomorphicRepresentation` is algebraic real-group data and `GenericUnitaryExponentBounds` classifies only its explicitly defined finite rank-one packets. No returned candidate constructs an adelic Maass representation, a compatible unbounded symmetric-power lift, or a generic higher-rank local factor. Thus approach 1 remains blocked at the first source-attached global construction; repackaging its completed real range would not bridge that gap.
- **Approach-1 arithmetic prerequisite test (current corpus, 2026-09-15).** A second deep search for a Maass Hecke/local-global/converse/Whittaker bridge produced only unrelated finite-adele constructions, along with existing ladder and quotient-L2 results. The current Maass definition contains no Hecke-eigen or finite-place datum, and no inspected declaration creates such data from it. Therefore even the adelic source object needed before symmetric-power lifting cannot presently be stated source-faithfully from the available Maass package. The positive survivor is a precise prerequisite: construct an adelic realization with finite-place Hecke action and prove its archimedean component agrees with the completed complementary model.
- `SelbergMaassCuspTransport.positive_laplacian_pullback_gl`, `smooth_pullback_gl`, and
  `eigenfunction_pullback_gl` now prove closed covariance of the actual positive hyperbolic
  Laplacian and Maass eigen-equation under every positive-determinant real `GL(2)` Möbius map.
  This removes determinant normalization as a Hecke-route obstacle; it does not establish source
  invariance or cuspidality for a rational correspondence.
- `SelbergMaassRationalCommensurator` proves that the embedded actual source level
  `Gamma (N + 1) : Subgroup GL(2, R)` is arithmetic and that every `GL(2, Q)` element maps into
  its Mathlib commensurator. This gives a closed finite-index home for every rational Hecke
  correspondence. The remaining first global bridge is an explicit finite trace on the current
  `SL2R`-invariant Maass source and a proof that it preserves integral-cusp decay.
- `SelbergMaassCongruenceTrace` is a source-attached template only for the finite quotient by
  integral principal-congruence matrices: it proves descent, finite summation, invariance, and
  cusp decay because every summand is an integral pullback. Its construction cannot absorb a
  rational commensurator element. Thus the positive survivor is the exact rational-trace theorem,
  not another deck average.
- **Rational Maass trace closed (current corpus, 2026-09-15).** `rationalGL_exists_integral_upperTriangular` factors every rational `GL₂` matrix after every integral cusp scaling as an integral `SL₂` factor followed by an upper-triangular real factor. Together with `UpperHalfPlane.tendsto_smul_atImInfty`, `rationalGL_cuspidal_pullback` proves that rational pullback preserves the actual integral-cusp decay condition; positive-determinant covariance preserves the Maass eigen-equation.
- **Source-attached rational correspondence closed (current corpus, 2026-09-15).** `rationalMaassPullback` constructs the nonzero conjugate-level source; `maassTraceInvariant` proves finite relative-coset trace invariance; `principalMaassTraceData` proves trace preservation of smoothness, eigenvalue, and cusp decay; `rationalPrincipalTrace_zero_or_eigenform` returns either zero or a nonzero principal-level `GLMaassCuspEigenform` at the original eigenvalue. Target build and axiom audits pass with only `propext`, `Classical.choice`, and `Quot.sound`.
- **Route boundary after rational trace.** The trace is zero-permitted and is not yet a Hecke endomorphism theorem: no fixed-eigenvalue vector space, trace linearity/operator identity, commuting/self-adjoint rational double-coset algebra, simultaneous eigenvector, finite-dimensional spectral realization, or adelic factorization has been proved. The next whole-route bridge is to package these zero-permitted maps on a proved finite-dimensional Maass eigenspace; only then can this correspondence supply finite-place data for a global lift.
- **Zero-inclusive Hecke precursor closed (current corpus, 2026-09-16).** `glMaassCuspEigenspace Γ λ` is a closed Lean `ℂ`-submodule of upper-half-plane functions: it retains GL invariance, the exact positive-hyperbolic-Laplacian equation, and every integral-cusp decay condition under zero, addition, and complex scalar multiplication. The proof uses exact second directional derivative sum/scalar rules, not a presumed linearity of the Maass equation.
- **Linear rational correspondence closed (current corpus, 2026-09-16).** `maassTraceLinear` is the finite relative-coset trace as a complex-linear map. `principalMaassTraceLinear` restricts it to the fixed Maass eigenspace using the new zero-inclusive analytic trace theorem. `rationalMaassPullbackLinear` and `rationalPrincipalTraceLinear` compose positive rational pullback with finite trace into a closed linear endomorphism of the same principal-level eigenspace. Target build and theorem-level axiom audit report only `propext`, `Classical.choice`, and `Quot.sound`.
- **Next global-route boundary.** Deep search finds generic joint-eigenvector theorems only conditional on a finite-dimensional module and commuting endomorphisms. It returns no source-attached double-coset product/commutation identity, finite-dimensional Maass eigenspace, compact resolvent, or spectral realization. The next proof attempt must establish rational-double-coset identities for `rationalPrincipalTraceLinear`, or construct a source-attached finite-dimensional spectral realization; without one, the linear maps cannot yet create finite-place Hecke eigenvalues or an adelic lift.
- **Nested finite-trace composition closed (current corpus, 2026-09-16).** `maassTraceCosetProductEquiv` proves the exact relative-coset factorization `K / (G ∩ K) ≃ (K / (H ∩ K)) × (H / (G ∩ H))` for `G ≤ H ≤ K`. `maassTraceCosetProduct_summand` identifies the actual Maass summand in these coordinates, and `maassTraceFunction_transitive` closes `Tr_{G→K} = Tr_{H→K} ∘ Tr_{G→H}` for finite nested chains. This supplies the composition engine missing from the rational correspondence route.
- **Generic rational pullback composition closed (current corpus, 2026-09-16).** `rationalMaassPullbackInvariant_general` and `rationalMaassPullbackLinearOfGroup` extend the rational pullback to every fixed Maass eigenspace. `rationalPullbackConjugateGroup_mul`, `rationalGL_map_det_mul_pos`, and `rationalMaassPullbackLinearOfGroup_comp_apply` prove subgroup, positivity, and pointwise function composition for successive positive rational matrices. The remaining operator-product bridge is base change through intersections of non-nested rational conjugate subgroups.
- **Rational-conjugate analytic trace closed (current corpus, 2026-09-16).** `rationalConjugateGroup_exists_positive_rational_lift` gives every target representative a positive rational lift. `SelbergMaassRationalConjugateTrace` uses it quotient-class by quotient-class to prove finite trace into every rationally conjugated principal target preserves smoothness, the exact Maass eigen-equation, and integral-cusp decay. `rationalConjugateMaassTraceLinear` and `rationalConjugateGroupsTraceLinear` therefore give closed complex-linear maps between all rational-conjugate fixed eigenspaces.
- **Trace/pullback base change closed (current corpus, 2026-09-16).** `SelbergMaassTraceBaseChange` constructs the conjugation equivalence of relative-coset quotients, transports finite relative index, and proves `maassTrace_rationalPullback_baseChange`: rational pullback commutes exactly with finite trace. This removes all analytic and conjugation-order defects from rational-operator composition. The remaining Hecke-algebra bridge is a finite double-coset decomposition for composition of traces through non-nested conjugate subgroups; no source-attached product formula or finite spectral realization is yet present.
- **Mackey combinatorics and block source closed (current corpus, 2026-09-16).** `SelbergMaassDoubleCosetTrace.maassTraceFunction_doubleCoset` gives the exact orbit--stabilizer reindexing of any finite Maass trace, `maassTrace_mem_stabilizer_iff` and `maassTrace_stabilizer_eq_conjugateComap` identify the stabilizer with the conjugated intersection, and `maassDoubleCosetBlockPullback` constructs its literal invariant pullback source. The exact remaining local bridge is analytic trace preservation for mapped subgroup intersections which inherit positive rational lifts from a rational-conjugate parent; after that, nested trace transitivity can convert each block into an explicit correspondence term.
- **Positive rational lifts descend to intersections (current corpus, 2026-09-16).** `HasPositiveRationalLifts` records the exact representative property needed by the analytic trace proof. `rationalConjugateGroup_hasPositiveRationalLifts` closes it for every rational-conjugate principal parent, and `HasPositiveRationalLifts.map_subgroup` closes it for every mapped subgroup, including the stabilizer intersections in the Mackey decomposition. Direct RationalTrace source and target audits pass.

- **Positive-rational Mackey blocks are now closed (current corpus, 2026-09-16).** `positiveRationalMaassTraceData_of_data` proves finite trace preserves invariant, Maass-eigen, and integral-cusp data for every target carrying a `HasPositiveRationalLifts` witness. `maassTrace_mappedStabilizerQuotientEquiv` proves the actual stabilizer-coset quotient is equivalent to the quotient of its mapped subgroup, so its mapped stabilizer has finite relative index. `maassDoubleCosetBlockTraceFunction_eq_orbitSum` identifies the finite trace of a literal double-coset block with its original stabilizer-orbit summands, and `maassDoubleCosetBlockTraceFunction_eq_representativeOrbitSum` attaches that equality to a representative-based orbit--stabilizer equivalence. The remaining global finite sum equality is mathematically reduced to these closed facts; its direct source proof reached Lean's default elaboration limit without any heartbeat modification, so no unverified global theorem was retained.
- **Rational-trace compact-core no-go (current corpus, 2026-09-16).**
  `glIntegralMaassCuspEigenformToMaass` now reindexes every principal-level
  `GLMaassCuspEigenform` to the identical `realImage (Gamma (N+1))` Maass source, retaining its
  literal function, nonvanishing, eigen-equation, and integral-cusp decay.  Consequently
  `rationalPrincipalTrace_zero_or_coreQuarter_strict_neg_at_transitionCutoff` proves that each
  rational principal trace of an exceptional source either vanishes or is represented by a
  principal-level Maass source with strictly negative `coreQuarter` at the canonical Bessel
  cutoff.  `weighted_coreQuarter_sum_strict_neg_at_transitionCutoff` extends this to every finite
  nonnegative-weight family having positive total weight.  Thus neither a positive finite trace
  average nor cross terms packaged as a nonzero traced eigenform can supply the required
  `0 ≤ coreQuarter` direct coercivity.  The positive survivor is exact: any direct route must use
  a new sign-indefinite/source-sensitive comparison (for example a lower flux or density-weighted
  quartic bound), while the global route still requires adelic finite-place realization followed
  by compatible unbounded symmetric-power lifts.  Source checks and targeted builds of
  `SelbergMaassGLCorrespondence` and `SelbergMaassTraceAverageNoGo` pass; theorem axiom audits
  report only `propext`, `Classical.choice`, and `Quot.sound`.
- **Quotient-Casimir prerequisite test (current corpus, 2026-09-16).**
  `MaassSmooth.laplacian_ofMaass` and `lower_raise_ofMaass` give the literal smooth
  upper-half-plane Laplace/Casimir factorization, while `MaassLadderQuotientL2` admits every
  individual raised and lowered automorphic ladder function to quotient `L²`.  The fresh deep
  search for a quotient derived Casimir, operator domain, closedness, resolvent, or source
  eigenvector compatibility returned no declaration.  Direct source inspection confirms that the
  quotient module exports only `toLp` vectors and almost-everywhere representatives, not an
  unbounded Laplacian/Casimir.  Therefore compact-resolvent or finite-dimensional-eigenspace
  arguments are not yet well-typed from the present data; pointwise differential identities cannot
  replace that missing operator layer.  Positive survivor: a source-attached smooth Casimir
  factorization and quotient-`L²` admission of every finite ladder vector.  A global spectral route
  first needs a closed cusp-Laplacian/derived-Casimir realization that contains this ladder and
  identifies its eigenvalue.
- **Geometric trace-formula audit (current corpus, 2026-09-16).** A deep search for a
  source-attached geodesic/orbital spectral-parameter positivity mechanism returned only the Maass
  correspondence, Fourier coefficients, and unrelated finite spectral positivity. An exhaustive
  name/text audit for `trace formula`, `Selberg trace`, `orbital integral`, `closed geodesic`, and
  `hyperbolic conjugacy` finds no congruence-Maass geometric trace-formula implementation; the
  apparent trace-formula modules belong to distinct Connes/RH carriers. Therefore no direct
  geometric positivity bridge is presently available for the Selberg source. Any such route first
  requires a new source-attached trace formula with a proved spectral side and an orbital-side sign
  estimate.
- **Global Mackey block decomposition closed (current corpus, 2026-09-16).**
  `maassTraceFunction_eq_sum_doubleCosetBlockTraceFunctions` proves that every finite Maass trace
  is exactly the finite sum of the analytic traces of its double-coset blocks. The proof uses the
  existing orbit--stabilizer decomposition, `Subgroup.quotientEquivOfEq` to transport the dependent
  stabilizer quotients between literal and quotient-chosen representatives, and enumeration
  independence of finite sums. `maassTraceDoubleCosetOrbitFintype` and
  `maassTraceDoubleCosetStabilizerFintype` are now public canonical enumerations so this equality
  composes definitionally with the existing trace reindexing. This removes the prior formal
  obstruction at the global finite sum, without asserting an adelic realization or an operator
  product formula. The next global bridge is to specialize the decomposition to products of
  `rationalPrincipalTraceLinear` maps and identify each block as a source-attached rational
  correspondence endomorphism; finite-place Hecke structure still requires that product theorem,
  then an adelic realization agreeing with the completed real model.
- **Mackey trace composition closed (current corpus, 2026-09-16).**
  `SelbergMaassMackeyTraceComposition.maassTrace_mackey_compose` proves the actual finite product
  mechanism: trace from `G` to `H`, restrict to the image of `J ≤ H`, then trace to an outer
  finite-relative-index target `K`; the result is exactly the finite sum of direct outer traces of
  the stabilized double-coset pullbacks. The proof establishes the canonical-representative
  summand law `maassTraceQuotientFunc_eq_out`, interchanges the two literal finite sums, and uses
  `maassTrace_block_then_outer_eq_direct` to flatten every block by nested transitivity. This
  closes Mackey composition without a heartbeat increase, an adelic premise, or an added axiom.
  What remains is a specialization of this general formula to the two
  `rationalPrincipalTraceLinear` maps, including the subgroup-intersection identification that
  selects `J`; only after that specialization can the finite correspondence algebra be presented
  as source-attached finite-place Hecke data. The global adelic realization and compatible
  symmetric-power lift remain separate unsolved bridges.
