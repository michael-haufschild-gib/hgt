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
- **Literal-trace coherence and rational Mackey product closed (current corpus, 2026-09-16).**
  `maassTraceFunction_congr_source` proves that a finite Maass trace is invariant under changing
  its source presentation when the induced target subgroup and underlying function agree;
  `maassTrace_restrict_subgroupOf_eq` resolves the intersection presentation required by the
  outer trace.  Therefore `maassTrace_mackey_compose_subgroupOf` is a literal two-stage finite
  trace product formula, rather than a restricted surrogate.  The new
  `rationalPrincipalTrace_mackey_baseChange` combines exact rational trace/pullback base change
  with that theorem: composing the source-attached rational traces for `g` and `h` equals the
  finite Mackey sum from `(P^g)^h`, whose subgroup is exactly `P^(g*h)` by the existing
  `rationalPullbackConjugateGroup_mul`.  Source check and targeted leaf builds pass without
  changed heartbeats; theorem-level axioms remain ordinary Lean foundations.  This supplies the
  finite-correspondence product law needed before finite-place data can be extracted.  It does
  **not** identify each stabilizer block with a rational principal endomorphism, construct an
  adelic realization/local factor, or produce any symmetric-power lift or exponent bound.
- **Principal Hecke-coset descent closed (current corpus, 2026-09-16).**
  `positiveRationalGLRealImage` is the actual positive-rational correspondence monoid in
  `GL(2,R)`. `principalCongruenceGL_isHeckeTriple_positiveRational` proves it contains and
  commensurates the principal source group, so it is a Mathlib `IsHeckeTriple`. The two exact
  invariances `rationalPrincipalTrace_right_mul_principal` and
  `rationalPrincipalTrace_left_mul_principal`, combined in
  `rationalPrincipalTrace_eq_of_principal_doubleCoset`, prove that the literal source trace is
  constant on principal double cosets. `rationalPrincipalHeckeCosetTrace` and
  `rationalPrincipalHeckeCosetLinear` consequently descend the trace to a closed complex-linear
  endomorphism for every Mathlib Hecke-coset basis element and every fixed Maass eigenspace.
  This eliminates representative ambiguity from the finite-place bridge. The next exact
  obstruction is convolution: Mathlib's installed Hecke file supplies only the coset/module
  carriers, while the corpus Mackey product still has stabilizer-block terms not identified as
  a finite combination of these descended basis endomorphisms. The larger adelic realization,
  compatible local factorization, and symmetric-power lift remain open.
- **Mackey multiplicity engine closed (current corpus, 2026-09-16).**
  `maassTraceFunction_eq_card_smul_of_targetInvariant` proves that an unnormalised finite trace
  of a function already invariant under its target is exactly the relative-coset cardinal times
  that function. `maassTraceFunction_eq_card_smul_of_le_of_targetInvariant` combines this with
  exact nested trace transitivity: for `L ≤ M ≤ K`, the outer trace from `L` is the relative
  multiplicity `[M:L]` times the outer trace from `M` whenever the source function is
  `M`-invariant. This is the precise coefficient law required to collapse a stabilizer block.
  The unresolved finite-algebra step is now concrete: identify each rational Mackey block's
  stabilizer source `L` as a finite-index subgroup of the relevant rational correspondence
  source intersection `M`, and prove its literal block pullback agrees with the `M`-invariant
  rational pullback. Only then does the existing Mackey sum become Hecke convolution.
- **Rational Mackey block source and finite index closed (current corpus, 2026-09-16).**
  `rationalMackey_blockPullback_eq_rationalPullback` identifies the literal function in a
  rational principal Mackey block with pullback by `g * h * b⁻¹`, where `b` is a rational lift
  of its relative-coset representative. `maassDoubleCosetBlockSource_eq_conjugate_inf` proves
  its mapped stabilizer source is exactly the intersection of the conjugated ambient source and
  mapped acting source. In the principal rational specialization,
  `rationalMackey_blockSource_le_rationalDoubleCosetSource` and
  `rationalMackey_blockSource_isFiniteRelIndex_rationalDoubleCosetSource` prove that this source
  lies in, and has finite relative index in, `P^(g*h*b⁻¹) ∩ P`. The finite-index argument uses
  rational-conjugate arithmeticity and arithmetic-intersection commensurability. The leaf module
  is source-checked and targeted-built; theorem axiom audits report only `propext`,
  `Classical.choice`, and `Quot.sound`. The finite bottleneck is now exact reindexing of the
  Mackey orbit sum by rational double cosets with these relative-index multiplicities; that
  coefficient identity is required for convolution.
- **Rational Mackey block coefficient collapse closed (current corpus, 2026-09-16).**
  `rationalMackey_blockTrace_eq_card_smul_rationalTrace` proves the exact analytic summand law:
  the outer trace of each actual principal rational Mackey block is the cardinality of its
  stabilizer-source quotient times the direct rational trace labelled by `g*h*b⁻¹`. The proof
  combines the literal block-pullback identity, the finite-index bridge into
  `P^(g*h*b⁻¹) ∩ P`, nested trace multiplicity, and source-inside-target trace coherence. It
  therefore closes the per-block coefficient calculation without an adelic assumption or added
  axiom. The remaining finite problem is global reindexing: construct and prove the relation
  between the Mackey orbit set and principal Hecke double cosets, including aggregation of blocks
  whose labels lie in one double coset. Targeted leaf build and axiom audit pass with only
  `propext`, `Classical.choice`, and `Quot.sound`.
- **Actual Mackey-orbit/Hecke-label coherence closed (current corpus, 2026-09-16).**
  `SelbergMaassMackeyOrbitDoubleCoset` proves the exact quotient descender: a relative representative
  `r` has real double-coset label `P · ((g*h) r⁻¹) · P`; this is invariant under its source relation
  and under the actual Mackey acting subgroup. For positive-determinant rational inputs, a chosen
  positive rational lift of `r` produces a positive-rational Hecke-coset label, and
  `rationalMackeyOrbitToHeckeCoset_toDoubleCoset` proves that forgetting its monoid membership
  recovers precisely that descended real label. This resolves representative and orbit coherence,
  with no replacement model. The remaining finite obstruction is aggregation: prove the exact
  finite fiber formula for the Mackey sum under this label, retaining the established stabilizer
  indices, and identify the resulting finite-support coefficient function as correspondence
  convolution. The leaf source check and targeted build pass; the final theorem uses only
  `propext`, `Classical.choice`, and `Quot.sound`.
- **Finite rational Mackey-to-Hecke convolution closed (current corpus, 2026-09-16).**
  `SelbergMaassMackeyHeckeAggregation` now proves the missing global finite algebra step. It
  defines the actual rational Mackey-orbit carrier, each block’s literal outer trace, and its
  exact stabilizer-index multiplicity. For positive-determinant inputs,
  `rationalMackeyBlockTrace_eq_multiplicity_smul_HeckeCosetTrace` identifies every actual block
  with that multiplicity times the descended positive-rational Hecke-coset trace of its canonical
  orbit label. `rationalMackeyBlockTrace_sum_eq_fiberwise_HeckeCosetTrace` then reindexes the
  entire finite Mackey sum over the finite image of the orbit-to-Hecke map; the coefficient of
  each label is the finite sum of its actual stabilizer indices. This makes no false finiteness
  claim about the ambient Hecke carrier. Source check and targeted leaf build pass; both theorem
  axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`. The finite
  correspondence-convolution stage is therefore closed at the level of source-attached Maass
  traces. The next actual barrier is an adelic/local realization that identifies these
  correspondence operators with local factors, followed by an independently constructed
  compatible symmetric-power lift and a generic exponent bound.
- The source frontier advanced: `SelbergMaassHeckeEigenspace` and
  `SelbergMaassRationalHeckeDoubleCoset` define the representative-independent
  endomorphism `rationalPrincipalHeckeCosetLinear` of the actual fixed
  principal-level Maass eigenspace.  `rationalPrincipalTrace_mackey_baseChange`
  and `rationalMackeyBlockTrace_sum_eq_fiberwise_HeckeCosetTrace` already give
  its finite correspondence composition at function level.  Thus the earlier
  bounded search's failure to find a Maass Hecke action is superseded; the
  missing link is not basis-level Hecke action or Mackey composition.
- The direct Hecke-coercivity attempt fails structurally.  A nonzero output of
  any source Hecke linear combination remains in the same exceptional Maass
  eigenspace and hence has strictly negative `coreQuarter` at the transition
  cutoff.  Existing `SelbergMaassTraceAverageNoGo` already proves the
  representative-trace version.  Hecke input can only help by forcing an
  annihilation or incompatible local parameter, not by averaging the signed
  compact-core form.
- The slice-rigidity alternative also has the wrong sign for the quarter
  contradiction.  `exceptional_compact_slice_mass_floor` supplies a
  source-dependent positive mass floor, while `core_quarter_identity` places
  that mass under the negative coefficient `lam - 1/4` for a hypothetical
  exceptional source.  It strengthens the negative side of the existing
  identity and gives no lower bound for `coreQuarter + boundarySum`.
- Deep search at snapshot generation `941269` for the global Hecke bridge
  found `Module.End.exists_eigenvalue`, whose explicit prerequisites are an
  algebraically closed scalar field, nontrivial carrier, and
  `FiniteDimensional`.  A lexical audit of all 112 Lean files containing a
  Maass source/carrier found no finite-dimensionality, local-factor,
  Euler-factor, finite-adele, or adelic-factorization theorem attached to that
  carrier.  The first global bridge is therefore: construct quotient L2
  spectral theory strong enough to prove finite multiplicity of the fixed
  cuspidal Maass eigenspace; a finite-adelic local factorization remains after
  that.  This is a source-audit fact, not a nonexistence assertion about
  mathematics outside the inspected corpus.
- Broad September 2026 arXiv screening under the one-word `automorphic` query
  found a Chenevier orthogonal-polynomial positivity result but no map from its
  kernel or variables to a congruence-Maass source, its Hecke operators, or the
  signed core--cusp functional.  It is rejected from this route pending such a
  source-level map.
- **Rational level-one trace separation is not a corpus route (2026-09-16).**
  `rationalPrincipalTraceFunction` in `SelbergMaassRationalTrace` traces a rational pullback
  back to `principalCongruenceGL N`, its original level; its strongest result is
  `rationalPrincipalTrace_zero_or_eigenform`.  It does not target level one.
  `SelbergMaassDeckAverage.scalarTrace_eq_zero` is a separate full deck average for integral
  congruence data.  Thus these theorems do not compose into a level-one separation argument.
- **The direct source problem has a sharpened exact form (2026-09-16).**
  `core_cusp_quarter_identity` gives
  `coreQuarter + boundarySum + squareSum = (lam - 1/4) * totalMass` for every hypothetical
  exceptional source; `squareSum_nonneg` therefore yields the already formalized strict negative
  upper bound.  Any analytic completion must add a genuinely arithmetic lower bound on the same
  left-hand functional, or an incompatible identity.  Existing phase/closed-period results only
  bound seam/current quantities and do not yet supply that lower bound.
- **Current rigidity closes only a conditional branch (2026-09-16).**
  `SelbergMaassPeriodCurrentRigidity.exceptional_positive_limit_or_flat_node` proves, at every
  positive height of a hypothetical exceptional source, either a strictly positive limiting
  horizontal current or a common source node whose complete horizontal derivative energy is zero.
  The Maass equation available in `SelbergMaassAverageCurrents.eigenfunction_planar_equation`
  constrains only the sum of the two second directional derivatives at a node.  The inspected
  corpus supplies no theorem turning the first-order flat-node alternative, or positive current,
  into a core--cusp quarter lower bound.  This makes that missing conversion the current direct
  route barrier.
- **The archimedean Maass-to-model step is now source-complete (2026-09-16).**
  `MaassModelIntertwiner.modelToMaass` is an injective map from the finite spherical
  complementary model to actual automorphic Maass derivatives, with exact compact action and
  three infinitesimal intertwining identities.  `MaassModelHilbertOrbitDerivatives`
  extends its completed quotient-`L²` image to an isometric complementary Hilbert model and
  proves invariance under every actual `SL2R` quotient unitary
  (`integralSubgroupUnitary_mapsTo_completedModelIsometry_range_SL2R`).
  Hence the earlier “find the Maass-to-model intertwiner” barrier is closed at the real place.
  This representation admits the exceptional parameter by construction; it cannot itself yield
  the quarter contradiction.  The remaining global-route bridge starts at finite-adelic action
  and source-attached local factorization.
- **Source Hecke composition is now an operator equality (2026-09-16).**
  `SelbergMaassHeckeOperatorConvolution.rationalPrincipalHeckeCosetLinear_apply` identifies
  each descended Hecke-coset endomorphism with its literal source trace after evaluation.
  `rationalPrincipalTraceLinear_comp_eq_fiberwise_HeckeCosetLinear` lifts the exact Mackey
  fiber formula from functions to endomorphisms of the fixed principal-level Maass eigenspace:
  the product of the two positive rational trace operators is the finite sum of the descended
  Hecke-coset operators with the established stabilizer-fiber coefficients.  The leaf source
  check and targeted build pass.  This does not construct a finite-adelic group action, a
  canonical placewise factorization, or any symmetric-power lift; those remain the global
  route's first unresolved mathematical bridge.
- **Closed-period cancellation does not reach the quarter functional (2026-09-16).**
  `source_period_product_floor` gives each original period cost a strict
  `8 / (N+1)^2`-scale floor, while `parameterMoment = N*(2*N+1)/12` carries
  the quadratic path factor.  Their product has a genuine level-independent
  lower scale for `N >= 1`.  But the resulting theorem is only a lower bound
  for nonnegative two-period current cost (`limiting_period_cost_lower_of_mean_zero`).
  A source audit found no identity from this cost, or its horizontal-current
  rectangle integral, to `coreQuarter + boundarySum`; it cannot reverse the
  strict-negative core--cusp inequality.
- **Nodal removal is formally ruled out as the direct bridge (2026-09-16).**
  `curvature_restrict_nodes` identifies the residual curvature with curvature
  restricted to the common-source node set, and `curvatureMeasure_noAtoms`
  removes only point atoms.  `SelbergNodalCurvature.nodal_curvature_survives_integration`
  gives the exact local countermechanism: regularized curvature tends to zero
  almost everywhere yet has nonzero limiting integrated nodal charge.
  `SelbergNodalResistance.nodalResistance_tendsto_atTop` gives the matching
  logarithmic resistance divergence.  Thus neither atomlessness nor regulator
  removal can delete nodal residuals; a new global theorem would have to control
  common nodal curves of the whole deck source.
- **Exact active direct target reaffirmed (2026-09-16).**
  `SelbergMaassPhaseStress.core_cusp_phase_stress_bound` reduces the remaining
  source inequality to the signed physical phase-stress record.  Its unresolved
  term contains the weighted top integral
  `∫ x, x * phaseStressXY(point x 1) + phaseStressYY(point x 1)`.
  `SelbergMaassKernelWronskian` proves positivity only for the antisymmetric
  tail Wronskian kernel, not this symmetric weighted stress.  The existing
  local Bessel/DtN no-go therefore leaves exactly a source-attached arithmetic
  Fourier-coefficient relation (the signed varying-modulus boundary comparison)
  as the direct route's active mathematical problem.
- **The first unresolved global bridge is Hecke/right-regular compatibility, not a new
  abstract adelic carrier (2026-09-16).**
  `MaassModelIntertwiner.modelToMaass` and `maassToModel` are inverse linear maps between
  the finite spherical model and the actual differentiated cyclic automorphic space;
  `modelToMaass_spherical` identifies its spherical vector with the original source
  function.  Separately, `maassTraceFunction` is literally the finite sum over relative
  cosets of `f (h⁻¹ • z)`, and a rational Hecke trace is this sum after the literal rational
  pullback `z ↦ f (g • z)`.  Searches of the Maass and rational-Hecke modules found no
  theorem transporting this operator through `modelToMaass`, or proving commutation with
  the right-regular differential directions.  The required exact lemma is to normalize a
  positive-real `GL₂` correspondence to its determinant-one `SL₂` representative and show
  its source action is left translation on the automorphic model; left and right
  translations then commute pointwise.  This would carry the *existing* source Hecke
  algebra into the real model, but would still leave finite-place factorization and lifts
  unresolved.
- **The active signed top term has a precise Fourier reduction target (2026-09-16).**
  `topPhaseFlux_eq` contains the mixed term
  `∫ x in -(1/2)..1/2, x * phaseStressXY N r s f (point x 1)`.
  The corpus proves full source smoothness in `MaassCuspEigenform.contDiffOn`, exact unit
  translation in `phaseStressXY_translation`, and generic absolute Fourier summability and
  pointwise inversion for periodic `C²` functions in `PeriodicFourierDecay`.  The phase-stress
  modules currently expose only continuity because their readout/stress regularity declarations
  stop at finite order.  Thus the next closed target is to carry `C∞` through the finite readouts
  and stress, instantiate that Fourier theorem for this literal term, and then prove an exact
  weighted coefficient identity.  That identity will expose the remaining signed off-diagonal
  arithmetic coefficients; it does not itself establish their sign.
- **The active mixed boundary term has an exact finite same-residue modal decomposition (2026-09-17).**
  `SelbergMaassModalMixedLoss.finiteModal_mixedLoss_sameResidue` retains precisely pairs
  `n ≡ m (mod N+1)`, with the literal horizontal factor
  `conj ((2π n/(N+1)) i)` and the value--height loss
  `coefficientMixedLoss`.  `two_coefficientMixedLoss_eq_deriv_sub_wronskian` gives the exact
  identity `2 mixedLoss = deriv coefficientLoss - coefficientWronskian`; the finite stress is
  therefore a signed same-residue derivative sum minus its Wronskian sum.  Existing tail
  positivity controls only the latter.  Thus the first remaining direct target is an arithmetic
  inequality or cancellation for the derivative sum, not another local positivity claim.
  The direct leaf audit currently stops at the absent dependency Olean
  `SelbergMaassSourceCurrents.olean` before parsing this source file; no completed module audit is claimed.
- **Rational pullback and finite trace are source-level right-regular intertwiners (2026-09-17).**
  `SelbergMaassGLAutomorphicIntertwiner` introduces the literal left-quotient carrier on
  `GL(2, ℝ)`. `glLift_rationalMaassPullbackInvariant_general` identifies the existing rational
  upper-half-plane pullback with left multiplication between the conjugate quotients;
  `glAutomorphicTrace_commutes_right` proves that the existing finite relative-coset trace
  commutes with every right `SL(2, ℝ)` translation; and
  `rationalPrincipalPullbackTrace_lift_commutes_right` composes the two for the actual
  principal-level rational trace. This removes the prior unproved right-regular compatibility
  bridge without choosing a determinant-normalized representative or falsely treating a
  correspondence as an endomorphism before tracing. The targeted leaf build passes and all three
  axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`. This is an
  operator identity in the new `GL(2, ℝ)` carrier. It does not yet construct a map from that
  carrier to `modelToMaass`'s `SL(2, ℝ)` cyclic carrier, nor show that a nonzero trace remains in
  the original cyclic representation. That carrier comparison and range-stability statement,
  then finite-place realization and a generic exponent bound, remain the global obstacle.
- **Actual Maass sources now enter the formal Hecke eigenspace without a carrier gap (2026-09-17).**
  `SelbergMaassGLCorrespondence.integralMaassCuspEigenformToGL` and
  `glIntegralMaassCuspEigenformToMaass` were already inverse-direction source reindexings between
  the real integral quotient and its identical `GL(2,R)` action. The new closed maps
  `glMaassCuspEigenformToEigenspace` and `principalMaassCuspEigenformToHeckeEigenspace` place the
  actual principal-level Maass form in `glMaassCuspEigenspace`, which is the exact domain of the
  existing rational Hecke endomorphisms; `principalMaassCuspEigenformToHeckeEigenspace_ne_zero`
  preserves the required nonvanishing and the `..._apply` theorem records literal equality of
  functions. Thus source-to-Hecke entry is closed. The corpus contains no compact-resolvent or
  fixed-eigenvalue finite-dimensionality theorem, no commuting self-adjoint Hecke family, no
  simultaneous Hecke-eigenvector selection, and no global `GL(2)` attachment. These are the active
  global obstruction; trace preservation of one arbitrarily preselected cyclic line is not required
  for the selection route. The leaf source check passed before the targeted final audit.

- **The corpus double-commutator mechanism has no source-specific Selberg input (2026-09-17).**
  `SchattenDoubleCommutatorRelocation` proves a conditional identity for bounded Hilbert operators
  `Q,B`: it requires a self-adjoint Hilbert--Schmidt skeleton `Q`, a self-adjoint bounded `B`, and
  an already supplied eigenbasis. Its own module documentation states that it neither constructs
  the physical boundary operator `B` nor proves its endpoint determinant identity. Exact scoped
  source search found no Maass/deck/trace commutator theorem instantiating these hypotheses. The
  finite congruence deck is finite-dimensional, but this does not turn the full quotient Maass
  energy or its unbounded Laplacian into the required Hilbert--Schmidt skeleton. Therefore this
  mechanism does not supply the missing complete coercivity `fullMass <= 4 * fullGradient`; the
  direct problem remains the signed source-attached arithmetic boundary comparison.

- **Full transfer-channel summation removes, rather than controls, the diagonal obstruction (2026-09-17).**
  For a fixed input residue `s`, `inversionTransfer_energy_sum` gives
  `sum_r ||T_{r,s} v||² = ||P_s v||²`; summing `phaseAverage_norm` over both residues therefore
  gives exactly `((N+1)^2 - 1) * ||v||²` for the aggregate phase loss, and `phaseAverage_dir`
  gives the same identity for each physical derivative.  This is a closed finite Parseval
  calculation from the inspected declarations, not a new spectral estimate.  The core--cusp
  inequality `core_cusp_phase_stress_bound` uses only the diagonal transfer `T_{r,r}`, because
  its seam is the upper character `r` matched to its inverted lower character.  The full
  `(r,s)` sum has no such core--cusp link and merely rescales the original energy identity;
  it cannot cancel the signed diagonal phase stress in the existing theorem.  The surviving
  direct target is consequently the diagonal same-residue derivative term itself.

- **Real-source and opposite-residue pairing does not cancel mixed phase stress (2026-09-17).**
  This was tested directly against the literal definitions.  For `r=s`,
  `tripleWeight N r r a b c = stdAddChar (r * (b-a-c))`; replacing `r` by `-r`
  conjugates the weight.  If the Maass source is real-valued, the deck permutation in
  `tripleMotion` commutes with coordinatewise conjugation, hence the `-r,-r` phase readout is
  the complex conjugate of the `r,r` readout.  From the literal definition
  `stressXY = 2 * Re(dx * conj(dy))`, both physical derivatives conjugate and `stressXY`
  is therefore unchanged.  Equivalently, under simultaneous `(r,n,m) -> (-r,-n,-m)`, the
  conjugated signed horizontal factor and the conjugated mixed loss have the same real part as
  before.  Opposite residues add their mixed stress; they do not cancel it.  Thus real/imaginary
  reduction of a hypothetical complex Maass form cannot resolve the diagonal derivative term.

- **Varying the cusp cutoff creates no monotone phase bound in the present identities (2026-09-17).**
  `phase_rellich_identity` makes `sidePhaseFlux(Y) + topPhaseFlux(Y)` independent of every
  `Y >= 1`, while `sidePhaseFlux_eq` is the integral up to `Y` of `phaseStressXX`.
  But `phaseStressXX_eq` is the signed difference of horizontal and vertical transfer losses,
  plus potential mass; no sign follows from transfer-loss positivity.  The exact Bessel boundary
  source independently records finite adverse mode blocks and shows their cutoff size is
  unbounded across integer widths at each fixed height (`integer_width_cutoff_unbounded`).
  Hence moving the cutoff only trades the same signed quantity between side and top terms.  It
  cannot produce a level-uniform coercive sign without the missing arithmetic control of those
  signed modes.

- **The current Hecke implementation has no Fourier-coefficient action theorem (2026-09-17).**
  A source-specific deep search for a relation between Maass coefficient derivatives, rational
  Hecke traces, and the signed transfer loss returned no lexical declaration and timed out during
  later ranking; inspected candidates supplied only the modal ODE, coefficient regularity, and
  the existing finite Hecke-trace/Mackey composition.  Exact source search of
  `SelbergMaassRationalHeckeDoubleCoset`, `SelbergMaassHeckeOperatorConvolution`,
  `SelbergMaassMackeyHeckeAggregation`, and `SelbergMaassHeckeEigenspace` found no coefficient
  formula.  This is not corpus-wide absence evidence.  It locates the concrete arithmetic bridge:
  derive the Fourier action of the already defined rational principal Hecke trace and then prove
  a source-specific estimate for the same-residue derivative loss.  Hecke action alone is not a
  Selberg proof—the needed estimate and, for eigenvalue relations, a simultaneous-eigenvector
  selection/local factorization remain open.

- **The principal real and rational-Hecke Maass carriers are now a closed equivalence (2026-09-17).**
  `SelbergMaassGLCorrespondence.integralMaassCuspEigenformGLCorrespondence` packages the two
  existing reindexing maps into an exact equivalence between the integral real `SL(2,R)` source
  and its identical integral `GL(2,R)` action.  It preserves the literal function, nonvanishing,
  Laplace equation, and cusp condition.  The source check and leaf build passed; its axiom audit
  has only `propext`, `Classical.choice`, and `Quot.sound`.  This closes the real-carrier
  dictionary edge needed by rational Hecke traces, but does not construct a finite-adelic action,
  local factors, or compatible lifts.

- **The finite-modal phase-stress obstruction is now strictly off-diagonal (2026-09-17).**
  `SelbergMaassModalMixedLoss` now compiles its exact finite same-residue modal reduction.
  `SelbergMaassKernelWronskian.coefficientLoss_conj_exchange` makes its coefficient loss Hermitian
  under `(n,m)` exchange, while `...coefficientWronskian_conj_exchange` makes the current
  anti-Hermitian.  The new
  `real_weighted_pair_decomposition` proves that each real horizontal pair is exactly the sum of a
  frequency-difference times `Im (deriv coefficientLoss)` and a frequency-sum times
  `-Im coefficientWronskian`.  In the exceptional range,
  `coefficientWronskian_self_eq_zero` and
  `real_weighted_diagonal_mixed_eq_zero` remove every `n=m` contribution.  Source checks and the
  two required leaf builds pass; all five new direct declarations audit with only `propext`,
  `Classical.choice`, and `Quot.sound`.  Thus generic loss positivity and diagonal analysis cannot
  prove Selberg even at finite modal level: its survivor is an off-diagonal same-residue arithmetic
  sum of those two imaginary quantities.  This module has not yet proved that finite modal
  truncations reconstruct the full `sourceDerivative` in the physical boundary integral, so the
  statement does not yet transfer this elimination to the full phase stress.

- **Fixed-height derivative reconstruction is blocked at elliptic regularity, not Parseval (2026-09-17).**
  The corpus proves `coefficient_norm_summable` from the actual `C²` inverse-square coefficient
  bound, and it proves Parseval `HasSum` identities for squared horizontal and vertical coefficient
  norms.  Neither is a vector-valued Fourier reconstruction theorem for `sourceDerivative` at a
  fixed boundary point: multiplying the available `O(|n|⁻²)` bound by one horizontal frequency
  gives only harmonic decay.  The corpus's arbitrary-order theorem
  `deningerSmoothPeriodic_coeff_decay` requires a separately supplied `DeningerSmoothPeriodic`
  object; deep search found no elliptic-regularity bootstrap from the Maass Laplace equation to
  that smoothness.  Thus the finite modal diagonal elimination cannot yet reach physical phase
  stress.  Even an eventual bootstrap would solve only this analytic bridge: the verified finite
  survivor remains the off-diagonal same-residue imaginary derivative/current sum.

- **The real Maass source and rational-Hecke `GL(2, ℝ)` carrier are now exactly equivalent (2026-09-17).**
  `SelbergMaassGLCorrespondence.integralMaassCuspEigenformGLCorrespondence` packages the existing
  reindexing maps into a two-sided equivalence between
  `MaassCuspEigenform (realImage Γ) λ` and
  `GLMaassCuspEigenform (Γ : Subgroup (GL (Fin 2) ℝ)) λ`.  Its maps preserve the literal function,
  nonvanishing, Laplace equation, and integral-cusp decay; the checked declaration depends only on
  `propext`, `Classical.choice`, and `Quot.sound`.  Thus the actual principal Maass source reaches
  the rational-Hecke carrier reversibly, rather than through a one-way source embedding.  This
  closes a real-group dictionary edge only: the carrier still has no source-attached finite-adelic
  local representation, Hecke character selection, or compatible unbounded lift family.

- **The fixed-height derivative bridge now exists in (L^2), with no elliptic bootstrap (2026-09-17).**
  `SelbergMaassFourierPartial` proves the exact substitution identity
  `l2Pair_fourierChar_unitRescaled_eq_coefficient`: after (x=(N+1)t), a unit-interval
  Fourier coefficient is exactly the literal normalized Maass coefficient.  For every continuous
  deck readout, it transports this identity to the source, horizontal derivative, and height
  derivative; each rescaled physical field has closed mean-square convergence of its symmetric
  Fourier partial sums.  The source check and leaf build pass, its six central declarations audit
  with only `propext`, `Classical.choice`, and `Quot.sound`, and the module is imported by the
  `RHTower` umbrella.  This replaces the prior need for pointwise/vector-series reconstruction:
  finite modal fields can now approach physical scalar derivative readouts in (L^2).  It does
  not control the (x)-weighted product in `topPhaseFlux_eq` yet.  That remaining product-limit
  theorem must preserve the same-residue off-diagonal terms, so it is now the direct analytic
  bottleneck before the finite diagonal elimination reaches the physical phase stress.

- **The (x)-weighted mixed-product estimate is now reduced to one convergence assembly (2026-09-17).**
  `SelbergMaassPhaseProductLimit.norm_l2Pair_le_sqrt_l2NormSq` gives closed complex
  Cauchy--Schwarz for the exact unit-interval pairing, and
  `l2NormSq_unitCoord_mul_le` proves that multiplication by the Rellich coordinate is an
  (L^2)-contraction.  Both pass source and leaf checks and audit with only `propext`,
  `Classical.choice`, and `Quot.sound`; the module is wired into `RHTower`.  Combined with the
  six (L^2)-convergence facts in `SelbergMaassFourierPartial`, these estimates reduce the
  physical top-term bridge to a standard telescoping product-limit proof for the horizontal and
  height partial sums, followed by finite deck-coordinate recombination into `lossPair`.  Neither
  step has been asserted yet.  In particular, no sign or cancellation has been claimed for the
  surviving same-residue off-diagonal terms.

- **Finite modal mixed products now converge to physical Maass derivative-readout pairings (2026-09-17).**
  `SelbergMaassPhaseProductLimit.tendsto_l2Pair_unitCoord_fourierPartialSum` proves the
  coordinate-weighted (L^2\times L^2\to L^1) product limit by a closed telescoping argument.
  Its physical specialization `tendsto_unitCoord_sourceReadout_partial_pair` applies it to every
  horizontal and height readout of the literal deck-valued Maass source.  The updated source and
  leaf checks pass; both declarations audit with only `propext`, `Classical.choice`, and
  `Quot.sound`.  This closes the analytic reconstruction gap identified for finite modal
  products: it neither discards nor bounds away same-residue off-diagonal terms.  The next exact
  obstruction is finite deck-coordinate recombination into the transfer form `lossPair`, followed
  by a proof controlling its surviving off-diagonal imaginary derivative/current sum.  No such
  recombination or sign conclusion is present yet.
- `SelbergMaassPhaseStressFourier.phaseStressXYHorizontal_fourierCoeff_neg`
  is closed: opposite Fourier coefficients of the real physical phase stress
  are complex conjugates.  Pairing signs therefore leaves an imaginary-part
  coefficient functional; conjugate symmetry supplies reality of the moment
  but no orientation.  This rules out deriving the needed nonnegativity from
  real-valuedness alone.
- `SelbergMaassPhaseStressFourier.phaseStressXYHorizontal_fourierCoeff_source`
  is closed: every coefficient of the residual centered moment is exactly twice
  the oscillatory integral of `lossPair` applied to the actual horizontal and
  vertical derivatives of the original congruence source.  This gives the
  required exact source attachment.  The remaining sign assertion is an
  arithmetic orientation estimate for these oscillatory derivative-loss
  integrals; neither translation symmetry nor horizontal conservation orients
  them.
- Leaf audit of `SelbergMaassPhaseStressFourier` passed after the coefficient
  attachment and conjugate-symmetry additions.  The three new declarations
  depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- The direct loss-pair query at generation `944116` found generic oscillatory
  magnitude estimates and the existing finite same-residue modal/Wronskian
  decomposition, but no congruence-source sign relation.  Magnitude decay is
  already stronger than needed for the closed absolutely convergent series, so
  these estimates do not orient its signed imaginary coefficient sum and do
  not advance the quarter inequality.
- Whole-route check: `SelbergExceptionalSphericalDegreeFamily` is the closed
  conditional receiver from an infinite compatible unitary degree family to a
  contradiction; `SelbergMaassGLAutomorphicIntertwiner` and the Mackey modules
  provide right-regular/finite-correspondence algebra only.  None produces a
  global lift, local factor, or Fourier action for the actual Maass source.
- Density-route test at generation `944143`: slice rigidity proves strictly
  positive exceptional slice mass and a source-dependent compact-band mass
  floor.  This does not lower-bound density variation or angular energy, while
  the positive horizontal density mean remains.  It therefore cannot prove
  the required level-uniform quartic coercivity `3*D + 4*A >= R`.

- **Completed Maass model now has a closed full local `SL(2,R)` realization (2026-09-17).**
  `MaassModelHilbertRepresentation` restricts literal quotient-`L²` translation to the proved
  invariant range of `completedModelIsometry`, proves the restricted action preserves the Hilbert
  inner product, and transports it through `completedModelRangeEquiv` to
  `completedComplementaryModelRepresentation` on `ComplementaryHilbert`.  The exact theorem
  `completedComplementaryModelRepresentation_intertwines` identifies the transported action with
  quotient translation of the original completed Maass embedding.  Source check and leaf build
  pass; both the range-unitarity theorem and the intertwiner audit with only `propext`,
  `Classical.choice`, and `Quot.sound`.  This closes the local Hilbert-representation arrow.  It
  does **not** construct finite-adelic local factors, a global functorial lift, or an
  unbounded-degree compatible lift family; those remain the only missing producer before the
  already formalized generic-unitarity degree contradiction can apply.

- **No pointwise Möbius-multiplier sign can close the direct phase-stress route (2026-09-17).**
  `SelbergMaassMobiusMultiplierNoGo` proves that the derivative-only top flux
  `2*a*u*v + b*(v^2-u^2)` is indefinite whenever `(a,b) ≠ (0,0)`, and that a
  translation--dilation--special-conformal combination with nonnegative top flux for every
  local derivative jet has all three coefficients zero.  The proof is source-checked, leaf-built,
  and audits with only `propext`, `Classical.choice`, and `Quot.sound`.  This is a no-go for a
  **universal pointwise stress-sign argument**, not a claim that arbitrary jets occur for a Maass
  form.  It leaves the circle-tangent `K-T` current as an additional exact-integral candidate, but
  forces any successful direct proof to add a global relation on the already isolated same-residue
  modal kernel.

- **Rational-trace loops do not yet orient the same-residue loss moment (2026-09-17).**
  The direct corpus searches for rational-cusp Fourier transport and for double-coset
  trace/phase composition found the exact finite orbit-sum theorem
  `maassTraceFunction_doubleCoset`, but no action on
  `phaseStressXYHorizontal_fourierCoeff_source` or on its coefficient-loss kernel.
  `SelbergMaassRationalCuspTransport.rationalGL_cuspidal_pullback` gives the useful exact
  factorization of every rational pullback at an integral cusp into an integral cusp transport
  and an upper-triangular map; current results use it only to transport decay.  Thus the
  specific missing direct bridge is an all-cusp nonconstant Fourier-coefficient transport
  formula, followed by an arithmetic orientation theorem for the resulting finite sum.  This is
  not supplied by trace averaging: `rationalPrincipalTrace_zero_or_coreQuarter_strict_neg_at_transitionCutoff`
  proves that each nonzero rational trace remains exceptional with strictly negative canonical
  compact-core quarter form.  Hence finite positive trace averages cannot create the coercivity
  or signed-loss cancellation required by the Selberg chain.

- **Global-lift producer remains absent after current corpus audit (2026-09-17).**
  The deep Maass/adelic/local-factor/lift search found the real spherical correspondence,
  all-integral-cusp transport, finite rational traces, and the completed local Hilbert
  representation only.  No source-attached finite-adelic local factor, global automorphic lift,
  or compatible unbounded-degree lift family was found.  Therefore the formal generic-unitary
  degree receiver cannot yet be applied to an actual Maass source.

- **`SelbergScattering*` is a separate Xi route, not a Maass route (2026-09-17).**
  The complete family was audited after filename discovery.  Its source declarations are typed by
  `XiZeroCopy`: `SelbergScatteringSourceVector.sourceVector q` is the cusp-subtracted
  `globalResidual q`, and `SelbergScatteringSourceGraph.sourceNativeDomain_equation` is an
  equation for that Xi source and its separate `energyOperator`.  Exact source search found no
  declaration taking `MaassCuspEigenform`, `CongruenceSubgroup`, `phaseStressXY`, or the Maass
  `lossPair` into this operator.  Consequently its residual and entire-eigenvector theorems do
  not advance Selberg's (1/4) chain.  A map from an exceptional congruence Maass source to this
  Xi operator would be a new, stronger unproved correspondence and must not be assumed.

- **The completed local Maass model cannot be substituted for generic symmetric-power
  unitarity (2026-09-17).**
  `completedComplementaryModelRepresentation` has the precise type
  `Representation ℂ SL2R (ComplementaryHilbert lam)`.  By contrast,
  `SymmetricPowerLocalExponentPositive` is an abstract direct sum of rank-one forms indexed by
  the proposed symmetric-power exponent packet.  The audited interfaces contain no map from a
  tensor/symmetric power of the completed `SL2R` model to that packet, no generic-constituent
  theorem, and no finite-adelic action.  Hence tensor-product unitarity of the local model cannot
  establish the receiver's generic packet condition.  The required missing theorem is actual
  generic local classification/compatibility for a source-attached global lift, in addition to
  construction of an infinite compatible lift family.

- **Present rational Hecke data cannot yet select a finite-place eigen-source (2026-09-17).**
  The deep audit found exact finite Hecke-coset composition and Mackey aggregation, including
  `rationalPrincipalTraceLinear_comp_eq_fiberwise_HeckeCosetLinear` and
  `rationalMackeyHeckeFiberCoefficient`.  It found no source theorem that these operators are
  self-adjoint, normal, or commuting, no finite-dimensional spectral realization of a fixed
  Maass Laplace eigenspace, no simultaneous Hecke eigenvector, and no local-factor definition.
  Generic finite-matrix joint-spectrum lemmas do not apply to the function-space eigenspace.
  The positive survivor is a concrete next global bridge: turn the existing Hecke-coset
  convolution into a commuting adjointable operator algebra on a proved finite spectral space;
  only then can it yield finite local eigenvalues.  It cannot presently feed the lift receiver.

- **The completed model is now attached to the actual Maass source orbit (2026-09-17).**
  `MaassSourceModelIntertwiner` defines the canonical vector
  `maassSourceModelVector` by taking the inverse of `completedModelRangeEquiv` at
  `MaassQuotientL2.sourceLp`. It proves
  `completedModelIsometry_maassSourceModelVector` and the full real-group equality
  `maassSourceModelVector_orbit_intertwines`: applying
  `completedComplementaryModelRepresentation g` and then the completed embedding is exactly
  literal quotient-`L²` translation of the actual Maass source by every `g : SL2R`. Source
  audit and leaf build passed; all three exported declarations audit with only `propext`,
  `Classical.choice`, and `Quot.sound`. This removes the real-place source-attachment
  ambiguity in approach 1. It still supplies no finite adelic action, local Hecke factor,
  generic constituent, global lift, or compatible lift family, so it cannot yet trigger the
  generic-unitary exponent receiver.

- **Global finite-multiplicity route currently stops before its first analytic operator (2026-09-17).**
  Deep corpus searches at generations `944985` and `945009` found the actual quotient-`L²`
  source vector and its pointwise Laplace equation, but no Laplacian `LinearPMap` on the
  cuspidal quotient carrier, no cusp Sobolev/Rellich compact embedding, no compact resolvent,
  and no finite-dimensionality theorem for the fixed Maass function space. The generic
  Friedrichs and compact-resolvent lemmas therefore cannot be instantiated. Finite multiplicity
  must concern the right-`K`-fixed Maass/Laplacian space, not the full completed `SL2R` source
  orbit, which contains all `K`-types. The earliest real global construction is a closed
  hyperbolic cusp Sobolev form and compact embedding on that `K`-fixed quotient space.

- **Direct coefficient route remains blocked at arithmetic orientation (2026-09-17).**
  The current deep search returned only generic Wronskian identities and preservation of the
  Laplace equation under rational trace. It found no source-attached all-cusp Fourier transport
  or relation that orients the signed same-residue derivative loss. Thus no local Wronskian
  positivity or trace-eigenfunction statement advances the core--cusp quarter inequality.

- **Commutant bridge has a precise three-part gap (2026-09-17).**
  Existing `rationalPrincipalTrace_restrictToSL_commutes_right` is an exact right-regular
  intertwiner on the function carrier. Scoped audit confirms no bounded quotient-`L²` trace
  operator, no theorem that it maps the source cyclic range to itself, and no Maass-model
  irreducibility theorem. `MaassModelIntertwiner.modelToMaass_range_minimal` does prove
  spherical cyclicity under its two differential directions, with nonzero ladder steps, but
  contains no extraction of a single `K`-type from an arbitrary finite vector. The next local
  bridge is therefore differential irreducibility of `SphericalKFiniteModel`; it still must be
  connected to a bounded source trace before a Schur argument can select Hecke scalars.

- **Compact (K)-finite local irreducibility was already present; the local gap is bounded trace preservation (2026-09-17).**
  `RealPrincipalSeriesCompactIrreducibility.compactSphericalPrincipal_irreducible_of_abs_lt_one`
  proves irreducibility of the compact spherical Harish--Chandra submodule for |`s`| < 1.
  The earlier statement that no Maass-model irreducibility theorem existed was therefore too
  broad. The remaining local obstruction is that no bounded quotient-ℒ² rational trace has
  been proved to preserve the source cyclic range, so this irreducibility cannot yet be used in
  a Schur argument on the actual Maass orbit.

- **Every rational trace component now has an exact source-coordinate cusp Fourier window (2026-09-17).**
  `SelbergMaassAffineFourierTransport` proves the positive upper-triangular affine action and
  exact Fourier dilation/translation formulas. `SelbergMaassRationalCuspFourierTransport` and
  `SelbergMaassRationalCuspFourierCoefficient` attach these formulas to a positive rational
  pullback. `principalCongruenceGL_hasPositiveRationalLifts` supplies positive rational lifts
  for literal target representatives, and
  `rationalPrincipalTrace_summand_cusp_affine` /
  `rationalPrincipalTrace_summand_cusp_fourier_windowed` carry the result through the actual
  `maassTraceQuotientFunc`. All exported declarations were leaf-built and axiom-audited with
  only `propext`, `Classical.choice`, and `Quot.sound`.

- **The finite rational trace has an exact common-width window identity, but not termwise modal orientation (2026-09-17).**
  `rationalPrincipalTrace_cusp_fourier_window_sum` expresses a literal target Fourier
  coefficient as a finite sum of integral-translate source windows with each component's exact
  positive scale and shift. A component becomes a standard source modal coefficient only at its
  adaptive width `(N+1)/scale`; those widths vary with the component. Thus summing individual
  modal character formulas does not produce a common-period sign theorem. The positive survivor
  is the explicit finite window sum now formalized; the remaining direct Selberg theorem must
  orient that sum (or its induced same-residue loss derivative) using arithmetic structure not
  yet present in the corpus.

- **Rational-trace positivity does not yet reach the direct phase obstruction (2026-09-17).**
  Deep corpus search at generation `946423` finds
  `rationalPrincipalTrace_cusp_fourier_window_sum` and its summand theorem, but no declaration
  relating either to `phaseStressXYHorizontal_fourierCoeff_source`, `lossPair`,
  `coefficientMixedLoss`, or `coefficientWronskian`.  This is structural: the trace-window
  identities are linear in the Maass source, whereas the unresolved coefficient is quadratic in
  two source derivatives.  A possible positive route would require first a bounded
  quotient-`L²` rational Hecke correspondence and then a proved quadratic intertwiner showing
  that its `T* T` form controls the same-residue derivative sum.  Neither bridge exists in the
  audited corpus, so trace-window positivity cannot presently orient the weighted top term.

- **The exact rational Hecke algebra is still only linear; its first missing quadratic bridge is now isolated (2026-09-17).**
  `rationalPrincipalTraceLinear_comp_eq_fiberwise_HeckeCosetLinear` already gives the full
  source-level finite Mackey convolution law, while
  `rationalPrincipalTrace_restrictToSL_commutes_right` gives right-regular equivariance on
  function carriers.  Audit of every Selberg--Maass Hecke, trace, quotient-mass, and unitary
  module found no quotient-`L²` Hecke map, adjoint, norm identity, or `T* T` formula.
  `integralSubgroupUnitary` is unitary only within one integral quotient, and its own source
  records that inter-level norm comparison is missing.  The direct bridge is therefore finite
  push--pull along the two coverings from the integral intersection subgroup
  `Γ ∩ g⁻¹ Γ g`, with the quotient-Haar normalization proved before defining the adjoint.
  This is necessary but not sufficient: no current theorem identifies that positive quadratic
  form with `phaseStressXYHorizontal` or `coefficientMixedLoss`.

- **The exact mixed phase loss has its sharp intrinsic Cauchy bound, but this does not orient the Selberg top flux (2026-09-17).**
  `SelbergMaassPhaseLossCauchy.lossPair_sq_le_lossEnergy_mul` proves
  `lossPair(v,w)^2 ≤ lossEnergy(v) * lossEnergy(w)` directly from the existing positive
  inversion-loss quadratic form, and
  `phaseStressXY_sq_le_derivative_losses` specializes it to the literal Maass horizontal and
  vertical derivatives.  Both were leaf-built and axiom-audited with only `propext`,
  `Classical.choice`, and `Quot.sound`.  Substitution in the exact top integrand gives
  `2*x*B + (Ly - Lx) + P`; the new theorem bounds `B` but supplies no relation on `Ly - Lx`.
  Therefore it cannot prove the needed sign or `3D + 4A ≥ R`.  The positive survivor is the
  sharp control of the actual signed coefficient; the next necessary direct target is an
  arithmetic covariance law for the horizontal and vertical diagonal losses (equivalently, for
  the same-residue Fourier loss derivative), not another generic positivity estimate.

- **Full residue averaging exactly destroys the finite arithmetic loss; it cannot orient Selberg's selective channel (2026-09-17).**
  `SelbergMaassAllChannelLoss.allChannel_lossEnergy_sum` proves
  `Σ_{r,s} lossEnergy r s v = ((N+1)^2 - 1) ‖v‖²`, and its polarization
  `allChannel_lossPair_sum` proves that the corresponding mixed form is only
  `((N+1)^2 - 1) Re⟨v,w⟩`.  The proof uses the actual transfer-column Parseval identity,
  not an estimate.  Both declarations were leaf-built and axiom-audited with only `propext`,
  `Classical.choice`, and `Quot.sound`.  Thus all-channel averaging restores the ambient
  scalar metric and loses the finite transfer defect; it cannot constrain the diagonal-residue
  phase stress that appears in the core–cusp inequality.  The surviving direct target remains a
  selective-residue covariance or an exact same-residue Fourier law.

- **Finite phase-readout products now recombine before the limit, closing the deck-coordinate analytic bridge (2026-09-17).**
  `SelbergMaassPhaseProductLossLimit.tendsto_phaseProductPartial` sums the finite
  `PhaseIndex` family of source-attached horizontal/height Fourier partial products and proves
  convergence to the corresponding literal phase-readout product.  This is the exact finite
  phase family whose normalized real part is identified pointwise with `lossPair` by
  `phaseAverage_pair`; it preserves every same-residue cross term.  The source check and leaf
  build pass, and its axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
  The remaining analytic calculation is explicit, not a missing reconstruction theorem: change
  from `t` to physical `x=(N+1)t`, use unit periodicity, and separate the centered top moment
  from the mean.  That calculation exposes the already isolated signed same-residue series; it
  cannot create its required arithmetic orientation.

- **The phase-product limit is now the exact literal mixed-loss moment (2026-09-17).**
  `SelbergMaassPhaseProductLossLimit.phaseProductExact_re_eq_unitLossMoment` proves
  `Re phaseProductExact = ∫₀¹ t · lossPair(F_x((N+1)t+i), F_y((N+1)t+i)) dt` for the
  actual source derivatives and the same finite phase family used by the core--cusp route.
  Its proof identifies each rescaled readout with its physical derivative, applies the exact
  finite phase average, and moves only finite sums through the interval integral.  Source check
  passes.  This removes the last analytic ambiguity between the phase-product limit and the
  selective source loss; it leaves the same-residue off-diagonal orientation unchanged.

- **The current inversion-transfer interface does not provide same-residue scalarity (2026-09-17).**
  `inversionTransfer_coefficientVector` and `inversionTransfer_coord` give an explicit
  character-projection/finite-regular-action transform, while
  `inversionTransfer_energy_sum` gives its all-output energy identity.  The direct deep search
  found no theorem making this transform scalar on a same-residue component, nor any theorem
  forcing the off-diagonal `coefficientLoss` or `coefficientWronskian` imaginary part to vanish.
  Thus those transfer identities cannot presently close the paired formula
  `real_weighted_pair_decomposition`; a new source-attached global coefficient relation is still
  required.

- **Level raising does not thin the same-residue collision channel (2026-09-17; paper no-go).**
  For a source already periodic with period `q`, its Fourier expansion regarded at period
  `Q = kq` has support only at indices `ka`.  The selective condition at the raised level is
  `ka ≡ kb (mod kq)`, which is equivalent to `a ≡ b (mod q)`.  Thus this proposed way to
  force finite partial sums toward the diagonal only rescales the original collision classes;
  it cannot orient the off-diagonal source series.  No source-level period-change/coefficient
  transport theorem was found in the current corpus, so this is recorded as a paper-level no-go,
  not a formal theorem.

- **Leaf audit completed for the exact phase-product loss moment (2026-09-17).**
  `lake build GaloisForLFunctions.RHTower.SelbergMaassPhaseProductLossLimit` passes.  Both
  `tendsto_phaseProductPartial` and `phaseProductExact_re_eq_unitLossMoment` have axiom audit
  exactly `[propext, Classical.choice, Quot.sound]`.

- **Selective mixed-loss mean is exactly zero in the exceptional range (2026-09-17).**
  `SelbergMaassPhaseProductMean.unitLossMean_eq_zero` proves, for every phase selector,
  `∫₀¹ lossPair(F_x((N+1)t+i), F_y((N+1)t+i)) dt = 0`.  Its finite partial theorem first
  uses Fourier orthogonality to retain only equal frequency indices.  Finite phase averaging
  turns each surviving summand into the literal selective loss, and
  `real_weighted_diagonal_mixed_eq_zero` proves it zero.  The new unweighted pairing limit
  `tendsto_l2Pair_fourierPartialSum` passes this cancellation to the source pairing.
  `SelbergMaassPhaseProductMean` is wired into `RHTower.lean`; its leaf build passes and both
  `phasePairPartial_re_eq_zero` and `unitLossMean_eq_zero` audit only
  `propext`, `Classical.choice`, and `Quot.sound`.  Hence the phase-product construction has no
  residual mean term.  The unresolved direct problem is precisely the centered moment, already
  represented by the source-attached same-residue off-diagonal Fourier series.

- **Zero mean and periodicity do not orient the centered loss moment (2026-09-17; paper no-go).**
  The new mean-zero theorem cannot by itself make the centered moment vanish: the smooth real
  unit-periodic function `sin(2πx)` has zero mean and a nonzero centered first moment.  Thus the
  direct proof cannot replace the remaining same-residue orientation theorem by periodicity,
  real-valuedness, or the new mean cancellation.  Any successful final step must use genuinely
  automorphic arithmetic information about the coefficient kernel.

- **The literal zero automorphic ladder is now identified with the completed-model source (2026-09-17).**
  `MaassLadderSourceIntertwiner.raisedFunction_zero_eq_sourceFunction` proves that inversion of
  `raisedAutomorphic f 0` is literally `MaassQuotientL2.sourceFunction`; its `L²` consequence
  `raisedLp_zero_eq_sourceLp` identifies their AE classes.  Hence
  `completedModelIsometry_maassSourceModelVector_eq_raisedLp_zero` and
  `maassSourceModelVector_orbit_intertwines_raisedLp_zero` attach the canonical completed
  complementary-model vector to the literal all-order automorphic ladder and its full real
  `SL(2,ℝ)` orbit.  The leaf build passes and all four theorems audit only `propext`,
  `Classical.choice`, and `Quot.sound`.  This closes a real-place identification gap; it has no
  finite-place action, restricted tensor product, global automorphic lift, or symmetric-power
  compatibility, so it does not reduce the remaining approach-1 global-lift obstruction.

- **Exceptional Maass sources now have a finite-deck equivariant Dirichlet completion (2026-09-17).**
  `MaassFiniteDeckDirichlet.formPreDomain` is the submodule of finite-deck-valued chart-C¹
  functions satisfying literal `SL2Z` regular-representation covariance and L² admission of
  their value and two hyperbolically weighted chart derivatives.  For an exceptional source,
  `sourceHypGrad_energy` identifies the sum of squared weighted derivative norms with the
  established `hyperbolicGradient`; `sourceHypGradX_memLp` and `sourceHypGradY_memLp` discharge
  both derivative coordinates.  `sourceInFormPreDomain` gives the source as an element of this
  exact pre-domain.  Its three-coordinate L² closure and `formInclusion` are constructed, and
  `formInclusion_sourceFormVector` identifies the completed source value coordinate with the
  existing nonzero `sourceLp`.  The current formal frontier has no theorem that this completed
  value-coordinate map is injective or compact, and no closed cuspidal subspace; these are the
  next finite-multiplicity obligations.  No scalar modular domain is used.

- **Finite-deck form coordinates are rigid on the pre-domain, but this does not establish closability (2026-09-17).**
  `MaassFiniteDeckDirichlet.formEmbeddingMap_injective` proves that the three-coordinate
  finite-deck form embedding is injective. Equality of its value L² coordinate gives equality
  almost everywhere on `fd`; chart-C¹ continuity upgrades that equality to the closed cell, and
  literal regular deck covariance transports it to all of `ℍ`. This is a closed proof of
  pre-domain rigidity. It does not imply injectivity of `formInclusion` on the topological
  closure, so it does not supply the closability or compact-resolvent premise required by the
  Friedrichs route.

- **Existing scalar closability isolates a coordinatewise finite-deck route (2026-09-17).**
  `HTGeometry.ModularDirichletFormClosable.formInclusion_injective` proves scalar closability by
  compactly supported interior tests, local integration by parts, and the chart fundamental
  lemma. Its integration-by-parts input is local to chart-C¹ functions; scalar modular invariance
  is not used in that argument. Therefore the exact next formal target is a finite-deck
  coordinatewise version of its test functionals and integration-by-parts identities, followed by
  the same fundamental-lemma argument for every deck coordinate. This would prove injectivity of
  the completed `MaassFiniteDeckDirichlet.formInclusion`. No such vector theorem currently occurs
  in the corpus. Compactness remains a separate cuspidal-tail obligation.

- **Finite-deck interior integration by parts is now formalized coordinatewise (2026-09-17).**
  `MaassFiniteDeckDirichletIntegrationByParts.component_c1` and the two
  `component_hypGrad*` theorems identify every deck coordinate of a finite-deck pre-domain
  element and its weighted derivatives with the scalar modular chart data. Consequently
  `component_testWeight_hypGradX` and `component_testWeight_hypGradY` transfer the scalar
  compact-interior integration-by-parts identities to every deck coordinate. Their leaf build
  and axiom audit pass with only `propext`, `Classical.choice`, and `Quot.sound`. This is the
  local weak-derivative input for completed-form closability; remaining work is to construct
  coordinate test functionals on the completed triple and apply the chart fundamental lemma.

- **The finite-deck Dirichlet inclusion is now closed and injective (2026-09-17).**
  `MaassFiniteDeckDirichletIntegrationByParts.componentL2_toModularL2` identifies each
  finite-deck coordinate projection with the existing scalar modular `L²` class, for every
  vector-valued `L²` function.  The two `componentTestFunctional_formEmbeddingMap_*` theorems
  put the literal horizontal and vertical integration-by-parts constraints into continuous
  scalar functionals on the vector form triple.  Their kernels contain the completed form
  domain.  The scalar chart fundamental lemma then makes every derivative coordinate projection
  vanish when the value coordinate vanishes, and
  `deckL2_eq_zero_of_forall_componentL2_eq_zero` recombines the finite deck coordinates.
  Consequently `formInclusion_injective` is a closed proof of finite-deck Dirichlet closability.
  The leaf build passes and its audited declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`.  The next finite-deck obstruction is separate: define the closed cuspidal tail
  condition and prove its compact resolvent; this result does not create the global compatible
  symmetric-power lift required by approach 1.

- **No finite-cover quotient-`L²` transfer exists in the current corpus (2026-09-17; source audit).**
  Deep search for a finite-index quotient pullback, its norm, and a finite direct-sum decomposition
  found no declaration. Mathlib does provide the needed generic ingredients: finite quotients from
  `Subgroup.FiniteIndex` and fundamental-domain measure decompositions. Thus the missing finite-place
  bridge is a new measure-comparison theorem for the exact common cover, not an already formalized
  Hecke boundedness result.

- **Rational Hecke correspondence has a closed integral common cover (2026-09-17).**
  `MaassRationalHeckeIntegralIntersection` defines
  `Γ(N+1) ∩ (rationalConjugateGroup N g).comap (mapGL ℝ)`.  It proves finite index in
  `SL(2,ℤ)`, finite relative index over `Γ(N+1)`, and the exact real identity
  `realImage(commonCover) = realImage(Γ(N+1)) ∩ rationalConjugateSL2Group`.
  `rationalConjugateSL2Group_map_toGL` also proves that the determinant-one real source maps
  onto the full rational conjugate GL source.  Leaf source check and build pass; all four
  declarations audit only `propext`, `Classical.choice`, and `Quot.sound`.  This removes the
  group-domain mismatch for a Hecke `L²` correspondence, but no quotient-measure comparison,
  trace norm, finite-place local factor, or global compatible lift is proved.

- **The actual Maass source has an `L²` lift to every rational common cover (2026-09-17).**
  `MaassRationalHeckeIntegralCoverL2` constructs the measurable, surjective quotient projection
  from the common-cover quotient to the principal quotient.  It restricts each principal Maass
  cusp eigenform to the cover and proves its quotient function is pointwise the pullback of
  `MaassQuotientL2.sourceFunction`; finite covolume then proves its `L²` admission.  The leaf
  build passes and audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
  The unsolved next edge is exact finite-cover quotient-measure scaling. Without it, the pointwise
  pullback has no proved norm formula and cannot yet be promoted to a bounded Hecke `L²` operator.

- **A finite-index integral cover now has a closed Haar fundamental selector (2026-09-17).**
  `IntegralSubgroupFiniteCoverDecomposition` proves the required left form of a Mathlib right-coset
  representative, `a = k q.out⁻¹`, and proves equality of two such decompositions forces equality
  of their quotient cosets. `IntegralSubgroupFiniteCoverFundamentalDomain` uses those results to
  construct the finite union `⋃ q, q.out • F_Γ` and prove that every `SL(2,ℝ)` point has exactly
  one `(realImage K).op` translate in it. It therefore supplies an
  `IsFundamentalDomain (realImage K).op` for every finite-relative-index inclusion `K ≤ Γ`.
  Source checks, its leaf build, and audits of all five declarations pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. This closes the selector and disjointness part of the
  finite-cover measure problem. The remaining statement is additivity of Haar measure across its
  finite translated pieces and its transfer to the quotient measures.
