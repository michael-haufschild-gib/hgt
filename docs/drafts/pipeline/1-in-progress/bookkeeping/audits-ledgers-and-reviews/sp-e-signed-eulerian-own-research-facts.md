# SP-E signed-Eulerian research facts

- `suzukiWordCoefficient k ν` is exactly a Volterra grade factor times the commutative product of
  the prime-power weights of `ν i`.  It is independent of every `Bool` orientation label and
  invariant under every `Equiv.Perm (Fin k)` reindexing.
- The associated physical inverse-log profile has the same invariance.  Hence this scalar/profile
  carrier cannot instantiate the SP-E open-core signed type-B word action.
- In particular, the physical coefficients of the two four-label orders `3142` and `3241` are
  equal for arbitrary prime-power labels and arbitrary independent Boolean assignments.  The
  carrier loses the first descent-bottom discriminator before a stable top-fibre specialization.
- Lean proof: `formal/GaloisForLFunctions/RHTower/PrimeGammaPhysicalWordHyperoctahedralBlindness.lean`.
- Positive survivor: P-G186's off-diagonal Cauchy Gram retains pair incidence absent from the
  scalar word coefficient.  Its zero-ordinate base edge is `2/(x+y)^3`; every ordered positive
  four-packet has strictly positive signed-Eulerian curvature, and every positive diagonal source
  transport preserves it exactly.  Thus the P-G186 pair source passes the four-label
  descent-bottom discriminator.
- Lean proof: `formal/GaloisForLFunctions/RHTower/PrimeGammaCauchyCubicSignedEulerianCurvature.lean`.
- No corpus theorem presently maps this pair incidence to completed signed-word columns or a
  type-B insertion action.  That categorical source bridge remains open.
- The literal Suzuki source has a non-abelian carrier before scalar word formation: for a strict
  physical aperture and the oriented prime steps `+e_2`, `-e_3`, the `2,3,7` valuation path has
  one retained and one pruned intermediate vertex.  Therefore the exact compressed products
  `P U_(+e_2) P U_(-e_3) P` and `P U_(-e_3) P U_(+e_2) P` differ.  This is source-derived
  chronological data, not a postulated word order.
- The uncompressed translations commute.  Thus order arises exactly from physical aperture
  compression, not from an invented noncommutative prime alphabet.
- The compressed operators for any two nonnegative seam displacements commute globally.  Hence
  the proved `2,3,7` chronology effect requires a genuine orientation reversal, not merely
  unequal positive primes.
- The actual positive-label Suzuki operator is not a single outward translation but the compressed
  symmetric step `P (U_δ + U_δ*) P`.  It is exactly the sum of its two oriented branches, and the
  literal positive prime steps for `2` and `3` have noncommuting compressed symmetric products
  at a positive physical aperture.  This supplies source-derived order for positive labels without
  assigning an artificial sign to a prime letter.
- Lean proof: `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiOrientedPrunedPathChronology.lean`.
- Route consequence: the remaining categorical bridge must preserve this oriented,
  support-pruned path algebra into P-G186 Julia columns and then establish its Type-B insertion
  law.  Passing first through `suzukiWordCoefficient` is ruled out by the blindness theorem above.
- For every positive literal matched polar cell, its mass-coordinate barycentre `b_n` satisfies
  the exact law `b_n^2 = 4 n + w_n^2 / 4`, where `w_n` is the critical-Mellin atom weight.  Since
  `0 ≤ w_n ≤ 2`, `n ↦ b_(n+2)` is strictly increasing without a prime-gap hypothesis.
- Every literal parabolic cross kernel is exactly `- orientationLedger - displacementDebt`.
  The debt is nonnegative.  For an ordered pair, the geometric coefficient in the ledger is
  nonnegative; for adjacent cells, the signed ledger is exactly the literal matched-cell
  overlap/gap times that coefficient.  Thus all source indefiniteness is confined to one
  all-scale signed orientation ledger, not an additional unknown geometry or a hidden quadratic
  term.
- This does not close SP-E: `SPEQuantileRieszParabolicPhysicalWall` proves that the completed
  Riesz readout additionally retains physical-wall/source-barycentre and terminal-mass mismatch
  terms.  A successful producer must control those literal channels together with the new ledger;
  a sign theorem for the strict-cross current alone would be insufficient.
- Lean proof: `formal/GaloisForLFunctions/RHTower/CCM/CCMActualHeadMatchedQuantilePolarParabolicOrientationLedger.lean`
  (`lake env lean` direct module check passed; no umbrella build run).
- The ordered all-pair orientation ledger is exactly twice the weighted covariance numerator of
  matched--quantile displacement with the matched-cell barycentre.  Consequently the complete
  strict-cross source current is exactly `-2 * covariance - displacementDebtSum`; the debt is
  retained and nonnegative.  Thus the sole remaining signed channel is one literal global
  displacement--centroid covariance, and the hard missing theorem is a source-faithful
  covariance--debt cancellation law—not any local overlap/gap estimate or diagonal energy bound.
  This is now formalized in
  `formal/GaloisForLFunctions/RHTower/CCM/CCMActualHeadMatchedQuantilePolarCovarianceHardCore.lean`;
  direct checks and the narrow axiom audit use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- The same literal covariance has an exact adjacent matched-gap representation only after Abel
  summation against a cutoff-dependent global prefix-mass/prefix-centroid kernel.  This retains
  all-pair information and rules out replacing the hard cancellation by a local gap energy;
  any bridge to a fixed inverse-incidence primitive requires an explicit new source map.
  Formalized and axiom-audited in
  `formal/GaloisForLFunctions/RHTower/CCM/CCMActualHeadMatchedQuantilePolarCovarianceHardCore.lean`.
- No cutoff-independent coefficient sequence equals that literal kernel at every finite head:
  its first coefficient is strictly larger at head `3` than at head `2`, with exact increment
  `weight(2) * weight(5) * (centroid(5) - centroid(2))`.  Thus P-G86's fixed adjacent primitive
  cannot be directly coefficient-preserving for SP-E.  This is not a no-go for a new explicit
  transformed source map.  Formalized and axiom-audited in
  `formal/GaloisForLFunctions/RHTower/CCM/CCMActualHeadMatchedQuantilePolarCovarianceHardCore.lean`.
- The global Abel kernel obeys an exact causal cutoff update: appending atom `K + 3` changes each
  retained gap coefficient by its weight times its matched-centroid excess over that gap's prefix.
  Any nonlocal inverse-incidence bridge must preserve this history law, not merely adjacent-gap
  support.  Formalized and axiom-audited in
  `formal/GaloisForLFunctions/RHTower/CCM/CCMActualHeadMatchedQuantilePolarCovarianceHardCore.lean`.
- At every prime-power append, this update is strictly positive for every already-visible gap.
  Hence each new prime atom broadcasts into the entire retained SP-E gap history; an inverse that
  only appends a local edge cannot be source-faithful. Formalized and axiom-audited in
  `formal/GaloisForLFunctions/RHTower/CCM/CCMActualHeadMatchedQuantilePolarCovarianceHardCore.lean`.
- Every coefficient visible in a finite SP-E head is nonnegative.  Therefore the exact Abel
  reduction puts all unresolved sign/cancellation in the literal oriented quantile gaps, not in
  the nonlocal inverse kernel. Formalized and axiom-audited in
  `formal/GaloisForLFunctions/RHTower/CCM/CCMActualHeadMatchedQuantilePolarCovarianceHardCore.lean`.
- After multiplication by the literal completed source mass, the actual SP-E physical-wall Riesz
  readout is exactly: twice that global adjacent-gap current, plus the full displacement debt,
  plus completed terminal interaction/form, plus both physical-wall gauge terms.  The equation
  retains every source term and is formalized/axiom-audited in
  `formal/GaloisForLFunctions/RHTower/SPEQuantileRieszParabolicCovarianceHardCore.lean`.
- Let `x_n = outgoingNodeError(n+2) + upperExcess(n+2)`, `w_n` be the atom weight, and `b_n` the
  matched barycentre.  Existing first- and second-moment identities give the exact finite,
  uncompleted physical-wall algebra
  `-sqrt(M) C_1 + C_2 = Σ_n w_n (x_n (b_n-sqrt(M)) - x_n^2/2)`
  `= (1/2) Σ_n w_n ((b_n-sqrt(M))^2 - (x_n-(b_n-sqrt(M)))^2)`.
  It supplies only a one-sided local square completion with an uncontrolled deterministic
  baseline; it is not the terminal-completed, two-sided SP-E bound.
- The actual SP-E and Suzuki discrepancies share the same completed outgoing charge.  Its exact
  uniformly conditioned three-sample representation by
  `unitRieszCoherentCompletedShiftCodiagonal` at `0`, `log N`, and `2 log N` was already
  formalized in `SPEQuantileRieszRelativeCarrier.lean`; it is not new knowledge.  No direct theorem
  was found connecting those arithmetic samples to uniformly bounded CCM/HG graph energy; existing
  graph-energy results concern freely chosen coherent packets.  This remains a concrete shared
  producer obligation, not a proof of RH.
- The attempted bulk bridge from the SP-E Riesz aperture family to the literal outgoing quadratic
  Stieltjes action fails at the physical wall.  With `H = log M`, the SP-E kernel is
  `2 * (exp ((H+h)/2) - exp h)` and vanishes at `h = H`; integrating such kernels over apertures
  up to `H` has a double terminal zero, whereas the Stieltjes cutoff `H^2-h^2` has a simple zero
  (derivative `-2H` for `H>0`).  Thus no bulk-only aperture superposition can be that source bridge.
  A genuine endpoint or finite-difference channel is necessary; this identifies the physical-wall
  residual as structural, not bookkeeping.
- The Route-P zero-ordinate Cauchy-cubic kernel has the exact ray-Laplace Gram realization
  `2 / (x+y)^3 = ∫_{(0,∞)} (t exp(-x t)) (t exp(-y t)) dt` for `0 < x+y`.  This is now an
  unconditional Lean theorem in `PrimeGammaCauchyCubicLaplaceGram.lean`, with only Lean's standard
  logical axioms (`propext`, `Classical.choice`, `Quot.sound`).  It gives the precise analytic
  target for a source-faithful two-port lift of pruned Suzuki histories.  The existing diagonal
  Cauchy realization covers only the exponent-one, endpoint/coordinate carrier and therefore
  does not provide that chronological lift or any RH conclusion.
- The literal first type-B top-fibre collision is now separated on the Route-P side: for every
  strictly increasing positive four-packet `x`, the Cauchy-cubic descent-edge weight of `3241` is
  strictly less than that of `3142`, although their complete type-B top signatures are equal.  The
  exact difference is the existing four-label Cauchy-cubic curvature.  This is an unconditional
  Lean theorem in `PrimeGammaCauchyCubicSignedEulerianWordSeparation.lean`, audited with only
  `propext`, `Classical.choice`, and `Quot.sound`.  It establishes the smallest required
  descent-bottom incidence certificate in P, but not a Suzuki-to-P source map or Type-B insertion
  law.
- Consequently the actual Route-P Cauchy-cubic descent-word weight cannot factor through the
  complete type-B top signature on any strictly ordered positive four-packet.  This closes the
  top-signature-only P-lift class, while identifying ordered descent-bottom incidence as an
  irreducible port of any surviving lift.
- The literal Suzuki source now has a public finite-word action
  `suzukiSupportPrunedSymmetricHistoryAction`: concatenation is operator composition, and a
  physical `2,3,7` source/readout witness gives amplitudes `1` and `0` for its two opposite
  two-letter words.  `SuzukiSupportPrunedHistoryAction.lean` is unconditional and audited with
  only `propext`, `Classical.choice`, and `Quot.sound`.  It supplies the source-side history port
  needed to state an honest lift; no map to P, compression law, or RH conclusion has been claimed.
- The source-side port is genuinely signed: the oriented free-word action on seam valuations has
  the same concatenation law, and the physical word `[+e_2,-e_3]` versus its reversal has literal
  amplitudes `1` and `0` at one retained source/readout pair.  The negative valuation is a source
  branch, not an added sign.  This is publicly available through
  `SuzukiSupportPrunedHistoryAction.lean` and standard-axiom audited.
- The Route-P fourth-depth `1/64` normalization debt is already locally source-realized, not merely
  an abstract target: `RoutePFourthDepthCoPoissonJuliaKreinPivot.lean` constructs the unique
  negative Julia--Krein co-Poisson pivot with cross `(sqrt 63 / 8) w`, and
  `RoutePFourthDepthGammaCyclicJuliaIntertwiner.lean` identifies its defect operator with the
  literal Gamma-cyclic operator.  The unresolved P hard core is cofinal, source-faithful assembly
  with the needed oriented/Stokes history and a valid Xi-divisor landing; the positive
  aperture-wall determinant landing is formally ruled out by
  `RoutePPrimitiveGammaJuliaStokesApertureWallXiDivisorNoGo.lean`.
- The literal SP-E profile has an exact endpoint, rather than bulk-aperture, Route-P port.  For
  `M > 0`,
  `speQuantileRieszProfile M h = 2 M * integral_(s=1/2)^1
  (u * exp (-s*u)) ds`, with `u = log M - h`; the integrand is exactly the Route-P cubic ray
  feature `primeGammaCauchyCubicRayFeature s u`.  Equivalently its scale integral is
  `exp (-u/2) - exp (-u)`.  This retains the required simple physical-endpoint zero, so it
  escapes the already ruled-out bulk-superposition class.
- Lean proof: `formal/GaloisForLFunctions/RHTower/SPEQuantileRieszEndpointRayLaplacePort.lean`
  direct-checked with `lake env lean`.  The exact `lake build` module target was terminated because
  Lake expanded it into an unrelated repository-wide rebuild, contrary to the no-full-build rule;
  no umbrella build was run.
- Route consequence: this is a transpose port—SP-E endpoint distance is Route-P ray coordinate
  while endpoint scale is Route-P rate.  It exposes a candidate P Gram pairing only after a
  Fubini/two-port construction.  It does not preserve Suzuki word history by itself, so scalar
  evaluation remains insufficient and the signed history lift remains the hard obligation.
- The actual P-G105F universal child/negative-pivot Julia--Krein block has the required target
  chronology before any cofinal limit: its literal child-row step followed by its literal
  negative-pivot-row step has child-coordinate amplitude `63/64`, while the reverse has amplitude
  `0`.  Here `63/64` is not fitted—it is exactly the forced fourth-depth Julia defect square.
  Normalizing the child readout by its forced inverse `64/63` gives the exact `1`/`0` shape of the
  physical Suzuki `2,3,7` history witness.
- Lean proof: `formal/GaloisForLFunctions/RHTower/RoutePJuliaKreinHistoryPort.lean`
  direct-checked with `lake env lean`; it supplies finite-word composition, calibrated ordered
  readout asymmetry, and noncommutation for the literal P block.  More strongly, after tensoring
  with any full finite P-G186 incidence matrix `H`, the ordered amplitudes from channel `0` are
  exactly `(63/64) * (H*H)_{ij}` and `0`.  Thus every prime/depth/ordinate incidence entry is
  retained through the port; it is not a scalar or diagonal reduction.  No `sorry`, `admit`,
  `axiom`, `opaque`, or `unsafe` declaration occurs in the new source.  As with the endpoint
  module, no `lake build` target is retained because that command expanded into an unrelated full
  rebuild.
- Route consequence: the source and target now have matching **canonical two-letter chronology
  ports**, not merely separate noncommutativity claims.  The remaining bridge is precise: construct
  a source-faithful map from pruned oriented Suzuki history into the P-G105F child/pivot action,
  retain the P-G186 prime/depth Gram factor, prove the Type-B insertion law, and carry that
  cofinally to a valid Xi-divisor/budget landing.  The finite port match does not by itself supply
  any one of those four obligations.
- The standard covariant commutant-lifting route is excluded for the eventual Xi landing.
  `RoutePPrimitiveBurnolApertureIntertwinerRigidity.lean` proves that no linear operator—bounded
  or not, local or not—can both commute with one strict positive P-G187 aperture shift and send a
  primitive P-G186 column to a strict-right Xi conormal.  More sharply, every proposed landing has
  an exact nonzero commutator equal to its primitive/Xi aperture-eigencharacter gap times that Xi
  column.  Thus the necessary source bridge must be a controlled **defect-intertwiner**, rather
  than an ordinary intertwiner; this is a route-wide restriction, not an implementation detail.
- The SP-E endpoint port is stronger than a Cauchy-kernel representation.  Its ray
  `u * exp (-s*u)` is, after complexification, exactly P-G197's common radial position-generator
  mode; this is the unbounded graph direction that creates P's cubic Xi conormal from the resolved
  Ward mode.  It also satisfies P-G187's literal weighted aperture-shift eigenlaw with eigenvalue
  `exp(-c*s)`.  Hence each SP-E endpoint ray enters P-G188's explicit boundary/tail defect
  colligation canonically.  `SPEQuantileRieszEndpointRayLaplacePort.lean` formalizes all three
  identities and direct-checks with `lake env lean`.
- Route consequence: a bounded or aperture-covariant bridge remains impossible, but the endpoint
  source supplies the correct **graph-mode eigenfamily** for a defect-colligation bridge.  The
  next hard theorem is not an abstract lift: construct the source-faithful second ray argument
  for the signed physical-wall/marked-boundary current while preserving the signed Suzuki/P-G105F
  history port.
- `RoutePPrimitiveBurnolMatrixCompleteColligation.lean` already proves P-G194: P-G188's three
  aperture channels preserve the full complex sesquilinear pairing, including every off-diagonal
  Gram entry.  The prior scalar-energy view was incomplete; a diagonal-energy identification
  cannot equal the signed linear SP-E wall readout by homogeneity, whereas a polarized two-port
  identity can carry it.
- `SPEQuantileRieszEndpointRayLaplacePort.lean` now specializes P-G194 directly to every pair of
  literal SP-E endpoint rays at positive exponential scales.  This is direct-checked by
  `lake env lean`; it preserves signed cross terms through transported, boundary, and tail
  channels without adding a scalar surrogate.
- A deep corpus search for a map simultaneously involving SP-E quantile/parabolic source,
  Cauchy-cubic ray/Laplace carrier, marked boundary, and source-faithfulness returned no such
  declaration.  Existing source theorems identify the marked boundary as the strict-cross
  current; existing P theorems provide its full pairing colligation.  Their missing connection is
  therefore a genuine two-port source construction, not a missing search hit.
- The parabolically weighted source has a sharper exact port than the unweighted profile:
  `exp (h/2) * P_M(h) = 2*M*sqrt(M) * integral_(s=1)^(3/2) u*exp(-s*u) ds`,
  `u = log M - h`.  Fubini gives every oriented height interval as the corresponding reversed
  endpoint interval two-port.  The positive portion is the literal P half-line indicator
  `(0,U]`; the complementary `h >= log M` summand is an explicit physical-wall remainder.
  No corpus theorem globally eliminates that remainder, so it remains a source obligation rather
  than an omitted term.
- P-G194 originally exposed continuity only because its proof derived cross-pairing
  measurability from it.  `RoutePPrimitiveBurnolMeasurablePairingColligation.lean` proves the
  exact measurable-L² version by deriving each weighted cross pairing on its restricted measure;
  it retains all three literal P channels and uses no approximation or density argument.
  `SPEQuantileRieszEndpointRayLaplacePort.lean` applies this theorem to the actual discontinuous
  positive interval indicator and a positive endpoint ray, yielding the full polarized aperture
  colligation for that source-faithful interval port.  Both modules direct-check with `lake env
  lean`; the required olean alone was generated with `lake env lean -o`, and no umbrella or full
  build was run.
- The physical-wall remainder itself is not outside the P interface.  Exact reflection gives
  `integral_(-L)^0 u*exp(-s*u) du = - integral_0^L u*exp(-(-s)*u) du`.  The reflected ray is
  compactly supported before entering P, hence measurable L² even though its negative scale would
  fail to be a global P eigenray.  The corpus now has its literal half-line pairing with the same
  endpoint indicator and its full three-channel P-G194 colligation.
- Consequently every SP-E interval crossing `log M` is exactly a signed two-port decomposition:
  a positive-scale P-G197 eigenray port of width `log M-a`, minus the reflected compact wall port
  of width `b-log M`.  Both widths and the orientation are proved nonnegative under the crossing
  hypotheses.  This removes the prior unrepresented-wall gap; it does **not** give a cancellation
  bound, since the reflected port has no global aperture eigenlaw.
- Lean proof: the extended `SPEQuantileRieszEndpointRayLaplacePort.lean` and
  `RoutePPrimitiveBurnolMeasurablePairingColligation.lean` direct-check with `lake env lean`.
  No full build was run.  The live hard core is now the source-faithful defect-intertwining lift of
  these two ports through oriented Suzuki/P-G105F history while retaining the P-G186 prime Gram
  factor and reaching a valid cofinal Xi/budget landing.
- The two physical-wall pieces do not merely have separate identities: at every positive source
  scale their difference is a **signed direct sum of two full P-G194 colligations**.  The first
  component is the global positive-scale eigenray/interval port; the second is the reflected
  compact wall-ray/interval port.  `crossingWallScaleSlice_eq_signedTwoPortSourcePairing` proves
  the literal endpoint integrals equal this signed P pairing, and
  `primeGammaCauchyCubicCrossingWall_signedTwoPort_aperture_colligation` proves its three-channel
  conservation.  Thus any future history lift must act on this signed two-port defect carrier;
  a one-channel covariant lift is structurally incapable of retaining the source.
- Narrow axiom audit of the four new core theorems reports only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`; no added mathematical axiom occurs.
- **Failed lift test — coherent Big-Witt graph.**  `DeningerBigWittFrobeniusCrossPairSingularOneLegGraphCompletion.lean` is not a P-history transport: every coherent complete right-leg fibre has exactly zero one-leg trace, and the only nonzero graph survivor is obtained by deleting a *selected* ordered edge before coherent summation.  The selected puncture has an exact four-prime readout and reconstructs the coherent fibre with its deleted edge, but carries no literal Suzuki valuation, signed-Eulerian word, or P-G186-incidence correspondence.  It cannot close the source-faithful lift obligation.
- **Failed lift test — word-curvature versus edge puncture.**  The P Cauchy-cubic certificate is an ordered descent-bottom four-label curvature, while Big-Witt puncturing is an unconstrained choice in the ordered-prime-edge index.  Deep corpus search and exhaustive source-name search found no theorem identifying these structures.  Installing such an identification by definition would discard the literal valuation source and violate the P/SP-E frontier; the next bridge must derive an edge-selection law from the source rather than choose one.
- **Failed cross-route test — E/P two-column margin.**  `RouteEPCubicHellingerPluckerLoadBridge.lean` gives an exact finite E/P projective identity, but `RouteEPCubicSourceNormalizationDebt.lean` proves its coefficient-faithful fourth-depth transport has ratio `737856/66015625`, below both the `13/98` Boolean ceiling and the `1/6` theta floor.  Restoring the apparent balanced margin forces amplitude `8` and exact trace debt `(63/64) w`.  Hence the finite E/P margin is not a producer for SP-E/P; source normalization is the same structural defect, not a removable scalar.
- **Route-U boundary audited.**  The corpus's degree-uniform parabolic floor and cofinal
  renormalized adaptive-source divergence do not close the route-U no-sparse-escape obstruction.
  `XiShiftedRouteUSparseParabolicCapitalEscape.lean` gives a closed cofinal model satisfying the
  local positive source-flow law, adjacent connector coercivity, strict all-degree reserve, and
  diverging renormalized pointwise action, while the selected entry fluxes are exactly
  `(1/2)^k` and summable.  Therefore any U closure must use an invariant tying **actual
  cross-degree selection** to source history; no scalar lower bound, terminal aggregate, or
  local flux corridor can supply it.
- **SP-E terminal gate.**  The actual terminal starts at quantile boundary `N`, whereas the
  threshold-centred time-head discrepancy reads through `N+1`.  Their exact difference is the
  literal atom `w_N`: the completed-codiagonal mass coordinate at `T=log N` is
  `2(1-exp(-log(N)/2)) - completedError(log N) - w_N`.  Thus the terminal begins before the
  physical wall iff `completedError(log N)+w_N` clears that threshold, and begins beyond it iff
  the reverse inequality holds.  This is a source identity, not an estimate.
- `SPEQuantileRieszTerminalErrorGate.lean` formalizes both gate iff laws and maps each branch of
  the **actual terminal readout** to its literal P port: the positive P-G197 eigenray before the
  wall, or the compact reflected P ray beyond it.  The branch lengths are returned as proved
  nonnegative quantities; equality belongs to both zero-width branches.  Hence the future
  Suzuki/P-G105F defect-intertwiner must carry a source-selected two-state terminal port, rather
  than an arbitrary crossing split.  Direct source check and its individual olean succeeded;
  narrow axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- **Boundary-excursion classification.**  In the literal strict-aperture Suzuki seam, let `P` be
  the coordinate projection and `U_δ,U_η` the commuting ambient valuation shifts.  The exact
  compressed chronology defect is
  `P U_δ P U_η P - P U_η P U_δ P = P U_δ (P-1) U_η P - P U_η (P-1) U_δ P`.
  Thus two oriented compressed shifts commute iff their two excluded-intermediate-vertex
  excursions agree.  The existing physical `2,3,7` certificate forces the skew excursion on the
  right to be nonzero.  `SuzukiPrunedBoundaryExcursionDefect.lean` closes these statements with
  no premises; direct source check, individual olean, and narrow axiom audit succeeded.
- **Whole-route consequence.**  Source chronology is now localized in a concrete nonzero
  aperture-boundary defect port, not merely in a pair of unequal word evaluations.  Any valid
  SP-E/P defect-intertwiner must transport this skew port while retaining the signed two-port
  terminal carrier.  The literal completed barycenter is separately an exact weighted signed
  Suzuki-curvature moment plus its archimedean renormalization
  (`CCMFUSuzukiSignedCurvatureUnitRieszBridge.lean`); current corpus audit finds no contraction
  from this boundary-excursion port to that signed curvature.  Constructing or disproving that
  contraction is the next hard source-side obligation; scalar/positive energy bounds cannot
  replace it.
- **No duplicate centered-transport theorem.**  `CCMActualHeadMatchedQuantilePolarParabolicSourceBoundary.lean`
  already gives the exact all-pair source invariant: for each pair of matched cells, the
  parabolic cross-kernel change is its oriented displacement difference times the literal moment
  determinant, minus one half its squared displacement difference times the two atom masses.
  `...VarianceBalance.lean` proves the same complete current is the matched-minus-quantile
  centroid-variance difference.  Hence a generic centered covariance/debt decomposition would
  add no knowledge.  The remaining possible refinement is source-forced control of the **adjacent
  displacement gaps**, whose telescoping generates every pairwise displacement; no such control
  is implied by centering or by the matched-current summability.
- **Unsigned chi-square closure is impossible.**  The source-faithful quantile displacement
  density does retain all displaced cells and overlap multiplicities, but
  `CCMActualHeadSignedCompletedErrorGammaProducer.lean` proves its reciprocal-higher-Binet
  chi-square diverges: each diagonal cell costs at least one eighth of the squared critical
  Mellin atom, prime atoms force those square partial sums to infinity, and nonnegative overlaps
  can only increase the full chi-square.  Thus no uniform positive/absolute Gamma absorption can
  control the completed SP-E current.  The exact survivor is the **signed** higher-Gamma plus
  completed-error autocorrelation producer; it converges on canonical Gamma--Slepian heads, but
  its scalar-shifted sign is exactly the RH-bearing restricted-Weil ground-energy condition.
  Any valid history/Route-P lift must therefore contract directly against this signed producer,
  never against an unsigned displacement envelope.
