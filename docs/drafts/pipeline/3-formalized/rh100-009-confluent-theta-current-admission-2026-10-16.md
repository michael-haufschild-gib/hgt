# Contribution 009 — Native confluent theta current admission

Status: formalized; contribution 009 completed, 9/100 audited.
All eight new leaves passed direct audits and are wired into RHTower. All 76
exported declarations have exactly `[propext, Classical.choice, Quot.sound]`
as axiom dependencies. Global lint failed only on six unrelated concurrent
umbrella omissions, listed below. No claim that repository-wide lint passed.

Structural outcome: every parameter jet of the literal compact theta cut
family is an actual BV mode with AC branches and its actual L1 derivative
current. At each full Xi multiplicity, every lower slot glues into an uncut
AC mode; the first terminal slot has an unavoidable nonzero finite-cut jump
carrying the original Meyer source. This removes differentiated-mode admission
from RN's frontier and supplies arbitrary-order confluent current tests.

Previous goal turn: verified progress, complete native Hasse Hilbert admission
and global zero-radical Paugam form, including RN current-factor totality.
Nine direct leaf audits and 26 standard-axiom audits passed; scratch cleaned.

Objective: a distinct structural advance combining frontier routes. Routine
corollaries, estimates, conditional receivers and RH equivalences do not count.
Use current Lean corpus and documented research search, with no web, external
novelty check, old reports, computations, subagents, or full/umbrella builds.
One foreground Lean process at a time; no proof holes, added axioms, or raised
heartbeats. Main constructions must have no unproved arithmetic premises.

Plan:
1. Inspect the current route map and search multiple independent source-native
   obstacles; test claims against the Lean corpus.
2. Iterate conjectures and record exact failures and positive survivors.
   Require a dependency-closed paper proof before new mathematical code.
3. Formalize one substantial construction, audit each leaf and its axioms,
   wire imports, run lint and clean owned scratch before counting.

Initial questions, not conclusions: can RN's admitted all-parameter cut family
support parameter derivatives in its original BV topology? Can the actual HF
generator, with all Jordan couplings, acquire a closed Hilbert realization and
an arithmetic compact-resolvent calculus rather than just diagonal proxies?
The latter must exceed routine consequences of contribution008. Other routes
remain candidates; no route selected from historical expectations.

Investigation checkpoint:
- Euler inversion: the split periodization quotient does not by itself put an
  Euler inverse in the literal Meyer quotient. Surjectivity of periodization on
  actual Poisson boundaries remains unpaid. Deferred, not a proved no-go.
- Closed generator: a diagonal closed realization already exists. The actual
  Hasse generator is diagonal plus a bounded truncated shift, but this alone is
  too close to contribution008 to count; a source-faithful full Jordan
  resolvent/determinant calculus would be needed. Deferred.
- RN: scalar cut-charge jets already have full multiplicity, but the corpus
  explicitly does not admit differentiated modes in native BV. This is the
  selected obstacle. Pointwise analyticity and separate pointwise BV do not
  establish that admission.

Paper construction under audit (no success claimed yet):
1. Prove entire parameter dependence of the literal source-ratio integral,
   using its existing all-real-tilt integrability and dominated differentiation.
2. For parameters on the unit circle about z, bound each spatial increment by
   the SAME decreasing positive budget B_z(a)-B_z(b). Cauchy's derivative
   formula then gives n! times that difference for the n-th parameter jet.
   Crucially the partition telescopes after differentiating, uniformly in its
   length. This pays every jet's native right-ray BV admission.
3. Reflect the left branch, glue at an arbitrary cut, and pull through the
   monotone singular quantile. These operations preserve finite variation.
   Finite endpoint values can be added without any assumed trace theorem.
4. Differentiate the actual connection formula. At Xi multiplicity m, all
   jets j<m match across every cut, yielding actual uncut native BV modes.
   The m-th jump is nonzero at every finite cut and is the previously proved
   actual theta/Meyer source moment. Thus the scalar multiplicity law becomes
   an admitted confluent family, rather than remaining a scalar receiver.
5. Do not assert BV-norm holomorphy, a spatial Jordan operator equation,
   positivity, or a proof of RH unless separately proved. Strengthen the
   construction if the finite-jet admission alone fails the significance bar.

Verified implementation checkpoint:
- `PaperThetaParameterAnalytic` direct leaf audit passed.
- `PaperThetaParameterVariation` direct leaf audit passed: every parameter
  derivative has actual right-ray bounded variation. No numerical evidence,
  source premise, or heartbeat increase.
- `PaperThetaParameterTraces` being audited; common budget is exactly a fixed
  positive multiple of the modulus of a native imaginary-parameter mode.
- `PaperThetaConfluentCut` written, not yet audited.

Stronger survivor now exposed by the proof: the increment domination also
transfers absolute continuity from that imaginary-parameter branch to every
jet after compactification. If completed, this pays actual L1 derivative
currents of the full confluent family, with the exact multiplicity-order
Meyer charge; not merely scalar jet matching or BV bounds. This is the next
paper/formal audit target. BV-norm holomorphy and spatial pencil/Jordan
equations still remain unclaimed.

Paper proof of the strengthened survivor:
- Let q_z be the literal right source quotient. Its source-ratio integral is
  entire in z, paid by the existing all-real-tilt theta moments.
- On the parameter circle |w-z|=1, integrate the nonnegative ratio difference
  K(h,a)-K(h,b) before taking norms. This bounds the whole analytic increment
  q_w(b)-q_w(a) by one decreasing B_z(a)-B_z(b). Cauchy gives the same increment
  domination for the n-th derivative with factor n!. Arbitrary partitions then
  telescope, paying every native right-ray BV jet.
- Exactly B_z(x)=(|z|+1)/(|Im z|+1) times
  |q_{-i(|Im z|+1)}(x)+1|. Its known continuity and right trace therefore pay
  continuity and endpoint traces of every jet. The reverse triangle inequality
  strengthens the increment domination to comparison with that actual
  imaginary-parameter mode itself, including the compact endpoint.
- The original compact branches are AC: their continuous representatives,
  everywhere interior derivatives and already-integrable derivative densities
  satisfy FTC. Comparison of every finite disjoint family of interval increments
  transfers AC to every parameter jet. Reflection pays the other branch.
- Complex AC integration by parts is justified by the vector FTC and a.e.
  product differentiation. Gluing the two branches leaves only the interior
  jump, exactly the parameter derivative of the original cut charge. Endpoint
  trace is -1 at order zero and 0 at every positive order.
- At multiplicity m, existing HF/RN charge-order and actual Meyer factorization
  identify the jump: all j<m vanish, hence give uncut AC modes; the m-th jump
  is nonzero at every cut and equals the original factorial-weighted Meyer
  Mellin value with the signed native cut gauge. This admits the full confluent
  current family; it does not infer a sign or constrain zero locations.

Final direct leaf audits all passed:
ParameterAnalytic, ParameterVariation, ParameterTraces, BranchAbsoluteContinuity,
ConfluentCut, ConfluentQuantile, ConfluentAdmission, ConfluentCurrent
(all prefixed PaperTheta). Each was checked in the foreground using
`lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<Module>.olean GaloisForLFunctions/RHTower/<Module>.lean`.
One owned Lean process at a time; no full or umbrella build. All eight have
exactly one umbrella import and no forbidden proof tokens. Final API checks
and the separate `/tmp` axiom audit passed. No heartbeat increases or
numerical experiments occurred.
Final cleanup removed all 13 owned `/tmp/hgt_rh009*` files. No owned leaf
artifact is older than its source; no owned search, Lean or lint process remains.

Main audited declarations, all in `RHTower.PaperThetaEndpoint`:
- `boundedVariationOn_cutQuantileParameterJet` admits all orders/parameters.
- `absolutelyContinuousOnInterval_closedParameterJet_right` and
  `absolutelyContinuousOnInterval_leftClosedParameterJet` pay actual AC branches.
- `intervalIntegrable_deriv_cutQuantileParameterJet` pays the actual derivative.
- `cutQuantileParameterJet_weak_current` retains the complete differentiated
  charge and both endpoint traces.
- `absolutelyContinuousOnInterval_divisor_closedParameterJet` admits every
  actual slot below the full Xi multiplicity as an uncut compact AC mode.
- `not_continuousAt_terminal_cutQuantileParameterJet` proves the first terminal
  jump is an actual discontinuity at every finite cut.
- `terminal_cutQuantileParameterJet_meyer_current` identifies that admitted
  current with the original factorial-weighted Meyer Mellin source.

`scripts/formal_tools.py lint` exited 1 solely for these unrelated modules
unreachable from their theorem-area umbrellas:
- RHTower.CHMDArchimedeanLevyTranslateForm
- RHTower.CHMDDAlembertSechKernel
- RHTower.CHMDLightConePrimeKernelDecomposition
- RHTower.CHMDMasslessContinuationPieces
- RHTower.CHMDMasslessZeroWaveExplicitFormula
- HTGeometry.KleinGordonLightConeBesselKernel
It also emitted existing large-file warnings. Unrelated work was preserved.

The construction combines RN source-ratio monotonicity, all-parameter native
cut admission and singular quantile transport with HF's full Xi multiplicity
and literal Meyer/Hedenmalm source realization. Its main statements have no
unproved arithmetic premises. It is neither an RH equivalence nor a conditional
receiver. The comparison estimates are internal admission proofs, not the
contribution being counted.

Limits: no BV-norm holomorphy, strong spatial Jordan/pencil identity, all-order
classification of uncut jets above the terminal order, boundary-work positivity,
or RH conclusion is asserted. Signed nonlinear and prime–Gamma orientation
remains open. Routine finite combinations or repackagings of these admitted
currents belong to 009 and must not be counted again.
