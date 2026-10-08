# WP03 evidence

## Corpus audit

- `research 'bounded zetaQuotient' --module Weil --budget-seconds 60`: complete;
  found the exact receiver and prime-coefficient consequence. Coverage compiler data
  are mostly source-only/pending/stale, so search hits are not compilation evidence.
- Deep search `actual reciprocal zeta quotient uniform growth logarithm Herglotz`:
  partial at 90 seconds; found reciprocal strip bounds and radial atom order.
  No useful new proof ideas or ingredient sets. Broadened with focused lexical searches.
- `research 'producerMobius partial sums' --module Weil --budget-seconds 40`:
  complete; located smoothed cancellation, not an unconditional sharp-cutoff theorem.
- Exhaustive `rg 'producerMobius'` across existing `Weil*.lean` confirmed the
  located uses. General `SmoothPerronLittlewood.partialSumSeq_subpower_of_smoothPerron`
  has an individual coefficient bound, which is not an available premise here.
- Deep Pick/reciprocal search: partial; no new mechanism beyond the existing
  Herglotz potential and radial atom-order interfaces.
- Serena symbol lookup reports Lean paths ignored. Read exact Lean source using
  filesystem tools after that failure; no source symbol was silently assumed.

## Reused exact interfaces

- `WeilSpectral.herglotzWeilPositive_of_weilPositiveFull`
- `exists_reciprocalZeta_continuation`
- `exists_reciprocalZeta_strip_bound`
- `producerMobius_zero`, `summable_norm_producerMobius_mul_rpow`
- `tsum_producerMobius_mul_cpow_eq`
- `Sieve.tsum_mul_smoothWeight_eq_integral_summable`
- `integral_mul_mellin_smoothWeight_shift`
- `integrable_mul_mellin_smoothWeight_line`
- `exists_integral_norm_mul_mellin_smoothWeight_fractional_bound`

## External parent-theory audit

- Schoolmann, *On Bohr's theorem for general Dirichlet series*, Math. Nachr. 293
  (2020), https://onlinelibrary.wiley.com/doi/full/10.1002/mana.201800542:
  bounded extension implies uniform convergence in smaller half-planes. Boundedness
  remains a hypothesis; this cannot produce WP03's missing bound.
- Andersson, *Mittag-Leffler type theorems for Helson zeta-functions* (2024),
  https://arxiv.org/abs/2408.15713: prescribed divisors are possible for Helson zeta
  functions. This supplies no counterexample with full Weil positivity and ζ's datum.
- Tao, *254A Notes 1: Elementary multiplicative number theory* (2014),
  https://terrytao.wordpress.com/2014/11/23/254a-notes-1-elementary-multiplicative-number-theory/:
  classical Dirichlet hyperbola parent for the prospective quotient-coefficient step.
- The short-smoothing/Perron mechanism is classified BRIDGE. Literature novelty
  is not claimed. Searches were performed on 2026-10-07; search absence is not a
  proof of absence from the literature or corpus.
- Updated parent-theory check: Lee–Leong, arXiv:2208.06141v5 (9 September 2026),
  https://arxiv.org/abs/2208.06141, relates reciprocal bounds in prescribed
  zero-free regions to Mertens estimates. It does not prove WP03's detector.
  The Cambridge 2014 Part III zeta paper, question 5,
  https://www.maths.cam.ac.uk/postgrad/part-iii/files/pastpapers/2014/paper_25.pdf,
  also documents Perron and Möbius-polynomial product analysis as classical
  parent machinery. Neither source is used as an extra Lean premise.

## Verification

- `lake env lean /tmp/wp03_api.lean`: exit 0. Checked mathlib names and exact
  local smoothing/contour-shift interfaces against the installed toolchain.
- `lake env lean GaloisForLFunctions/RHTower/WeilWorkSingularArithmeticSharpReciprocal.lean`:
  exit 0 after correcting a positivity tactic and a real-to-complex numeral cast.
  No mathematical change to the paper proof; no heartbeat override.
- `lake build --old +GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSharpReciprocal`:
  exit 0 for the strengthened all-height bound plus ordinary-series capstone.
  Only the targeted dependency closure was requested; no umbrella build.
- Intermediate axiom audit of sharp reciprocal cancellation and ordinary
  identification: only `propext`, `Classical.choice`, `Quot.sound`.
  Updated all-five-theorem audit `/tmp/wp03_axioms.lean`: exit 0, with the same
  three standard axioms for every declaration, including the all-height bound.
- Final `lake env lean GaloisForLFunctions/RHTower/WeilWorkSingularArithmeticSharpReciprocal.lean`:
  exit 0, no diagnostics. The source exactly matches the successful targeted
  build and axiom audit. No heartbeat options or new axioms were introduced.
- New leaf wired into RHTower; generated indexes refreshed with
  `scripts/formal_tools.py index` (exit 0).
- Latest `scripts/formal_tools.py lint`: exit 1; no failure names this leaf.
  Seven failures are unrelated unwired modules: `WeilWorkDeficitSharedMass`,
  `WeilWorkExposingRayPacketCoercivity`, `ApertureConeCalculus`,
  `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`,
  `BoundaryCoronaCStarAlgebra`. Other work's changing module set was preserved.
- No numerical computation, full build, commit, or push performed.

## Cycle 3 quotient verification

- `WeilWorkSingularArithmeticWeightedZeta`: targeted `--old` build exit0;
  final direct `lake env lean` audit exit0, no diagnostics.
- `WeilWorkSingularArithmeticMellinMass`: targeted `--old` build exit0;
  final direct `lake env lean` audit exit0, no diagnostics. Removed one tactic
  sequencing linter warning before the final build and direct audit.
- `WeilWorkSingularArithmeticQuotient`: targeted `--old` build exit0;
  final direct `lake env lean` audit exit0, no diagnostics. Its first build
  accepted the entire quotient assembly and ordinary-convergence consequence.
- Builds were foreground, sequential within this agent, and restricted to the
  requested leaves and dependency closure. No umbrella/full build requested.
- The quotient umbrella import reaches all three new modules. Latest formal lint
  exit1 reports nine unrelated unreachable modules: `WeilWorkDeficitLeakageIntegral`,
  `WeilWorkDeficitMassBounds`, `WeilWorkDeficitPoissonLeakage`,
  `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`,
  `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`, `CrouzeixObservationEnergy`.
  None of this work's leaves is reported. Other agents' files were preserved.
- Index refresh exit0; generated API/gaps/overview files have no Git diff.
  Scoped whitespace check exit0. Global whitespace check reports only unrelated
  trailing spaces in `docs/prompts.md`.
- Nine-public-declaration axiom audit exit0. Every declaration uses exactly
  `propext`, `Classical.choice`, `Quot.sound`; no additional axiom, admitted
  declaration, or heartbeat override. The final audit source was a /tmp import
  file, never an edited theorem-tree file.

## Further source audit and next-cycle handoff

- Main goal remains active; detector unproved. Main card remains in progress.
  Ordinary quotient cancellation and convergence are now formalized.
- Deep translated-quotient search was partial and returned mostly irrelevant
  categorical quotient hits; focused Weil searches were used afterward.
  The horizontal-potential/quotient and full-positive-rigidity searches completed
  and recovered the existing receiver, proper-subclass rigidity, and rational
  spectral-mass interfaces. They supplied no proof of the missing source bound.
- Brevig–Kouroupis–Perfekt, *Almost periodicity and boundary values of Dirichlet
  series*, https://arxiv.org/html/2405.03522v2, Theorems1.3 and1.6–1.7:
  boundary and vertical-mean limits cannot in general be interchanged. These
  counterexamples do not carry the present full Weil-positive datum.
- Booker, *L-functions as distributions*, https://arxiv.org/pdf/1308.3067,
  Definition1.3 and Theorem1.7 assume coefficient conditions and a discrete spectrum
  with only finitely many noninteger masses. Corpus refinement: the dyadic theorem
  `WeilMeanSquare.exists_sum_sq_Ioc_le_of_weilPositiveFull` already implies
  subpolynomial square prefixes for f(n)=lam(n)/sqrt(n), by dyadic summation.
  This is NOT the new square-law conjecture for qλ. Discreteness, eventual integer
  masses, and the other coefficient conditions must still be checked; the
  low-degree converse theorem is not a proof for arbitrary boundary measures.
- New exact conjecture: subpolynomial square mass of qλ. Dyadic Cauchy–Schwarz
  would supply absolute quotient convergence on Re s>1/2 and the desired uniform
  bound. The source estimate is OPEN. Do not formalize it with a supplied square
  bound or replace it by another conditional receiver.
- Alternating eta coefficients refute inference of that square law from signed
  cancellation alone. The corresponding reciprocal has extra strict-right zeros,
  so it is not a counterexample to full positivity. Full details and a proposed
  divisor-energy mechanism are recorded in PROOF.md.
- Letting ε→0 in the reciprocal estimate remains invalid because Cε depends on ε.
  Translating the quotient's weighted ζ integral changes its constant. The next
  cycle must attack actual arithmetic square mass or exceptional-height control,
  rather than accumulate further ordinary-cancellation corollaries.

## Cycles 4–5 audit

- Cycle4's subcritical absolute quotient regularity reduces on paper to the
  known summable-deviation class via the ordinary Dirichlet Wiener inverse
  theorem. Source: Deutsch1974, AIF24(3), pp165–169,
  https://aif.centre-mersenne.org/item/10.5802/aif.524.pdf. A current weighted
  extension is Dabhi2026, https://articles.math.cas.cz/10.21136/MB.2026.0072-25.
  The classical inverse theorem has not been located in the corpus. This result
  remains paper-level; no inverse axiom or conditional substitute was added.
- The initial Carlson/Fourier search completed with source-only candidate
  metadata, but the subpower-coefficient follow-up was partial and mostly
  irrelevant. Direct source search recovered the exact finite sharp mean-value
  theorem and divisor bound used in the new paper proof. No search absence
  is treated as a mathematical nonexistence claim.
- Montgomery–Vaughan1974, *Hilbert's Inequality*, Corollaries2–3,
  https://personal.science.psu.edu/rcv4/personal/Publications/s2-8-1-73.pdf,
  is the classical parent for finite polynomial energy extraction. Read the
  primary paper; the proof uses the existing corpus constant104.
- Current descendant checked: Rodgers, arXiv:2608.12315 (12Aug2026),
  https://arxiv.org/abs/2608.12315. Its result that the optimal weighted-Hilbert
  constant exceeds π has no effect on using the proved nonsharp constant104.
- Cycle5's Oε(N^(1+ε)) square-mass proof now uses the existing all-twist
  reciprocal estimate directly. No infinite-series mean limit, distribution
  identification, or generalized Carlson theorem is needed. Classification:
  BRIDGE. Lean verification is underway, not yet asserted here.

## Cycle 5 final verification

- `lake build --old +GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSquareMass`
  exit0; new leaf built without diagnostics. Other dependencies were replayed.
- Final `lake env lean GaloisForLFunctions/RHTower/WeilWorkSingularArithmeticSquareMass.lean`
  exit0, no diagnostics. Two unused-variable/tactic warnings were removed before
  the final build and direct audit; no heartbeat option was raised.
- `/tmp` import-only axiom audit exit0. Both public theorems use exactly
  `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella wired; no umbrella/full build. Index refresh exit0 (one changed
  indexed document). Owned source/docs whitespace check clean.
- Formal lint exit1 only on ten unrelated unreachable modules:
  WeilWorkDeficitArithmeticMean, WeilWorkDeficitFourierTransport,
  WeilWorkHigherDenominatorFiniteBoundary, WeilWorkHigherDenominatorPeriodDefect,
  WeilWorkHigherDenominatorPoleModes, ApertureConeCalculus, ApertureConeWinding,
  ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra.
  No failure names a WP03 leaf. Other work was preserved.
- Cycle6 source obstruction is in a separate new leaf under verification;
  do not confuse its paper proof or unverified source with these completed checks.

## Cycle 6 final verification

- Narrow targeted `lake build --old +GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticReciprocalObstruction`
  exit0. The earlier broad-import build was canceled and exited143 before the
  narrower replacement; it is not counted as a successful audit.
- Final direct `lake env lean GaloisForLFunctions/RHTower/WeilWorkSingularArithmeticReciprocalObstruction.lean`
  exit0, no diagnostics. Import-only public capstone axiom audit exit0:
  propext, Classical.choice, Quot.sound. No added axiom or heartbeat override.
- Umbrella wired. Latest formal lint exit1 only on eight unrelated unreachable
  modules: WeilWorkQuantizationRadialContour, WeilWorkQuantizationRadialGrowth,
  WeilWorkSettledPhaseMellinTrace, ApertureConeCalculus, ApertureConeWinding,
  ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra.
- Primary parent: Brevig–Kouroupis–Perfekt, Section3,
  https://arxiv.org/html/2405.03522v2. Read the exact recurrence argument;
  the parent is REDISCOVERED and this source application is a BRIDGE.
- Cycle8's prime-power detection proposal repeats Bohr-route row80. Its failed
  Euler-product payoff is not a refutation of the exact support conjecture.

## Cycle 7 final verification and current mean-value audit

- `lake build --old +GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticGrowthComparison`
  exit0. Final direct `lake env lean` leaf audit exit0, no diagnostics.
  Import-only axiom audit exit0: propext, Classical.choice, Quot.sound.
- Initial direct check caught a beta-reduction rewrite and an under-specified
  real-power simplification. Both were corrected before the successful build
  and final audit; the mathematical statement and paper proof were unchanged.
- Import wired; index refresh exit0. Latest lint exit1 names seven unrelated
  unreachable leaves: WeilWorkDeficitSquareMoment, WeilWorkHigherDenominatorPoissonMode,
  ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation,
  ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No WP03 failure.
- Operator audit: Bommier-Hato2020, Theorem1 and the introduction,
  https://link.springer.com/article/10.1007/s00605-020-01396-6,
  distinguishes bounded Volterra operators from coefficient-space membership;
  neither is automatically an H-infinity multiplier bound. Primary full text read.
  Two other primary operator PDFs were access-denied; no result relies on them.
- Current primary audit: Brevig–Kouroupis, 28Sep2026,
  https://arxiv.org/html/2609.35496v1, Theorems1,6 and Corollary2. Order-zero
  continuation plus H² coefficients gives the mean formula. Ordinary convergence
  plus H² alone does not: their theta=0 example has mean abscissa1/4.
  This is a generic counterexample, not a full-positive-system counterexample.
- A search page initially associated that title with arXiv2608.04853; opening
  the primary record showed it was unrelated. Correct record2609.35496 was
  found by title and verified before use. No claim relies on the wrong identifier.
- Broucke–Hilberdink's general mean-value theorem, primary PDF at
  https://backoffice.biblio.ugent.be/download/01JGXHDE2Q0S9WCC8RJZX6D8EN/01JPMEVX4Z2D3XK0D1C162RFKW,
  assumes positive coefficients and a specified counting-function remainder.
  Those premises do not hold automatically for the signed quotient coefficients.

## Cycle 11 external premise audit

- Pintz–Révész, *Zero-density estimates for Beurling zeta functions*, Section4
  Lemma1, https://www.impan.pl/shop/publication/transaction/download/product/116232:
  Ramanujan bounds for both reciprocal coefficient sequences are assumptions;
  the integral Beurling system and AxiomA are also additional structure.
  This does not derive the source coefficient concentration conjecture.
- Klurman et al., *Zeros of L-functions and large partial sums of Dirichlet
  coefficients*, https://link.springer.com/article/10.1007/s00208-026-03542-1:
  the weak generalized Ramanujan condition and automorphic setup are premises.
  Primary text checked; neither may be imported into the arbitrary source.

## Cycle 13 converse-theorem premise audit

- Ki–Lee2011, *On the zeros of degree one L-functions from the extended
  Selberg class*, primary https://www.impan.pl/shop/publication/transaction/download/product/82665.
  The introduction and TheoremB assume global continuation of finite order
  and a functional equation. The degree-one classification is not a theorem
  about half-plane continuation plus reciprocal coefficient growth alone.
- Kaczorowski–Perelli2015, *Twists, Euler products and a converse theorem for
  L-functions of degree2*, primary
  https://journals.sns.it/index.php/annaliscienze/article/download/382/372/601,
  Section3 definitions and Theorem1.1. Functional equation, global continuation,
  and the Selberg-class Euler structure are genuine premises. Search indexing
  showed recent crawl dates; the primary publication is2015, not2026.
- Internal finite-type source checked: `WeilFiniteTypeUniqueness` assumes a
  finite arithmetic decomposition plus a remainder holomorphic across the
  critical line with polynomial strip growth. No such continuation follows
  merely from the new square-summability or mean-square theorems.

## Cycle 10 final verification

- Targeted `lake build --old +GaloisForLFunctions.RHTower.<leaf>` succeeded
  for ReciprocalTail, SquareSummability, MeanComparison, ReciprocalMeanSquare
  (all names have the prefix `WeilWorkSingularArithmetic`). Final leaf builds
  had no diagnostics from these leaves. No full or umbrella build was run.
- Each of the four final `lake env lean GaloisForLFunctions/RHTower/<leaf>.lean`
  commands exited0, without diagnostics. Their sequential audit reached the
  separate scratch axiom command only after all four succeeded.
- All six new public declarations report only propext, Classical.choice,
  Quot.sound. The first scratch run additionally failed on unconstrained
  universe levels in generic API-name probes; specializing those universes
  fixed the probes. The final complete scratch command exited0. No source
  premise, axiom, heartbeat override, or numerical experiment was added.
- Imports are wired into RHTower. Scoped whitespace check passed. Latest
  formal lint exited1 on seven unrelated unreachable modules only:
  WeilWorkDeficitZeroTransport, WeilWorkSettledPhaseAbelRigidity,
  ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation,
  ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No WP03 failure or
  forbidden-declaration failure was reported; unrelated work was preserved.
- The paper proof distinguishes the false generic convergence-plus-H2
  implication from the source-specific all-height tail bound. Its positive
  survivor is now formally complete; the bounded-quotient detector is not.
- Post-audit `scripts/formal_tools.py index` exited0; generated LEAN_API,
  LEAN_GAPS, LEAN_OVERVIEW show no Git diff. No umbrella build was used.

## Post-mean arithmetic audit

- Brevig–Perfekt–Seip, *Volterra operators on Hardy spaces of Dirichlet series*,
  https://arxiv.org/pdf/1602.04729, Theorem5.1: boundedness requires a Carleson
  inequality tested against all Hardy-space inputs. A one-sided finite
  Toeplitz ceiling has not been shown to imply that inequality. Section5.2
  does not replace the missing source estimate by coefficient membership.
- Rechecked Booker Definition1.3 in https://arxiv.org/pdf/1308.3067: discrete
  spectral support and almost-everywhere integral multiplicities are required;
  they have not been derived for the source measure. This repeats the earlier
  premise audit and is not a new obstruction.
- Deep full-form correlation query completed partial=false, with complete
  inventory but an older-generation coverage snapshot, unavailable semantic
  coverage, and mostly source-only compiler metadata. Its proposed RH transfer
  omitted actual nonnegativity/order assumptions; it was rejected after
  inspecting the exact theorem statement. No new Lean proof uses that proposal.

## Cycles 15--20 research audit (no new Lean result claimed)

- Venturini, *Non vanishing of Dirichlet series of completely multiplicative
  functions* (2020), publisher/repository abstract:
  https://cris.unibo.it/handle/11585/729849. The abstract requires bounded
  completely multiplicative coefficients. The journal PDF returned401;
  its proof was not read. The elementary proper-subclass calculation is our
  premise audit, not a claim about an unread proof.
- Burnol, *Deux extensions de Theoremes de Hamburger*,
  https://arxiv.org/abs/1106.4749, verified abstract: functional equation and
  moderate meromorphic continuation remain part of the framework. No
  positivity-to-functional-equation transfer was supplied by that source.
- Broad external queries for the exact forward-energy mechanism returned
  no verified exact analogue. This is not evidence of novelty; the proof's
  parents are classical and its current classification is BRIDGE.
- Source checks: WeilFullConeRiemannKernelRigidity:256--267 fixes full-form
  normalization; WeilPositivitySummablePerturbationRigidity:60 supplies the
  regular symbol bound; WeilProducerZetaQuotientBohrRecurrence:574 supplies
  the prime exponential coefficient; WeilPositivityMultiplicativeToeplitzBound:
  775 and970 supplies the finite arithmetic ceiling; DirichletConvolution-
  Exponential:204 supplies the literal forward series; WeilPositiveProducer-
  Lindelof:89 supplies logarithmic differentiation. Names must still be
  checked against the active Lean toolchain before the new formal proof.
- Deep queries covered prime-square cancellation, bounded deviations,
  multiplicative detection, squarefree support, margin/spikes, spectral
  deficits, Toeplitz determinants, forward energy and log convolution.
  Candidate and source-argument signatures were inspected. Multiplicative
  detection was partial: text/source stages interrupted, semantic deadline.
  Forward energy was partial: two refinement queries and reranking unfinished
  after a local runtime deadline. Other queries completed partial=false.
  Inventory was complete, semantic coverage unavailable, most compiler
  metadata source-only; some early snapshots were one generation old.
  Searches do not establish exhaustive absence or theorem applicability.
- No new Lean code was changed in these cycles yet. Previous successful
  leaf audits remain the latest formal evidence; no redundant build or lint
  was run for prose-only research. Cycle20's new bound is PAPER, not LEAN.

- Cycle20 formalization subsequently started in the owned
  WeilWorkSingularArithmeticForwardCoefficients leaf. API scratch probes
  passed after fixing unconstrained universe levels. First source checks
  exposed elaboration errors (Summable versus LSeriesSummable, an implicit
  evaluation point, EReal coercions, and a reserved lambda token); these are
  being repaired. No successful final leaf audit is yet claimed.
  One accidental overlapping launch was terminated by its exact owned PIDs
  and confirmed exit143 before continuing. Subsequent checks are sequential.
- Cycle21 source comparison: Hough, equation36 of Lemma6,
  https://www.math.stonybrook.edu/~rdhough/angle_results.pdf, gives the
  classical half-divisor logarithmic1/4 energy using multiplicativity.
  Mastrostefano, Definition1.2,
  https://link.springer.com/article/10.1007/s11139-020-00374-8,
  requires multiplicativity, prime statistics and a divisor majorant. No
  transfer from full positivity alone has been verified. The focused corpus
  query was partial after a Qdrant semantic-retrieval deadline; inventory was
  complete, coverage snapshot one generation old, semantic coverage absent.

## Cycles 22--23 audit continuation

- Fractional-energy deep search completed partial=false, errors empty;
  inventory complete, coverage snapshot11 generations old, semantic coverage
  not measured. All candidate and source-argument signatures were inspected.
  Its unrelated square-root ingredient set was rejected. Broader Weil query
  was partial=true with interrupted text/source retrieval, complete inventory,
  one-generation-old snapshot and semantic coverage not measured.
- The broader query's applicable comparison was
  WeilConeSoundararajanMoments:896. Source checked: both rest-weight
  summability and |lambda(n)|<=kappa*log n are extra premises. Its conclusion
  is a height moment near the critical line, not our coefficient energy.
- Ponnusamy--Sugawa2019, Theorem1.1 and introductory class definition,
  https://arxiv.org/pdf/1903.09974, require normalized univalence.
  Chang--Gui2021, Section2 equation(2.1),
  https://arxiv.org/pdf/2109.13385, recalls a circle exponentiation inequality
  with a weighted logarithmic-coefficient square norm. No transfer to the
  arbitrary Weil source or prime polydisc has been justified.
- The star-resonator candidate is already exactly formalized in
  WeilPrimitiveSetMeanSquare:284; its statement and parent mechanism were
  read. It is REDISCOVERED, not a new no-go or a new theorem.
- ForwardCoefficients first complete direct check exited0 without diagnostics.
  Its logarithmic moment inequality is now public; import wired. Targeted
  --old build and final direct/axiom audits remain in progress at this entry.

- Subsequent forward leaf targeted --old build passed (only target rebuilt;
  dependencies replayed). Final direct leaf audit exited0 without diagnostics.
  Axiom audit is running. Latest lint exited1 solely on16 unrelated
  unreachable leaves: WeilWorkDeficitRadicalTranslateObstruction,
  WeilWorkHigherDenominatorFinitePoleMellin,
  WeilWorkHigherDenominatorQuotientMellin, WeilWorkHigherDenominatorThetaDefect,
  WeilWorkPBAPCriticalCoefficients, WeilWorkPBAPCriticalDatum,
  WeilWorkPBAPCriticalKernel, WeilWorkPBAPCriticalLaplace,
  WeilWorkPBAPCriticalResonator, WeilWorkPBAPCriticalWindow,
  WeilWorkQuantizationPowerRigidity, ApertureConeCalculus, ApertureConeWinding,
  ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra.
  No owned WP03 or forbidden-declaration failure was reported.
- Cycle23 deep search was partial after source retrieval was interrupted;
  inventory complete, snapshot9 generations old, semantic coverage not
  measured. All candidate/source-argument statements were inspected. A broad
  lexical query returned no applicable variance theorem and supplied no
  coverage metadata. Exhaustive exact-form text searches found only the
  existing primitive-set prime bound. No absence/novelty conclusion follows.
- Cycle24 primary calibration: Jean Gallier, *The Schur Complement and
  Symmetric Positive Semidefinite (and Definite) Matrices*, Proposition2.1,
  https://www.cis.upenn.edu/~jean/schur-comp.pdf. The positive-semidefinite
  block criterion directly explains the finite completion; it is classical,
  not new scientific knowledge. Exact source-specific algebra is in PROOF.md.
- Cycle24 corpus search was partial after malformed local-model JSON during
  filter/judge; inventory complete, snapshot21 generations old, semantic
  coverage not measured. All returned candidate/source-argument signatures
  were inspected. No applicable exact completion appeared. The finite
  calibration will be formalized as a classical positive survivor, not as
  a full-source counterexample or a novelty claim.
- Forward leaf axiom audit subsequently exited0: all seven public
  declarations use only propext, Classical.choice, Quot.sound. Formal
  checkpoint is complete. No umbrella build or heartbeat override was used.
- Cycle25 deep search completed partial=false, errors empty; inventory
  complete, snapshot5 generations old, semantic coverage not measured. All
  candidate and source-argument signatures were read. Mathlib's Hermitian
  Schur identities were relevant generic parents; the generated ingredient
  set did not supply the actual product-cutoff prime-layer estimate.

## Completed cycles20/24 formal checkpoint

- ForwardCoefficients: targeted --old build, final direct lake env lean,
  seven public axiom checks all passed. DivisorCompletion: targeted --old
  build, final direct lake env lean, three public axiom checks all passed.
  Every declaration uses only propext, Classical.choice and Quot.sound.
  Both imports are wired. No umbrella/full build or raised heartbeat.
- Final lint still exits1 solely for16 unrelated unreachable modules:
  WeilWorkHigherDenominatorFinitePoleMellin,
  WeilWorkHigherDenominatorQuotientMellin, WeilWorkHigherDenominatorThetaDefect,
  WeilWorkPBAPCriticalAbel, WeilWorkPBAPCriticalCoefficients,
  WeilWorkPBAPCriticalDatum, WeilWorkPBAPCriticalKernel,
  WeilWorkPBAPCriticalLaplace, WeilWorkPBAPCriticalResidue,
  WeilWorkPBAPCriticalResonator, WeilWorkPBAPCriticalWindow,
  ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation,
  ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No owned WP03 failure.
- Anti-theatre/laziness audit: forward energy is a completed source consequence;
  finite completion is a classical obstruction with an exact positive
  survivor. Neither is scientific closure of WP03. No hard step was dropped
  for effort. Next exact work is the coupled prime-layer source inequality,
  with composite disappearance proved by support and the product cutoff kept.
- Post-audit index refresh exited0; generated API/gaps/overview files have
  no Git diff. Owned whitespace check passed. All owned scratch API/axiom
  files, search JSON and final lint log were removed after recording evidence;
  no owned build/search process remains active. Cross-session memory saved.

## Cycle27 sharp Toeplitz relaxation, 2026-10-07

- Corpus search `Weil positivity prime layer semiprime product cutoff
  incidence norm sharp variance`: partial=false, no errors; complete file
  inventory, coverage snapshot one generation old, semantic coverage not
  measured. Candidate and source-argument signatures inspected; no exact
  applicable coupled estimate supplied.
- Broader Toeplitz source search was partial (text/source retrieval
  interrupted), complete inventory, snapshot one generation old. Verified
  actual source at WeilPositivityMultiplicativeToeplitzBound:970 and the
  primitive mean-square proof, rather than source-only scratch duplicates.
- Zero-free/Gaussian query was partial (source retrieval interrupted),
  snapshot three generations old; returned hypotheses did not supply an
  all-source sharp exponential-energy bound. No Gaussian claim adopted.
- Lacunary Toeplitz query was partial (local runtime deadline during
  semantic retrieval), complete inventory, snapshot one generation old.
  Read all returned candidate/source signatures. Relevant parents include
  WeilFullConeLacunaryRigidity:778 and
  WeilPositivitySparseWeightsObstruction:484. Neither is a logarithmic
  Toeplitz sharpness construction. Sparse-source exclusion is consistent
  with, and distinct from, the constructed relaxation witness.
- Primary operator calibration: Haykel Gaaya, *A sharpened Schwarz-Pick
  operatorial inequality for nilpotent operators*, Theorem1.6,
  https://arxiv.org/pdf/1202.3962. Its nilpotent numerical-radius bound
  confirms the classical parent mechanism. The present proof needs only
  the elementary matching bound1 and arbitrary-shift bound2. No external
  theorem is imported as an unproved premise or scientific novelty claim.
- Other primary papers inspected: https://arxiv.org/abs/2110.14323 and
  https://arxiv.org/abs/1411.7294. Their specific LCM/Hankel operators do
  not supply the sought all-source inequality. Reading-host and repository
  PDFs returned access errors; no inaccessible content was used.
- New leaf WeilWorkSingularArithmeticToeplitzSharpness:385 lines; targeted
  `lake build --old +GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticToeplitzSharpness`
  exited0, final direct `lake env lean <leaf>` exited0 without diagnostics.
  Six public theorems audited in a /tmp scratch file; each uses only
  propext, Classical.choice, Quot.sound. Imports narrowed; no heartbeat
  increase, numerical job, umbrella build, or overlapping Lean process.
- No-go card records the exact positive survivor:
  docs/drafts/pipeline/5-failed/weil-work-03-toeplitz-prime-variance.md.
  The all-source C23 conjecture is not retired.
- Final lint exit1 has18 unrelated unreachable leaves:
  WeilWorkHigherDenominatorEndpointResidues,
  WeilWorkHigherDenominatorMaassDefect,
  WeilWorkPBAPCriticalAbel, WeilWorkPBAPCriticalBoundary,
  WeilWorkPBAPCriticalCoefficients, WeilWorkPBAPCriticalDatum,
  WeilWorkPBAPCriticalDensityLaplace, WeilWorkPBAPCriticalKernel,
  WeilWorkPBAPCriticalLaplace, WeilWorkPBAPCriticalResidue,
  WeilWorkPBAPCriticalResonator, WeilWorkPBAPCriticalWindow,
  WeilWorkSettledPhaseInteriorCancellation,
  ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation,
  ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. First lint output
  was stderr-truncated; repeated solely to capture the complete error list.
  No owned WP03 or forbidden-declaration error.
- Next-source query on local cancellation was partial (reranking deadline),
  complete inventory, snapshot two generations old. Read all candidate and
  source-argument signatures. Exhaustive rg for LocalMassBounded combined
  with coneDeviation found the source theorem only with nonnegativity at
  WeilDeviationLocalMass:584; other occurrences were conditional consumers.
  This motivates an unproved signed-source extension, not an extra premise.
- Post-audit index refresh exited0; generated LEAN_API/LEAN_GAPS/
  LEAN_OVERVIEW have no Git diff. Owned whitespace check passed. All owned
  /tmp API, axiom, search and audit scratch files removed; every owned
  process terminated normally. Cross-session memory saved. WP03 goal active.

## Cycle29 research and proof audit, complete

- Receiver correction: LocalMassBounded gives bounded harmonic sums via
  WeilConeMultiplesOfPrimeLaw:134. WeilLittleODeviationHarmonicConvergence:369
  requires local mass tending to zero for convergence. The earlier checkpoint
  conflated these; both the working card and saved memory are corrected.
- Deep source-summatory query: partial, semantic deadline; deep Perron query:
  partial, reranking deadline. Both complete inventories, semantic coverage
  unmeasured, compiler coverage largely source-only, refresh still running.
  Candidate and source-argument statements inspected. No all-source sharp
  summatory or plain harmonic convergence producer found in these results.
- Verified source mechanism: WeilPositiveProducerLindelof:170 gives logarithmic
  growth of A-Phi; SharpReciprocal:25 supplies exact integer-gap smoothing;
  HTGeometry/SmoothWeightShift supplies the holomorphic contour shift;
  SmoothWeightSharpMellin:247 supplies the fractional cost.
- Primary calibration: [Harper, Riemann zeta lecture notes, Lemma2.4 and
  Remark2.6](https://warwick.ac.uk/fac/sci/maths/people/staff/harper/zetacoursenotes1.pdf)
  explicitly treats arbitrary absolutely convergent coefficients and smoothing.
  [de Roton--Revesz](https://arxiv.org/pdf/1210.2284) requires extra signed
  Tauberian control in its more general setting. No such control is assumed here;
  the full-source analytic bound supplies the effective Perron argument.
- Novelty verdict BRIDGE. The source specialization appears absent in audited
  corpus hits; the analytic method is classical, with no publication claim.
- Initial local elaboration/algebra issues repaired. Exact full scratch source
  and API probes passed. Both targeted --old leaf builds and both final direct
  lake env lean source checks exited0, without new-leaf diagnostics. Dependency
  diagnostics were replayed by Lake; no umbrella or full build was run.
- Five public declarations audited from /tmp: only propext, Classical.choice,
  Quot.sound. Both leaves wired into RHTower. Lint exited1 on eight unrelated
  unreachable leaves: WeilPaperCauchyProfileRecovery,
  WeilWorkHigherDenominatorPoissonSmooth,
  WeilWorkHigherDenominatorWeightedIntegral, ApertureConeCalculus,
  ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal,
  BoundaryCoronaCStarAlgebra. No owned WP03 or forbidden-declaration error.
- Index refresh exited0; LEAN_API, LEAN_GAPS, LEAN_OVERVIEW unchanged in Git.

## Cycle30 source audit: sign of the ordinary harmonic limit

- Deep harmonic and Gonek/contour queries completed, with no errors and full
  inventoried-file coverage. Semantic coverage unmeasured; compiler coverage
  mostly source-only. The Gonek snapshot was three generations old with
  background refresh active. All candidate and source-argument signatures read.
- Existing sign receiver WeilConeHarmonicPinning:224 requires NotchSmall.
  Its absolute-mass fields are not consequences of C29's signed cancellation.
  The leading refined-envelope error retains L*sum |d(n)|/n, so using this
  envelope unchanged cannot exploit the new theorem.
- [Laaksonen, thesis, Lemma3.5](https://nikolaaksonen.fi/wordpress/wp-content/uploads/2016/05/laaksonen-thesis-online-final.pdf)
  gives a modified Gonek coefficient-extraction formula but requires pointwise
  a(n)=O(n^epsilon). The actual source only supplies a dyadic mean-square
  estimate through WeilPrimitiveSetMeanSquare:295. Direct use rejected.
- Corpus chi stationary-phase bounds were read, including complex-amplitude
  and displaced-line variants. They are ingredients, not the required aggregate
  estimate. A whole-contour route keeping signed coefficients is recorded on
  the pipeline card with three unproved obligations. Verdict OPEN CORE.
- Subsequent direct corpus reads located ZetaChiGaussianKernel and
  ZetaLeftLineGaussianIntegrals. Their exact transform, near approximation,
  and quadratic tail remove the need for the published Gonek lemma.
  The generic series identity requires only absolute summability at3/2.
  Summability at9/8 gives a new paper aggregate error O(T^(5/6)).
- Deep Gamma/Mellin query completed without errors; boundary query partial
  at reranking deadline. Both full inventories, mostly source-only compiler
  coverage, unmeasured semantic coverage, background refresh active. All
  returned candidate and source-argument statements inspected. Exhaustive
  harmonic-sign text search still finds the NotchSmall-conditional receiver.
- [Zagier, The Mellin Transform, sections1-2](https://people.mpim-bonn.mpg.de/zagier/files/tex/MellinTransform/fulltext.pdf)
  calibrates the classical inversion and Gamma/Dirichlet-series mechanism.
  It is not a theorem about full-positive sources; that application is
  derived in the Cycle30 paper candidate in PROOF.md.
- Paper refinement cancels canonical Lambda before the contour shift and
  uses symmetric-strip Cauchy reflection against the source's positive
  boundary measure. The resulting sign argument is recorded in full, with
  explicit pole coefficients and error exponents. Status PAPER CANDIDATE,
  pending exact Lean assembly and second proof audit. WP03 stays OPEN.
- Checkpoint cleanup: all owned C28-C30 search, API, Lean scratch, lint and
  index scratch paths removed after their processes exited. No owned build
  or research process remains. Working card, paper, results and cross-session
  memory saved; final owned whitespace check passed. Goal remains active.

### Cycle30 second audit and source pairing implementation

- Fresh deep query `WeilPositiveFull harmonic limit nonpositive Gaussian chi
  Herglotz`, 180-second budget: complete, no reported errors, generation
  1280046, full inventory, mostly source-only compiler coverage, unmeasured
  semantic coverage. All 20 candidates and 20 source arguments inspected.
  No unconditional harmonic-sign theorem was returned; this is not an
  exhaustive novelty proof.
- [Booker, L-functions as distributions, Definition1.3(A3)](https://arxiv.org/pdf/1308.3067)
  requires discrete spectral support and almost-everywhere integer
  multiplicity. The source hypotheses do not supply these. Its classification
  cannot replace the missing source argument.
- Second paper audit accepts the C30 argument as a BRIDGE, with no publication
  novelty claim. Lean assembly remains open. The first implementation target
  is the exact Herglotz pairing, preserving regularization through Fubini.
  Existing `WeilFullConeHorizontalPotential.sFinite_boundaryMeasure` supplies
  the measure instance; no additional measure assumption is introduced.
- Cycle30a completed: all three new leaves pass targeted --old builds and
  final direct `lake env lean` source checks, with no owned warnings.
  Scratch API/axiom audit exits0. The reflected Cauchy identity, generic
  source identity, actual Gaussian integrability, exact Gaussian identity
  and nonnegativity all use only propext, Classical.choice and Quot.sound.
- Imports wired in RHTower; no umbrella/full build run. Formal lint exits1
  solely for unreachable unrelated leaves: WeilWorkDeficitRepairCost,
  WeilWorkHigherDenominatorPoissonAnalytic, WeilWorkPBAPJointConvex,
  ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation,
  ApertureOpenHistoryIdeal and BoundaryCoronaCStarAlgebra. No WP03-owned
  failure or forbidden-declaration error. Global gate is not reported green.
- Proof-consumer follow-up located canonical critical identity in
  WeilZetaSquareBoundaryInequality:274, exact Mertens tail constant in
  MertensSecondTheorem:257, and double-pole principal-part/rectangle
  machinery in HTGeometry/AnalyticDoublePoleSplit and RectangleDoublePole.
  These are ingredients for the still-unformalized remainder of C30.
- Index refresh exits0 (six changed source entries); generated formal/LEAN_API,
  LEAN_GAPS and LEAN_OVERVIEW have no Git diff. All 12 owned C30 scratch/log
  files removed after jobs exited. No owned build/search process remains.
  Final owned whitespace check passed; goal remains active.

### Cycle30b canonical subtraction and common pole numerator

- Fresh deep query `WeilPositiveFull canonical zeta Gaussian harmonic
  nonpositive limit`, 180-second budget, completes with no reported errors
  and partial=false. Search generation1280322, coverage generation1280329,
  full inventory68488; compiler coverage mostly pending/source-only, 43
  compiled snapshots, semantic coverage unmeasured, background refresh active.
  All20 candidate lemmas and20 source arguments inspected. No closing
  harmonic-sign or quotient-bound theorem found. This is not an exhaustive
  novelty proof.
- [Suzuki, The screw line of the Riemann zeta-function (2023)](https://londmathsoc.onlinelibrary.wiley.com/doi/full/10.1112/jlms.12785)
  concerns the canonical von Mangoldt explicit formula and the associated
  xi logarithmic derivative. It does not supply the arbitrary-source
  rigidity step. The attempted RIMS low-degree notes fetch timed out and
  is not counted as reviewed evidence.
- Exact corpus critical-line identity
  `WeilZetaSquare.re_datum_normSq_add_deriv_mul_conj` includes zeta zeros;
  no zero-freeness assumption is needed for canonical subtraction.
  `WeilWorkSettledPhaseMellinTrace.exists_decay_sourceRemainder` instead
  concerns bigEG(sourceCompletion), not the logarithmic remainder A-Phi;
  using it directly as a bound for A-Phi was rejected.
- C30b implements the exact negative spectral-mass identity and the common
  holomorphic pole numerator. Verdict BRIDGE; verification in progress.
  These are substatements of the dependency-closed C30 paper argument,
  not an assertion that harmonic sign or WP03 has been formalized.
- Continuation audit: interrupted CanonicalGaussian build has no terminal
  success or olean. Its missing process handle and absence from process
  inventory establish it is no longer running. Verification is resumed;
  no passed build is inferred from a silent log.
- Extraction deep query `signed Dirichlet convolution zeta square Gaussian
  kernel arithmetic`, budget120 seconds: partial at reranking deadline,
  search generation1280549, coverage1280557, full inventory68501, compiler
  mostly pending/source-only, semantic coverage unmeasured. All20 candidate
  and20 source-argument statements inspected; proposed ingredient set is
  generic and unverified. Direct primary corpus reads verify the signed
  convolution product and the actual Gaussian kernel's near and tail
  bounds; no coefficient-asymptotic closure was found in these results.
- Lexical follow-up `leftKernel LSeries Gaussian --any --module Zeta`
  locates `ZetaDerivZeroSumMainTerm.exists_abs_tsum_logVM_leftKernel_sub_le`.
  Its exact statement requires the canonical nonnegative logVM sequence
  and uses its summatory bound. It is not an arbitrary-source estimate.
  The pointwise near/tail split is reusable; C30 replaces its coefficient
  bound by absolute Dirichlet summability at9/8 and keeps signed main terms.
- One-sided Mellin refinement query: partial from a semantic-retrieval
  timeout, search generation1280624, full inventory68510, mostly source-only
  compiler metadata, semantic coverage unmeasured. All20 candidates and20
  source-argument statements inspected; proposed ingredient set does not
  prove this source statement. Direct source reads instead locate mathlib
  `hasSum_mellin_pi_mul_sq`, which handles arbitrary complex coefficients
  with the exact absolute weighted sum, and
  `GaussianMellinMoments.mellinConvergent_gaussianKernel`. No bounded-
  coefficient assumption is needed in the generic mathlib transform.
- C30c paper refinement passes a second sign/integrability audit: a signed
  Gaussian upper bound controls the real Mellin integral near sigma=1,
  forcing the double-pole coefficient nonpositive. This replaces the
  stronger full-asymptotic obligation for the sign target, while retaining
  the need to identify the pole value with the ordinary harmonic limit.
  Status PAPER BRIDGE, Lean implementation pending.
- Primary-literature follow-up read the introduction and Theorem1 of
  [Connes–Consani, Weil positivity and Trace formula: the archimedean place](https://alainconnes.org/wp-content/uploads/Selecta.pdf)
  (paper dated July4,2021). Its stated lower bound concerns the canonical
  archimedean functional on a restricted support interval with transform
  vanishing conditions. It does not supply the arbitrary arithmetic-source
  harmonic-sign or bounded-quotient step. Search-engine upload dates are not
  treated as the paper date. No literature novelty claim follows from this
  limited comparison.
- Frontier recheck `full Weil positivity source harmonic limit lower bound
  rigidity`, deep120 seconds: partial=false, no errors, search generation
  1280818, coverage1280826/1280827, inventory68519, mostly source-only or
  pending compiler metadata, semantic coverage unmeasured. All20 candidate
  statements and20 source-argument statements inspected after stripping
  verbose dependency metadata from the display.
- Direct source follow-up confirms the exposed-point theorem gives a
  nonpositive autocorrelation functional, with rigidity only at equality.
  It does not give the missing opposite harmonic inequality. The rough
  fibre sign law still explicitly assumes NotchSmall. The generated RH
  transfer proposal omits the retrieved theorem's nonnegative-coefficient
  and Mangoldt-majorant premises and is rejected as a source closure.
  These hits reinforce the distinction between an unconditional untwisted
  harmonic sign and the still-missing fibre/local-mass or quotient bound.
- Current C30b lint exits1, with no WP03-owned error and no prohibited
  declaration. Its six unreachable modules are
  WeilWorkExposingRayDifferentialWidth, ApertureConeCalculus,
  ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal and
  BoundaryCoronaCStarAlgebra. These are outside the assigned write scope;
  the global gate is not reported green. Older eight-module lint counts
  above describe their earlier snapshots only.
- Final C30b audit: CanonicalGaussian, PoleCancellation, GaussianShift,
  SignedConvolution and GaussianError targeted --old builds pass. All five
  final direct lake-env-lean checks pass without warnings. All37 public
  definitions/theorems were individually printed in a /tmp axiom scratch;
  every dependency list is contained in propext, Classical.choice and
  Quot.sound. No sorryAx or error marker. All five umbrella imports verified.
- API probes pass, including universe-instantiated generic analysis APIs.
  The error proof's unused tactic was removed and the leaf rebuilt and
  directly audited. No heartbeat override, added axiom, computation,
  source-sign premise or full/umbrella build. Source index exits0; generated
  LEAN_API/LEAN_GAPS/LEAN_OVERVIEW have no Git diff. C30b classification
  PROGRESS/BRIDGE. C30c's GaussianBound file is separately under verification;
  harmonic sign and the WP03 uniform quotient detector remain OPEN.
- Final GaussianBound audit: targeted --old build and final direct source
  check pass without warnings. All four public theorems have standard-only
  axiom lists. Together with C30b this gives six audited new leaves and41
  individually audited public declarations. GaussianBound is wired into
  RHTower; no full/umbrella build. Its capstone proves the actual signed
  Gaussian sum is bounded above by C*T^(5/6) from hW alone.
- Latest C30c lint exits1 for six unrelated unreachable leaves:
  WeilWorkDeficitXiApproximationCost, ApertureConeCalculus,
  ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal and
  BoundaryCoronaCStarAlgebra. No WP03-owned or prohibited-declaration error.
  The changed RHTower leaf replaces the earlier snapshot's unrelated
  ExposingRay leaf. Index refresh exits0. No broader green claim is made.
- Minimal Mellin API and integrability scratch exits0 without diagnostics
  after fixing an unscoped infinity notation. Its actual proof of
  integrability of the complex sum from summable integral norms is saved
  in PROOF.md. It adds no new source conclusion; the actual-source Gamma
  norm-integral instantiation remains required. Generated catalog files
  have no Git diff; final owned whitespace check has no diagnostics.

## C30d audit

- GaussianProfile, Mellin, MellinBound, PoleSign and HarmonicSign each pass
  a targeted lake build --old +Leaf. Each final lake env lean source
  check exits0 with an empty diagnostic log. No full or umbrella build.
- All12 public definitions/theorems were individually printed in a /tmp
  axiom scratch; every list contains only propext, Classical.choice and
  Quot.sound. No added axiom, sorryAx, heartbeat override or computation.
- The two actual-source Mellin statements prove convergence and the
  transform separately. The final scalar sign is obtained by an upper
  envelope, not an unproved absolute bound. HarmonicSign uses the
  already-proved centered ordinary convergence to identify its limit.
- Fresh C30d deep search:68538 files,generation1281256,partial because
  reranking exceeded its deadline; all returned statements and proposed
  ingredient sets inspected. C31 audit:68550 files,generation1281376,
  partial=false; all20 candidate and20 source statements inspected.
  Neither search supplies the missing quotient bound.
- External comparison: [DLMF2.5](https://dlmf.nist.gov/2.5) and
  [Miller--Schmid](https://arxiv.org/html/math/0403030) support the
  classical Mellin mechanism, not an arbitrary-source WP03 closure.
  The corpus delta is removal of NotchSmall from the scalar harmonic
  sign. The new three-dilate equality candidate remains unproved.
- Final C30d lint exits1 for seven unrelated unreachable modules:
  WeilWorkHigherDenominatorBesselBoundary,
  WeilWorkHigherDenominatorFourierBoundary, ApertureConeCalculus,
  ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal
  and BoundaryCoronaCStarAlgebra. No WP03-owned or prohibited-declaration
  error. Global lint is not claimed green. The source index exits0;
  all five new imports and owned whitespace checks are verified.
- Generated LEAN_API/LEAN_GAPS/LEAN_OVERVIEW have no Git diff. All25
  completed scratch/log/research files were removed; no owned process or
  unverified Lean source remains. C31 paper candidate is retained in the
  working card and PROOF.md for the next conjecture cycle.

### 2026-10-08 C31a: arithmetic phase and uniform scaled extraction

- Kill audit: the historical C31 phase-free three-dilate profile is
  false as stated. The kernel contains cos(2*pi*y); half-integer
  frequencies give (-1)^n. C30's integer-frequency argument is intact.
  No harmonic equality was proved or claimed by this cycle.
- `WeilWorkSingularArithmeticTwistedGaussianError.lean` proves the
  all-positive-real-frequency weighted error and its summation over
  the actual full-positive source. One source constant works for all
  positive scales, with raw sum error C/r^(9/8)*T^(5/6).
- `WeilWorkSingularArithmeticTwistedExtraction.lean` proves absolute
  summability of both series, legitimate sum subtraction, actual contour
  integrability, exact scaled coefficient extraction, uniform contour
  error C*r^(-1/8)*T^(5/6), and the exact half-scale parity identity.
- Final targeted command:
  `lake build --old +GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticTwistedExtraction`.
  Both leaves built successfully; no owned warnings. Final audits ran
  `lake env lean` on each of the two source files separately; both exit0
  with empty diagnostic logs. All nine public declarations were checked
  using `#print axioms` in /tmp: only propext, Classical.choice,
  Quot.sound. Two minimal mathlib API probes also exit0.
- Both imports wired into RHTower; no umbrella/full build. Index exits0.
  Generated LEAN_API, LEAN_GAPS, LEAN_OVERVIEW have no Git diff.
- Formal lint exits1 on nine unrelated unreachable modules:
  RHTower.WeilWorkHigherDenominatorBesselBoundary,
  WeilWorkHigherDenominatorFourierBoundary,
  WeilWorkHigherDenominatorWeakTrace, WeilWorkQuantizationPairing;
  HTGeometry.ApertureConeCalculus, ApertureConeWinding,
  ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra.
  No owned-source or prohibited-declaration error. Global lint is not green.
- Searches: C31a/b deep searches completed (latest68559files,
  generation1281694,partial=false). All candidate/source statements
  inspected. C32 quadratic/gcd deep search was partial at the semantic
  deadline (68565files,generation1283089); all available20+20 statements
  inspected. Follow-up lexical/rg reads located existing dilation,
  notch-Bochner and gcd-inversion results; their additional convergence,
  NotchSmall and absolute-tail hypotheses cannot be imported here.
- External primary comparison: Booker arXiv1308.3067 has discrete and
  almost-integral spectral assumptions; these are absent for arbitrary
  hW. Fazzari arXiv2306.15553 confirms the classical additive-twist setting;
  Guillot--Wu arXiv1901.01947 gives the classical gcd/totient Gram
  factorization. No literature-novelty claim for C31a. Verdict BRIDGE.
- C31b paper proof is recorded, Lean proof pending. C32's first open
  core is actual arithmetic limit existence; neither a scalar harmonic
  limit nor finite gcd algebra supplies it. WP03 remains OPEN.
- All18 owned scratch/log/research files removed after their processes
  exited; no owned job or unverified source remains. Whitespace check
  passes on owned changes. Goal remains ACTIVE.

## C31b final audit — 2026-10-08

- Five new leaves: PolynomialWeight, PolynomialPairing, PolynomialShift,
  PolynomialGaussian, PolynomialProfile (prefix WeilWorkSingularArithmetic).
  They prove polynomial analytic/reflection/strip laws, actual weighted
  Herglotz pairing, canonical cancellation, exact residue shift, actual
  three-scale Gaussian extraction, and the literal parity-weighted profile
  upper bound. Final endpoint takes hW and arbitrary real c only.
- Final targeted command:
  `lake build --old +GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPolynomialProfile`.
  All five owned leaves pass. Each source then passes a separate
  `lake env lean GaloisForLFunctions/RHTower/WeilWorkSingularArithmeticPolynomial<Suffix>.lean`.
  Five empty diagnostic logs. All30 public declarations (24 theorems,
  six definitions) audited with #print axioms in /tmp: only propext,
  Classical.choice, Quot.sound. The sequential audit exits0.
- Imports wired; no full/umbrella build, new axiom, numerical experiment,
  or heartbeat override. Index exits0; generated catalogs have no Git diff.
- Formal lint exits1 on seven unrelated unreachable modules:
  RHTower.WeilPaperNullSamplingSpace, WeilWorkQuantizationPositiveFactor;
  HTGeometry.ApertureConeCalculus, ApertureConeWinding,
  ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra.
  No owned-source or prohibited-declaration error. Global lint is not green.
- Fresh searches completed: weighted Gaussian68568files,generation1283236;
  parity-pole68573files,generation1283395; sourceSquareCoeff68573files,
  generation1283416. All partial=false, errors[]. Candidate and source
  statements inspected. The suggested dirichletLimit ingredient was
  rejected after reading its actual Dirichlet-character-test definition.
- Primary comparison retained: https://arxiv.org/html/1901.01947v1
  establishes the classical gcd algebra. Also opened
  https://arxiv.org/html/2506.24053v1; internal date August2026, so no
  July2026 novelty conclusion depends on it. No literature novelty is
  claimed for C31b's classical analytic machinery. Verdict PROGRESS/BRIDGE.
- C32a next paper result and kill audit recorded in PROOF. Actual parity
  Mellin implementation started; interval extraction and parent C32's
  full arithmetic fibre law are not yet formally closed. WP03 stays OPEN.
