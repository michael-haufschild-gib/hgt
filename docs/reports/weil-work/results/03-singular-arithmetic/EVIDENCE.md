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
