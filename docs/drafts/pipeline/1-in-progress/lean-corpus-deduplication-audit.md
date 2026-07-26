# Lean corpus deduplication & generalisation audit (HTGeometry / HilbertMetric / RHTower)

- **ID:** dedup-audit-2026-07
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — refactor / generalisation, behaviour-preserving + strictly generalising
- **Source:** loop task 2026-07-26
- **Statement:** Every duplicated Lean declaration in the three owned areas is replaced by a single
  canonical declaration, and every family of parallel special-case theorems is replaced by one
  general law that the special cases derive from in one line.

## Goal
Reduce total corpus size and raise reusability without weakening any theorem. All rewrites are
either (a) exact clone elimination or (b) strict generalisation: the general law implies each
former special case definitionally or by a one-line instantiation. No `sorry`, no axioms, no
hypothesis strengthening.

## Gates
- [x] 0 → 1  in-progress: mechanical clone census complete (scan tool + 128 exact-clone groups)
- [ ] 1 → 2  every identified clone group collapsed, `lake build` green
- [ ] 2 → 3  generalisation targets (abstract-vs-concrete duplicated hierarchies) unified
- [ ] 3 → 4  n/a (internal refactor, no paper)

## LANDED AND VERIFIED (2026-07-26)

Eight general laws, each proved unconditionally and each with every former site re-pointed and
compiled. Verification was per-module `lake build <module>` / per-file `lake env lean`, never an
area build.

| law | module | replaces |
|---|---|---|
| `norm_inv_mul_add_one_le` (Perron kernel) | `HTGeometry/PerronKernelBound` | 24 clones / 8 modules |
| `analyticAt_Gamma_off_poles` | `HTGeometry/GammaAnalyticOffPoles` | 9 statements |
| `SpectralFamily := AbstractSpectralFamily XiZeroCopy` | `RHTower/XiSpectralFamily` | 9-module chain, −1191 lines |
| `four_mul_le_tsum_of_quartet_invariant` | `RHTower/XiEndpointOffLineQuartetHeightGap` | 8 sites, −259 lines |
| `lieModulePointStabilizer` | `HTGeometry/LieModulePointStabilizer` | 3 sites (absent from mathlib) |
| `hasDerivAt_powExpKernel` (Erlang ladder) | `HTGeometry/ErlangWignerSmithPacket` | 3 sites |
| `re_pow_pos_of_abs_arg_lt` (sector positivity) | `HTGeometry/SectorPowerPositivity` | 5 sites, removes the `n ≤ 7` cap |
| `xiDivisorSupport_univ_countable` + global instances | `RHTower/XiCanonicalProduct` | 14 sites |

Plus the mechanical layer: 50 exact-clone groups collapsed corpus-wide, 15 lemmas lifted to
common-ancestor hosts, `Nonempty XiZeroCopy` promoted to a global instance (10 `letI` removed).
**Net ≈ −2,720 lines. No theorem weakened, no `sorry`, no axiom.**

### Defects found by compilation (4), all fixed
Every one had a single root cause: the sweep tooling promoted `private` lemmas to public without
checking whether the name was already taken in the downstream import cone.
1. 9 declarations left with doubled namespaces — the corpus-wide rename ran before the deletion step
   on a job's *other* members, so deletion silently missed them.
2. `integrableOn_criticalMellinPrimeMass_Ioc` — collision; the two were the same lemma up to
   implicit vs explicit binders.
3. `natCast_cpow_conj` — collision; identical statement, different proof. (I had earlier called this
   pair harmless after checking the wrong direction of reachability.)
4. `ae_nonneg_thetaCuspHigherLikelihoodSpectralMeasure` — collision; identical statement.
A targeted grep over every promoted name now reports **zero** remaining duplicates.

**Method note:** three attempts at a static collision scanner all failed (2631 → 203 → 64 candidates,
all false positives from namespace mis-tracking). What worked was a narrow grep for the declaration
form over a known name list — and ultimately, compiling.

## B18 / B19 instance-bundle results (2026-07-26)

**B18 — `upperEnd` stack: COMPLETE.** `HTGeometry/UpperEndDifferentialInstances.lean` carries the
8-instance stack plus a companion `UpperEndComplexTowerInstances` scope (3 more: `Differential ℂ`,
`DifferentialAlgebra ℂ _`, `IsScalarTower ℂ _ _`). 35 files converted to one or two `open scoped`
lines, **−1,032 lines**, every shape (subset / exact / prefix / superset) verified by compilation.
13 files still carry small `upperEnd` runs (114 lines total) that use instances outside the bundle
(`Algebra (RatFunc ℂ) upperEndMeroField`, `Differential digammaBase`, `Differential (RatFunc ℂ)`);
low yield, left alone.

**B19 — `analyticSubring Set.univ` stack: PARTIAL, and the remainder needs different tooling.**
Measured extent is far larger than first estimated: **95 files, 1758 significant lines**.
`HTGeometry/UnivMeroFieldInstances.lean` carries the maximal 8-instance shape and compiles.
25 files converted and each verified clean (−~500 lines).

**8 files reverted.** The `EllipticGamma*` group carries preambles that *contain* the universal
instances **and** elliptic-specific ones (`Differential ℂ`,
`Differential meromorphicRationalCoordinateField`,
`Differential (meromorphicEllipticCompositum σ τ)`). A "delete the whole block containing meroField"
heuristic removes those too. My static audit for this caught only 4 of the 8; **compilation caught
all 8** — the third time this session a regex check under-reported where compiling did not.

**Attempted fix abandoned.** A selective converter (drop only instances whose provided type is in the
bundle) produced three successive corruptions of one test file — a bad span finder, a Python
precedence bug (`a + b if m else c` discarding the file body), and duplicated declarations. Each was
reverted. The remaining ~62 files need a Lean-aware edit, not line-span regex. Do not retry this with
generated regex scripts.

### B19 stopping point and why the remainder is correctly excluded

**66 files converted and individually compile-verified (−~1,343 lines).** 25 candidates remain,
totalling only 468 lines, and they are dominated by the `EllipticGamma*` /
`HomogeneousMultipleEllipticGamma*` / `MeromorphicElliptic*` families.

**These are not simply "harder" — they bind a different instance.** Their preambles set

```lean
local instance …ComplexAlgebraMero : Algebra ℂ (meroField Set.univ) :=
  meromorphicEllipticCompositumComplexAlgebraMero
```

whereas `UnivMeroFieldInstances` binds the same class to
`((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp (constToAnalytic Set.univ)).toAlgebra`.
`Algebra` is data-carrying, so these are two *different* ℂ-algebra structures on the same type, and
the elliptic development depends on its own. Opening the bundle in those files therefore changes the
structure under their theorems, which is exactly why they fail to elaborate. The compile-check drew
the correct boundary; the classification-by-instance-type never could have, because the types agree
and only the terms differ.

**Corpus hazard worth recording:** there are (at least) two competing `Algebra ℂ (meroField Set.univ)`
instances in HTGeometry. They are never in scope together today, but any future attempt to globalise
either one will collide. Whether they are propositionally equal is unresolved — I could not locate
the declaration site of `meromorphicEllipticCompositumComplexAlgebraMero` by grep at all, which is
itself a reason to leave this family alone until someone establishes the relationship.

The elliptic group needs its own companion scope (adding `Differential ℂ`,
`Differential meromorphicRationalCoordinateField`,
`Differential (meromorphicEllipticCompositum σ τ)` and their `DifferentialAlgebra`s) built around
*their* ℂ-algebra, not the universal one. That is a separate, well-defined task.

### The two `Algebra ℂ (meroField Set.univ)` structures actively conflict (established, not conjectured)

Attempting to give the elliptic family its own scope produced, from Lean:

```
synthesized type class instance is not definitionally equal to expression inferred by typing rules
  synthesized  ellipticComplexAlgebraMero
  inferred     UnivMeroFieldInstances.univComplexAlgebraMero
```

So the two ℂ-algebra structures on `meroField Set.univ` — `meromorphicEllipticCompositumComplexAlgebraMero`
and the `constToAnalytic` composite — are **not** definitionally equal, and once both are reachable
Lean silently prefers whichever it finds first. This is no longer a latent hazard; it fired.

**Consequence, and a mistake corrected.** I had converted 16 `Meromorphic*`/`EllipticGamma*` files to
the *universal* scope. Each compiled individually, but several sit inside the elliptic development,
where the elliptic algebra is intended — so those conversions could silently swap the algebra
structure underneath the elliptic theorems. All 16 were reverted. **Compiling green is not sufficient
evidence of correctness when data-carrying instances are involved**; that is the operative lesson,
and it is why B19 is deliberately restricted to files outside the elliptic development.

The subsequent failures after reverting were **stale oleans**, not source damage — `lake build` on the
cone restored everything. Worth remembering: after a revert, rebuild before judging.

**Remaining task, well-defined:** build `EllipticMeroFieldInstances` (9 instances: the elliptic
ℂ-algebra, `Differential ℂ`, the mero derivation and char-zero, the elliptic compositum's
differential and differential-algebra, the rational coordinate field's) and convert the elliptic
family to it — but only after confirming no file in that cone opens `UnivMeroFieldInstances`. The
scope module itself compiled cleanly on the first attempt; it was removed only because the universal
scope was reachable from its cone.

**Tooling note:** `meromorphicEllipticCompositumComplexAlgebraMero` could not be located by grep in
any form. `#check @name` in a `/tmp` scratch importing a consumer found it immediately. Use Lean, not
grep, to locate declarations in this corpus.

### B17 — assessed and declined (not a no-go, a poor trade)

Extracting `iInter_goodPattern_mem_residual` from `AnalyticNevanlinnaCarrierRelationFree` requires a
standalone statement carrying: 13 binders (including `[Countable Γ]`, `[Fintype ιf]`,
`[DecidableEq ιf]`, `[IsProbabilityMeasure eta]`), the `let frozen := …` / `let S := LinearMap.ker …`
definitions, the `IsClosed`/`CompleteSpace`/`BaireSpace` derivation for `S`, the `goodPattern`
family, and the 15-line `hgoodPattern` obtained by `simpa … using
global_injectiveShifts_actualNevanlinna_fullRankWitness_dense_residual`.

That is ~45 lines of lemma to replace ~34 duplicated lines across the two independent proofs — a net
saving of roughly 17 lines. The naming value is real (this Baire-genericity statement is the file's
actual mathematical content and is currently anonymous), but the statement is long and delicate and
the payoff is small. Deferred deliberately, with the full binder list recorded above so a future
attempt starts from the design rather than re-deriving it.

### B17 LANDED — and it needed no new lemma
`allFinitePatterns_abstractCarrier_fullRankWitness_dense_residual` **is** the Baire-genericity
statement; `…_relationFree_dense_residual` was rebuilding it from scratch (the `goodPattern` family,
the 15-line `hgoodPattern`, the `countable_iInter_mem` residual step) before applying its own subset
step. It now calls the first theorem and keeps only the subset step. `865 → 840` lines, and all four
theorems in the file derive from one proof of genericity instead of two.
Note: destructuring the first theorem's `let`-bound conclusion blocks instance resolution —
`have h := …; dsimp only at h; obtain ⟨…⟩ := h` is required.

Earlier I assessed B17 as "~17 lines, not worth it" and declined. Reconsidering under the rule to
stop only on impossibility found a cheaper route worth 25 lines and a better structure. The
assessment was wrong because it assumed a new lemma was needed.

### B11 — connector landed, inversion still open
`SpectralBandwidthFano.endpointBudget_eq` now states the fact that makes the whole Slater/quasi-free
identification work:

```lean
theorem endpointBudget_eq (lower upper : ℝ) :
    lower - (upper - lower - 1) ^ 2 / 4 = lower * upper - (lower + upper - 1) ^ 2 / 4 := by ring
```

The per-orbital budget used by every Slater estimate and the product budget used by the
occupation-weighted ones are the same number. Without it the two `…_lower_bound` theorems and the two
nonnegativity thresholds look unrelated; with it they are one statement at two normalisations. This
belongs in the corpus independently of the restructure.

**Remaining:** `SlaterPluckerConnector` (the only external consumer of the Slater names) reaches
`QuasiFreeFillingFano`, so route (b) is open — delete the ~9 duplicated Slater proofs from
`SpectralBandwidthFano` and re-state them in `QuasiFreeFillingFano` as `occupation ≡ 1` instances
using `endpointBudget_eq` and `∑ i, (1:ℝ) = card ι`. Each conversion is a few lines of rewriting;
estimated ~100 lines over 9 theorems.

## Execution order for the next session (research is done; build next)

Backlog research is complete and over-supplied — the next session should **land code, not scan**.
Ordered by (value ÷ risk), each item's design already settled above:

1. **B20** — `four_mul_le_tsum_of_quartet_invariant` in `XiEndpointOffLineQuartetHeightGap`.
   One theorem, eight one-line replacements, no new import edge. Start here.
2. **B16** — Erlang ladder derivative + unit mass over the existing `erlangPowKernel`; move the
   definition up into `ErlangWignerSmithPacket`. Two files.
3. **B12** — wire the three current-algebra stabilisers to `lieModulePointStabilizer`
   (module already written and compiles; `b12_lie.py` ready).
4. **B21** — `re_pos_of_pow_inv_sub_mul_I`, replacing five per-order sector theorems with the sharp
   arctan form.
5. **B18** — the `upperEnd` scoped-instance bundle (36 files, ≈ −700 lines); shapes classified, one
   build-time check flagged.
6. **B14** — `DegreeFiveGaussianCurvature` jet unification (≈ −700 lines).
7. **B11** — Slater/quasi-free module inversion (both obstacles discharged).
8. Then B19, B17, B13/B8 host moves, B15, B22, B10.

## Census (2026-07-26)

Scanner `scan2.py` extracts top-level decls, splits statement/proof at the first depth-0 `:=`/` by`,
and groups by normalised text.

| Metric | Count |
|---|---|
| declarations scanned (3 areas) | 67018 |
| identical statement groups | 1136 (~14234 redundant lines) |
| identical proof groups | 381 (~4926 redundant lines) |
| identical statement **and** proof (exact clones) | 128 (~2063 redundant lines) |

An import-closure pass (`clone_plan.py`) splits the 128 exact-clone groups into 55 with a unique
upstream copy reachable from every other copy (mechanically collapsible, ~892 lines) and 73 with no
common upstream (need a new shared module, or are genuinely independent).

## Work batches

### B1 — `xiDivisorSupport_univ_countable` (14 sites) — EDITED, build pending
13 `private` verbatim copies + 1 public copy of the same 8-line proof, each followed by
`noncomputable local instance : Countable XiDivisorSupport` and usually `… Countable XiZeroCopy`.
Fix landed: one `theorem xiDivisorSupport_univ_countable` + global
`instance Countable XiDivisorSupport` / `instance Countable XiZeroCopy` in
`RHTower/XiCanonicalProduct.lean`, where the abbrev is defined. `Countable` is a `Prop`-class, so a
global instance introduces no diamond. −228 lines.

### B2 — Perron kernel bounds (24 clones over 8 files) — EDITED, build pending
`qcc_/qtp_/cnd_/gw/kernel_/inv_quad_` variants of the same four estimates in
`QuietCrossing{Cocycle,CocycleTPoly,Conductor,Escalation,Rigidity}`, `QuietPathRigidity`, plus the
same reciprocal-quadratic integrability in `XiThetaSquareRate{Hardy,SourceL2}`.
**Generalisation, not just dedup**: new `HTGeometry/PerronKernelBound.lean` proves the single law

> `norm_inv_mul_add_one_le : 0 < r → r ≤ ‖s‖ → r ≤ ‖s+1‖ → ‖(s(s+1))⁻¹‖ ≤ (r^2)⁻¹`

and derives all three contour specialisations (`_of_abs_im`, `_of_line`, `_of_re_pos`, `_of_re_neg`)
from it, plus `integrable_inv_sq_add_sq`. The 24 clone bodies are deleted and all 48 call sites point
at the general law. −388 lines.

### B3 — Γ- and ζ-analyticity prerequisites (11 clones) — EDITED, build pending
`analyticAt_Gamma_of_re_pos*` (6×) and `analyticAt_zetaResidueUnit*` (5×).
**Generalisation**: new `HTGeometry/GammaAnalyticOffPoles.lean` carries
`analyticAt_Gamma_off_poles` (the general law: analytic away from `-ℕ`) and derives
`analyticAt_Gamma_of_re_pos` from it. The two pre-existing HTGeometry statements
(`GammaDifferentialFE.analyticAt_Gamma`, `GammaGammaFactorialBlowUp.analyticAt_Gamma_on_rightHalfPlane`)
now delegate to it as well, so nine former statements reduce to one law + two named corollaries.
`analyticAt_zetaResidueUnit` moved to `RHTower/ZetaLogDerivResidue.lean` next to the definition of
`zetaResidueUnit`. −74 lines.

### B4 — Abstract-vs-concrete spectral family hierarchy (~1400 lines) — PLANNED
`HTGeometry.AbstractSpectralFamily ι` is literally `RHTower.SpectralFamily` at `ι = XiZeroCopy` with
`inv := xiZeroCopyLineConjEquiv`; `RHTower/XiAbstractInstance.lean` already builds the bridge
(`SpectralFamily.toAbstract`, with `toAbstract_traceC := rfl`) but the
`XiSpectralFamily{,Analytic,Decay,Graded,Shell,OnLine,GradedOnLine,Lift,RH}` chain still re-proves
`AbstractSpectral{Family,Decay,Graded,Shell,Charge,Mass,Defect,Rigidity}` line for line.

Verified correspondence (name-by-name):
`re_nonneg weight weight_pos term norm_term norm_term_le summable_norm_term traceReal traceC
traceReal_nonneg norm_traceC_le traceReal_antitone exists_min_re_of_nonempty differentiable_term
norm_term_le_on_box differentiableOn_traceC_box differentiableAt_traceC analyticOnNhd_traceC
bottomCopy/bottomIndex bottomHeight bottomHeight_le bottomHeight_pos
exp_bottomHeight_mul_traceReal_le twist norm_exp_twist differentiableOn_twist norm_twist_le
norm_twist_imaginary_ray norm_twist_real_ray norm_twist_le_of_line_bound
norm_traceC_le_of_line_bound gtwist norm_gtwist differentiableOn_gtwist norm_gtwist_le
norm_twist_le_of_line_growth norm_traceC_le_of_line_growth bottomShell mem_bottomShell
mem_bottomShell_lineConj/mem_bottomShell_inv aboveBottom mem_aboveBottom exists_secondHeight
bottomShellSum aboveBottomSum bottomShellSum_eq traceC_vertical_split
exp_bottomHeight_mul_norm_aboveBottomSum_le bottomShell_regroup im_le_of_line_growth
abs_im_le_of_line_growth abs_im_le_of_line_growth_all abs_im_le_iff_exists_line_growth
norm_traceC_le_of_abs_im_le` — all present on both sides.
Genuinely Xi-only: `xiPoissonFamily`, `xiMassFamily`, `cut`, `below`, `lift`,
`im_eq_zero_of_line_bound(_all)`, `im_eq_zero_iff_exists_line_bound`, `im_eq_zero_of_subexponential`.

Blast radius is 13 files, 3 constructors (`xiPoissonFamily`, `xiMassFamily`, `lift`) and 8
`.conj_stable` uses.

Planned move: `abbrev SpectralFamily := HTGeometry.AbstractSpectralFamily XiZeroCopy` (an `abbrev`
is reducible, so `F.weight` etc. keep resolving by dot-notation to the abstract namespace), the
three constructors gain `inv := xiZeroCopyLineConjEquiv`, the duplicated lemmas are deleted, and the
`lineConj`-specific statements are generalised to `F.inv` — which is a strict generalisation, since
the Xi instances satisfy `inv = xiZeroCopyLineConjEquiv` by `rfl`.
Open sub-issue: `xiPoissonBox` vs `AbstractSpectralFamily.box` — same set, two constants; the box
lemmas must be re-pointed or `xiPoissonBox` made an abbreviation of `box`.
Also generalisable into the abstract layer while there: `cut`, `below`, `lift` are index-free.

### B5 — Sonin `SoninTimeBandHilbertSchmidt.legacy_*` (5 clones) — in B6 sweep
Import direction checked: `SoninTimeBandHilbertSchmidt` imports `SoninTimeBandIdeal`, so the
`legacy_` copies are the *downstream* re-proofs. They are deleted in favour of the upstream
originals by the B6 sweep.

### B6 — mechanical sweep of the 55 upstream-resolvable clone groups — tooling ready
`clone_exec2.py` deletes each downstream copy, rewrites every corpus reference (checking first that
each referencing module can reach the upstream module), and promotes the upstream copy from
`private` to public when needed. Restricted to `theorem`/`lemma` clones; `def`/`abbrev`/`structure`
clones are held back because merging two conceptually distinct definitions that happen to share a
body is a semantic regression, not a cleanup.

### B7 — HilbertMetric
46 files, 18041 lines. Only one exact clone
(`SymmetricFockShadowRigidity.symmetricFockAnnihilation_mem_loweringShadow` ←
`SymmetricFockShadow.annihilation_mem_loweringShadow`), handled by B6. A structural review for
parallel special-case families is still owed.

### B8 — the 73 groups with no common upstream — not started
These need a new shared module (like B2/B3) rather than a delegation. Ranked by size in
`clone_plan.json`.

### B9 — the 381 identical-*proof* groups — queued, ranked
A statement-only match usually means two lemmas about different objects, but an identical *proof*
with a different statement is almost always a missed generalisation: the proof does not depend on
what the statement is about. 41 groups have ≥3 members. Ranked queue:

| ×n | lines | shared proof | members |
|---|---|---|---|
| ~~8~~ | ~~22~~ | ~~`exact HTGeometry.finiteDerivativeReporterMap_postcomp_newBlindPacket …`~~ | **not a defect** — inspected: the HTGeometry law is already fully general in `f : ℂ → ℂ`, and the eight Gamma/Digamma/Zeta/Xi/XiLogDeriv statements are one-line named instantiations at particular `f`. That is the intended API surface, not duplication. |
| 3 | 34+9 | `LSeries_sqrt_eq_riemannZeta_shift`, `sqrt_LSeriesSummable` | BVPrimeWindowContinuation / CCMInverseTiltedDyadicPrimeTomography / CCMSharpPrimeWindowDirichlet |
| 3 | 27 | point-stabilizer submodule of a current algebra | ProjectiveHorizon{,Higher,ArbitraryRank}CurrentAlgebra — one law over the rank |
| 3 | 21 | `meroField_deriv_algebraMap_complex_*` | EllipticGamma{RationalBaseMatroid,StructuralGeneratorSpectrum}, MultipleEllipticGammaHypertranscendence |
| 3 | 21 | `ratFuncAlgHom_ext_X` | FreeJetTranslationFixedField / RatFuncAffineNormalForm / ScalarDifferentialTorsor |
| 4 | 8 | `norm_spectralTranslationPhase_*` | ThetaCuspShellIncompleteGammaCoordinate + XiCTaylorThetaTail{MonotonePacketCurrent,PhaseAdaptedProuhetHalfLine} |
| 5 | 8 | `Polynomial.induction_on` evaluation | ExpPolynomialDA / Hypertranscendence / HypertranscendencePolynomial / PolynomialFirstOrderActivationBoundary |
| 3 | 14 | `intCast_conv_integral` | GammaCell{DegreeZeroAction,Mobility} / UnboundedGearCount |
| 3 | 9 | `norm_l2_sq_complex` | MobiusLaplaceMellinPlancherelBridge / SoninTimeBandHilbertSchmidt / XiThetaSquareRateSourceL2 |
| 4 | 7 | `mobiusContactGammaFactorialScale_eq` | four MobiusContactGamma…UniversalityLaw modules |

### B11 — HilbertMetric: the Slater family is the quasi-free family at full occupation — PLANNED
`SpectralBandwidthFano.lean` (460 lines) develops six spectral quantities for a Slater determinant
(`slaterCompressedSpectralEnergy`, `slaterSpectralMean`, `…Variance`, `…FanoMargin`,
`…SecantDefect`, `…CoherenceDefect`) together with ~16 theorems about them.
`QuasiFreeFillingFano.lean` (568 lines) develops the *same six quantities weighted by an occupation
function* and the same ~16 theorems, and already closes the loop with four bridge lemmas —
`quasiFreeSpectralMean_one`, `quasiFreeCompressedSpectralEnergy_one`, `quasiFreeSpectralVariance_one`,
`quasiFreeSpectralFanoMargin_one` — proving that at `occupation ≡ 1` the weighted quantities *are*
the Slater ones. So the corpus already knows the special case is an instance; it just still carries
a full parallel proof of it.

Matched theorem pairs (Slater ⟵ quasi-free at `occupation = 1`):
`slaterCompressedSpectralEnergy_eq_diagonal_add_coherence`, `slaterSpectralSecantDefect_nonneg`,
`slaterSpectralCenteringDefect_nonneg`, `slaterSpectralCoherenceDefect_nonneg`,
`slaterSpectralFanoMargin_three_defect`, `slaterSpectralFanoMargin_lower_bound`,
`slaterSpectralFanoMargin_nonnegative_of_bandwidth` (↔ `…_nonnegative_of_filling`),
`slaterSpectralFanoMargin_negative_forces_bandwidth` (↔ `…_negative_forces_filling_failure`),
`slaterSpectralFanoMargin_eq_lower_bound_iff`.

Import direction is currently wrong for a one-line derivation (`QuasiFreeFillingFano` imports
`SpectralBandwidthFano`), so there are two routes:
- **(a) module inversion** — move the occupation-weighted family and the orbital-level lemmas it
  needs (`spectral_sq_le_secant`, `lower_le_orbitalSpectralMean`,
  `orbitalSpectralSecondMoment_le_secant`, `endpointPairSpectralFanoMargin_square`) into a new
  bottom module; `SpectralBandwidthFano` then keeps only the `occupation = 1` specialisations.
  Cleanest, largest reduction, most churn.
- **(b) relocate the specialisations** — delete the duplicated Slater proofs from
  `SpectralBandwidthFano` and re-state them in `QuasiFreeFillingFano` as one-line instances. No new
  module, but downstream users of the Slater names must move their import.
Route (a) is preferred; each pair needs its hypothesis shape checked, since the quasi-free versions
carry occupation bounds (`0 ≤ occupation i`) that must be discharged at `occupation ≡ 1`.

**Obstacle found and discharged.** The two Fano floors *look* different, which would block the
specialisation:

- Slater: `card ι * (lower - (upper - lower - 1)^2 / 4) ≤ slaterSpectralFanoMargin`
- quasi-free at `occupation ≡ 1`: `lower*upper*card ι - card ι * (lower + upper - 1)^2 / 4 ≤ …`

They are the same number. Writing `a = lower`, `b = upper`,

  `(a + b - 1)^2 - (b - a - 1)^2 = ((a+b-1) - (b-a-1))((a+b-1) + (b-a-1)) = (2a)(2b - 2) = 4a(b-1)`,

so `a*b - (a+b-1)^2/4 - (a - (b-a-1)^2/4) = a*b - a - a(b-1) = 0`. Hence

  **`lower - (upper - lower - 1)^2 / 4 = lower*upper - (lower + upper - 1)^2 / 4`**  (provable by `ring`)

is the connector that aligns the two floors, and with it the Slater bound is literally the quasi-free
bound at full occupation. The three defect terms match directly:
`slaterSpectralSecantDefect`, `…CenteringDefect`, `…CoherenceDefect` are the `occupation ≡ 1` cases of
their quasi-free namesakes by `simp`. So `slaterSpectralFanoMargin_three_defect` and
`slaterSpectralFanoMargin_lower_bound` — the two largest Slater proofs — reduce to one-line
instantiations plus this `ring` identity. No hypothesis is strengthened.

**Second obstacle, also discharged: the threshold hypotheses.** The two nonnegativity theorems
carry thresholds that also look unrelated:

- Slater: `(upper - lower - 1)^2 ≤ 4 * lower`
- quasi-free: `card ι * (lower + upper - 1)^2 ≤ 4 * (lower*upper) * ∑ i, occupation i`

At `occupation ≡ 1` the sum is `card ι`, so the quasi-free threshold reads
`(lower + upper - 1)^2 ≤ 4 * lower * upper`. By the same connector identity,

  `(upper - lower - 1)^2 ≤ 4*lower  ⟺  lower - (upper-lower-1)^2/4 ≥ 0
                                    ⟺  lower*upper - (lower+upper-1)^2/4 ≥ 0
                                    ⟺  (lower + upper - 1)^2 ≤ 4*lower*upper`,

so the two thresholds are the *same* hypothesis. Consequently
`slaterSpectralFanoMargin_nonnegative_of_bandwidth`,
`slaterSpectralFanoMargin_negative_forces_bandwidth` and
`slaterSpectralFanoMargin_eq_lower_bound_iff` are literal `occupation ≡ 1` instances of
`quasiFreeSpectralFanoMargin_nonnegative_of_filling`,
`…_negative_forces_filling_failure` and `…_eq_lower_bound_iff`. Both floors are `card ι` times the
same scalar, so the `card ι = 0` case degenerates identically on both sides and needs no separate
argument. Route (a) is therefore fully validated: nothing in the Slater development survives as
independent mathematical content.

### B12 — Lie-module point stabiliser — module written, wiring PLANNED
`ProjectiveHorizon{,HigherRank,ArbitraryRank}CurrentAlgebra` each carry a verbatim copy of the same
27-line construction — the annihilator `{A | ⁅A, v⁆ = 0}` of a vector in a Lie module — specialised
to `Matrix (Fin 2)`, `Matrix (Fin 3)` and `Matrix (arCurrentIndex ι)` coefficients. Nothing in the
proof uses the matrix structure: closure under `+` and `•` is bilinearity of the action, closure
under brackets is `lie_lie`. mathlib has no such construction.
`HTGeometry/LieModulePointStabilizer.lean` now carries the general law
`lieModulePointStabilizer R L v : LieSubalgebra R L` plus its membership `simp` lemma; the three
copies become instantiations once it is compiled and wired in.

### B13 — cross-area duplication is now essentially cleared
After B1–B8 only 15 identical-*proof* groups have members in two different areas, all ≤26 lines.
The survivors that are real duplication and still need a host module (neither member reaches the
other):

| lines | pair |
|---|---|
| 26 | `HTGeometry.PrimeDependentValuationLayerBarrier.primeProfileJetCombination_layer_finite` ↔ `RHTower.XiTransverseShiftAllValuationLayerRank.xiTransversePrimeProfileJetCombination_layer_finite` |
| 12 | `HTGeometry.HilbertSchmidtRankOne.hsNormSq_smul` ↔ `RHTower.SoninTimeBandHilbertSchmidt.hsNormSq_smul_eq` |
| 12 | `HTGeometry.CompactTailDensePrimeShiftJet.tendsto_primeReal_cofinite_atTop` ↔ `RHTower.SectorPrimeZeroUniqueness.tendsto_prime_coe_real_cofinite_atTop` |
| 11 | `HTGeometry.ProjectiveHorizonLaurentResidueSeam.trace_lie_mul_cyclic` ↔ `RHTower.EulerLaurentResidueDouble.trace_lie_mul_cyclic_complex` |
| 8 | `HTGeometry.ConstantFieldQEDGammaClock.complex_half_ne_integer` ↔ `RHTower.ZetaHorizonGammaIntensitySeparation.complex_half_ne_integer` |
| 7 | `HTGeometry.SectorPowerMassLower.complexArg_eq_arctan_of_re_pos` ↔ `RHTower.AnchorTilt.arg_eq_arctan_of_re_pos` |
| 6 | `HTGeometry.PointedFisherCutoffWardTrace.opTrace_smul` ↔ `RHTower.TraceClassOperatorTrace.opTrace_smul` |

(The earlier note that `complex_half_ne_integer` had been merged was wrong: `ZetaHorizonGammaIntensitySeparation`
does not reach `ConstantFieldQEDGammaClock`, so the sweep correctly left it alone. It belongs here.)

**Latent hazard found:** `RHTower.natCast_cpow_conj` is defined twice — in `RHTower/Reflection.lean`
and in `RHTower/SymmetrizedEMCarrier.lean` — with the same fully-qualified name. It is currently
harmless only because no module reaches both (checked: `MollifiedCarrier` and `ZetaCarrier` reach
`Reflection` and not `SymmetrizedEMCarrier`). Any future merge that puts them in one import cone
will produce an ambiguous reference. Same-name-different-module pairs should be renamed before the
next sweep.

### B14 — HilbertMetric: `DegreeFiveGaussianCurvature` is one jet development written three times
`DegreeFiveGaussianCurvature.lean` (1392 lines, the second-largest HilbertMetric file) carries
**13 declaration families, each in exactly three copies** — a `Value`, a `First` and a `Second`
version, i.e. jet orders 0, 1, 2 of the same construction:

`degreeFive<J>Limit`, `degreeFive<J>LimitMatrix`, `degreeFive<J>Remainder`,
`degreeFiveNormalized<J>Entry`, `degreeFiveNormalized<J>Matrix`, `degreeFiveRecombined<J>Matrix`,
`degreeFiveGaussian<J>Matrix`, `degreeFiveNormalized<J>Entry_eq_recombined_div`,
`degreeFiveNormalized<J>Matrix_eq_scale_recombined`, `degreeFiveRecombined<J>Matrix_eq_congr`,
`tendsto_degreeFiveNormalized<J>Entry`, `tendsto_degreeFiveNormalized<J>Matrix`,
`degreeFive_gaussian<J>Jet` (plus `degreeFiveGaussianBandwidth<J>Matrix` in two copies).

The three normalised entries are literally the same formula,

  `normalized<J>Entry lam nodes c e q r = (if q = r then <J>Limit lam q else 0)
      + <J>Remainder lam nodes c q r e / e ^ (q.1 + r.1)`,

differing only in which `Limit`/`Remainder` pair is plugged in. Plan: bundle the pair as a
`DegreeFiveJetDatum d` (fields `limit : ℝ → DegreeFiveIndex d → ℝ` and the remainder function,
plus the hypotheses the convergence proofs consume — `degreeFiveSecondLimit` ignores `lam`, so the
uniform arity `ℝ → Index → ℝ` covers all three), prove the six theorem families once over the
datum, and recover all 39 existing declarations as one-line instances so no downstream name
changes. Estimated reduction ≈700–900 lines with no statement weakened.

**Highest-confidence piece, design settled.** The three `tendsto_degreeFiveNormalized<J>Entry`
proofs are identical modulo substitution, and — crucially — the jet plays no role at all: the proof
only needs the remainder to be `o(e^10)` at the origin. So the general law does not even need the
jet datum, only a real constant and a real remainder function:

```lean
theorem tendsto_degreeFiveNormalizedEntry {d : ℕ}
    (limitVal : ℝ) (remainder : ℝ → ℝ)
    (hrem : remainder =o[nhds 0] fun e : ℝ => e ^ 10)
    (q r : DegreeFiveIndex d) :
    Tendsto (fun e => limitVal + remainder e / e ^ ((q.1 : ℕ) + (r.1 : ℕ))) (nhds 0)
      (nhds limitVal) :=
  by simpa using (tendsto_const_nhds (x := limitVal)).add
    ((hrem.trans_isBigO (degreeFive_pow_ten_isBigO_degreeSum q r)).tendsto_div_nhds_zero)
```

Since `degreeFiveNormalized<J>Entry` unfolds definitionally to `limitVal + remainder e / e^(q+r)`
with `limitVal := if q = r then <J>Limit … else 0`, each of the three existing statements follows by
supplying its own `o(e^10)` remainder bound (`degreeFive_gaussian<J>Jet`). One four-line lemma
replaces three twelve-line proofs *and* is strictly more general. The three
`tendsto_degreeFiveNormalized<J>Matrix` proofs then collapse the same way through a single
"entrywise → diagonal matrix" step.

**LANDED:** four of the families collapsed and are verified — `tendsto_degreeFiveNormalizedEntry`,
`tendsto_matrix_of_tendsto_entry`, `matrix_eq_scale_conj_of_entry_div`,
`matrix_eq_congr_of_double_sum`, each with its three instantiations.

The `<J>Entry_eq_recombined_div` triple is the one family that does **not** collapse. Per-case check
done (masked diff of the three bodies):
- Value vs First: only 4 differing lines, two of them the jet name in the statement, one a stray
  `mul_one` in a `simp only` set. Essentially the same proof.
- Value vs Second: 26 differing lines out of 25/17. `Second` is structurally different — no
  `topDegreeIndex` case split at all.

**No-go, and the reason is structural rather than incidental.** Each of these proofs works by
`unfold`ing its own `Limit`/`Remainder` definitions in order to *establish* the
entry-equals-recombined-quotient relation. A general lemma over an abstract jet would have to take
that relation as a hypothesis — its hypothesis would be its conclusion. Merging Value with First
alone would save ~25 lines at the cost of a lemma parameterised by three jet-specific constants
whose only role is to be unfolded. Left as three proofs.

**Positive residue.** The four families that *did* collapse never inspect the jet — they consume only
a stated property of it (`o(e^10)`, entrywise convergence, an entry quotient, a double sum). That is
the dividing line for this entire class: a jet-indexed family generalises exactly when its proof uses
a *property* of the jet rather than the jet's definition. That criterion is what should be applied to
the remaining B15 ThetaCusp families before attempting them.

### B15 — the dominant remaining pattern: jet-order-indexed families written one order at a time
Scanning declaration *names* for families that differ only by an order token
(`Value/First/Second/Third/Fourth/…`, `One/Two/Three/Four/…`) and counting families with ≥3 members
inside a single file gives the corpus's largest remaining duplication class. Ranked:

| decls | families | file |
|---|---|---|
| 43 | 12 (mostly ×4) | `RHTower/ThetaCuspFullReflectionFourthTuran` (1576 lines) |
| 39 | 13 (×3) | `HilbertMetric/DegreeFiveGaussianCurvature` — this is B14 |
| 23 | 7 | `RHTower/ThetaCuspShellIncompleteGammaCoordinate` |
| 15 | 5 (×3) | `HTGeometry/ErlangWignerSmithPacket` |
| 10 | 3 (×3–4) | `RHTower/ThetaCuspReflectionFourthTuran` |
| 10 | 3 (×3–4) | `RHTower/ThetaCuspLikelihoodGapCumulantRiccati` |
| 9 | 3 (×3) | `RHTower/ThetaCuspReflectedLikelihoodCumulantObstruction` |
| 7 | 2 | `HilbertMetric/FourthJetCoalescedCusp` |
| 6 | 1 (×6) | `HTGeometry/DifferentialLurothComponentTransfer` (`Primitive<T>BlockDifferentialCharacteristic`) |
| 6 each | 2 | `ThetaCuspGlobalReflectedRiccati`, `PrimeArchThetaGaussianApertureColdWatson`, `HedenmalmCenterMixedFourthJetCusp`, `HilbertMetric/CoherentCollisionJet` |

The ThetaCusp cluster alone spans eight files, all instances of the same shape: a jet
`thetaCusp…Jet<order>` with its derivative lemma, summability lemma and log/cumulant variant, spelled
out separately for orders 0–3. These are the natural continuation of B14 — the same
"index the order, prove once" move. Two entries in the scan are false positives and should be
ignored: `<T>tuallyNonnegative` (the token matcher hit "**Even**tually") and `Is<T>Cocycle` /
`IsLattice<T>d` in `OmegaObstruction`. A third, checked by inspection: the ×6
`Primitive<T>BlockDifferentialCharacteristic` entry in `DifferentialLurothComponentTransfer` is
**not** a family — it is one structure, `PrimitiveTwoBlockDifferentialCharacteristic`, with six
methods in its namespace; the matcher hit the "Two" inside the structure's own name.

**Yield estimate, checked rather than assumed.** Inspecting the largest entry
(`ThetaCuspFullReflectionFourthTuran`) shows the family is real —
`thetaCuspHigherLikelihoodJet<J> x = ∑' k, thetaCuspAtomLikelihoodRatioJet<J> (k+2) x`, with
`summable_…`, `…_pos` and `…_lt` repeated per order — but the shared skeletons are short (the
summability proof is essentially one `Summable.of_norm_bounded` call, differing only in the majorant
constant and lemma name). Abstracting over the atom jet,
`thetaCuspHigherLikelihoodOf (atom : ℕ → ℝ → ℝ) x := ∑' k, atom (k+2) x`, with each order supplying
its own majorant/positivity facts, is correct and worth doing, but the realistic reduction for that
file is ~150–250 lines, not the ~700 that `DegreeFiveGaussianCurvature` offers. B14 should go first.

### Architecture finding (pre-existing, not introduced here)
`formal/README.md` states that `HilbertMetric/` "must not depend on `HTGeometry` or `RHTower`".
One module breaks it: `HilbertMetric/FourthCurvatureMixture.lean` imports
`GaloisForLFunctions.HTGeometry.HalfLineSteinRobertson`. Confirmed pre-existing (the file is
unmodified in the working tree; the import came in with commit `bd26bc96`). Every other
HilbertMetric module is clean, so the area is one import away from satisfying its own contract —
either `HalfLineSteinRobertson`'s needed content moves down to a shared base, or the rule is
amended. Flagged rather than fixed: it is outside this card's scope and touches another area.

### B16 — the Erlang kernels are one family: `erlangKernel k` — statements settled
`HTGeometry/ErlangWignerSmithPacket.lean` defines three kernels separately:

  `erlangOneKernel ε s = exp(-s/ε)/ε`,  `erlangTwoKernel ε s = s·exp(-s/ε)/ε²`,
  `erlangThreeKernel ε s = s²·exp(-s/ε)/(2ε³)`

and re-proves nonnegativity, unit mass and the derivative law for each. These are the Erlang(k)
densities with mean `(k+1)ε`.

**The corpus already has the general shape** — no new definition is needed.
`HTGeometry/ErlangBoundedSource.lean` defines

```lean
def erlangPowKernel (ε : ℝ) (k : ℕ) (c s : ℝ) : ℝ := s ^ k * Real.exp (-s / ε) / c
```

together with the three bridge lemmas `erlang{One,Two,Three}Kernel_eq_powKernel`
(`erlangOneKernel ε = erlangPowKernel ε 0 ε`, etc.). What is missing is the general *laws* over it.
Two suffice, both verified on paper:

- **Ladder derivative, unconditional and uniform in `k`:**
  `HasDerivAt (erlangPowKernel ε k c) ((k : ℝ) * erlangPowKernel ε (k-1) c s - erlangPowKernel ε k c s / ε) s`.
  From `d/ds [s^k e^{-s/ε}/c] = (k·s^{k-1}e^{-s/ε} - s^k e^{-s/ε}/ε)/c`. The `k = 0` case needs no
  separate statement: the cast `(↑0 : ℝ) = 0` kills the first term, so the ℕ-subtraction `0 - 1 = 0`
  is harmless. This single law reproduces `hasDerivAt_erlangOneKernel`, `…Two…` and `…Three…`.
- **Unit mass:** `∫ s in Ioi 0, erlangPowKernel ε k (k ! * ε^(k+1)) s = 1`, since
  `∫₀^∞ s^k e^{-s/ε} ds = Γ(k+1)·ε^{k+1} = k!·ε^{k+1}`. Generalises
  `integral_Ioi_erlangThreeKernel_eq_one`.

Import direction needs one fix: `erlangPowKernel` currently sits *downstream* (`ErlangBoundedSource`
references `erlangOneKernel`, so it imports `ErlangWignerSmithPacket`). Moving the definition and the
two general laws up into `ErlangWignerSmithPacket` lets the three specific theorems become instances
there, with `ErlangBoundedSource` keeping its bridge lemmas unchanged. Self-contained in two files,
so this is the cheapest of the remaining generalisations to land.

### B17 — repeated hypothesis blocks (same-file families with ≥4 members)
Restricting the identical-*statement* pool to groups whose members all live in one file, with ≥4
members and ≥8 lines, leaves only 8 groups — but two are substantial:

- `HTGeometry/AnalyticNevanlinnaCarrierRelationFree.lean`, 4 theorems × ~79 lines
  (`allFinitePatterns_{abstractCarrier_fullRankWitness, positiveAbstractCarrier_fullRankWitness,
  abstractCarrier_relationFree, positiveActualCarrier_relationFree}_dense_residual`).
  **Checked:** these are *not* four copies of one theorem — the conclusions genuinely differ
  (`fullRank` vs `positiveChart`+`fullRank` vs `relationFree` vs `positiveChart`+`actualRelationFree`).
  What *is* duplicated is the identical 12-line hypothesis block (`hCmin`, `hnoCommon`, `hCp`, `hCc`,
  `hupperMap`, `zf`, `hqf_inj`, `hupperf`, `nf`, `eta`, `heta`) repeated verbatim four times, plus the
  three shared `let` bindings. A `variable` block is the behaviour-preserving fix (~36 lines) and
  makes the four-way parallelism explicit.

  **Shared proof core located (verified by diffing the bodies).** Only two of the four are
  independent: the `positiveAbstractCarrier` and `positiveActualCarrier` variants already delegate
  (`have habstract := F.allFinitePatterns_…_dense_residual` at lines 434 and 569), so they are
  already thin. The two that are not are `abstractCarrier_fullRankWitness` (lines 344–377) and
  `abstractCarrier_relationFree` (lines 475–516): both build the same `goodPattern` family, prove
  the same `hgoodPattern : ∀ p, Dense (goodPattern p) ∧ goodPattern p ∈ residual S`, and derive the
  same `(⋂ p, goodPattern p) ∈ residual S` by `countable_iInter_mem` — ~34 lines verbatim. They
  diverge only afterwards: one rewrites the intersection to the `fullRank` set (`heq`), the other
  pushes it through `actualNevanlinnaExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness`
  to land in `relationFree` (`hsubset`).

  Fix: promote `goodPattern` to a top-level `def` and extract
  `iInter_goodPattern_mem_residual : (⋂ p, goodPattern …) ∈ residual S` as its own theorem — the
  Baire-generic full-rank statement, which is the file's actual mathematical content and is
  currently unnamed. Each of the two theorems then costs ~10 lines instead of ~79.
- `RHTower/PrimeArchThetaGaussianApertureHeightLocalizedContraction.lean`, 5 theorems × ~44 lines —
  **inspected and dismissed.** The grouping is an artefact of the normaliser: the five share only the
  two-binder prefix `{lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ)` and a `let s := …`. Their
  conclusions and proofs concern genuinely different quantities (leading-channel damped moment,
  higher-atom half moment, tail-channel moment, first-atom half moment). The only available saving is
  a `variable` block for the shared binders, ~10 lines. Not a duplication target.

The other six groups are ≤23 lines each and are definition families rather than theorem duplication.

### B18 — the `upperEnd` differential-instance preamble, copy-pasted into 36 files (~912 lines)
Found by a **fragment-level** scan (`frag_scan.py`: hash every window of N consecutive indented,
non-comment lines, report windows repeated across ≥2 files). This class is invisible to the
declaration-level scanner because the repeated text is a run of `local instance` declarations, not
theorems — `scan2.py` only spans `theorem`/`lemma`.

Measured on the current tree:

| shape | files | lines each | total |
|---|---|---|---|
| A (dominant) | **26** | 27–31 | ~730 |
| B (prefix of A) | 5 | 16–20 | ~90 |
| one-offs | 5 | 14–27 | ~92 |
| | **36** | | **912** |

Shape A is byte-identical across all 26 files once the per-file instance *names* are stripped:

```lean
local instance …UpperEndComplexAlgebra : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
local instance …UpperEndCharZero : CharZero upperEndMeroField := charZero_of_injective_ringHom upperEndComplexToMero.injective
local instance …UpperEndDifferential : Differential upperEndMeroField := upperEndMeroFieldDifferential
local instance …CoordinateDifferential : Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed
local instance …CoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField); rfl
…
```

**Design — `scoped instance`, not global.** These are `local` on purpose: `Algebra ℂ _`,
`CharZero`, `Differential` and `DifferentialAlgebra` are data-carrying classes, so promoting them to
plain global instances would change elaboration in every downstream module and risks a competing
`Algebra ℂ …` path. The safe move with the same payoff is a `scoped instance` bundle in one base
module (the one defining `upperEndMeroField` / `upperEndRationalCoordinateField`), so each of the 26
files replaces its ~28-line preamble with a single `open scoped …` line and files that do not opt in
see no change at all. Net ≈ −700 lines, and the instance stack acquires one place to change instead
of 36.

**Open checks now resolved.** Classifying every file by the *sequence of instance types* it provides
(names stripped) gives:

| files | instances | relation to A |
|---|---|---|
| 26 | 8 | shape **A** |
| 5 | 6 | **exact prefix of A** (A minus the two valuation-layer instances) |
| 3 | 9 | superset: adds `Differential ℂ`, `DifferentialAlgebra ℂ upperEndMeroField`, `IsScalarTower ℂ upperEndRationalCoordinateField upperEndMeroField` |
| 1 | 7 | superset: adds `IsScalarTower ℂ …` |
| 1 | 5 | subset: A minus `CharZero` and the valuation-layer pair |

**Convention check before executing.** `scoped instance` is *not* used anywhere in this corpus today
(zero occurrences), so B18/B19 would introduce the pattern — standard mathlib practice, but a new
convention here and worth calling out rather than slipping in. Scoped *namespaces* are already
heavily used (`open scoped BigOperators` ×1098, `open scoped Differential` ×334, …), and note that
the name `Differential` is already taken as a scope, so the new bundle needs a distinct name such as
`UpperEndDifferentialInstances`.

Shape A provides, in order: `IsDomain upperEndAnalyticSubring`, `Algebra ℂ upperEndMeroField`,
`CharZero upperEndMeroField`, `Differential upperEndMeroField`,
`Differential upperEndRationalCoordinateField`,
`DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField`,
`Differential analyticScalarValuationLayerDifferentialField`,
`DifferentialAlgebra analyticScalarValuationLayerDifferentialField upperEndMeroField`.

**No file conflicts with A** — every shape is a subset or a superset, and the bodies agree wherever
the types agree. So one scoped bundle for A plus a small companion bundle for the ℂ-tower extras
(`Differential ℂ`, `DifferentialAlgebra ℂ _`, `IsScalarTower ℂ _ _`, needed by 4 files) covers all
36; each preamble becomes one or two `open scoped` lines. The one genuine behaviour change to verify
at build time rather than assume: the prefix/subset files (6 of them) would gain canonical instances
they do not currently have in scope. Additive and canonical, but it must be built, not argued.

### B19–B23 — the rest of the fragment-level layer (72 cross-file clusters, ≥3 files each)
Re-running `frag_scan.py` with the B18 `upperEnd` text excluded leaves **72 distinct cross-file
fragment clusters** spanning ≥3 files. This whole layer is invisible to the declaration-level
scanner: the repeated text is instance preambles and in-proof `let`/`have` boilerplate, not whole
theorems. Ranked by breadth:

- **B19 — the `analyticSubring Set.univ` / `meroField Set.univ` instance preamble.** The same disease
  as B18 on a different object, in at least four shapes (14 + 9 + 6 + 6 files) built from
  `IsDomain (analyticSubring Set.univ) := Bottcher.isDomain_analyticSubring …`, plus per-shape
  `Algebra ℂ`/`Algebra ℤ`/`Differential (meroField Set.univ)` instances. Same `scoped instance`
  remedy; ≈35 files affected.
- **B20 — the Xi functional-equation quartet.** Seven files
  (`XiOrder{Fourteen,Fifteen,Sixteen,Seventeen,Eighteen}CornerSourceExclusion`,
  `XiCenteredOrderFourteenSourcePositivity`, `XiCenteredOrdersFifteenSixteenSourcePositivity`) open
  with the identical block `let qJ := xiZeroCopyLineConjEquiv q; let qC := xiZeroCopyConjEquiv q;
  let qCJ := xiZeroCopyLineConjEquiv qC; let s : Finset XiZeroCopy := {q, qJ, qC, qCJ}` followed by
  the same six pairwise-distinctness `have`s (`hqCJ`, `hqJqC`, …).

  **Corpus check (rule 5): the six distinctness lemmas already exist**, in
  `RHTower/XiEndpointOffLineQuartetHeightGap.lean` (`xiZeroCopy_ne_lineConj_of_re_ne_half`,
  `xiZeroCopy_ne_conj`, `xiZeroCopy_ne_lineConjConj`, `xiZeroCopy_lineConj_ne_conj`,
  `xiZeroCopy_lineConj_ne_lineConjConj`, `xiZeroCopy_conj_ne_lineConjConj_of_re_ne_half`). What is
  missing is the theorem they exist to support. Reading a consumer end to end shows each of the seven
  files repeats the *same five-step argument*, ~30 lines: build the quartet `Finset`, discharge the
  six distinctness facts, produce summability, apply `Summable.sum_le_tsum` over the quartet, and
  prove the weight is constant on the orbit (`hJ`, `hCq`, `hCJ`).

  **The general law that subsumes all of it** — this is where the factor 4 in these files comes from:

  > For `f : XiZeroCopy → ℝ` nonnegative, summable and invariant under both
  > `xiZeroCopyLineConjEquiv` and `xiZeroCopyConjEquiv`, and `q` off the critical line,
  > `4 * f q ≤ ∑' r, f r`.

  ```lean
  theorem four_mul_le_tsum_of_quartet_invariant
      {f : XiZeroCopy → ℝ} (hnonneg : ∀ r, 0 ≤ f r) (hsum : Summable f)
      (hJ : ∀ r, f (xiZeroCopyLineConjEquiv r) = f r)
      (hC : ∀ r, f (xiZeroCopyConjEquiv r) = f r)
      {q : XiZeroCopy} (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
      4 * f q ≤ ∑' r, f r
  ```

  The off-line hypothesis is exactly the one the existing lemmas already take,
  `hoff : (q.1 : ℂ).re ≠ 1 / 2` — no new notion of "off-line" is needed.

  **Eighth instance, and the right home.** `XiEndpointOffLineQuartetHeightGap` itself already
  contains `four_mul_xiEndpointCrossCharge_le_curvature_of_offLine`, which is this same argument
  specialised to the single weight `xiEndpointCrossCharge`. So the law covers *eight* sites, and its
  natural home is that file — beside the distinctness lemmas and the first instance. All seven
  consumers already import it (they call its lemmas), so **no new import edge is required**. This is
  the cleanest item in the queue: one new theorem, eight one-line replacements, zero structural
  change.

  Each of the seven files then instantiates at its own weight (fourth reciprocal trace atom, source
  positivity atom, …) in one line. This is the strongest generalisation in the fragment layer: it
  replaces ~210 lines of boilerplate with a named, reusable, unconditional theorem that states the
  actual content — the functional-equation orbit of an off-line zero has four distinct elements, so
  any invariant nonnegative summable weight carries at least four times its value there.
- **B21 — sector positivity of `((A : ℂ) - B*I)⁻¹ ^ n`.** Six `XiOrder*EdgeCorner` /
  `XiCenteredOrders*` files repeat the same block for `mu := ((A : ℂ) - B*I)⁻¹`: `hden : 0 < A^2+B^2`,
  `hmure : mu.re = A/(A^2+B^2)`, `hmuim : mu.im = B/(A^2+B^2)`, `hmurepos`, and
  `htan : Real.tan (arg mu) = B / A`.

  **But the duplication is a symptom.** Reading what the block *supports* shows the six files prove
  `orderNReciprocalPower_re_pos_of_sectorRatio : 0 < ((((A : ℂ) - B*I)⁻¹) ^ N).re` separately for
  `N = 14, 15, 16, 17, 18`, each under its own algebraic sector hypothesis (e.g. `100 * B^2 < A^2`
  for `N = 15`). That is one theorem written five times at different `N`. The general law is

  **Better factorisation, found by reading the existing proof rather than guessing.** My first
  design put `Real.arctan` in the hypothesis. The corpus proof does not use `arctan` at all: it
  bounds the argument by its own tangent via `Real.lt_tan`, getting
  `|arg mu| < tan |arg mu| = |B/A|`, then `|n · arg mu| < π/2`, then
  `cos (n · arg mu) > 0`, then `(mu^n).re = ‖mu‖^n · cos (n · arg mu) > 0`. That splits cleanly into
  two lemmas, one of which is not about the Xi setting at all:

  ```lean
  -- general complex analysis; belongs in HTGeometry
  theorem re_pow_pos_of_abs_arg_lt {z : ℂ} (hz : z ≠ 0) {n : ℕ}
      (h : |(n : ℝ) * Complex.arg z| < Real.pi / 2) : 0 < (z ^ n).re

  -- the sector estimate for this particular family
  theorem abs_arg_inv_sub_mul_I_lt {A B : ℝ} (hA : 0 < A) :
      |Complex.arg ((A : ℂ) - B * I)⁻¹| < |B / A|
  ```

  Each `orderNReciprocalPower_re_pos_of_sectorRatio` is then the composite plus its own arithmetic
  (`100 B^2 < A^2 ⟹ |B/A| < 1/10 ⟹ 15 · |B/A| < 3/2 < π/2`).

  **Corpus check (rule 5) — this is a capability gap, not just duplication.**
  `HTGeometry/SectorPowerPositivity.lean` already exists for exactly this purpose, but takes a
  deliberately *trigonometry-free* route: it iterates the tangent addition law `(c+d)/(1-cd)` and its
  headline result `re_pow_pos_of_abs_im_le_fifth` is hard-capped at `m ≤ 7` — its own docstring says
  "for `c = 1/5` the rounded budgets are `1/5, 1/2, 4/5, 5/4, 2, 4, 21`, and the seventh power is the
  last one the budget covers". The `XiOrder*EdgeCorner` files need `n = 14…18`, which that module
  cannot reach, so they re-derived the whole thing with trigonometry instead.

  So the fix is to *extend the existing module*, not to add a competing one: put
  `re_pow_pos_of_abs_arg_lt` there together with the tangent-budget corollary in the module's own
  idiom,

  ```lean
  theorem re_pow_pos_of_abs_im_le_mul {z : ℂ} {c : ℝ} (hz : 0 < z.re) (hc : 0 ≤ c)
      (him : |z.im| ≤ c * z.re) {n : ℕ} (hn : (n : ℝ) * c < Real.pi / 2) :
      0 < (z ^ n).re
  ```

  (from `|tan (arg z)| ≤ c ⟹ |arg z| ≤ arctan c ≤ c ⟹ n·|arg z| < π/2`).

  **This strictly generalises `re_pow_pos_of_abs_im_le_fifth` and explains its cap.** At `c = 1/5`
  the hypothesis `n/5 < π/2` holds exactly for `n ≤ 7`, since `π/2 · 5 ≈ 7.85` — so the module's
  hard-coded budget list and its mysterious cutoff at the seventh power are both consequences of the
  single inequality `n · c < π/2`. Removing the cap is what lets the five order-14…18 files collapse
  into instances.
- **B22 — the balanced-jet-group preamble**, six HTGeometry resonance files
  (`DATaylorLogRatioResonance`, `PolynomialPowerADEResonance`, `HierarchicalResonanceBreaking`,
  `RapidConvexCurvatureResonance`, `RoughSubleadingPolynomialMagnitudeHypertranscendence`,
  `StretchedExponentialIntegerDominance`). Larger than the 14-line detection window suggested: the
  shared run is ~20+ lines (`dsimp [Z]`, `change magnitudeMaxXDegree Q < N`, `omega`, the
  `obtain ⟨hνw, hww, _hgroup⟩ := … hbalanced q hqbal`, `let P`, `hsUpper`, `hNupper`, …) and it also
  repeats *twice inside* `PolynomialPowerADEResonance` alone (lines 133 and 496).
  Only one piece is cleanly separable without more study — the arithmetic core
  `∑ i : Fin (jetMonomialDegree n anchor), s i ≤ jetMonomialDegree n anchor * (q + Boff)`, which
  follows from `Finset.sum_le_sum` and `offset_le_magnitudeOffsetMax`. The rest of the block is
  entangled with the surrounding `let`s and needs a proper interface before it can be lifted; not yet
  designed.
- **B23 — resolvent summability transfer under line conjugation**, seven files
  (`PrimeArch{Endpoint,HighFrequency,OffLineQuartet,ExactOffLineQuartet}Accretivity`,
  `Hedenmalm*Hankel*`): `have hsum := summable_xiRelativeResolventTerm hXi` followed by the same
  `xiZeroCopyLineConjEquiv.summable_iff` transfer.

Method note: this class only surfaced because the detector hashes *windows of consecutive lines*
rather than declarations. Any future audit of this corpus should run both.

### B10 — the 1136 identical-*statement* groups — not started
Lowest-yield pool; most matches are unrelated lemmas that share a binder prefix. Needs a stronger
normaliser (alpha-normalised full statements) before it is worth acting on.

## Re-census after B1–B6 (2026-07-26)

| Metric | before | after |
|---|---|---|
| identical statement **and** proof (exact clones) | 128 groups / 2063 lines | 70 groups / 889 lines |
| identical proof groups | 381 / 4926 | 330 / 3791 |
| identical statement groups | 1136 / 14234 | 1071 / 12690 |

### B8 — no-common-upstream groups: host-move sweep — EDITED
`common_ancestor.py` computes, for each remaining group, the maximal element of the intersection of
the members' import closures: 68 of 73 groups already have a shared ancestor module that can host
the lemma, so no new bottom module is needed. `clone_move.py` lifts the declaration into the host
(carrying the donor's `open`s), deletes every copy and rewrites references corpus-wide. 15 groups
moved this pass (−~490 lines). Held back:
- `ratFuncAlgHom_ext_X` — `HTGeometry.RatFuncAffineNormalForm` carries a third copy and cannot reach
  any candidate host, so a corpus-wide rename would be unsound. Needs a fresh bottom module.
- `norm_add_sq_complex` (HardyCarrier / RouteBSublevel) — the two closures intersect in nothing;
  also needs a fresh bottom module.
Post-move fixes: `exists_coprime_monic_repr` needed the donor's
`variable {C K : Type*} [Field C] [Field K] [Algebra C K] {S : IntermediateField C K}` carried over;
`div_le_div_of_le_of_pos` was already present in its host from the B6 pass and the appended copy was
removed.

## Log
- 2026-07-26 — created; census complete.
- 2026-07-26 — B1/B2/B3 edited (−690 lines); `HTGeometry/PerronKernelBound.lean` and
  `HTGeometry/GammaAnalyticOffPoles.lean` added to the area umbrella and compile standalone;
  full dependency-cone build pending.
- 2026-07-26 — B4 correspondence verified name-by-name; blast radius measured (13 files).
- 2026-07-26 — B4 landed: `abbrev SpectralFamily := HTGeometry.AbstractSpectralFamily XiZeroCopy`;
  the nine-module Xi chain reduced to import shims; `norm_traceC_le_of_im_eq_zero`, `cut`/`mem_cut`/
  `cut_inv`/`finite_cut_shell` and `im_eq_zero_of_subexponential` generalised *into* the abstract
  layer; `Nonempty XiZeroCopy` promoted to a global instance (10 `letI` sites removed);
  `SpectralFamily.toAbstract` retired as unnecessary.
- 2026-07-26 — B6 landed: 50 clone groups collapsed corpus-wide; second pass after re-census landed
  6 more. B8 host-move sweep landed 15 groups.
- 2026-07-26 — per-file `lake env lean` checks green for `AbstractSpectral{Family,Graded}` and for
  the hosts `ShiftMinpolyTranscendence` (after carrying the donor `variable` line),
  `DifferentialIndependence`, `FiniteDifferentialCircuitBoundary`, `CentralReciprocalMoments`,
  `DegreeZeroOffline`, `GaussLattice`, `ConstrainedProlateInfiniteSecular` (after removing a
  duplicate append), `EulerFisherCurvature`, `CompletedFluxPrimeArchDecomposition`,
  `SoninSemilocalJacobiTransform`, `MobiusGammaContactTransgression`. Final three-area
  `lake build` audit running.
- 2026-07-26 — first audit run reached 9545/9672 modules with **zero errors**, then was killed by an
  interrupt before completing. Restarted detached (`nohup`) so a mid-turn interrupt cannot take it
  down; lake's cache retains the already-built modules.
- 2026-07-26 — **process rule**: exactly one Lean invocation at a time, `lake env lean` scratch
  probes included. Violating it once cost the audit run above. While a build is in flight, only
  non-Lean work (source reading, grep/python scans, card updates).
- 2026-07-26 — backlog researched and ranked while the audit ran: B11 (both obstacles discharged),
  B12 (module written and checked), B13, B14 (design settled), B15, B16 (reuses the corpus's own
  `erlangPowKernel`), B17. Execution order: B16 → B12 wiring → B14 → B11 → B13/B8 → B15.
