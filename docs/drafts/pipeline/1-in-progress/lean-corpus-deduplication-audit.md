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

**The reduction is now machine-checked.** Three further bridges landed in `QuasiFreeFillingFano`,
each closing by `simp` alone:

```lean
quasiFreeSpectralSecantDefect    v energy (fun _ => 1) lower upper = slaterSpectralSecantDefect    v energy lower upper
quasiFreeSpectralCenteringDefect v energy (fun _ => 1) lower upper = slaterSpectralCenteringDefect v energy lower upper
quasiFreeSpectralCoherenceDefect v energy (fun _ => 1)             = slaterSpectralCoherenceDefect v energy
```

and with them `slaterSpectralFanoMargin_three_defect_of_quasiFree` derives the Slater three-defect
identity entirely from `quasiFreeSpectralFanoMargin_three_defect` at `occupation ≡ 1` plus
`endpointBudget_eq`. **So "the Slater development carries no content beyond the occupation-weighted
one" is a Lean fact, not a card note.** (Placement matters: the derivation must sit *after* the
`_one` bridges in the file.)

**Remaining is bookkeeping only.** `SlaterPluckerConnector` — the sole external consumer — reaches
`QuasiFreeFillingFano`, so the ~9 Slater theorems can be deleted from `SpectralBandwidthFano` and
re-stated there as instances. Leaf analysis (uses inside `SpectralBandwidthFano` / external):
`negative_forces_bandwidth` 0/0, `lower_bound_of_width_le_one` 0/0, `eq_lower_bound_iff` 0/connector,
`positiveQuarticDegree_…` 0/connector are movable immediately; `three_defect` (2 internal uses),
`lower_bound` (1), `nonnegative_of_bandwidth` (2), `quartic_…` (1), `lower_endpoint_defect` (1) must
move with their dependents. Estimated ~40–150 lines, no mathematical risk — deferred because the
proofs being replaced are already short and the payoff is bookkeeping.

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

## B11 closed — Slater/quasi-free layer, measured outcome

**Kept (general law, new):** `slaterSpectralFanoMargin_split` in `SpectralBandwidthFano.lean`.
Any pointwise identity `m - q + m^2 = base + ((l+u)m - l·u - q) + rest m` splits the Slater Fano
margin into `card ι · base + secant + (∑ rest ∘ mean) + coherence`. The balancing decomposition
(`three_defect`) and the lower-endpoint decomposition (`lower_endpoint_defect`) were two ~39-line
calc proofs sharing an 8-line `hmargin` block and differing only in one summand; both are now
3-line instantiations with `hrest` closing by `ring`.

**Kept (general law family):** the eight `quasiFree…_one` specializations in
`QuasiFreeFillingFano.lean` (mean, compressedEnergy, variance, fanoMargin, secant, centering,
coherence, compression). These state precisely that the Slater notions are the quasi-free notions
at occupation ≡ 1. Each is 1-3 lines.

**Removed as net-negative:** the four `slaterSpectralFanoMargin_…_of_quasiFree` restatements and
`endpointBudget_eq`. Each re-derived a theorem that already exists upstream in
`SpectralBandwidthFano.lean` with a *shorter* direct proof. The reason is structural and worth
recording: the Slater floor is normalised per orbital as `card ι · (l - (u-l-1)^2/4)` while the
quasi-free floor is normalised by the product `l·u·(∑ occupation) - card ι·(l+u-1)^2/4`. Every
descent therefore pays `∑ 1 = card ι` plus the budget re-massaging, which costs more than the
direct three-defect + `linarith` proof. `_of_quasiFree` restatements: 16/19/21/33 lines against
3/8/14/14 for the direct forms.

**Criterion generalised from this:** a specialization bridge `X_of_Y` pays for itself only when the
specialized statement does *not* already exist upstream. When it does, the bridge is a second proof
of one statement, and the reusable content is the *definitional* `_one` family, not the
theorem-level restatements.

**Net for B11:** QuasiFreeFillingFano 696 -> 600, SpectralBandwidthFano 456 -> 435.
Audit: `lake build GaloisForLFunctions.HilbertMetric.SlaterPluckerConnector` -> 2513 jobs, success.

## B24 — within-file proof clones (new scanner class, highest yield so far)

The declaration-level and fragment-level scanners both miss *within-file* pairs of theorems whose
proofs share a long common structure. A scanner over same-file declaration pairs (longest common
prefix of normalised proof lines + set overlap, threshold `prefix ≥ 6` or `overlap ≥ 10` and
`≥ 75%` of the smaller proof) returns 1391 pairs across HTGeometry, HilbertMetric and RHTower.
Script: `within_file.py` in the job tmp dir.

Landed from the top of that list (each `lake env lean` clean on the first attempt):

| module | before | after | general law introduced |
|---|---|---|---|
| `HTGeometry/PolynomialPowerADEResonance` | 1827 | 1388 | none needed — the two exact-profile bend-pair theorems are the eventual-profile ones at `T = 0` |
| `RHTower/WindowBudget` | 1153 | 860 | `anchorMirrorDefect_reachable_signed` + `sqrt_two_div_two_le_sign_mul_sin`, `sign_mul_mirrorTiltIncrement_nonneg`, `sign_mul_mirrorTiltIncrement_ge` |
| `HTGeometry/SuperIncreasingSourceUnique` | 412 | 181 | none needed — `multiset_source_window_free` implies the other two (card equality bounds the target size; exact mass is a zero-width window) |
| `RHTower/ThetaCuspShellIncompleteGammaCoordinate` | 9996 | 9845 | `hasDerivAt_atom_phaseTransform` (dominated differentiation under `∫ a(x) e(x,z)` for any continuous nonnegative atom with integrable exponential tilts) |
| `HilbertMetric/SpectralBandwidthFano` | 456 | 435 | `slaterSpectralFanoMargin_split` |

Three shapes recur, and they are worth checking in this order on any new pair:

1. **Hypothesis-lattice**: the variants sit at different points of a lattice of hypotheses and one
   variant is the join. Then the others are corollaries and no new law is needed
   (ADE resonance, super-increasing uniqueness).
2. **Sign/phase parameter**: the proofs are one argument run at `σ = ±1` with a matching phase
   offset. Introduce `σ` with `hσ : σ = 1 ∨ σ = -1`, push the case split down into three small
   sign-normalised lemmas, and the 350-line body is shared (WindowBudget).
3. **Abstract the varying object**: the proofs differ only in one function and its analytic
   witnesses. Take the function plus those witnesses as hypotheses (ThetaCusp atom).

Audit: `lake build` of `PolynomialPowerADEResonance`, `PermanentCoefficientIdentity`, `WindowBudget`
(8706 jobs) and `ThetaCuspShellIncompleteGammaCoordinate` (8942 jobs) — both successful.
`scripts/formal_tools.py lint` reports no `sorry`/`axiom`/`opaque` and no finding against these
files; its two `unreachable from umbrella` errors are another agent's untracked modules
(`FieldOneMultiplicativeCore`, `ShiftStableLatticeStructure`), not touched here.

## B25 — the reciprocal tangent-sector family (8 files)

`HTGeometry/SectorPowerPositivity.lean` already had `re_pow_pos_of_abs_arg_lt` (any exponent, from
polar form).  Eight RHTower modules nevertheless re-derived, in full, the passage from a sector
ratio `c·B² < A²` to `Re ((A - B i)⁻¹ ^ m) > 0`: `Complex.inv_re`/`inv_im`, `Complex.tan_arg`,
the `|tan|arg||= |B/A|` case split on the sign of the argument, and `Real.lt_tan`.  About 60 lines
each, identical up to three numerals.

Two laws added to `SectorPowerPositivity.lean` (needs `Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds` for `Real.lt_tan`):

- `abs_arg_inv_sub_mul_I_lt : 0 < A → |B| < t * A → |arg ((A - B i)⁻¹)| < t`
- `re_inv_sub_mul_I_pow_pos : 0 < A → |B| < t * A → (m : ℝ) * t ≤ π/2 → 0 < ((A - B i)⁻¹ ^ m).re`

The `≤` in the angle budget is deliberate: `m = 0` is handled separately, and for `m ≥ 1` the
strictness comes from `|arg| < t`.  This matters — every call site is numerically tight
(e.g. order 20 uses `20 · 784/10000 = 1.568` against `π/2 = 1.5707…`).

| module | before | after | exponent, budget |
|---|---|---|---|
| `XiOrderFourteenEdgeCorner` | 224 | 171 | 15, `1/10` |
| `XiOrderFifteenEdgeCorner` | 223 | 170 | 16, `981/10000` |
| `XiOrderSixteenEdgeCorner` | 224 | 171 | 17, `923/10000` |
| `XiOrderSeventeenEdgeCorner` | 216 | 163 | 18, `872/10000` |
| `XiOrderEighteenEdgeCorner` | 216 | 163 | 19, `826/10000` |
| `XiCenteredOrdersNineteenTwentySourceBudgetBoundary` | 506 | 377 | 20 and 21 |
| `XiSquaredSeamPowerThirtyTwoAnnulus` | 297 | 233 | 32, `49/1000` |

Each call site is now the sector-ratio arithmetic (5 lines) plus one `norm_num`/`nlinarith
[Real.pi_gt_d20]` angle check.  Audit: `lake build` over all seven plus
`SectorPowerPositivity` — 9177 jobs, successful.

Note for the next pass: `SectorPowerMassLower`, `AnchorTilt` and
`PrimeArchScaledHausdorffDivisorValueRelation` also use `Real.lt_tan` but in a different argument
(no `htanabs` case split), so they are not instances of this family.

## B26 — hypothesis-lattice pairs (shape 1 of B24)

Each of these was two proofs of the same argument at two points of a hypothesis lattice; in every
case the stronger one already existed and the weaker is a two-to-eight line corollary.

| module | before | after | specialisation |
|---|---|---|---|
| `RHTower/RouteBChiDecay` | 588 | 519 | `..._left_line_sphere` is `..._of_K_bound` with `hKbound := le_of_eq hK.symm` |
| `RHTower/BourgainA6TaylorErrorAbsorption` | 473 | 405 | `..._of_lower` is `..._of_lower_of_radius_le` at `R := M²/12`, `le_rfl` |
| `RHTower/BourgainExactLocalMomentTransfer` | 508 | 475 | `..._application` is `..._application_of_lower` at `A := 1/2`, using `bourgainSquareRootPhaseOperatorBound (1/2) ≤ 6` (it is `11/2`), so `12N ≤ H²` implies the general `2·bound(A)·N ≤ H²` |
| `RHTower/BohrCoefficientUniqueness` | 687 | 556 | `conductor_datum_finite_support` is `conductor_datum_pairing` with every `if` in the else branch; `m^{−½} ≠ 0` finishes |

The Bohr case is the one to remember: the module docstring *already stated* "`conductor_datum_finite_support` is the special case where every divisibility fails", and the
two proofs had been written out separately anyway. **Docstrings that say "special case of" are a
free index into this class of duplication** — worth grepping for directly.

Trap hit once here: `conductor_datum_finite_support`'s block is not contiguous with its own proof
end — two `private theorem`s used by the *other* theorem sit between them. Cutting on the first
plausible tactic line silently deleted `diag_collapse_add`. Always anchor the end of a block on the
last line of *that* proof, and re-read the declaration list of the whole span before cutting.

Audit: `lake build` over the four modules plus `BourgainExactLocalTranslation` — 8630 jobs,
successful.

## B27 — SeamCongruence: one core, four readers

`SeamCongruence.lean` 2478 -> 2304.  Four window theorems were four copies of one argument:

- `window_online_of_line_real_sign_data` (generic carrier, strict sign interleaving)
- `window_online_of_line_real_zero_brackets` (generic carrier, disjoint non-strict brackets)
- `window_online_of_sign_data` (ξ)
- `window_simple_of_sign_data` (ξ, simplicity instead of on-line-ness)

Now:

- `window_online_of_line_real_zeros` — **the core**.  Takes `s` strictly increasing critical-line
  parameters in the ball at which the real trace vanishes, and concludes *both* the on-line
  identity/right-half vanishing *and* `∀ w ∈ t, m w ≤ 1`.  Strengthening the conclusion to a
  conjunction is what lets the simplicity reader share the argument; the extra tail is the
  tightness squeeze `s ≤ ∑_P m ≤ ∑_online m = ∑_t m ≤ s`.
- `exists_line_real_window_zeros` — the strict-interleaving construction, extracted so both the
  generic and the ξ reader use it once each.
- `xi_window_full_of_sign_data` (private) — discharges `hFcont`, `hline_zero`, and reflection
  symmetry of the multiplicities (`xi_orderAt_lineReflect`) once; the two public ξ theorems are
  its `.1` and `.2`.

**Shape 4, new**: when two theorems share a construction but state *different* conclusions, the
merge is to strengthen the shared core to a conjunction and project. Look for this whenever two
proofs share a long prefix and diverge only in the last block.

Two scripting traps, both cost a revert:
- A textual `z` -> `zs` rename hit `hz i` and `z j`. Never rename by substring in Lean source;
  either keep the original identifier or use a real word-boundary pattern.
- Anchoring the conclusion by `∑ z ∈ t.filter (fun z => 1 / 2 < z.re), m z = 0 := by` matched a
  *different* theorem, because the core's own conclusion had been written with `w`. Anchor on text
  that is unique to the target declaration, and assert the match index lies inside it.

Audit: `lake build GaloisForLFunctions.RHTower.SeamCongruence` — 8574 jobs, successful.

## B28 (staged, analysed not yet executed) — the mirrored `With` API

`HTGeometry/RationalIncrementHolderElimination.lean` (560 lines) is a declaration-for-declaration
mirror of the `Jet`/`Elimination` development in `HTGeometry/HolderShiftElimination.lean`
(831 lines), with every statement parametrized by an arbitrary increment family
`rj : ℕ → RatFunc ℂ` and the suffix `With`: `jetTranslateWith`, `transMonomialWith`,
`subTopMonomialWith`, `coeff_transMonomial_of_degSum_eqWith`, …, `no_shift_stable_annihilatorWith`
— 20 declarations against 20.

The two engines differ in **nine lines**: the translate used, four `…With rj` helper names, `polePart (k : ℕ)` vs `rj (k : ℕ)`, and `ratShift_sub_polePart_combination` vs the new hypothesis
`Hres`.  The specific development is exactly the general one at `rj := polePart`.

Direction is the only obstacle: `jetTranslateWith` lives *downstream* of `jetTranslate`.  The
low-risk resolution is **not** to move the general API upstream (namespace `RationalIncrementHolder`
is referenced by `RationalShiftHypertranscendence`) but to delete the specific development from
`HolderShiftElimination` and re-introduce those exact names, in their original namespaces, as
`rj := polePart` specializations inside `RationalIncrementHolderElimination`; then re-point the two
consumers (`DigammaHypertranscendental`, `GammaFactorialHarmonicSequenceFreeness`) to import the
downstream module, which already imports the upstream one.  Expected: about -500 lines.

Before executing, enumerate which of the 20 upstream `Jet` declarations are referenced outside
`HolderShiftElimination` — only those need specializations; the rest are deleted outright.

## B29 — cross-file body scan (new instrument) and the Landau-gate pairs

The within-file scanner of B24 cannot see duplication that spans modules. `xfile.py` (job tmp dir)
indexes every proof body by its rarest normalised lines and reports cross-file pairs with
`overlap ≥ 25` and `≥ 60%` of the smaller body: 5647 declarations with ≥25 distinct body lines,
and a long tail of genuine pairs.

Landed from it — both are the same shape (a *general* theorem taking the abscissa `beta` and the
base summability as parameters, and a *specialised* one that picks `beta := δ/4` and derives the
base from an energy hypothesis), and in both cases the general one sat **downstream** of the
specialised one, so the fix was to move the general theorem up and leave a six-line corollary:

| pair | before | after |
|---|---|---|
| `CCMSharpPrimeWindowExcessEnergyGate` + `CCMSharpPrimeWindowEnergySpectrum` | 970 + 329 | 988 + 165 |
| `CCMRectangularNegativePartEnergyGate` + `CCMRectangularNegativeChannelSpectrum` | 555 + 541 | 571 + 417 |

Placement matters and is not free: the moved block must land *after* every helper it uses in the
target module. `differentiableOn_xiRectangularNegativePartLandauContinuation_landauBall` sits at
line 107 of the gate, so inserting before line 80 failed. The plain gate theorem has **no**
docstring, and a backward scan for one walked ~90 lines up into a previous proof — check
`Lg[gt-1]` actually ends with `-/` before treating the preceding lines as a docstring.

Audit: `lake build` of both gates (8744 / 8722 jobs) and both spectra (8752 jobs), all successful.

## B30 — sibling generalisations found by the cross-file scan

**`GradedShiftInertness` 381 -> 147.**  `HTGeometry.GradedLead Λ D` and
`HTGeometry.Rel.GradedLeadOver C Λ D` are field-for-field the same structure with `C := ℂ`, and the
three theorems on them (`mul_ne_zero'`, `ord_eq_of_rel`, `lead_shift_identity`) were
character-identical up to `ℂ`/`C`.  The two modules were *independent* — neither imports the other —
so the fix is simply `abbrev GradedLead … := Rel.GradedLeadOver ℂ Λ D` plus three one-line
delegations, and `complex_eq_of_scaled_shift_eq := Rel.scalar_eq_of_scaled_shift_eq`.  Structure
projections, anonymous constructors and named-field construction all pass through an `abbrev`
unchanged, so the only consumer (`GradedDefectInertness`) needed no edit.

**`XiCTaylorThetaTailCoreCurrent{,Remainder}Equivalence` 219 + 342 -> 246 + 202.**  The remainder
module's `eventually_abs_… _lt_scaled_normSq_of_riemannHypothesis` is the two-sided (`|·|`) form of
the predicate `XiCTaylorThetaTailCoreCurrentSublinearUpper`, and its proof never used the
predicate's `0 < sigma.re`.  Moved upstream; the predicate version is now
`intro …; filter_upwards […] with n hn; exact lt_of_abs_lt hn`.

**Pattern worth stating.**  In four of the five cross-file collapses so far the *more general*
statement lived **downstream** of the specialised one, so the mechanical move is: relocate the
general theorem into the upstream module (after every helper it uses) and leave a corollary behind.
Check `reach(specialised, general)` and `reach(general, specialised)` first — where the two modules
are independent siblings (the `GradedLead` case) an `abbrev` is enough and nothing moves.

Audit so far in this batch: `lake build` of `GradedShiftInertness` (8482 jobs) and
`XiCTaylorThetaTailCoreCurrentEquivalence` (8776 jobs), plus `lake env lean` on both downstream
consumers — all clean.

## B31 — Perron horizontal mass, and the running total

**`PerronCarrierFlankMass` + `PerronStripMassDischarge` 883 + 199 -> 912 + 87.**  The escape
theorem and the integrability lemma built the same kernel envelope `K`, the same contour-norm
function `u`, the same continuity, the same high-`T` domination and the same `Ioc ∪ Ioi` split —
about 95 lines — and then diverged.  `perronHorizontalContourNorm_integrableOn_Ioi` (downstream)
moved up; the escape proof now keeps only `u`, the four continuity `have`s it still needs
downstream, and one call.

### Session total for the within/cross-file body-clone programme (B24–B31)

28 files, **+1032 / -3718 = -2686 lines**, no `sorry`, no `axiom`, nothing weakened.
Every statement that existed before still exists with the same name, namespace and signature.

Named general results introduced:

| law | home |
|---|---|
| `slaterSpectralFanoMargin_split` | `HilbertMetric/SpectralBandwidthFano` |
| `anchorMirrorDefect_reachable_signed`, `sqrt_two_div_two_le_sign_mul_sin`, `sign_mul_mirrorTiltIncrement_nonneg`, `sign_mul_mirrorTiltIncrement_ge` | `RHTower/WindowBudget` |
| `hasDerivAt_atom_phaseTransform` | `RHTower/ThetaCuspShellIncompleteGammaCoordinate` |
| `abs_arg_inv_sub_mul_I_lt`, `re_inv_sub_mul_I_pow_pos` | `HTGeometry/SectorPowerPositivity` |
| `window_online_of_line_real_zeros`, `exists_line_real_window_zeros` | `RHTower/SeamCongruence` |

### The four shapes, in the order worth testing them

1. **Hypothesis lattice** — one variant is the join; the others are corollaries. No new law needed.
   Cheapest to check: compare the binder lists first, not the proofs.
2. **Sign / phase parameter** — one argument run at `σ = ±1`. Introduce `σ` with
   `hσ : σ = 1 ∨ σ = -1` and push the case split into small sign-normalised lemmas.
3. **Abstract the varying object** — the proofs differ in one function plus its analytic witnesses;
   take both as hypotheses.
4. **Shared construction, different conclusions** — strengthen the core to a conjunction and
   project.

### Deferred with reasons

- **B28**, the mirrored `With` API (`HolderShiftElimination` vs `RationalIncrementHolderElimination`,
  ~500 lines): analysed above, ready to execute.
- `PolynomialPowerADEResonance`'s two *eventual-profile* theorems (343/214 bodies, 161 shared) are
  **not** a clean merge: the shared lines are scattered `let`-bindings and the degree-one proof has
  242 lines with no counterpart. Unifying them means abstracting the confinement mechanism
  (convex confinement vs coefficient grading) into a hypothesis — a real restructuring, not a
  factorisation. Left alone deliberately.
- `PrimeArchExactOffLineQuartetKMSMaster`'s pair is a **false positive** of the first scanner: the
  specialised theorem was already a three-line instantiation, and the "overlap" was its long
  *statement*. This is why the second scanner compares only lines after `:= by`.

## B28 executed — the mirrored `With` API is gone

`HolderShiftElimination.lean` 831 -> 904; `RationalIncrementHolderElimination.lean` 560 -> deleted.
**Net -487 lines**, and one fewer module.

The decisive observation is that `jetTranslate` and `jetTranslateWith polePart` are not merely
equal but **definitionally identical** — both are
`((mvPolynomialBaseTranslation (fun j => ‹increment› (j : ℕ))).toAlgHom.toRingHom).comp (MvPolynomial.map ratShift)` —
so every specialisation is a term-mode application with no rewriting, and `Hshift` transports
across `jetTranslate m` vs `jetTranslateWith polePart m` by `rfl`.

What was done, against the plan recorded in B28:

- The whole arbitrary-increment development (21 declarations) moved verbatim into
  `HolderShiftElimination.lean`, keeping `namespace RationalIncrementHolder`, so the one external
  reference (`RationalShiftHypertranscendence`) needed no rename — only its import changed.
- The specific development shrank from 20 declarations to the **8** that are actually referenced
  outside the module (`jetTranslate`, `jetTranslate_C`, `jetTranslate_X`, `transMonomial`,
  `jetTranslate_monomial`, `totalDegree_jetTranslate_le`, `coeff_jetTranslate_of_le_degSum`,
  `no_shift_stable_annihilator`), each now a one-line `polePart` specialisation. The other 12 were
  internal scaffolding for the deleted proofs and are gone.
- `no_shift_stable_annihilator` is `no_shift_stable_annihilatorWith polePart …` with the residue
  hypothesis discharged by `ratShift_sub_polePart_combination` — exactly the nine-line difference
  the earlier analysis predicted.
- The deleted module's docstring (what the increment parameter buys) folded into the
  `## The arbitrary-increment jet substitution` section comment.
- Umbrella import dropped; `scripts/formal_tools.py index` regenerated (`LEAN_API.md`,
  `LEAN_GAPS.md`, `LEAN_OVERVIEW.md`) so no index entry points at the removed file.

Trap: `section Jet` had to be re-closed. Splicing a block that *starts* with `end Jet` and then
opens a fresh `section Jet` leaves the new section unterminated, and Lean reports it only at the
file's final `end GaloisForLFunctions` — read that error as "an inner scope is still open", not as
a problem with the last line.

Audit: `lake build` of `HolderShiftElimination` (8477 jobs) and of all five consumers
(`RationalShiftHypertranscendence`, `DigammaHypertranscendental`, `GammaShiftEigenrelation`,
`GammaFactorialHarmonicSequenceFreeness`, `GammaHypertranscendental`, 8487 jobs) — successful.

## B32 — the ThetaTail signed/unsigned mirror (3 modules removed)

Five `XiCTaylorThetaTail*` modules carried an `abs` mirror of an `0 ≤ a` development: every
statement identical except that `a` is replaced by `|a|` and the hypothesis `ha : 0 ≤ a` is
dropped.  The `abs` form is therefore the *general* one, and each unsigned theorem is
`rwa [abs_of_nonneg ha]` away from it — nine such pairs in total.

| module | before | after |
|---|---|---|
| `XiCTaylorThetaTailFiniteTranslationBounds` | 1495 | 1586 |
| `XiCTaylorThetaTailSignedFiniteTranslationEdge` | 265 | **deleted** |
| `XiCTaylorThetaTailSignedFiniteTranslationIntegrated` | 203 | **deleted** |
| `XiCTaylorThetaTailUniformFiniteTranslationDefectCurrent` | 416 | 470 |
| `XiCTaylorThetaTailSignedFiniteTranslationDefectCurrent` | 305 | **deleted** |

Net **-628 lines** and three fewer modules.  Import repairs: two lines out of `RHTower.lean`,
`…SignedFiniteTranslationPacket` re-pointed at `…FiniteTranslationBounds`,
`…SignedFiniteTranslationDefectSup` at `…UniformFiniteTranslationDefectCurrent`, and
`…UniformFiniteTranslationDefectCurrent` gained an import of `…SignedFiniteTranslationPacket`
(checked acyclic first: neither module reached the other).

**Shape 5, and the most mechanical one yet: `|·|` versus a sign hypothesis.**  Whenever a module
name carries `Signed`/`Abs` and a sibling does not, expect the whole development to be mirrored.
The general form is always the `abs` one; the specialised proofs are one `rwa [abs_of_nonneg h]`
each, and the mirror module usually disappears entirely.  Grep for module-name pairs differing by
`Signed`/`Abs`/`Uniform` before reading any proofs.

Audit: `lake build` of `…FiniteTranslationBounds` (8779), `…SignedFiniteTranslationPacket` (8791),
`…UniformFiniteTranslationDefectCurrent` (8792) and `…SignedFiniteTranslationDefectSup` (8793) —
all successful.  `scripts/formal_tools.py index` regenerated after the deletions.

## B33 — module-name mirrors as a search key, and `ShiftJetTower`

B32's shape suggested a cheap corpus-wide index: **module names that differ by a qualifier**.
Stripping `Signed`, `Abs`, `Uniform`, `Exact`, `Relative`, `Rel` from every module basename and
looking for the stripped name yields 14 pairs. Not all are real (the base
`XiCTaylorThetaTailFiniteTranslationDefectCurrent` genuinely holds different content from its
`Uniform` sibling; `Bottcher/RelativeMinimalRelation` has nothing to do with
`RHTower/BakerProof/MinimalRelation`), but the true ones are found in seconds instead of by
reading proofs.

**`ShiftJetTower` 206 -> 120.**  All thirteen declarations — `jetTower`, `jetTower_zero`,
`mem_jetTower_succ_iff`, `le_jetTower_succ`, `jet_mem_jetTower_succ`, `base_le_jetTower`,
`adjoin_stable_of_gen`, `defectSpan`, `defectSpan_zero`, `defectSpan_succ`, `defectSpanAll`,
`mem_defectSpanAll`, `defectSpanAll_le_of_mem`, `jetTower_induction`, `jetTower_transcendental` —
are `HTGeometry.Rel`'s at `C := ℂ`, character for character. The modules were independent siblings
(neither imported the other), so `ShiftJetTower` now imports `RelativeShiftJetTower` and every
declaration delegates.

Two details that made it safe:

- `jetTower` stayed a plain `noncomputable def` rather than an `abbrev`. `jetTower_zero` and
  `mem_jetTower_succ_iff` are still `rfl`/`Iff.rfl` through the delegation because
  `Rel.jetTower F y 0 = F` is definitional. An `abbrev` would have been reducible and changed how
  consumers' `simp` sets behave.
- Checked first that no consumer unfolds the definitions: the only `simp [defectSpan]` in the
  corpus was inside the module being rewritten. Seven consumers
  (`DirichletDefectInertness`, `JetTowerFreeness`, `OrbitIsolatedPoleLaw`, `UpperEndDigammaShift`,
  `DigammaOverDirichletBase`, `ShiftRationalBase`, `UpperEndDirichletCoordinate`) all compile
  untouched.

Audit: `lake build GaloisForLFunctions.HTGeometry.ShiftJetTower` — 8480 jobs, successful; the seven
consumers verified individually with `lake env lean`.

**Remaining name-mirror candidates for the next pass** (unexamined):
`SignedReflectionParity` (445) vs `ReflectionParity` (165); `IndexWiringRelative` (321) vs
`IndexWiring` (262); `RouteBFourPhaseUniform` (332) vs `RouteBFourPhase` (97);
`JacobiThetaExactDivisor` (330) vs `JacobiThetaDivisor` (180);
`PrimeArchExactOffLineQuartetAccretivity` (365) vs `PrimeArchOffLineQuartetAccretivity` (442);
`UniformPrimePowerTailPacket` (184) vs `PrimePowerTailPacket` (187);
`RelativeNaturalBoundary` (147) vs `NaturalBoundary` (57);
`SignedGammaHypertranscendental` (57) vs `GammaHypertranscendental` (441);
`ContinuumAnalyticEulerTailExactFaithfulnessUniversalityLaw` (55) vs its non-`Exact` sibling (183).

## B34 — two more name-mirror collapses

**`ReflectionParity` 165 -> 188, `SignedReflectionParity` 445 -> 347 (net -75).**
`neg_one_pow_orderAt_of_signed_reflection` (`f(2c − s) = ε·f(s)` with `ε = ±1`, concluding
`(−1)^{ord} = ε`) is the general law; `analyticOrderAt_even_of_reflection` is its `ε = 1` case and
`analyticOrderAt_odd_of_antireflection` — which the signed module *already* derived in five lines —
its `ε = −1` case. The even case had simply been proved out separately upstream. Both signed laws
(plain and germ form) moved into `ReflectionParity`; the two even-parity theorems are now the same
five-line `rcases Nat.even_or_odd … / Odd.neg_one_pow` idiom the odd ones already used.

**`PrimeArchExactOffLineQuartetAccretivity` 365 -> 172 (-193).**  The two band predicates are
**character-for-character the same definition**:

```
XiEndpointOffLineQuartetAccretiveBand R  :=  0 ≤ R ∧ xiEndpointCompletedCurvature * ((R + 1/2)^2 + 1) < 4
XiOffLineQuartetAccretiveBand         R  :=  0 ≤ R ∧ xiEndpointCompletedCurvature * ((R + 1/2)^2 + 1) < 4
```

so the whole "exact" development — `XiC_ne_zero_of_upperHalf_*`, `xiRelativeResolventTrace_im_nonpos_*`, `continuedPrimeArchSourceRelativeTrace_im_nonpos_*`,
`continuedPrimeArchUpperAntiHerglotz_of_positiveFrequencyAbove_*`,
`continuedPrimeArchPositiveFrequencyAbove_iff_*` — states the same five theorems as the
`offLineOrbit` development, reached only by a different internal route to the height bound. The
exact module reaches the other, so its band is now an `abbrev` and its five theorems are one-line
delegations; the private helper lemma they used (78 lines) became dead and was deleted.

**Worth checking before reading any proof: are two `def`s with different names the same term?**
A `def`-body comparison across the corpus is cheap and would have found this instantly. Two names
for one predicate make every theorem about them duplicate.

Audit: `lake build` of `ReflectionParity` (8562), `PrimeArchExactOffLineQuartetAccretivity` (8989)
and `PrimeArchExactOffLineQuartetKMSMaster` (9134) — all successful; the six other consumers of the
band verified with `lake env lean`.

**Next target found in passing.**  `xiRelativeResolventTerm_lineConj_pair_im_nonpos` appears in
*five* modules with five suffixes — `PrimeArchHighFrequencyAccretivity` (bare),
`…EndpointFrequencyAccretivity` (`_of_endpointBand`), `…OffLineQuartetAccretivity` (`_offLineOrbit`),
`…ExactOffLineQuartetAccretivity` (`_exactOffLineQuartetBand`, now deleted),
`…VerifiedHeightAccretivity` (`_of_verifiedHeight`) — each about 50-80 lines and differing only in
which hypothesis supplies the height bound on off-line atoms. One lemma taking that bound as a
hypothesis should replace all of them.

## B35 — the accretive-band tower reduced to one inequality

Four modules each carried a ~55-80 line lemma
`xiRelativeResolventTerm_lineConj_pair_im_nonpos*` with the *same* conclusion — the
line-conjugate resolvent pair has nonpositive imaginary part — under four different hypotheses
(a rational radius bound, an endpoint accretive band, an off-line quartet band, a verified
height). All four proofs converge on one intermediate fact and then run an identical 30-line tail.

New general law in `PrimeArchHighFrequencyAccretivity`:

```
lemma xiRelativeResolventTerm_lineConj_pair_im_nonpos_of_core
    (z : ℂ) (hzIm : 0 < z.im) (q : XiZeroCopy)
    (hcore : 0 < (z.re - (xiSpectralPoint q).re) ^ 2 + z.im ^ 2 - (xiSpectralPoint q).im ^ 2) :
    (xiRelativeResolventTerm z q + xiRelativeResolventTerm z (xiZeroCopyLineConjEquiv q)).im ≤ 0
```

The pair's imaginary part is `−2·z.im·core` over a positive denominator, so the core plus
`0 < z.im` is the whole content. **The core is also enough to separate `z` from `a` and from its
line conjugate** — both make it vanish identically — so the four call sites no longer need their
`hdistAbs`-based `z ≠ a` / `z ≠ conj a` arguments. The two positive denominators come from
`Complex.normSq_pos` rather than `nlinarith`, which makes the derivation deterministic.

Each of the four lemmas is now its own `hcore` derivation followed by one `exact`.
`PrimeArchHighFrequencyAccretivity` 444 -> 459 (it hosts the law),
`…EndpointFrequencyAccretivity` 237 -> 210, `…OffLineQuartetAccretivity` 442 -> 413,
`…VerifiedHeightAccretivity` 468 -> 433. Net **-76 lines**, and every accretive-band hypothesis in
the tower now enters through a single named inequality.

### Verification-method correction

Three of these files were briefly reported clean by
`lake env lean … | grep -c "error:"`. That pattern is **wrong for this toolchain**: Lean 4.30 emits
`error(lean.unknownIdentifier):`, `error(lean.synthInstanceFailed):` and friends, none of which
contain the substring `error:`. The three files were in fact failing with unknown-identifier errors
against a stale olean. **Grep for `error`, never `error:`** — or rely on `lake build`'s exit status,
which is unaffected. The six band consumers of B34 were checked with the same faulty pattern and
have now been re-verified inside the audit build below.

Audit: `lake build` of `PrimeArchHighFrequencyAccretivity` (8980 jobs) and of
`PrimeArchVerifiedHeightAccretivity`, `PrimeArchExactOffLineQuartetKMSMaster` and all six B34 band
consumers together (9182 jobs) — both successful, zero error lines.

### Identical-`def` scan (the B34 lesson, executed)

`defdup.py` compares every `def`/`abbrev` in the three areas by (signature-with-name-erased, body).
19 groups of identically-defined declarations under different names, e.g.
`thetaCuspLiouvilleGibbsAtom` = `thetaCuspWardGibbsAtom`,
`vonMangoldtComplexCoefficient` = `vonMangoldtComplexCoeff`,
`primeWeight` = `primeLogWeight`, `mertensBound` = `primeMertensBound`,
`finiteGramLowerConstraint` = `finiteScaleShellConstraint`, and a four-way
`mobiusContact*Scale` group. Most are 2-5 lines, so the defs themselves are cheap; the value is
where a *development* sits on top of one — which is exactly how the `XiOffLineQuartetAccretiveBand`
duplication was found. Worth walking the list next and checking, per pair, whether the theorems
about the two names are parallel.

## B36 — three pivot presentations, one development

The corpus carried **three** parallel pivot-elimination developments, ~14 declarations each,
identical except for the jet that replaces a dependent variable:

| module | jet `J r n` |
|---|---|
| `DifferentialPivotRelationIdeal` | `C (h r n) + ∑_b C (A r b) · X (b, n)`, needs `[Fintype B]` |
| `DifferentialFinsuppPivotRelationIdeal` | `C (h r n) + (A r).sum fun b c ↦ C c · X (b, n)`, arbitrary `B` |
| `DifferentialShiftPivotRelationIdeal` | `C (c r n) · X (base r, n + offset r)` |

New module `DifferentialJetPivotCore` proves the whole development once for an arbitrary
`J : R → ℕ → DifferentialPolynomial B F`: elimination, inclusion, the four rewriting lemmas,
surjectivity, the displayed relation and its ideal, the normal-form membership, the kernel
description, the PBW quotient equivalence, the evaluation factorisation and the complete relation
theorem. Nothing in any of them depends on the shape of `J`; the only jet-specific step is
converting each module's `hrel` into
`differentialJet n (y r) = aeval (fun bn ↦ differentialJet bn.2 (x bn.1)) (J r n)`,
which is a two-to-nine line `rw`/`simp` at each of the three call sites.

`DifferentialPivotRelationIdeal` 251 -> 174, `…Finsupp…` 251 -> 176, `…Shift…` 212 -> 135, core
+196. Net **-33 lines** — modest, because the three keep their (long) signatures — but three
parallel developments became one, and a fourth jet now costs a page instead of a module.
`differentialAdjoin_sumElim_eq_left_of_affineJets` is genuinely jet-specific and stayed put.

Audit: `lake build` of the three modules (2954 jobs) and of six consumers across all three
developments — `PrimeValuationVeroneseMaster`, `CompactTailDensePrimeValuationMaster`,
`AnalyticDirichletCompleteRelationPresentation`,
`DifferentialShiftPivotLinearCovarianceUniversalityLaw`,
`Hurwitz.IntegerTranslationCompleteRelationIdeal`, `CofinalRecurrentPrimeValuationMaster`
(8802 jobs) — both successful, zero error lines. Core registered in the `HTGeometry` umbrella;
indexes regenerated.

### Incident: a tracked module was overwritten and restored

Building this, I created the core as `DifferentialPivotRelationIdeal.lean` with a shell `cat >`
redirect — **a path that already held a tracked, umbrella-registered module** (the `[Fintype B]`
development above). The redirect destroyed it. It was caught one step later, when the dependent
module failed against declarations (`differentialPivotAffineJet`) that my file did not contain,
and restored with `git checkout --`; `git status` confirms both affected files are byte-identical
to `HEAD` apart from the intended rewrites. No lasting damage, but the near-miss is the lesson:

- **Never create a file with `cat > path`.** Use the guarded write tool, which refuses to
  overwrite a file that has not been read. `cat >>` for appending stays fine.
- **Check the name is free before choosing it** — both the source path *and* `.lake/build` for a
  stale olean of that module name. A leftover olean is what first made the collision look like a
  pre-existing declaration rather than my own overwrite.
- The corpus is large enough that a "new" descriptive module name is quite likely to be taken.
  `DifferentialJetPivotCore` and its `differentialJetPivot*` declaration names were checked
  against the whole tree before use.
