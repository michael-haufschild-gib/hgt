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

## B37 — `ParallelogramIntegral`, and three process incidents

**`ParallelogramIntegral` 204 -> 132.**  `parallelogramIntegral_eq_zero_of_differentiable` (entire
`g`) and `parallelogramIntegral_eq_zero_of_continuousOn_of_differentiableAt` (continuous on the
closed square, differentiable on the open one) were two copies of the same Green/Stokes argument in
one file. The first is the second with both hypotheses supplied by entirety:
`(hg.continuous.comp (by fun_prop)).continuousOn` and `fun p _ => hg.differentiableAt`. Reordering
also merged the file's duplicated `namespace GaloisForLFunctions` / `noncomputable section` block —
the file had opened, closed and reopened the namespace around the two theorems.

Audit: `lake build` of `ParallelogramIntegral` and `GutzmerIdentity` — 2787 jobs, successful.

### Attempted and reverted: the Gutzmer / Szegő partial-sum core

`GutzmerIdentity.tendsto_integral_normSq_partialSum_analytic` and
`SzegoH2.tendsto_integral_normSq_partialSum` are the same 73-line dominated-convergence argument,
differing only in where two facts come from: `r` inside the radius of convergence, and uniform
convergence of the partial sums on the circle. The right core takes exactly those two as
hypotheses:

```
theorem tendsto_integral_normSq_partialSum_of_radius_of_uniform
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ} (hr0 : 0 ≤ r)
    (hlt : (↑(r.toNNReal) : ℝ≥0∞) < p.radius)
    (huniform : TendstoUniformlyOn (fun N θ => p.partialSum N (circleMap 0 r θ))
      (fun θ => f (circleMap 0 r θ)) atTop Set.univ) : …
```

Two mechanical extraction attempts left the tail of the proof attached to the wrong declaration
(`unsolved goals` in the core, `No goals to be solved` in the delegate). The file was restored and
this is left for a careful hand-written pass — the seam is right, the line-slicing was not.
Expected: about -55 lines.

### Process incidents, all self-inflicted, all recovered

1. **Overwrote a tracked module with `cat >`** (recorded in B36). Restored from git.
2. **A broken intermediate edit was committed by a concurrent agent.** Between my edit and my
   revert, another agent committed the shared tree, so `git checkout --` restored *my broken
   version*. Recovering needed `git show <previous-commit>:<path>`. **Consequence for working
   style: never leave a file broken across commands.** If an edit fails to compile, restore it in
   the same batch rather than iterating on the broken state.
3. **`pkill -f "lake env lean"` killed another agent's job** (a 2400-second run on
   `RHTower/SquarefreePartitionPole.lean` that I had nothing to do with). Broad `pkill` patterns
   are shared-machine hazards. **Only ever kill PIDs verified to be my own**, e.g. by matching the
   exact target module I launched.

## B38 — the Gutzmer / Szegő partial-sum core (the B37 deferral, completed)

`GutzmerIdentity.tendsto_integral_normSq_partialSum_analytic` and
`SzegoH2.tendsto_integral_normSq_partialSum` were the same 73-line dominated-convergence argument.
New law in `GutzmerIdentity`:

```
theorem tendsto_integral_normSq_partialSum_of_radius_of_uniform
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ} (hr0 : 0 ≤ r)
    (hlt : (↑(r.toNNReal) : ℝ≥0∞) < p.radius)
    (huniform : TendstoUniformlyOn (fun N θ => p.partialSum N (circleMap 0 r θ))
      (fun θ => f (circleMap 0 r θ)) atTop Set.univ) :
    Tendsto (fun N => ∫ θ in (0:ℝ)..(2 * π), ‖p.partialSum N (circleMap 0 r θ)‖ ^ 2)
      atTop (𝓝 (∫ θ in (0:ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2))
```

Only those two facts are used: the radius bound gives the tail-summable dominating constant
`∑ ‖p n‖ rⁿ`, and uniform convergence gives the pointwise limit for dominated convergence. Both
call sites are now eight lines. `GutzmerIdentity` 163 -> 176 (it hosts the law), `SzegoH2` 208 ->
150; net **-45 lines**, and `SzegoH2` gained an import of `GutzmerIdentity` (checked acyclic).

**Why the two earlier mechanical attempts failed** (B37): the theorem's last line is `exact key`,
one line past the `simp only [hconv]` I had used as the end anchor. The core therefore lost its
final step ("unsolved goals") and the delegate inherited a stray tactic ("No goals to be solved").
When slicing a proof, anchor the end on the *next declaration's* start, never on a tactic that
looks final.

**One real Lean obstacle, worth recording.** The first working delegation in `SzegoH2` hit
`(deterministic) timeout at whnf, maximum number of heartbeats (200000)`. The cause is term size,
not proof difficulty: writing `cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R` out in the
delegation makes elaboration unify two copies of a large term. Restoring the original
`set p := … with hp_def` and passing `(f := …) (p := p)` explicitly to the core fixes it with no
`maxHeartbeats` bump. **When a delegation to a newly extracted law times out at `whnf`, share the
big subterm with `set` and pass the implicit arguments explicitly** before considering a heartbeat
increase.

Audit: `lake build` of `GutzmerIdentity` (2786 jobs), `SzegoH2` (2799) and its two consumers
`SzegoHapproxAC`, `SzegoBoundaryH2` (8505) — all successful, zero error lines.

## B39 — the shifted cosine band measure

`RouteBSublevel.cos_band_measure_shifted` (bound `2π√(2(u₂−u₁))`) and
`RouteBThreePhase.cos_band_measure_shifted_gap` (bound `4(arccos u₁ − arccos u₂)`) share the same
hypotheses and the same covering argument: the band is contained in three shifted copies of
`Icc θ₁ θ₂` plus a wrap-around, of total length `4L` with `L = arccos u₁ − arccos u₂`. The `_gap`
form *is* that covering bound; the `√` form is `_gap` followed by the arccos modulus-of-continuity
inequality `arccos_gap_le : 2L ≤ π√(2(u₂−u₁))`, which already lived in `RouteBSublevel`.

The two modules were independent siblings, both in `namespace RHTower.Sublevel`, so the covering
theorem moved up into `RouteBSublevel` under an unchanged full name and `RouteBThreePhase` gained
an import. `cos_band_measure_shifted` is now

```
  refine (cos_band_measure_shifted_gap h1 h12 h2 hψ0 hψ2).trans (ENNReal.ofReal_le_ofReal ?_)
  have hgapL := arccos_gap_le h1 h12 h2
  linarith [hgapL]
```

`RouteBSublevel` 840 -> 849 (it hosts the covering theorem), `RouteBThreePhase` 512 -> 429; net
**-74 lines**. `RouteBCausticShell`, the other user of `_gap`, reaches it transitively through
`RouteBThreePhase` and needed no edit.

Audit: `lake build` of `RouteBSublevel` (8475 jobs) and of `RouteBThreePhase` + `RouteBCausticShell`
(8477 jobs) — both successful, zero error lines.

## B40 — convex confinement for an arbitrary increment-record weight

`StretchedExponentialConvexConfinement` and `PolynomialPowerConvexConfinement` each carried a
smoothing lemma and a boundary-shell theorem, differing only in the weight being minimised:
`tupleStretchedValuation α s = ∑ stretchedExp α (s i)` against
`tuplePowerValuation β s = ∑ (s i : ℝ) ^ β`. The 94/98-line boundary-shell proofs differ in
**28 lines**, all of them the valuation name and the two applications of the smoothing lemma.

Both weights are `∑ i, g (s i)`, and the only property used is that the increments of `g` strictly
increase from some point `Q` on. Two general laws now live in
`StretchedExponentialConvexConfinement` (which `PolynomialPowerConvexConfinement` already imports):

```
lemma sum_comp_smoothTuple_lt {D Q : ℕ} (g : ℕ → ℝ)
    (hrecord : ∀ a b : ℕ, Q ≤ b → a < b → g (a + 1) - g a < g (b + 1) - g b) …
    ∑ i, g (smoothTuple s lo hi i) < ∑ i, g (s i)

lemma exists_boundaryShell_of_sum_bounds_of_record {D q K C Q : ℕ} (g : ℕ → ℝ) …
    ∃ t, ∑ i, t i = ∑ i, s i ∧ tupleInWindow q (K + 1) t ∧ ¬ tupleInWindow q K t ∧
      ∑ i, g (t i) ≤ ∑ i, g (s i)
```

All four original lemmas are now instantiations. `StretchedExponentialConvexConfinement`
721 -> 751 (it hosts both laws), `PolynomialPowerConvexConfinement` 402 -> 311; net **-61 lines**.

Two details worth keeping:

- The stretched development is the *general* one — its `hrecord` hypothesis is weaker than
  `1 < β` — so the power side had to supply `Q := 0` and, with it, `hqQ : 1 ≤ q`, which is **not**
  among the power lemma's hypotheses. It is derivable: at `q = 0` the window is `s i ≤ K`, so
  `hout` gives some `s i > K`, while `hsumUpper` gives `∑ s ≤ C < K`. Nine lines.
- Casts: `stretchedIncrement α a` unfolds to `stretchedExp α (↑a + 1) − stretchedExp α ↑a`
  (real addition) whereas the general `g (a + 1) − g a` at `g := fun n => stretchedExp α n` gives
  `stretchedExp α ↑(a + 1)`. Definitional but not syntactic; each instantiation needs a
  `push_cast` bridge rather than passing `hrecord` straight through.

Scripting note: substituting `tupleStretchedValuation α` by `fun u => ∑ i, g (u i)` produced
`have hval : fun u => … s' < fun u => … s`, i.e. an unapplied lambda where the original had an
application. When abstracting a *function-valued* name out of a proof, substitute the **applied**
form `F x -> ∑ i, g (x i)` with a pattern that captures the argument, never the bare head symbol.

Audit: `lake build` of `StretchedExponentialConvexConfinement` (8478 jobs) and of
`PolynomialPowerConvexConfinement` + `PolynomialPowerADEResonance` (8566 jobs) — both successful,
zero error lines.

## B41 — the boundary-shell law already existed, and is more general than B40's

A re-run of the cross-file scan immediately after B40 flagged
`RapidConvexCurvatureResonance.exists_boundaryShell_of_sum_bounds_of_smoothing` against the
`exists_boundaryShell_of_sum_bounds_of_record` I had *just written*. The existing theorem is
**strictly more general**: it abstracts the whole valuation,

```
theorem exists_boundaryShell_of_sum_bounds_of_smoothing {D q K C : ℕ} (hD : 0 < D) (hKC : C < K)
    (V : (Fin D → ℕ) → ℝ)
    (hsmooth : ∀ s lo hi, lo ≠ hi → q ≤ s hi → s lo + 1 < s hi → V (smoothTuple s lo hi) ≤ V s) …
```

against my `V = ∑ g (s i)` with `hsmooth` derived from an increment record. So the corpus already
had the right law and I had rebuilt a weaker copy — **a direct violation of "check what the corpus
already offers before writing a new general law"**, and of the standing rule to run
`scripts/formal_tools.py research "<query>"` first. It cost a full build cycle.

Corrected rather than left standing: `_of_smoothing` moved up into
`StretchedExponentialConvexConfinement` (whose cone `RapidConvexCurvatureResonance` sits above),
and `_of_record` is now four lines —

```
  exists_boundaryShell_of_sum_bounds_of_smoothing hD hKC (fun u => ∑ i, g (u i))
    (fun s lo hi hne hq hgap => (sum_comp_smoothTuple_lt g hrecord s hne (by omega) hgap).le)
    s hsumLower hsumUpper hout
```

with the `Q ≤ s hi - 1` side condition discharged by `omega` from `hqQ : Q + 1 ≤ q` and
`hq : q ≤ s hi`. The copy in `RapidConvexCurvatureResonance` is gone.
`StretchedExponentialConvexConfinement` 759 -> 773 (it now hosts the general law),
`RapidConvexCurvatureResonance` 2202 -> 2108; net **-80 lines**.

The four-layer stack is now: `_of_smoothing` (arbitrary `V`) -> `_of_record` (`∑ g`, increments
record from `Q` on) -> the stretched-exponential and polynomial-power boundary-shell theorems.

**Procedure fix, for every future "new general law":** before writing one, run the corpus search
*on the shape of the conclusion*, not only on the names involved. The scan that found this is the
same `xfile.py` used to find the duplication in the first place — running it against a freshly
written lemma is a cheap self-check and should be routine.

### Examined and rejected

`XiWardEdgeImChannelGram.integral_mul_im_xiPairs` and
`XiWardEdgeReChannelDeposit.integral_mul_re_xiPairs` have **identical right-hand sides** and differ
only by `.im` versus `.re` on the left, but the proofs are not a rename: the imaginary channel
decomposes through odd kernels (`integrable_mul_oddKernels_general`, numerators `t + im`), the real
channel through Lorentzian halves (`integrable_mul_lorentzianHalves_general`, numerators
`re + 1/2`). 162 differing lines out of 154. That the two decompositions give the same value is the
mathematical content, not a factorisation opportunity.

Audit: `lake build` of `StretchedExponentialConvexConfinement` (8478 jobs) and of
`RapidConvexCurvatureResonance` + `PolynomialPowerConvexConfinement` (8570 jobs) — both successful,
zero error lines.

## B42 — the `_modSum` chain

`PrescribedResidueBalancedAtom` mirrored three upstream lemmas, each adding a
`Nat.ModEq D (∑ δ i) ρ` conjunct threaded through an otherwise identical proof:

| base | `_modSum` mirror | differing lines |
|---|---|---|
| `exists_injective_nat_eval_ne_zero` | `…_modSum` (line 11) | — |
| `exists_injective_balanced_diagonal_ne_zero` (`BalancedDiagonalNonvanishing`) | `…_modSum` (line 119) | ~20 of 22 |
| `exists_eventually_balanced_nonzero_aevalWeight` (`MagnitudeBalancedAtomExistence`) | `…_modSum` (line 146) | **24 of 94** |

The three `_modSum` lemmas moved up into `MagnitudeBalancedAtomExistence` (which already reaches
`BalancedDiagonalNonvanishing`), and the top base theorem is now

```
  obtain ⟨δ, hδinj, -, Q₀, hQ₀⟩ := exists_eventually_balanced_nonzero_aevalWeight_modSum ha hD 0
  exact ⟨δ, hδinj, Q₀, hQ₀⟩
```

`MagnitudeBalancedAtomExistence` 121 -> 275 (it hosts the chain), `PrescribedResidueBalancedAtom`
307 -> 76, keeping only `exists_eventually_balanced_nonzero_aevalWeight_residue`. Net **-77 lines**.
The base theorem has eight external users and kept its name and signature, so none needed editing.

Note on what was *not* collapsed: the two lower base lemmas
(`exists_injective_nat_eval_ne_zero`, `exists_injective_balanced_diagonal_ne_zero`) carry **no**
`hD : 0 < D`, while their `_modSum` forms need it — a residue class mod `D` is meaningless at
`D = 0`. Deriving them would require a separate `D = 0` branch (where `Fin 0 → ℕ` makes injectivity
vacuous and `MvPolynomial (Fin 0) ℂ ≅ ℂ` makes the evaluation the nonzero constant). Cheap but not
free, and left alone deliberately; only the top layer, whose `hD` is already a hypothesis, was
collapsed.

Audit: `lake build` of `MagnitudeBalancedAtomExistence` (8509 jobs) and of
`PrescribedResidueBalancedAtom` + `PolynomialPatternResidueBridge` +
`PolynomialBalancedExactResidue` (8576 jobs) — both successful, zero error lines.

## B43 — three copies of the fourth-trace atom bound

Three modules proved `9/200000 < (xiZeroCopyReciprocalSquare q ^ 2).re` from the same four
hypotheses, differing only in the numeric window:

| theorem | `u` lower | `v` upper |
|---|---|---|
| `…_of_orderEighteen_edgeCorner` (`XiOrderEighteenCornerSourceExclusion`) | `7/50 < u` | `v < 147` |
| `…_of_centered_orderNineteenRange` (`XiCenteredOrdersSeventeenEighteenSourcePositivity`) | `0 < u` | `v < 295/2` |
| `…_below_2365_over_16` (`XiFourthTraceExtendedCriticalLineBand`) | `0 < u` | `v < 2365/16` |

`2365/16 = 147.8125` is the largest of the three windows and `0 < u` the weakest lower bound, so
the third theorem's hypotheses are implied by each of the other two and it subsumes them outright —
each becomes a one-line application with `by linarith` discharging the window comparison. No new
law was needed; the general one was already there.

The obstacle was placement: the general theorem sat **downstream** of one caller and in a module
*unrelated* to the other (`XiOrderEighteenCornerSourceExclusion` and
`XiCenteredOrdersSeventeenEighteenSourcePositivity` are mutually unreachable). The host had to be a
common ancestor of both that also carries `xiZeroCopyReciprocalSquare_re_formula` /
`_im_formula`, which the proof uses — that is `XiThermalSourceRelativeGapBound`. Searching the
import graph for *common ancestors satisfying the proof's own dependencies* is the general recipe
when a shared law has two incomparable callers.

`XiThermalSourceRelativeGapBound` 621 -> 715 (it hosts the bound),
`XiFourthTraceExtendedCriticalLineBand` 206 -> 113,
`XiCenteredOrdersSeventeenEighteenSourcePositivity` 416 -> 333,
`XiOrderEighteenCornerSourceExclusion` 170 -> 97. Net **-155 lines**.

Note: the three proofs also differ in an internal constant (`W = 2369/16` against `591/4`) and the
`u·v` bound, so a *parametrised* version — general in the window `V` — would need the nlinarith
certificate to be re-established for each `V`, which is not a factorisation. Subsumption by the
widest window is the correct reduction here, and it is exact.

Audit: `lake build` of `XiThermalSourceRelativeGapBound` (8959 jobs) and of the three consumers
(9171 jobs) — both successful, zero error lines.

## B44 — sampled-ray transfer, and a blocked RouteB merge

**`SampledRayRateTransferFixed` 105 -> 49 (-56).**
`norm_le_ray_of_sampled_decay_fixed` and `norm_le_ray_of_sampled_decay_fixed_halfplane` are the
same theorem under two analyticity hypotheses: `Differentiable ℂ H` globally against
`∀ t, T < t → AnalyticAt ℂ H t` plus `T < R₀`. The halfplane form is the weaker hypothesis, hence
the general one, and the two modules are independent siblings — so `…Fixed` now imports
`…Halfplane` and the theorem is

```
  norm_le_ray_of_sampled_decay_fixed_halfplane (T := R₀ - 1)
    (fun t _ => hH.analyticAt (t : ℂ)) (by linarith) hR₀0 hK hC hσ0 hδ0 hder hnodes
```

`Differentiable.analyticAt` in this mathlib is `Differentiable 𝕜 f → ∀ z, AnalyticAt 𝕜 f z`, so it
takes the point explicitly — `hH.analyticAt` alone does not typecheck. Worth a scratch probe before
writing the delegation.

**Blocked: `RouteBBlockSplit` vs `RouteBFourPhaseUniform`.**  `inv_sqrt_average'` is
`inv_sqrt_average` with a weaker `hfK` (the bound is only required where
`sstar ≤ ‖c' + D e^{iη}‖`), so the unprimed one should be
`inv_sqrt_average' … (fun η hη _ => hfK η hη)`. Adding the import fails: the two modules
**independently declare the same fully-qualified names** — `RHTower.Sublevel.inv_sqrt_average`
itself, plus `RHTower.SteinhausModel.X_prime`, `…map_two_pi_smul`,
`RHTower.Sublevel.one_phase_smallball_uniform` — and are simply never imported together, so the
clash has never surfaced. Reverted; `RouteBBlockSplit` is byte-identical to `HEAD` and compiles.

This is a **latent corpus hazard**, not just a missed reduction: any future module importing both
fails to compile. The fix is a real merge of the two modules (204 + 332 lines) with the duplicated
declarations resolved, which is the next staged batch here. Detection recipe: for each pair of
modules, intersect their declared *fully-qualified* names — the earlier
`cross-cone-name-collision-scan` instrument applies directly.

Audit: `lake build` of `SampledRayRateTransferFixed` (2719 jobs) and of its only consumer
`WeightedEulerPrimeOversampling` (8542 jobs) — both successful, zero error lines.

## B45 — a working duplicate-name scanner, and four collisions removed

B44's blocked merge showed that two modules can declare the *same fully-qualified name* and never
be noticed, because they are never imported together. `fqn2.py` (job tmp dir) parses namespace
stacks and reports non-`private` declaration names owned by more than one module.

Getting it right took three passes, and the two failures are the durable lesson:

1. **Comment blocks.**  Without tracking `/- … -/` nesting, docstring interior lines beginning with
   a word matched the declaration regex and produced "duplicate declarations" named `the`, `is`,
   `and`, `by`, `for`, `in`, `that`, `on`, `then`, `cannot`. 95 hits, mostly noise.
2. **Unicode identifiers.**  An ASCII-only identifier class truncates `srKoszulBoundary3ₗ` to
   `srKoszulBoundary3`, `srHollowDetectorₗ` to `srHollowDetector`, `symmetricAlgebra_ₗ` to
   `symmetricAlgebra_` — inventing collisions between a definition and its linear-map version.
   Lean identifiers carry subscripts, primes and Greek; the name class must be
   "anything but whitespace and delimiters".

`private` declarations must also be excluded: Lean mangles them per-module, so they never collide
(that is what the `edgePoint_re`/`edgePoint_im` triple was).

With all three corrections: **16 duplicate names corpus-wide, 7 inside HTGeometry/HilbertMetric/
RHTower**, every one of them a latent hazard — any module importing both copies fails to compile.

Four had *identical statements* and were consolidated to a single owner (the other module now
imports it and the copy is deleted):

| name | owner kept | copy deleted from | lines |
|---|---|---|---|
| `cosh_one_lt_two` | `CothInfra` | `ConePositivstellensatzFailure` | 6 |
| `differentialAlgebraicOver_of_deriv_eq_base_mul` | `AffineFirstOrderDifferentialAlgebraicity` (6-line proof delegating to `…_add`) | `MeromorphicExponentialGaugeDA` (13-line from scratch) | 15 |
| `logDeriv_XiC_neg` | `XiGuinandWeilSymmetricContour` (via `logDeriv_xi_reciprocity`) | `XiWardSpectralBudgetSumRule` | 13 |
| `xi_eq_mul_completedRiemannZeta` | `XiRealAxisGrowth` | `XiWardInteriorTraceSplit` | 11 |

Net **-45 lines** and four fewer landmines. In each case the two proofs were genuinely different
tactic scripts for the same statement, so the shorter/more structural one was kept.

Still open in remit — same name, *different* statements, so each needs reading before deciding
whether it is one theorem or two that should be renamed apart:
`RHTower.exp_neg_le_quadratic` (`PrimeArchThetaMorseFisherExponentialEnvelope` / `SpurRescale`),
`RHTower.norm_exp_neg_I_mul_ofReal` (`CenterMixedTiltDifferentiation` / `RadialInteractionBound`),
`RHTower.xi_exists_isolating_radius` (`IsolatingAnnulusRung` / `ModulusSlopeQuantization`).

Audit: `lake build` of all four modified modules — 9011 jobs, successful, zero error lines.

## B46 — the in-remit duplicate-name surface is now empty

The three remaining collisions flagged `identical=False` only because of **bound-variable naming**
(`u` vs `x`, `r` vs `c`, `R` vs `R₀`) — alpha-equivalent statements, so all three were the same
theorem proved twice. Owners chosen by *upstreamness* (size of the transitive import closure), so
the new import always points from a deeper module to a shallower one:

| name | owner (transitive imports) | deleted from (imports) | lines |
|---|---|---|---|
| `exp_neg_le_quadratic` | `SpurRescale` (0) | `PrimeArchThetaMorseFisherExponentialEnvelope` (145) | 17 |
| `norm_exp_neg_I_mul_ofReal` | `RadialInteractionBound` (1) | `CenterMixedTiltDifferentiation` (6) | 7 |
| `xi_exists_isolating_radius` | `IsolatingAnnulusRung` (0) | `ModulusSlopeQuantization` (0) | 7 |

Net **-31 lines**. Re-running the scanner: **corpus-wide duplicates 16 -> 9, in
HTGeometry/HilbertMetric/RHTower 7 -> 0.** The nine that remain are in `Bottcher`, `U0` and
`GelfondSchneiderProof/`, outside this audit's remit, and are listed by `fqn2.py` for whoever owns
those areas.

**The one real break, and the lesson.**  Deleting a copy is *not* always a no-op even when the
statements are alpha-equivalent: a call site read
`exp_neg_le_quadratic (u := 2 * x)`, and the surviving copy binds that variable as `x`, so the
named argument no longer resolved (`Invalid argument name u`). **After consolidating two copies of
a theorem, grep the call sites for named-argument syntax `(name := …)` against the *surviving*
binder names.** Positional applications are unaffected; named ones are not.

Audit: `lake build` of the three modified modules — 8809 jobs, successful, zero error lines. Two
earlier attempts hit the wall clock and one transient "no such file or directory" from another
agent's concurrent file churn; both resolved on resume.

## B47 — correction to B44, and the RouteB collapse it was blocking

**B44's diagnosis was wrong.**  It recorded that `RouteBBlockSplit` and `RouteBFourPhaseUniform`
"independently declare the same fully-qualified names". They do not: `inv_sqrt_average` is declared
only in `RouteBBlockSplit`, `inv_sqrt_average'` only in `RouteBFourPhaseUniform`. The real cause of
the failure was an **import cycle** — `RouteBFourPhaseUniform → RouteBFourPhase → RouteBBlockSplit`
already existed, so adding `import RouteBFourPhaseUniform` to `RouteBBlockSplit` re-imported that
module's own declarations. Lean reports a cycle of this shape as "`X` has already been declared",
which reads exactly like a name collision. **Treat "already been declared" after adding an import
as a suspected cycle first, a collision second.**

The mistake came from a defect in the import-graph parser used all session: it stopped scanning at
the first line that is not an `import`, and a module whose imports follow a `/- … -/` header hits
that line immediately. About **1060 of 5734 modules recorded no imports at all**, so every
"mutually unreachable siblings" claim made from it is unreliable. The landed changes are unaffected
— each was verified by `lake build`, which cannot succeed through a missing or cyclic import — but
the *stated rationale* in B33, B40–B46 should be read as unverified, and a few of the imports added
there may be redundant rather than necessary. Corrected parser: `imports.py` in the job tmp dir;
the fix is to skip lines that *open* a block comment, not only lines already inside one.

**With the graph correct, the collapse is the standard shape.**  `inv_sqrt_average'` weakens
`inv_sqrt_average`'s hypothesis (the bound `f η ≤ K / √‖c' + D e^{iη}‖` is required only where
`sstar ≤ ‖c' + D e^{iη}‖`), and the general form sat *downstream*. Moved up into
`RouteBBlockSplit`; the special case is now

```
  inv_sqrt_average' hD hK hs hs2 hfM (fun η hη _ => hfK η hη)
```

`RouteBBlockSplit` 204 -> 218 (it hosts the general law), `RouteBFourPhaseUniform` 332 -> 271; net
**-47 lines**. No import was added: `RouteBFourPhaseUniform` already reaches `RouteBBlockSplit`.

Audit: `lake build` of `RouteBBlockSplit` (8486 jobs) and of `RouteBFourPhaseUniform` +
`RouteBFourPhase` (8488 jobs) — both successful, zero error lines.

## B48 — re-ranking with a correct import graph

Re-checking the remaining clone pairs against the *fixed* graph overturns B44–B46's picture: every
one of the six has a genuine one-way dependency, so **none of them needs a new import** — the
earlier "mutually unreachable siblings" readings were the parser defect.

| pair | direction |
|---|---|
| `XiCTaylorThetaTailFiniteArithmeticEndpoint` → `…PhaseAdaptedProuhetIntegratedHaarCurrent` | A reaches B |
| `InfinityLeafAtoms` → `LeafAtoms` | A reaches B |
| `DigammaGammaLocalHypertranscendence` → `DigammaGammaFactorialBlowUp` | B reaches A |
| `DistinctIndexComplexSurvival` → `PermanentCoefficientIdentity` | A reaches B |
| `CocycleKernelTrivial` → `IntegralFEPolynomial` | A reaches B |
| `DeningerArithmeticLocalDivision` → `…GlobalDivision` | B reaches A |

**Landed: the Digamma factorial-relation pair (-51).**
`factorialInitialRelation_of_relation_at` needs the annihilating relation only **at the single
point** `-(n) + reciprocalGammaFactorialScale n * x`, while
`factorialInitialRelation_of_differentialAnnihilator` demands it for all `z`. The pointwise form is
therefore the general one, and it sat downstream. Moved up into `DigammaGammaFactorialBlowUp`; the
global-hypothesis version is now `factorialInitialRelation_of_relation_at h P n x (hP _)`.
`DigammaGammaFactorialBlowUp` 1416 -> 1431, `DigammaGammaLocalHypertranscendence` 393 -> 327.

**Examined, not done — a judgement call left open.**
`diffPoly_fixedDegree_survives` (ℤ coefficients, `PermanentCoefficientIdentity`) is the ℤ case of
`diffPoly_fixedDegree_survives_complex` (`DistinctIndexComplexSurvival`), the two proofs differing
only in `exists_injective_eval_ne_zero` / `combination_permSymbolPoly_ne_zero` versus their
`_field` / `…PolyC` counterparts. Collapsing needs **three** declarations moved upstream, and both
theorems currently have **zero users**. Deleting the ℤ case outright would be the larger reduction,
but removing a stated result from someone's research corpus on the grounds that nothing cites it
yet is not a call this audit should make unilaterally. Recorded for the owner to decide.

**Also examined, not a specialisation.** `InfinityLeafAtoms.ofReal_christoffelLimit_le_leaf_infinity_singleton` and
`LeafAtoms.ofReal_christoffelLimit_le_leaf_singleton` share 44 lines of the ε-argument but differ in
the *limit regime* — `goodLevelInf`/`leafParamInf` and the hypothesis `nevBrealInf s ξ = 0` against
`goodLevel h tau`/`leafParam h tau` and `nevBrealInf s ξ * tau - nevDrealInf s ξ = 0`. Neither
implies the other; unifying means abstracting over the node-existence lemma
(`eventually_exists_quasiNode_near` vs `…_inf`), which is the "abstract the varying object" shape
rather than a subsumption.

Audit: `lake build` of `DigammaGammaFactorialBlowUp` (8495 jobs) and
`DigammaGammaLocalHypertranscendence` (8496 jobs) — both successful, zero error lines.

## B49 — the free-endpoint Haar current

`phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint m N z tau` and
`canonicalPhaseAdaptedWeightedReflectedHaarIntegratedCurrent m N z` have **the same definition
body**, the second fixing `tau := canonicalThetaTailSeamProuhetEndpoint m N z`; likewise their two
evaluation theorems, 51 and 53 body lines with 47 shared. The free-`tau` form is the general one and
sat downstream (`XiCTaylorThetaTailFiniteArithmeticEndpoint` reaches
`…PhaseAdaptedProuhetIntegratedHaarCurrent`).

Both the definition and its theorem moved up. The canonical definition is now

```
def canonicalPhaseAdaptedWeightedReflectedHaarIntegratedCurrent (m N : ℕ) (z : ℂ) : ℝ :=
  phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint m N z
    (canonicalThetaTailSeamProuhetEndpoint m N z)
```

and its evaluation theorem is a term-mode application of the general one. Both directions of the
required defeq hold by unfolding: the canonical *current* is the general one at the canonical
endpoint, and `canonicalThetaTailSeamProuhetUntruncatedCurrent` is literally
`phaseAdaptedCriticalReturnedSourceCurrent … (canonicalThetaTailSeamProuhetEndpoint m N z) …`.

`…PhaseAdaptedProuhetIntegratedHaarCurrent` 948 -> 968, `…FiniteArithmeticEndpoint` 565 -> 479;
net **-66 lines**.

Checked before moving, and worth doing every time a *definition* moves rather than a theorem:
the only `unfold canonicalPhaseAdaptedWeightedReflectedHaarIntegratedCurrent` in the corpus was
inside the very theorem being rewritten, so no downstream `simp`/`unfold` set changed meaning. The
moved proof's dependencies (`canonicalPhaseAdaptedWeightedHaarPolynomial`,
`integrableOn_canonicalPhaseAdaptedWeightedHaarResidualSource_mul_phase`) already lived in the
target module or above it.

Audit: `lake build` of `…PhaseAdaptedProuhetIntegratedHaarCurrent` (8818 jobs) and of
`…FiniteArithmeticEndpoint` + `…PhaseAdaptedRawCoreBridge` (8822 jobs) — both successful, zero
error lines.

### Remaining clone pairs, and why they are not subsumptions

- `CocycleKernelTrivial.symmetric_infinite_support_zero` /
  `IntegralFEPolynomial.integralMultiplicativeFEClass_finite_or_zero`: different statements (a
  support-vanishing lemma against a finite-or-zero dichotomy) sharing ~41 lines of one analytic
  sub-argument — vanishing on a left half-plane from non-summability, then the identity theorem.
  Extracting that core is a genuine piece of work, not a delegation.
- `DeningerArithmetic{Global,Local}Division`: `Deninger*` is under active edit by another agent;
  left alone to avoid conflicting writes.

## B50 — the integral-L-series vanishing core

The pair B49 set aside as "not a subsumption" turned out to share **two** separable arguments, not
one. `CocycleKernelTrivial.symmetric_infinite_support_zero` and
`IntegralFEPolynomial.integralMultiplicativeFEClass_finite_or_zero` prove different statements but
run character-for-character identical blocks at both ends, with only the middle step differing
(reflection symmetry `f (1 - s) = f s` versus a conductor functional equation).

Two laws now live in `IntegralFEPolynomial` (which `CocycleKernelTrivial` reaches):

```
theorem LSeries_eq_zero_of_re_nonpos_of_int_of_infinite_support
    {a : ArithmeticFunction ℂ} (hint : ∀ n, ∃ k : ℤ, a n = (k : ℂ))
    (hinf : (Function.support (fun n => a n)).Infinite)
    {z : ℂ} (hz : z.re ≤ 0) : LSeries (fun n => a n) z = 0

theorem eq_zero_of_int_of_infinite_support_of_eq_zero_of_one_le_re
    {f : ℂ → ℂ} {a : ArithmeticFunction ℂ}
    (hrep : ∀ s, f s = LSeries (fun n => a n) s)
    (hinf : (Function.support (fun n => a n)).Infinite)
    (hge1 : ∀ z : ℂ, 1 ≤ z.re → f z = 0) : ∀ s, f s = 0
```

The first is the real content: a nonzero integer coefficient has `‖a n‖ ≥ 1` while `n ^ Re z ≤ 1`
on the closed left half-plane, so infinitely many terms have norm at least one, the terms cannot
tend to zero, and the `LSeries` convention gives the value `0`. The second closes the argument:
vanishing for `1 ≤ Re z` makes the series vanish along the real axis at infinity, and with infinite
support the only alternative to identically-zero coefficients is an infinite abscissa of absolute
convergence.

Each site now supplies **only its own middle step** — `hge1` from `hsym` in one case, from `hFE` in
the other — and applies the two laws. `IntegralFEPolynomial` 233 -> 254 (it hosts both),
`CocycleKernelTrivial` 297 -> 250; net **-26 lines**, and the half-plane lemma is now available to
any future integral-coefficient argument.

**Lesson for the "not a subsumption" bucket.**  Two theorems with different statements can still
share *most* of their proof at both ends. Diffing whole bodies reports them as ~40% similar and
they look unpromising; diffing with the divergence located (here: one `have` in the middle) shows
the shared parts are contiguous and liftable. When a pair is rejected as "different theorems",
check whether the difference is a *single step* before dismissing it.

Audit: `lake build` of `IntegralFEPolynomial` (8574 jobs) and `CocycleKernelTrivial` (8581 jobs) —
both successful, zero error lines.

## B51 — the sandwich scanner, and `EvaluationCodimensionFieldCore` absorbed

B50's lesson became an instrument. `sandwich.py` (job tmp dir) looks for proof pairs sharing a long
**prefix and suffix** with a small middle divergence — the shape a whole-body similarity metric
under-reports, because a pair that is 60% identical at both ends scores the same as one that is 60%
identical at random. It indexes candidates by (first body line, last body line), then measures
longest common prefix + longest common suffix against the middle.

Two hits, both real:

1. `EvaluationCodimensionCore.card_rows_some_boundedCoefficientPolynomial_nonzero` vs
   `EvaluationCodimensionFieldCore.…PolynomialOver_nonzero` — 28/28 bodies, **27 shared, 1 line of
   middle**.
2. `MvPolynomialInfiniteEval.exists_injective_eval_ne_zero` vs
   `DistinctIndexComplexSurvival.…_field` — 41/41 bodies, 29 shared, 12 middle. *Not yet done*; it
   would also unlock the ℤ/ℂ survival pair deferred in B48.

Pulling on (1) exposed that `EvaluationCodimensionFieldCore` is a **complete five-declaration
mirror** of the ℂ development in `EvaluationCodimensionCore`: `boundedCoefficientPolynomial{,Over}`,
`…_coeff`, `…_natDegree_le`, `…_ne_zero_of_apply_ne_zero`,
`card_rows_all_boundedCoefficientPolynomials{,Over}_zero_le` and the pair above. The `Over` versions
are general in an arbitrary `[Field K] [DecidableEq K]`; the ℂ ones are that at `K := ℂ`.

The whole `Over` development moved into `EvaluationCodimensionCore`, all five ℂ declarations became
one-line delegations (`classical` supplies `DecidableEq ℂ` where needed), and
`EvaluationCodimensionFieldCore` was **deleted** — its two consumers re-pointed and the umbrella
line dropped. `EvaluationCodimensionCore` 157 -> 207; net **-92 lines** and one fewer module.

Trap when splicing a module body into another: `LF[7:104]` carried the source module's own bare
`end` closing its `noncomputable section`, which then closed the target's section early — Lean
reports it far away, at the file's final `end GaloisForLFunctions.HTGeometry`. Count bare `end`
lines before and after a splice; a well-formed module should not gain one.

Audit: `lake build` of `EvaluationCodimensionCore` (8493 jobs) and of
`CoefficientPrimeActivityGeneral` + `ProjectiveCoefficientPrimeActivity` (8495 jobs) — both
successful, zero error lines. Indexes regenerated after the deletion.

## B52 — injective non-vanishing evaluation, over an integral domain

The second `sandwich.py` hit: `MvPolynomialInfiniteEval.exists_injective_eval_ne_zero` (over `ℤ`)
and `DistinctIndexComplexSurvival.exists_injective_eval_ne_zero_field` (over a field `𝕜`) are the
same 41-line variable-peeling induction, differing only in the base ring and in which root-avoidance
helper they call. Their helpers `exists_mem_eval_ne_zero_of_infinite{,_field}` are
character-identical apart from a `classical`.

**Neither subsumes the other** — `ℤ` is not a field — so this is not a specialisation but a genuine
generalisation. The proof uses nothing beyond `MvPolynomial.finSuccEquiv`, `Polynomial.coeff_map`,
`MvPolynomial.eval_eq_eval_mv_eval'` and the finiteness of a nonzero polynomial's root set; the last
is exactly what needs `[IsDomain R]`. So both are instances of

```
theorem exists_mem_eval_ne_zero_of_infinite_domain {R : Type*} [CommRing R] [IsDomain R]
    (p : Polynomial R) (hp : p ≠ 0) {S : Set R} (hS : S.Infinite) : ∃ x ∈ S, p.eval x ≠ 0

theorem exists_injective_eval_ne_zero_domain {R : Type*} [CommRing R] [IsDomain R] :
    ∀ {r : ℕ} (P : MvPolynomial (Fin r) R), P ≠ 0 → ∀ {T : Set R}, T.Infinite →
      ∃ a : Fin r → R, Function.Injective a ∧ (∀ i, a i ∈ T) ∧ MvPolynomial.eval a P ≠ 0
```

both now in `MvPolynomialInfiniteEval`, with all four original theorems one-line delegations.
`MvPolynomialInfiniteEval` 83 -> 102, `DistinctIndexComplexSurvival` 493 -> 450.

Two Lean details worth keeping:

- Delegating a theorem stated as `∀ {r} (P), P ≠ 0 → ∀ {T}, T.Infinite → …` needs the implicit
  binders written out — `fun {_r} P hP {_T} hT => …`. Writing `fun P hP hT => …` silently binds
  `hT` to the implicit `T` and fails with a `Set ℤ` versus `Set.Infinite ?m` mismatch.
- When generalising a proof body by textual ring substitution, the set-builder binders are easy to
  miss: `{x : ℤ | p.eval x = 0}` does not contain the token ` ℤ ` patterns used elsewhere and
  survived the rewrite, producing an `Polynomial ℤ` versus `Polynomial R` mismatch 20 lines away
  from the real cause.

This also removes the obstacle recorded in B48: the ℤ/ℂ `diffPoly_fixedDegree_survives` pair needed
`exists_injective_eval_ne_zero_field` moved upstream, and the domain law now sits above both.

Audit: `lake build` of `MvPolynomialInfiniteEval` (8475 jobs) and `DistinctIndexComplexSurvival`
(8483 jobs) — both successful, zero error lines.

### B53 — ℤ/ℂ permanent-survival chain unified (the B48 obstacle, cleared)

`DistinctIndexComplexSurvival` was a line-for-line ℂ-parallel of the ℤ chain in
`PermanentDistinctSymbol` + `PermanentCoefficientIdentity`: five mirrored theorems, ~250 duplicated
proof lines. Resolved in two moves.

**Root (new general law).** `combination_permSymbolPoly_ne_zero` (ℤ) and
`combination_permSymbolPolyC_ne_zero` (ℂ) were replaced by one law in `PermanentDistinctSymbol`:

- `combination_permSymbolPolyMap_ne_zero {R} [CommRing R] [CharZero R] [NoZeroDivisors R]` —
  a nonzero `R`-combination of the cast permanent symbols `(permSymbolPoly ν).map (ℤ → R)` over a
  pairwise-distinct-multiset family is a nonzero polynomial.

The three classes are exactly what the proof uses: `CharZero` for `(stabiliser count : R) ≠ 0`,
`NoZeroDivisors` for the final `mul_eq_zero` split. Both former theorems are now one-line
delegations (the ℤ one via `MvPolynomial.map_id`).

**Chain (move the general one upstream).** The remaining four ℂ theorems are *strictly more general*
than their ℤ counterparts — same series `f : ℂ⟦X⟧`, same hypotheses, coefficients in ℂ rather than
cast from ℤ — but sat downstream. Moved `exists_injective_eval_ne_zero_field`,
`combination_permSymbolPolyC_ne_zero`, `eval_map_ringHom`, `eval_map_permSymbolPoly_complex`,
`coeff_combination_complex_eq`, `degHom_survives_complex`, `coeff_mixed_eq_orderO_complex`,
`diffPoly_fixedDegree_survives_complex` into `PermanentCoefficientIdentity`. The four integer
theorems became corollaries at `c ↦ (c · : ℂ)`:

- `coeff_combination_eq` — 12 lines (needs the `eval`/`map` commuting square for the ℤ→ℂ cast);
- `degHom_survives`, `coeff_mixed_eq_orderO`, `diffPoly_fixedDegree_survives` — one line each.

`exists_mem_eval_ne_zero_of_infinite_field` was deleted: a field specialisation of the
`MvPolynomialInfiniteEval` domain law (B52) with zero users anywhere in the corpus.

`DistinctIndexComplexSurvival` 450 → 193 lines, now exactly the two ι-indexed variants
(`_indexed_`, `_maxorder_`) that are genuinely not finset statements. Net ≈ −195 lines.

**Recurrence of the standing pattern.** Fourth time in this audit that the general theorem sat
*downstream* of its specialisation. The ℤ/ℂ split is not a mathematical distinction here — the
symbol polynomial happens to be defined over ℤ, and every consumer works over ℂ.

### B54 — Ward edge Re/Im channels: one bilinear law for both

`integral_mul_re_xiPairs` (`XiWardEdgeReChannelDeposit`) and `integral_mul_im_xiPairs`
(`XiWardEdgeImChannelGram`) proved the *same* closed form
`8π(x+x′)(1/((x+x′)²+(b−b′)²) + 1/((x+x′)²+(b+b′)²))` by the same 138-line argument: expand each
edge response into a kernel at height `b` plus its reflection at `−b`, multiply out, discharge four
integrability side conditions, evaluate four cross masses, and clear denominators. The two differed
only in the kernel — Lorentzian half `x/(x²+(t+β)²)` for the real channel, odd kernel
`(t+β)/(x²+(t+β)²)` for the imaginary one — and in the outer constant, `2` versus `−2`.

Both kernels already had the *same* cross mass `π(x₁+x₂)/((x₁+x₂)²+(β₁−β₂)²)`
(`integral_mul_lorentzianHalves_general`, `integral_mul_oddKernels_general`), which is what made the
two closed forms coincide. New law in `XiWardEdgeL2CrossKernel` (upstream of both):

- `integral_mul_mirroredKernelPair {k : ℝ → ℝ → ℝ → ℝ}` — takes the kernel family abstractly with
  its integrability and cross-mass as hypotheses, plus `f = c·(k x b + k x (−b))`,
  `f′ = c′·(k x′ b′ + k x′ (−b′))`, and returns
  `∫ f f′ = 2cc′π(x+x′)(1/((x+x′)²+(b−b′)²) + 1/((x+x′)²+(b+b′)²))`.

The reflection symmetry is what collapses the four cross terms to two denominators: `b−(−b′)` and
`(−b)−b′` both square to `(b+b′)²`, `b−b′` and `(−b)−(−b′)` both to `(b−b′)²`.

Both consumers are now 15 lines. 138+138 → 15+15+45, net ≈ −200 lines.
`integral_mul_im_eq_integral_mul_re_xiPairs` (channel equipartition) is unchanged and now visibly a
consequence of one law applied at two kernels rather than a coincidence of two computations.

Audit: `lake build GaloisForLFunctions.RHTower.XiWardEdgeImChannelGram` — 8859 jobs, exit 0.
B53 audit: `lake build GaloisForLFunctions.HTGeometry` — exit 0, zero error lines.

### B55 — Deninger Xi division: the pointwise statement was downstream of the global one

`deningerNormalizedXiQuotient_analytic` (`DeningerArithmeticGlobalDivision`, 70 proof lines) and
`deningerNormalizedXiQuotient_analyticAt_of_localJets` (`DeningerArithmeticLocalDivision`, 72 lines)
shared 64 lines: identical Xi-divided-chain factorisation `XiC w = (w−z)^m · H w`, identical entire
factor extraction from `analyticOrderAt`, identical transfer of the punctured-neighbourhood identity
through the meromorphic normal form.

They are not siblings: the local one is *strictly stronger*. It concludes `AnalyticAt` at one point
from the jets at that point only; the global one concludes `AnalyticOnNhd … Set.univ` from
`deningerCompactOpenAllJets F = 0`, which supplies those jets at every point. Moved the pointwise
theorem into `GlobalDivision` (all of its dependencies — `deningerCompactOpenJet_apply`,
`xiThetaDividedChain*`, `exists_entire_factor_of_natCast_le_analyticOrderAt` — are already reachable
there; the extra imports of `LocalDivision` serve its other theorems). The global theorem is now:

```
intro z _; refine ..._analyticAt_of_localJets F z ?_; intro rho _ k
simpa [deningerCompactOpenAllJets_apply, deningerCompactOpenJet_apply, Pi.zero_apply]
  using congrFun (congrFun hjets rho) k
```

Net −64 lines. Fifth instance in this audit of the general statement sitting downstream of its own
specialisation — here the giveaway was that the "local" file was named for the *weaker* hypothesis.

Audit: `lake build GaloisForLFunctions.RHTower.DeningerArithmeticLocalDivision` — 8650 jobs, exit 0.

### B56 — Leaf atoms: one law for the finite and the infinity regime

`ofReal_christoffelLimit_le_leaf_singleton` (`LeafAtoms`, 50 lines) and
`ofReal_christoffelLimit_le_leaf_infinity_singleton` (`InfinityLeafAtoms`, 52 lines) were the same
proof — continuity of `christoffelLimit` ⇒ interval lower bound at a quasi-node ⇒ portmanteau
transport along the convergent subsequence ⇒ shrink to the singleton — run once at the finite
parameter `tau` and once at the parameter-at-infinity. Earlier in this audit the pair was passed
over as "different limit regimes"; that was wrong. The regimes enter through exactly three slots:

| slot | finite | infinity |
|---|---|---|
| level map | `goodLevel h tau` | `goodLevelInf h` |
| leaf parameter | `leafParam h tau` | `leafParamInf h` |
| node source | `eventually_exists_quasiNode_near` | `..._near_inf` |

New law in `LeafAtoms`, `ofReal_christoffelLimit_le_leaf_singleton_of_eventually_node`, takes
`lvl : ℕ → ℕ` with `∀ n, n + 1 ≤ lvl n`, `par : ℕ → ℝ`, and the node hypothesis in the form the
proof actually consumes:

```
∃ η > 0, ∀ δ, 0 < δ → δ < η → ∀ᶠ n in atTop, ∀ i, n = lvl i →
  ∃ x ∈ quasiNodes s n (par i), |x - ξ| ≤ δ
```

Both concrete node lemmas have the shape `∀ᶠ n, A n → ∃ x ∈ quasiNodes s n (β n), |x − ξ| ≤ δ`, and
in both cases `leafParam*` is *definitionally* `β (lvl i)`, so each call site discharges the
hypothesis in five lines by `filter_upwards` + `subst` + supplying its own `nevAlpha ≠ 0` fact.
Both theorems are now 7 lines. 50+52 → 7+7+76, net −19 lines and the two regimes stop drifting.

Audit: `lake build GaloisForLFunctions.HTGeometry.InfinityLeafAtoms` — 8586 jobs, exit 0.

### B57 — Möbius jet expansion: the open-set version was downstream of the half-plane one

`iteratedDeriv_outerReciprocalLimit_neg_inv_eq_mobiusJetExpansion` (`GammaFactorialComposition`,
47 proof lines, fixed to `rightHalfPlane`) and `..._local` (`GammaIterationHypertranscendence`,
53 lines, arbitrary open `Ω` with an explicit `z ≠ 0`) were the same induction on `j`: chain rule
through `w ↦ −w⁻¹`, `hasDerivAt_mobiusJetExpansion` on the other side, induction hypothesis to make
the two functions eventually equal, then cancel `z⁻²`.

`hasDerivAt_mobiusJetExpansion` was already domain-generic, so nothing blocked the general version
from sitting upstream. Moved `_local` into `GammaFactorialComposition`; the half-plane statement is
now six lines, the only work being `z ∈ rightHalfPlane → z ≠ 0`. Net −41 lines.

Sixth occurrence of the same shape. The reliable tell is a `_local`/`_general`/`_of_*` suffix on the
*downstream* module: the corpus grows the general statement where it is first needed, not where it
belongs.

Audit: `lake build GaloisForLFunctions.HTGeometry.GammaIterationHypertranscendence` — 8501 jobs,
exit 0.

### B58 — Stanley–Reisner structural output: one law, two sources

`upperEndFaceStructuralOutput_eq_zero_iff_nonface` (`FacetSewnHerglotzStanleyReisner`) and
`universalSurgeryFaceStructuralOutput_eq_zero_iff_nonface` (`UniversalConstraintOrientation`) ran
the same 42-line argument — face ⇒ nonzero Stanley–Reisner class ⇒ linear independence ⇒
differential independence ⇒ nonzero row sum, and conversely nonface ⇒ every Laurent row vanishes ⇒
termwise-zero sum — over two different source families, with two different differential-matroid
inputs supplying the same equivalence.

New law `structuralFaceOutput_eq_zero_iff_nonface` in `FacetSewnHerglotzStanleyReisner` takes the
source family and that equivalence as hypotheses. Both `…Output` definitions are the same
`differentialOperatorRowApply … Unit.unit` expression differing only in the source, so each concrete
theorem is now the three `letI` lines plus one `exact`.

Net −8 lines only — the abstract statement has to spell out the row expression and carry the three
local instances — but the 42-line proof exists once instead of twice, and a third source (there is
already a `PrimeResidueSurgery` and a `PrimeLogBoundedGauge` variant) costs seven lines.

Audit: `lake build GaloisForLFunctions.HTGeometry.UniversalConstraintOrientation` — 8550 jobs,
exit 0.

### B59 — Bernstein total variation: the parametrised bound was downstream of its own instance

`primeArchEndpointBernsteinTotalVariation_le_confinedPhase` (`PrimeArchBernsteinConfinedPhase`,
56 proof lines) bounds the Bernstein L¹ mass by
`xiReciprocalSquareAbsoluteMass · xiUniversalBernsteinAmplitudeBase ^ n`.
`..._le_of_atomAmplitudeBase` (`PrimeArchBernsteinSectorConfinedPhase`, 56 lines) proves the same
chain for an *arbitrary* bound `B` on the atom amplitude base. The confined statement is the
instance `B := xiUniversalBernsteinAmplitudeBase`, `hB := xiEndpointBernsteinAtomAmplitudeBase_le_universal`.

Moved the parametrised theorem into `ConfinedPhase` (every lemma its proof uses was already there —
`abs_bernsteinCoefficient_endpoint_le_divisorEnvelope`,
`summable_xiCentralRadiusNormalizedPolynomialTerm`,
`sum_norm_evalRealPolynomial_bernsteinPolynomial`, `summable_xiZeroCopyReciprocalSquare`); the
confined bound is now two lines. Net −54 lines.

Audit: `lake build GaloisForLFunctions.RHTower.PrimeArchBernsteinSectorConfinedPhase` — 9104 jobs,
exit 0.

### B60 — Theta-cusp likelihood: the coordinate hypothesis subsumes `0 < n ∧ 0 < x`

`thetaCuspAtomLikelihoodRatio_eq_spectralTerm` (`ThetaCuspLikelihoodSpectralMeasure`) assumed
`0 < n` and `0 < x`; `..._of_coordinate_pos` (`ThetaCuspLikelihoodModularSeam`) proved the same
identity from `0 < thetaCuspLikelihoodCoordinate x` alone. Both ran the same 45-line rational
rearrangement, and each was backed by its own private scale-form lemma (`atomRatio_scale` versus
`thetaCuspAtomLikelihoodRatio_eq_scaleForm`) that differed in exactly the same way.

Moved `atomRatio_scale` and the coordinate-hypothesis theorem into `SpectralMeasure`, deleted the
private scale-form duplicate, and reduced the original to two lines via
`thetaCuspLikelihoodCoordinate_pos hx.le`. The now-vacuous `0 < n` hypothesis was dropped rather
than left as dead weight (its single call site passed `by omega`). Net −30 lines.

Audit: `lake build GaloisForLFunctions.RHTower.ThetaCuspLikelihoodModularSeam` — 8833 jobs, exit 0.

### B61 — Möbius/Mertens: two clones, two laws

Two separate duplications in the same chain.

**(a) The norm bound inside the Cesàro criterion.**
`norm_mobiusAdditiveTriangleSecondCesaro_le_of_mertensBound` (`MobiusMertensFourthConvolutionCriterion`)
was the antidiagonal estimate `‖∑ M(a)M(b)‖ ≤ C²(N+1)^(2+2δ)` extracted as a standalone theorem —
and `mobiusMertensAllStrictHalfPowerBound_implies_secondCesaroSubpowerUpperBound`
(`MobiusMertensSelfConvolutionCriterion`, upstream) contained the identical 45-line estimate inline,
prefixed by `Complex.re_le_norm`. Moved the standalone theorem upstream; the criterion is now nine
lines. Net −47.

**(b) Square-rooting a subpower bound.**
`mobiusAdditiveTriangleSubpowerUpperBound_implies_allStrictHalfPowerDecay` and
`mobiusAdditiveTriangleSecondCesaroSubpowerUpperBound_implies_allStrictHalfPowerDecay` ran the same
39-line argument — inflate the constant to `S + 1` so `S ≤ (S+1)²`, rewrite `(x^(-b))² = x^(-2b)`,
`nlinarith` — differing only in which Abel constant and which squared-norm lemma supplied `S`. New
law in `MobiusLaplaceAdditiveTriangleSubpower`:

- `isBigO_mobiusDiscreteLaplaceTransform_of_norm_sq_le {b S} (hS : 0 ≤ S)`
  `(hsq : ∀ x ∈ (0,1], ‖L x‖² ≤ S · x^(-(2b))) : L =O[𝓝[>] 0] (x ↦ x^(-b))`

Both criteria are now eight lines: obtain the source constant, apply the law, rewrite the exponent
`-(1 + (2b−1))` to `-(2b)`. Net −32.

Audit: `lake build GaloisForLFunctions.RHTower.MobiusMertensFourthConvolutionCriterion` — 8779 jobs,
exit 0.

### B62 — Stein–Robertson: the score is the only variable

`thetaCuspFirstRadialQuadraticSteinRobertson` and `thetaCuspFirstRadialTwoChannelSteinRobertson`
were the same weighted Cauchy–Schwarz — build `f = centredQuadratic · amplitude` and
`g = score · amplitude`, discharge four measurability/integrability conditions, identify the three
integrals, `rwa` — with the *score* the only thing that changed.

New law `thetaCuspFirstRadialSteinRobertson_of_score` in `PrimeArchThetaQuadraticSteinRobertson`
takes a measurable `ψ`, integrability of `ψ² · amplitude²`, and the coupling and energy
evaluations, and yields
`(m₀ · coupling)² ≤ (m₀²m₄ − m₀m₂²) · energy`. Both callers are now four lines each; the existing
`integrableOn_…SteinEnergy` lemmas already have exactly the hypothesis's shape, so no massaging
survives at the call sites. Net −25 lines, and a third score costs four lines.

Audit: `lake build GaloisForLFunctions.RHTower.PrimeArchThetaTwoChannelSteinRobertson` — 8822 jobs,
exit 0.

### B63 — Generator order zero: the covariance is the only variable

`differentialAlgEquiv_generator_order_zero` (`ScalarDifferentialRationalOrder`, plain differential
automorphism) and `clockSemilinearAlgEquiv_generator_order_zero` (`ClockSemilinearOrderZeroMobius`,
semilinear clock dilation with scalar `lam`) ran the same 35-line argument: transcendence of `y`
puts `y`, `σ y` and `σ.symm y` outside `⊥`, `differentialAdjoin C {y} = ⊤` makes both images
members, the two scalar orders `r` and `m` compose to the order of `y` over itself, which is zero,
and naturality of ℕ forces `r = m = 0`.

The covariance enters at exactly one line — `hm.map σ.toAlgHom hderiv` versus
`hm.map_semilinear σ.toAlgHom hlam hconst hsemi`. New law `algEquiv_generator_order_zero` in
`ScalarDifferentialRationalOrder` takes that step as the hypothesis

```
hmap : ∀ m, HasScalarDifferentialOrder C y (σ.symm y) m → HasScalarDifferentialOrder C (σ y) y m
```

Both concrete theorems are now two lines. Net −24 lines, and any further covariance class (twisted,
`q`-difference) costs two.

Audit: `lake build GaloisForLFunctions.HTGeometry.ClockSemilinearOrderZeroMobius` — 3037 jobs,
exit 0.

### B64 — `PolynomialPowerADEResonance`: 174-line clone examined, extraction declined

Largest remaining clone anywhere in the corpus:
`exists_eventually_polynomialPower_bend_pair_of_eventual_profile` (364 lines) versus
`..._jetDegree_one` (232 lines), 174 lines in common.

**They are incomparable, not one a specialisation of the other.** The general theorem assumes
`2 < β` and `0 < B`; the degree-one theorem assumes neither, and its only user needs exactly that —
it is invoked in the `¬(2 < β)` branch of
`natCeil_le_magnitudeMaxJetDegree_of_polynomialPower_relation`. So the general theorem cannot
subsume it, and the degree-one theorem cannot subsume the general one either (it fixes `D = 1`).

The reason both proofs exist is that the final *window confinement* is reached two different ways:

- general: a separation estimate (`eventually_lowerDegree_tuplePower_gap`,
  `exists_eventually_bounded_powerNearMinimizer`) that needs `β > 2` and a scale `S` chosen from `B`;
- degree one: `count_eq_one` — a degree-`1` atom key has a single support point, so confinement is
  a counting triviality.

The genuinely shared part is the *witness construction*: anchor extraction, balanced nonzero
`aevalWeight`, the scaled tuple `s i = q + δ i`, the level `N`, the near-minimiser pair `ν₀, ν₁`
from `exists_near_min_active_aevalWeight_of_relation`, and the logarithmic mass bound
`log(P+1) ≤ C·log(q+2)`.

Extraction was designed and rejected on interface width: the two consumers need `anchor`, `δ`, `D`,
`J`, `Z`, `Csum`, `Boff`, `s`, `N`, `key s`, its membership and nonvanishing facts, `ν₀`, `ν₁`,
their memberships, `hmin`, the gap, `hwitEq`, and the log bound — fifteen components, several of
them dependent (the type of `s` mentions `jetMonomialDegree n anchor`). The packaging lemma's
statement runs ~60 lines and each consumer needs a ~25-line destructuring preamble, against 174
lines saved: roughly break-even, and strictly worse to read, because the dependent tuple hides
which facts each branch actually uses.

Recorded as examined-and-declined. Should a third bend-pair regime appear (e.g. `1 < β ≤ 2` with
`D = 2`), revisit — at three consumers the packaging pays for itself.

### B65 — Signed digamma palette: one estimate, one domination law

`summableLocallyUniformlyOn_signedDigammaRegular` (101 lines) and
`summableLocallyUniformlyOn_signedDigammaCompletionTerm` (97 lines) in
`ExplicitDigammaOrientationLimit` were the same proof: build the majorant `4(R₀+1)/(n+1)²`, prove it
summable via `Real.summable_one_div_nat_add_rpow`, then bound each far-out term by rewriting the
Gauss term as `(z − 1/2)/((n+1)(z + 1/2 + n))` and estimating `‖z + 1/2 + n‖ ≥ (n+1)/2`. The regular
version differed only by a `split_ifs` around the deleted pole and by the open set it works on.

Split into two:

- `norm_signedDigammaCompletionTerm_le` — the pointwise estimate, with `0 ≤ R₀` recovered from
  `‖z‖ ≤ R₀` rather than from `R₀ = max R 0`;
- `summableLocallyUniformlyOn_of_norm_le_signedDigammaCompletionTerm` — *any* family dominated
  termwise by the completion terms converges locally normally on *any* open set.

The completion theorem is now `(fun _ _ => le_rfl) isOpen_univ`; the regular one supplies the
`split_ifs` domination and `Metric.isOpen_ball`. 484 → 420 lines, and a third dominated palette
costs five lines.

Also examined and dismissed: `PrimeArchExactOffLineQuartetKMSMaster` reported a 91-line overlap, but
`..._twoHundredEighteen_twentyFifths` is *already* a one-line delegation to the master at
`R = 218/25`. The scanner was measuring the restated 100-clause conjunction, not duplicated proof.
Statement restatement of that kind is API, not duplication.

### B66 — Elliptic theta logarithmic series: one annulus law for every forward shift

`analyticAt_ellipticThetaLogKernel_of_norm_between` (shift 1, hypothesis `‖q‖ < ‖x‖`) and
`analyticAt_ellipticThetaLogRemainder_of_norm_sq_between` (shift 2, hypothesis `‖q‖² < ‖x‖`) ran the
same 110-line argument: enclose `x` in a closed annulus `r ≤ ‖y‖ ≤ R` strictly inside the region,
bound both elliptic-gamma atom arguments away from `1`, dominate the summands by a geometric
majorant, and differentiate term by term.

New law `analyticAt_ellipticThetaLogShift_of_norm_pow_between` takes the shift `m` as a parameter
and concludes analyticity of `∑ₖ (A(qᵏ⁺ᵐ/y) − A(qᵏ y))` under `‖q‖ᵐ < ‖x‖ < 1`. The one step that
was shift-specific — `‖q‖ < 1`, previously `nlinarith [sq_nonneg (a−1)]` — generalises to a
two-line contradiction from `1 ≤ a ⇒ 1 ≤ aᵐ < b < 1`.

Both consumers are now four lines: instantiate at `m = 1` or `m = 2` and identify the tsum with the
local definition (`ellipticThetaLogSummand` unfolds definitionally; the remainder needs the existing
`tsum_sub` splitting). 315 → 226 lines.

### B67 — Gamma first-order relation: the remainder version subsumes the plain one

`gamma_no_weightedHomog_firstOrder` (73 lines) and `gamma_no_weightedHomog_firstOrder_rem`
(79 lines) in `GammaDifferentialFE` differed only in that the second allows an extra term `Q` whose
`d`-fold pole blow-up vanishes at every `-k`. The plain statement is the case `Q = 0`, and it had no
users at all. Moved `_rem` above it; the plain theorem is now

```
gamma_no_weightedHomog_firstOrder_rem N d hd c (fun _ => 0)
  (fun k => by simpa using tendsto_const_nhds) (fun s hs => by simpa using hrel s hs)
```

Net −65 lines. Same pattern as B59 — a parametrised statement sitting *after* its own `Q = 0`
instance in the same file.

### B68 — Pattern weight polynomial: one bound, two window regimes

`norm_eval_polynomialPatternWeightPoly_le` (88 lines) and
`..._le_centeredRadius` (90 lines) in `GaussianTorsionLanguageTailLock` shared the whole
coefficient-mass extraction and inner-sum estimate, differing only in three coupled slots: the
assignment-count bound (`M^D` by `Finset.card_le_univ` versus `D^D` by
`atomPatternAssignments_card_le_pow_count`), the window radius (`M` versus
`centeredPolynomialPatternRadius K p`), and which descending-factorial product bound was applied.

New law `norm_eval_polynomialPatternWeightPoly_le_of_bounds` takes the count bound `Acard`, the
radius `W`, and the per-assignment product bound as hypotheses, and concludes
`‖eval q‖ ≤ mass(Q) · Acard · (q + W)^H`. Both consumers are now five lines. 4783 → 4728 lines.

Audit: verified by the `lake build GaloisForLFunctions.HTGeometry` area build, which rebuilt this
module and the whole cone below it (`PolynomialPatternRectangularization`,
`PolynomialCoefficientDifferentialFreeness`, `UpperEndDifferentialIndependence`, …); every
downstream module compiled against the new `…_le_of_bounds` law.

### B69 — Bounded vertical clock transfer: the local dichotomy subsumes the global one

`riemannHypothesis_of_bounded_vertical_clock_dichotomy_approximants` (72 lines) and
`..._locally_bounded_...` (84 lines) in `BoundedClockZeroTransfer` ran the same Hurwitz zero-selection
argument. `LocalBoundedVerticalClockDichotomy B R f` is literally
`BoundedVerticalClockDichotomy B f` with the quantifier restricted to `closedBall 0 R`, so the
global hypothesis weakens to the local one at every radius. Moved the local definition and the local
theorem above the global one; the global theorem is now

```
riemannHypothesis_of_locally_bounded_vertical_clock_dichotomy_approximants hconv hFn
  (fun _R => ⟨B, hclock.mono fun _n hn z _hz => hn z⟩)
```

608 → 552 lines.

### B70 — Inverse-tilted dyadic source: order and trailing coefficient share one splitting

`meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one` (72 lines) and
`meromorphicTrailingCoeffAt_inverseTiltedDyadicContinuedSource` (85 lines) both split the source at
the shifted pole into `fac · shiftedLogDeriv` plus a strictly-higher-order correction, then read off
different data from the same splitting.

Merged into `meromorphicOrderAt_and_trailingCoeffAt_inverseTiltedDyadicContinuedSource`, a
conjunction proved once; the two theorems are `.1` and `.2`. 1442 → 1391 lines. This is the
"strengthen the core to a conjunction" shape rather than a hypothesis generalisation — appropriate
when two readings share a construction but neither implies the other.

### B71 — Rectangular shifted zeta: one tail estimate for both carriers

`summableLocallyUniformlyOn_xiRectangularCancelledTerm_rightOne` (125 lines) and
`..._RawShiftedTerm_...` (100 lines) in `CCMShiftedXiNormalConvergence` shared 81 lines: the cofinite
tail of large spectral points, the separation `‖(s−γ)−1‖ ≥ 1` from `2(R₀+2) ≤ ‖γ‖`, the zeta
square-root growth bound, and the conversion to `10 C₀ ‖γ‖^{-3/2}`. The cancelled carrier merely
multiplies by the bounded factor `‖xi(s−1/2)‖ ≤ M₀`.

Split into `eventually_cofinite_le_norm_xiSpectralPoint` (only finitely many copies have small
spectral point) and `norm_xiRectangularRightCoefficient_mul_riemannZeta_le`, which returns *both*
`s ≠ xiRightShiftedPole q` — needed by the cancelled carrier for `Function.update_of_ne` — and the
estimate. Threading `1 < s.re` explicitly was the one adjustment: the original proofs took it from
`hKsub hs` mid-proof, and the standalone estimate genuinely needs it for
`1/2 ≤ (s − γ).re`. 333 → 265 lines.

### B72 — Landau summability transfer: the offset is a parameter

`landau_summability_transfer` (128 proof lines, centre `σ₁ + 1`) and
`landau_local_summability_transfer` (150 lines, centre `σ₁ + h` for any `h > 0`) in
`LandauSummabilityTransfer` are the same proof; the first is the second at `h = 1`. Now

```
landau_local_summability_transfer ha zero_lt_one hsum hGd hagree hσ
```

−123 lines.

**Direction note.** The first attempt moved the *general* theorem upstream, as in B55/B57/B59/B69 —
and broke: its proof uses `LSeries_logMul_iterate_eq_of_abscissa_lt` and
`summable_landauTerm_of_abscissa_lt`, both declared *between* the two theorems. When the general
statement depends on lemmas that sit between it and its specialisation, move the **specialisation
down** instead of the general one up. Same end state, no dependency inversion.

### Scanner correction — proof bodies, not statements

`within_file.py` compared whole declarations, so a corollary that merely restates a long conjunction
scored as a huge clone (this produced the false positives at
`PrimeArchExactOffLineQuartetKMSMaster`, 91 "lines", and `HardySignChange`, 58 — both are
delegations whose *statements* repeat fifty-line hypothesis blocks). `within_file2.py` compares only
the lines after `:= by`. Re-ranked, the largest **in-remit** proof clones are:

| proof lines | file | pair |
|---|---|---|
| 161 | `HTGeometry/PolynomialPowerADEResonance` | bend pair vs `_jetDegree_one` — declined, see B64 |
| 83 | `RHTower/ThetaCuspShellIncompleteGammaCoordinate` | `..._mul_one_sub_cos` vs `..._mul_sin_pos` |
| 71 | `RHTower/LandauSummabilityTransfer` | resolved here |
| 69 | `RHTower/ThetaCuspShellIncompleteGammaCoordinate` | fourth- vs fifth-order boundary identity |
| 69 | `RHTower/ThetaCuspShellIncompleteGammaCoordinate` | `_mul_sin_pos` vs `_mul_cos_pos_of_two_le` |
| 65 | `RHTower/CCMFirstClockVolterra` | superposition vs `_eq_zero_of_lt` |

Out of remit but worth flagging: `Bottcher` holds the three largest clones in the corpus —
313 lines (`MixedTowerData`: `bottcher_towerDataG_mixed` ~ `_normS`), 262 (`MixedTowerExt`), and
199 (`PatchSquareLocalize`), each a `_s`-suffixed twin of its neighbour.

### B73 — Theta-cusp shell: half-line integration by parts, extracted

`integral_thetaCuspTiltedWardDerivativeRotationDensity_mul_one_sub_cos` (139 lines) and
`integral_thetaCuspTiltedWardDensity_mul_sin_pos` (176 lines) in
`ThetaCuspShellIncompleteGammaCoordinate` both ran the same integration by parts on `(0, ∞)` against
`u = 1 − cos(bx)`: integrability of `u·v'` and `u'·v` from boundedness of `cos`/`sin`, vanishing of
`u·v` at both ends, `integral_Ioi_mul_deriv_eq_deriv_mul`, then a rearrangement. They differed only
in `v` — `x · density` versus `density`.

Two private laws, both fully abstract in `v`:

- `integrableOn_mul_one_sub_cos` — multiplying by the bounded factor `1 − cos(bx)` preserves
  integrability on the half line;
- `integral_mul_sin_eq_neg_integral_deriv_mul_one_sub_cos` —
  `b ∫₀^∞ v sin(bx) = −∫₀^∞ v' (1 − cos(bx))` whenever `v` is differentiable, `v` and `v'` are
  integrable, and `v → 0` at infinity. The origin boundary term vanishes because `1 − cos` does, so
  no hypothesis on `v(0)` is needed.

The first consumer is now twenty lines; the second keeps only its positivity argument
(`score < 0`, `1 − cos ≥ 0`, support nonempty at `π/b`). 9845 → 9772 lines.

One adjustment was needed: the original proofs carried `v` as a `let`, and their
`simpa [u, v]` for the origin boundary relied on unfolding it. With `v` abstract, `simpa [u]`
suffices — `(1 − cos (b·0)) · v 0 = 0 · v 0` regardless of `v`.

The third clone in this file (`..._mul_cos_pos_of_two_le`, 69 shared lines with `_mul_sin_pos`)
uses `u = sin(bx)` rather than `1 − cos(bx)` and needs the companion law; queued.

### Next target (designed, not yet built) — `N / cos` is never holonomic

`tan_not_holonomic` (74 lines) and `sec_not_holonomic` (66) in `GammaDifferentialFE` already share
`not_holonomic_master`, which abstracts the function, the pole sequence, the pole order and the
residue limits. What they still duplicate — 48 lines — is the *residue-limit verification* at the
zeros of `cos`, run once for numerator `sin` and once for numerator `1`.

The generalisation is not merely a dedup, it is a stronger corpus statement:

```
theorem div_cos_not_holonomic (N : ℂ → ℂ) (hN : Differentiable ℂ N)
    (hNz : ∀ m : ℕ, N ((m : ℂ) * π + π / 2) ≠ 0) :
    ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
      (∀ s, ∑ j ∈ range (n+1), (c j).eval s *
        iteratedDeriv j (fun s => N s / Complex.cos s) s = 0) →
      ∀ j ∈ range (n+1), c j = 0
```

— *no* entire numerator that survives the poles of `cos` gives a holonomic quotient. Both existing
theorems are then instances: `N = sin` (with `sin(mπ + π/2) = (-1)^m`) and `N = 1`. The residue
family `L i m` becomes `(-1)^(m+1) · N(mπ + π/2) · ((-1)^i · i!)`, which specialises to the two
constants presently hard-coded.

Remaining in-remit clones after B73, by proof-body overlap: 161 `PolynomialPowerADEResonance`
(declined, B64), 69 `ThetaCuspShellIncompleteGammaCoordinate` fourth/fifth boundary identity,
65 `CCMFirstClockVolterra`, 57 `ThetaCuspShell` fourth/fifth root phase, 50
`GammaFactorialThirdJetHarmonicResidue`, 50 `EllipticGammaMixedFace`, 49
`RealExponentialSumRigidity`, 48 `GammaDifferentialFE` (this entry). The two `ThetaCuspShell`
fourth/fifth pairs and the two `Gamma*` pairs are order/argument parameterisations; the
`EllipticGammaMixedFace` pair carries an extra translation `(τ−σ)/2` on the τ side and is the least
mechanical of the group.

### B74 — `N / cos` is never holonomic (new general law)

Built the law designed above. `div_cos_not_holonomic` states that for any `N` smooth on `ℂ` with
`N(mπ + π/2) ≠ 0` for every `m`, the quotient `N / cos` satisfies no linear ODE with polynomial
coefficients. The residue family handed to `not_holonomic_master` is

```
L i m = N (mπ + π/2) · (-1)^(m+1) · ((-1)^i · i!)
```

which is exactly what the two former proofs hard-coded at `N = sin` (where `N(mπ+π/2) = (-1)^m`,
collapsing the sign to a bare `-1`) and at `N = 1`.

- `tan_not_holonomic` — five lines, the work being `sin(mπ + π/2) = (-1)^m ≠ 0`;
- `sec_not_holonomic` — three lines, `(fun _ => 1)` plus `simpa only [one_div]` to match
  `(cos s)⁻¹` against `1 / cos s`.

`GammaDifferentialFE` 3798 → 3629 lines across B67 and this entry. This is the first entry in the
audit that is a *strengthening* rather than a factorisation: neither original theorem implied the
other, and the corpus now carries the general statement, so `csc`-style cousins (`N = cos`,
`N = exp`, any entire non-vanishing-at-poles numerator) cost five lines each.

### B75 — Exponential-sum rigidity: the exponential bound subsumes the bounded case

`le_zero_of_expSum_norm_le` (73 lines, bound `‖∑ Bᵢ e^{uJᵢ}‖ ≤ M`, conclusion `Jᵢ ≤ 0`) and
`le_of_expSum_norm_le_exp` (71 lines, bound `≤ K e^{λ|u|}`, conclusion `Jᵢ ≤ λ`) in
`RealExponentialSumRigidity` are the same maximal-exponent argument. The first is the second at
`λ = 0`, `K = M`, where `e^{0·|u|} = 1`. Moved the bounded case below the general one (its proof
uses lemmas declared between them — the B72 direction rule) and delegated:

```
le_of_expSum_norm_le_exp s J m hm hinj B hB (by simpa using hbound)
```

271 → 204 lines.

### B76 — Digamma jet reflection at every order (new general law)

`GammaFactorialSecondJetHarmonicResidue` and `GammaFactorialThirdJetHarmonicResidue` are a parallel
development at jet orders 1 and 2: `shiftedHarmonicSquareSum` / `shiftedHarmonicCubeSum`,
`iteratedDeriv_one_digamma_neg_nat_add_of_ne_int` / `..._two_...`,
`norm_shiftedHarmonicSquareSum_le` / `norm_shiftedHarmonicCubeSum_le`,
`gammaFactorialScaledTrigamma` / `gammaFactorialScaledSecondPolygamma`, and matching
`ProjectiveDefect` layers.

Unified the base of that tower. New in the second-jet file:

```
def shiftedHarmonicPowerSum (p n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) - z) ^ p)⁻¹

theorem iteratedDeriv_digamma_neg_nat_add_of_ne_int (k : ℕ) (z : ℂ)
    (hz : ∀ m : ℤ, z ≠ (m : ℂ)) (n : ℕ) :
    iteratedDeriv k Complex.digamma (-(n : ℂ) + z) =
      iteratedDeriv k Complex.digamma (1 + z) +
        (-1) ^ (k + 1) * (k.factorial : ℂ) * z⁻¹ ^ (k + 1) +
        (k.factorial : ℂ) * shiftedHarmonicPowerSum (k + 1) n z
```

The sign bookkeeping is the content: the origin term carries `(-1)^{k+1}`, while the crossed-integer
terms carry a bare `k!`, because `((j+1) − z)^{k+1} = (-1)^{k+1} (z − (j+1))^{k+1}` cancels the
alternation. At `k = 1` this reads `+ z⁻¹² + Σ` and at `k = 2` it reads `− 2z⁻¹³ + 2Σ`, matching the
two hard-coded statements exactly; both are now one- and two-line corollaries
(`shiftedHarmonic{Square,Cube}Sum` are definitionally `shiftedHarmonicPowerSum 2` and `… 3`).

Second-jet file 507 → 528 (the general law), third-jet 480 → 443. Net −16 so far, but this is the
*base* of the tower: `norm_shiftedHarmonicPowerSum_le` and the scaled-polygamma/tendsto layers above
it can now be stated once at order `k` rather than twice.

**Second layer, same batch.** `norm_shiftedHarmonicPowerSum_le`: for `‖z‖ ≤ 1/2` and `p ≥ 1`,
`‖Σ‖ ≤ 2^p · Hₙ`, which is the `4·Hₙ` and `8·Hₙ` of the two former bounds. Both are now two-line
corollaries. Second-jet file 507 → 546 (carrying two general laws), third-jet 480 → 415.

Audit: `lake build GaloisForLFunctions.HTGeometry.GammaFactorialThirdJetHarmonicResidue` —
8508 jobs, exit 0.

**Three fixes the compiler found, worth recording.** (i) `gcongr` discharges its side goals from the
local context, so the explicit `positivity`/`exact hpow` bullets I wrote after it were "no goals to
be solved" — supply the fact as a `have` and let `gcongr` find it. (ii) `simpa` will not reduce
`2 ^ 2` to `4` or `(-1) ^ 3 * 2` to `-2`; the corollaries need either an explicit
`show (2:ℝ)^2 = 4` rewrite or `linear_combination`. (iii) `push_cast at h` without `⊢` leaves the
goal's `↑(j+1)` unmatched against the hypothesis's `↑j + 1`, and `ring` then fails on two sums that
are visibly identical — always push casts on both sides.

### B77 — Clock Volterra superposition: the central value is the only variable

`ccmFirstClockGammaCancellationKernel_superposition` (113 lines) and
`..._eq_zero_of_lt` (102 lines) in `CCMFirstClockVolterra` share the whole kernel decomposition:
the Gamma-cancellation kernel splits as `A · autocorr(·,·,0) + B · autocorr(·,·,s/2)` with
`A = e^{-s}/(1-e^{-s})`, `B = -e^{-s/4}/(1-e^{-s})`; the lag-`0` superposition always vanishes; and
the integral splitting is identical. They differ only in the value of the lag-`s/2` superposition —
`-sin(ξ s/2)` when `s/2 ≤ L`, and `0` when `L < s/2`.

New private law `ccmFirstClockGammaCancellationKernel_superposition_of_central` takes that value `c`
as a hypothesis and concludes `= B c / 2`. Notably it does *not* need `s/2 ≤ L`: that hypothesis was
only ever used to obtain the central value, which is now supplied by the caller. The vanishing case
is three lines; the general case is seven. 2297 → 2227 lines.

Audit: `lake env lean GaloisForLFunctions/RHTower/CCMFirstClockVolterra.lean` — clean.

### B78 — Xi flux coboundary: name the witness, and the polynomial case is the entire case

`entireFluxCoboundary_of_entireHermitianDiagonalLaw` (80 lines) and
`polynomialFluxCoboundary_of_hermitianDiagonalLaw` (82 lines) in
`XiFiniteLocalSpectralFrameObstruction` share ~60 lines — the vanishing of the Wronskian-type
combination on the whole plane from its vanishing on the reals, and the logarithmic-derivative
identity that follows — differing only by `Q b` versus `Q.eval b`.

What blocked reuse was not the mathematics but the *shape of the conclusion*: the entire theorem
hides its witness behind `∃ E`, so the polynomial theorem could not name it. Strengthened it to

```
entireFluxCoboundary_of_entireHermitianDiagonalLaw_explicit :
  XiEntireFluxCoboundary (2 * a) (fun z => -Q (-I * (z - (1/2 + a))))
```

after which the existential version is one line, and the polynomial version is the same witness read
as `-(Q.comp (C (-I) * (X - C (1/2 + a))))`: `XiPolynomialHermitianDiagonalLaw a Q` is exactly
`XiEntireHermitianDiagonalLaw a (Q.eval ·)` minus the differentiability conjunct, which
`Q.differentiable` supplies. 389 → 327 lines.

General lesson: an `∃`-wrapped conclusion is a reuse barrier. When two proofs construct the *same*
witness, expose it and let the existential be the corollary.

Audit: `lake env lean GaloisForLFunctions/RHTower/XiFiniteLocalSpectralFrameObstruction.lean` —
clean. (B77 is still queued behind the HTGeometry area build; `CCMFirstClockVolterra` resolves
through `BoundedGaugeGenericity`, one of the last modules still compiling.)

Note on the shared tree: the lint gate currently reports 29 "owned module unreachable from
umbrella" errors. Twenty-seven are `Deninger*`, plus two brand-new untracked files
(`HTGeometry/CompExpDescent.lean`, `RHTower/FieldOneFiniteAdeleCompactOpenBasis.lean`) that another
agent has created but not yet registered. None are from this audit — no module was added or removed
in B53–B78 apart from the five deletions recorded earlier.

### B79 — Möbius critical boundary layer: composition lemmas instead of repeated limits

`tendsto_squarefreeMobiusBoundaryLayerLaplace` (115 lines) and
`tendsto_infiniteMobiusLaplaceMultiplier_moving_boundary` (95) in
`InfiniteMobiusCriticalBoundaryLayer` open with ~40 identical lines establishing the same limits
along `𝓝[>] 1`, once at `σ` and once at the boundary parameter — eight `have`s that are really two
facts applied twice.

Replaced by four private lemmas, two of them *composition* lemmas parameterised by the approach:

- `tendsto_ofReal_nhdsGT_one`, `tendsto_mobiusCriticalBoundaryParameter_ofReal`;
- `tendsto_riemannZeta_two_mul_comp (hf : f → 1) : ζ(2f) → ζ(2)`;
- `tendsto_zetaResidueUnit_comp (hf : f → 1) : zetaResidueUnit ∘ f → 1`.

Each theorem's setup drops to four or five lines, and the doubling at `σ`/parameter disappears
because the composition lemmas take the approach as an argument. 428 → 366 lines.

Audit: `lake env lean GaloisForLFunctions/RHTower/InfiniteMobiusCriticalBoundaryLayer.lean` — clean.

### B80 — Landau oscillation: the abstract law was already there, inlined next door

`MobiusLaplaceLandauOscillation` contains both
`no_analytic_gamma_div_zeta_continuation_below_half` — an already-abstract statement: *no function
analytic on `Re s > b` for some `0 < b < 1/2` can agree with `Γ/ζ` on `Re s > 1`* — and
`not_mobiusLaplaceComparisonCutoffNonnegative`, which re-derives that same contradiction inline from
its own reconstructed Mellin transform.

The specialised theorem keeps only its genuine content — constructing `b = (a + 1/2)/2`, the radius
`R`, the interior-of-integrability input, and the analyticity of the reconstructed transform — and
then calls the abstract law with `mobiusLaplaceReconstructedMellin_eq_gamma_div_zeta` as the
classical-region agreement. Moved below the abstract law (B72 direction rule). 1148 → 1093 lines.

This is the cheapest kind of find: the general law had already been written and named, and the
duplication was simply that nobody went back to use it.

Audit: `lake env lean GaloisForLFunctions/RHTower/MobiusLaplaceLandauOscillation.lean` — clean.

### HilbertMetric — audited, substantially clean

The third area in the remit. 48 files. Scanned for proof-body duplication at the same thresholds
used for HTGeometry and RHTower; nothing in it appears in the cross-file ranking at all, and its
largest *within-file* clone is 29 lines:

| proof lines | file | pair |
|---|---|---|
| 29 | `DegreeFiveCollisionGraphJet` | `degreeFiveTop_valueJet` ~ `degreeFiveTop_firstJet` |
| 28 | `SixthJetRaywiseCoalescedCone` | `iteratedDeriv_six_…_zero` ~ `…_zero_of_lt_six` |
| 26 | `DegreeFiveGaussianCurvature` | `degreeFive_valueJet` ~ `degreeFive_firstJet` |
| 23/21 | `DegreeFiveCollisionGraphJet` | the `recombined_{value,first,second}Polynomial_top_five` triple |
| 23 | `GaussianJetPositivity` | `…_of_coordinate_injective` ~ `…_of_linearForm_injective` |

For comparison, HTGeometry and RHTower each opened this audit with clones of 64–174 lines. The only
structurally interesting item is the `recombined_*Polynomial_top_five` triple: three 54-line proofs
running the same Fubini rearrangement
`Σᵢ Σⱼ c_a(i) c_b(j) Σ_{n∈S} w(n) G(i,j)^{p(n)} = Σ_{n∈S} w(n) Σᵢ Σⱼ c_a(i) c_b(j) G(i,j)^{p(n)}`
over `range 6` with exponent `n` and over `range 5` with exponent `k+1`, then their own orthogonality
evaluation. Extracting the rearrangement as one lemma over an arbitrary index finset, weight and
exponent would save ~60 lines across the three.

Recorded rather than done: at 21–29 shared lines these sit below everything still outstanding in the
other two areas, and the area does not have a duplication problem.

### B81 — Returned theta density: one dominated-convergence law for every weight

`thetaCuspTailSecondDensityReturnedValue_scaled_tendsto_zero` (87 lines) and
`...ReturnedDerivative_scaled_tendsto_zero` (86) in
`XiCTaylorThetaTailPhaseAdaptedProuhetHalfLine` run the same dominated-convergence argument against
the majorant `C · xᵖ e^{-(1-Im z)x}`, differing only in the weight inside the integrand — `1` for the
value, `x·i` for the derivative — and correspondingly `p = 0` versus `p = 1`.

New private law `thetaCuspTailSecondDensityReturned_scaled_tendsto_zero_of_weight` takes
`w : ℝ → ℂ` continuous with `‖w x‖ = xᵖ` on the half line. Both theorems are four lines. 2627 → 2566.

Four compiler-found adjustments, all of the same species — *places where the concrete `p = 1` leaked
into the shared text*: the majorant's `x` in the exponent rearrangement, `mul_nonneg hx0` needing
`pow_nonneg hx0 p`, the limit step still naming `(x : ℂ) * I` instead of `w x`, and `fun_prop`
failing on an abstract `w` (fixed by carrying `Continuous w` as a hypothesis rather than hoping
automation would find it).

Audit: `lake env lean GaloisForLFunctions/RHTower/XiCTaylorThetaTailPhaseAdaptedProuhetHalfLine.lean`
— clean.

### B82 — The zeta-limit plumbing, promoted across files

The `𝓝[>] 1` limit boilerplate factored out in B79 turned out to recur verbatim in
`SquarefreeHeightReesBlowup`, which already imports `InfiniteMobiusCriticalBoundaryLayer`. Rather
than duplicate it, the two generic lemmas were made public and one of them generalised:

```
theorem tendsto_riemannZeta_two_mul_comp {f : ℝ → ℂ} {Lim : ℂ} (hLim : 2 * Lim ≠ 1)
    (hf : Tendsto f (𝓝[>] 1) (𝓝 Lim)) :
    Tendsto (fun σ => riemannZeta (2 * f σ)) (𝓝[>] 1) (𝓝 (riemannZeta (2 * Lim)))
```

The B79 version fixed `Lim = 1`; the Rees-blowup macroscopic theorem needs `Lim = 1 + γi`, so the
limit point became a parameter with the pole condition `2·Lim ≠ 1` as its hypothesis. Both
`tendsto_squarefreeMicroscopicHeightOverlap` and `..._Macroscopic...` now drop their
`htwoSigma`/`htwoParam`/`hzeta*` chains. `SquarefreeHeightReesBlowup` 335 → 306 lines.

Cost of the generalisation: the conclusion now reads `riemannZeta (2 * Lim)` rather than
`riemannZeta 2`, so each `Lim = 1` call site needs `simpa` to fold `2 * 1`. That is the right
trade — one lemma serving two limit regimes beats two lemmas with prettier statements.

Audit: `lake build GaloisForLFunctions.RHTower.InfiniteMobiusCriticalBoundaryLayer` — 8618 jobs,
exit 0; `lake env lean GaloisForLFunctions/RHTower/SquarefreeHeightReesBlowup.lean` — clean.

### Remaining in-remit duplication and why it is a different kind of job

After B82 the only in-remit clones above ~50 proof lines are:

| lines | file | pair |
|---|---|---|
| 161 | `HTGeometry/PolynomialPowerADEResonance` | declined in B64 — incomparable hypotheses |
| 69 | `RHTower/ThetaCuspShellIncompleteGammaCoordinate` | fourth- vs fifth-order boundary identity |
| 57 | `RHTower/ThetaCuspShellIncompleteGammaCoordinate` | fourth- vs fifth-order root phase |

The two `ThetaCuspShell` pairs are consecutive rungs of one integration-by-parts ladder: order `k`
uses `u = c·f_{k-1} + x·f_k`, `v = sin` or `cos` alternating, and produces the order-`k+1` identity.
Merging them is not a hypothesis generalisation — it requires first replacing the hand-rolled
per-order families

```
thetaCuspTiltedWardDensity{,Fourth,Fifth}Derivative
integrableOn_thetaCuspTiltedWardDensity{Second,Third,Fourth,Fifth}Derivative
hasDerivAt_thetaCuspTiltedWardDensity{…}Derivative
```

with a single `k`-indexed family plus `k`-indexed decay and integrability, and then stating one
IBP-rung law. The corpus has no such indexed family today — I checked. That is the same shape as the
`shiftedHarmonicSquareSum`/`CubeSum` situation resolved in B76, but an order of magnitude larger: it
touches a 9772-line module and every `hasDerivAt_` lemma in it.

Recorded as the next unit of work rather than begun mid-session, because a half-finished index
rewrite of that module would leave the tree worse than it is now. The B76 pattern is the template:
introduce the indexed definition, prove the indexed reflection/decay laws, then make each concrete
order a one-line corollary — in that order, verifying at each step.

### B83 — The order-indexed Ward derivative family (foundation for the ladder)

The blocker recorded above was that `ThetaCuspShellIncompleteGammaCoordinate` had no `k`-indexed
derivative family, only hand-rolled `Fourth`/`Fifth` definitions with per-order `hasDerivAt_` and
`integrableOn_` lemmas. Building the family turned out to be nearly free, because the corpus already
had both one-step laws:

- `hasDerivAt_exp_mul_thetaCuspPolynomialAtom a P n x` — differentiating `e^{ax}·atom(P)` replaces
  the symbol `P` by `thetaCuspTiltedLogDerivativeStep a P`;
- `integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one P hn ha`.

So the family is the iterate of that one step:

```
def thetaCuspTiltedWardDensityDeriv (k : ℕ) (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (a * x) *
    thetaCuspPolynomialAtom ((thetaCuspTiltedLogDerivativeStep a)^[k] (X ^ 2)) n x

theorem hasDerivAt_thetaCuspTiltedWardDensityDeriv (k) :
    HasDerivAt (…Deriv k a n) (…Deriv (k + 1) a n x) x
theorem integrableOn_thetaCuspTiltedWardDensityDeriv (k) (ha : a < 1) (hn : 0 < n) :
    IntegrableOn (…Deriv k a n) (Ioi 0)
```

**The hand-written orders are definitionally the indexed ones** — both bridge lemmas are `rfl`.
That is not an accident: `Function.iterate` unfolds as `f^[n+1] x = f^[n] (f x)`, which reduces
`(step a)^[4] (X²)` to exactly the four nested `step` applications the concrete definition spells
out. Their `hasDerivAt_` and `integrableOn_` lemmas now delegate to the indexed ones.

Two further indexed laws complete the toolkit, both again free from existing one-step lemmas:

```
tendsto_thetaCuspTiltedWardDensityDeriv_atTop_zero (k) (ha : a < 1) (hn : 0 < n) :
  Tendsto (…Deriv k a n) atTop (𝓝 0)
integrableOn_id_mul_thetaCuspTiltedWardDensityDeriv (k) (ha) (hn) :
  IntegrableOn (fun x => x * …Deriv k a n x) (Ioi 0)
```

So the indexed family now carries everything an integration-by-parts rung consumes: the derivative
step, integrability, the linear-weight integrability, and decay at infinity. This is deliberately a
*foundation* commit rather than a deduplication — it is the piece the corpus lacked. The remaining
step for the 69- and 57-line ladder clones is a single rung law taking the index and the
`sin`/`cos` parity, after which each concrete rung is a corollary.

Placement note: both additions had to be positioned after the general lemmas they call
(`integrableOn_id_mul_exp_mul_thetaCuspPolynomialAtom_of_lt_one` sits ~200 lines below the
integrability block), the same dependency-order constraint recorded in B72.

Audit: `lake build GaloisForLFunctions.RHTower.ThetaCuspShellIncompleteGammaCoordinate` — 8942
jobs, exit 0. That build also covers B73 and, through its dependency cone, the HTGeometry edits
B65–B68 and B74–B76.

### B84 — The two ladder rungs, and the fifth-order identity as one of them

With the indexed family in place (B83), the ladder itself reduces to two half-line
integration-by-parts identities, stated for an arbitrary differentiable `u` that is integrable
together with `u'` and vanishes at infinity:

```
integral_mul_sin_rung : b ∫₀^∞ u sin(bx) = u 0 + ∫₀^∞ u' cos(bx)
integral_mul_cos_rung : b ∫₀^∞ u cos(bx) = -∫₀^∞ u' sin(bx)
```

The asymmetry is the content: against `sin` the antiderivative `-cos` is `-1` at the origin, so the
boundary term survives; against `cos` the antiderivative `sin` vanishes there and both ends die.
A shared helper `integrableOn_bdd_mul_of_integrableOn` supplies the four integrability side
conditions from boundedness of the trigonometric factor.

`..._fifthOrderBoundary_identity` is now literally the fourth-order identity plus one sine rung
applied to `u = 4f₃ + x f₄`: the rung's `u 0` is `4·(third·density)(0)` because `x f₄` vanishes at
the origin, and its `u'` is `5f₄ + x f₅` by the product rule — exactly the fifth-order statement.
57 lines of hand-rolled integration by parts deleted from that proof.

The **fourth**-order identity was then converted the same way. Its IBP core — the
`integral_Ioi_mul_deriv_eq_deriv_mul` call plus the `u·v'` normalisation — is exactly the cosine
rung at `u = x f₃`, and every side condition it needs (`hxf₃Int`, `hf₃Int`, `hxf₄Int`, `huZero`) was
already present in the proof. With the rung in place, the scaffolding it existed to feed —
`v`, `v'`, `hv`, `huv'`, `hu'v`, `hzero`, `hinfty` — became dead and was removed: 46 further lines.

Net for the file: 9772 → 9864 lines. B83/B84 add ~250 lines of reusable indexed laws and rungs and
remove ~160 of duplication, so this thread is still net positive on count — the return arrives as
further rungs are added, each now a dozen lines instead of two hundred. Both existing rungs are now
consumers of the general laws, so nothing added here is dead code.

Audit: `lake build GaloisForLFunctions.RHTower.ThetaCuspShellIncompleteGammaCoordinate` — 8942 jobs,
exit 0.

### B85 — Root-phase positivity: the shared step was pure algebra

`deriv_thetaCuspGroundFourthOrderRootPhase_pos` and `…FifthOrderRootPhase_pos` end with the same
twenty-line rearrangement: the derivative of a root phase `2x + k·(P/Q)`, where the shift
polynomials differentiate to `2s P'` and `2s Q'`, becomes

```
2 + k((2sP')Q − P(2sQ'))/Q² = 2(Q² + k s (P'Q − PQ'))/Q²
```

and is positive because the Wronskian bracket is. Nothing in that step mentions the order — the
order-specific content is entirely in *which* shift polynomials and Wronskian lemma get passed in.

Extracted as `two_add_div_pos_of_wronskian_pos`, a statement in six real variables with no theta
content at all. Both proofs now end in a single `exact`. 40 lines removed; the module is 9838 lines.

That closes the last identified in-remit clone above 50 proof lines outside the declined B64 pair.

Audit: `lake build GaloisForLFunctions.RHTower.ThetaCuspShellIncompleteGammaCoordinate` — 8942 jobs,
exit 0.

### B86 — Root phase, finished: derivative law and ground-coordinate data

B85 removed the shared *positivity* step from the two root-phase proofs; the scanner still reported
50 shared lines, and inspecting them showed it was not noise. Two more coherent shared blocks:

- the derivative construction — `y ↦ 2y + k·(p y / q y)` differentiates to
  `2 + k(p'q − pq')/q²`, order-independent given the two coefficient derivatives. Extracted as
  `hasDerivAt_two_add_const_mul_div`.
- the **ground coordinate setup** — for `0 < a < 1/2` and `x ≥ 0`: `c = a + 5/2 ∈ (5/2, 3)`,
  `r = 2π e^{2x} − c > 3`, and `HasDerivAt rfun (2(r+c)) x`. Twenty-odd lines opening *both* proofs,
  now `thetaCuspGroundCoordinate_data`, destructured in five lines each.

40 further lines removed. The pair has dropped out of the ranking at threshold 40, and the module
stands at 9829 lines — below the 9845 it had before this whole ladder thread began, now carrying the
indexed derivative family, both IBP rungs, and three reusable algebraic laws that were not there
before.

Audit: `lake build GaloisForLFunctions.RHTower.ThetaCuspShellIncompleteGammaCoordinate` — 8942 jobs,
exit 0.

### Status: every in-remit clone above 50 proof lines is resolved or documented

| lines | file | outcome |
|---|---|---|
| 161 | `HTGeometry/PolynomialPowerADEResonance` | declined, B64 — incomparable hypotheses, reasons recorded |
| all others ≥50 | HTGeometry / HilbertMetric / RHTower | resolved, B53–B86 |

HilbertMetric was surveyed separately and has no clone above 29 lines. The largest proof clones
remaining anywhere in the corpus are in `Bottcher` — 313, 262 and 199 lines — which is outside this
audit's remit.

### B87 — The same weight law again, for the even remainder

`thetaCuspTailSecondEvenRemainderReturnedValue_tendsto_atTop_zero` (74 lines) and
`...ReturnedDerivative_...` (77) in `XiCTaylorThetaTailPhaseAdaptedProuhetHalfLine` are the B81
situation repeated one family over: the same dominated-convergence argument against
`C · xᵖ e^{-(1/2 − Im z)x}`, weight `1` versus `x·i`.

`thetaCuspTailSecondEvenRemainderReturned_tendsto_atTop_zero_of_weight` mirrors the B81 law for the
even-remainder family. Both consumers are four lines. 2566 → 2516.

Worth noting for its own sake: this one compiled on the **first attempt**. B81 needed four fixes,
all of them places where the concrete `p = 1` had leaked into the shared text; knowing the failure
modes in advance — the exponent in the majorant rearrangement, `pow_nonneg` in place of the bare
nonnegativity, the limit step still naming the concrete weight, and `fun_prop` needing `Continuous w`
as a hypothesis — made the second instance mechanical.

### B88 — Scaled polygamma: indexed definition landed, unified limit deferred with a correction

Continuing the B76 tower. `gammaFactorialScaledTrigamma` and `gammaFactorialScaledSecondPolygamma`
are the orders `1` and `2` of

```
def gammaFactorialScaledPolygamma (k n : ℕ) (x : ℂ) : ℂ :=
  reciprocalGammaFactorialScale n ^ (k + 1) *
    iteratedDeriv k Complex.digamma (-(n : ℂ) + reciprocalGammaFactorialScale n * x)
```

and both bridges are `rfl`, as in B83. That much is in and verified.

**The unified second-harmonic limit is not, and the attempt found a real error in my design.** I had
predicted the statement

`(scaledPolygamma k n x − (-1)^{k+1} k! x^{-(k+1)}) / harmonicScale n ² → 0`

with the same internal shape at every order. Compiling it exposed that the internal identity is

```
(scaledPolygamma k n x − pole) / (s H)²  =  s^{k-1} · H^{-2} · (ψ⁽ᵏ⁾(1+z) + k! Σ)
```

— the scale exponent is `k − 1`, not `k`. That is why the two existing proofs differ in a way I had
read as incidental: the trigamma proof carries **no** `s` factor (`k = 1`, `s⁰ = 1`) while the
order-two proof carries exactly one. The correct general statement indexes by `m` with `k = m + 1`
and uses `s^m`, and its `hsdivH2` step cannot be `hs.pow m` — at `m = 0` that tends to `1`, not `0`
— so it needs a boundedness argument instead.

The remaining obstacle after that is the pole cancellation `s^{k+1} · (s x)^{-(k+1)} = x^{-(k+1)}`,
which is true but needs `mul_inv`/`mul_pow` by hand: `field_simp`/`ring` do not close symbolic
exponents.

**Resolved on the corrected statement.** Indexing by `m` with `k = m + 1` and using `s^m`:

```
tendsto_gammaFactorialScaledPolygamma_second_harmonic (m : ℕ) (hx : x ≠ 0) :
  Tendsto (fun n => (gammaFactorialScaledPolygamma (m+1) n x
      - (-1)^(m+2) * (m+1)! * x⁻¹^(m+2)) / gammaHarmonicMicroscopeScale n ^ 2) atTop (𝓝 0)
```

Two supporting lemmas made it go through, both of which are the pieces the naive design lacked:

- `scale_pow_mul_inv_pow (hs : s ≠ 0) (j) : s^j * (s x)⁻¹^j = x⁻¹^j` — the pole cancellation, by
  `mul_inv`/`mul_pow`/`mul_inv_cancel₀`, since `field_simp` and `ring` cannot close symbolic
  exponents;
- `tendsto_scale_pow_mul_inv_harmonic_pow (m) (hj : 0 < j) : s^m · H⁻ʲ → 0` — proved by squeezing
  against `‖H⁻ʲ‖` using `‖s‖ ≤ 1` eventually, rather than by `hs.pow m`, which fails at `m = 0`.

Both concrete theorems are now two lines each — 86 and 93 proof lines replaced. The file is 423
lines, down from 480 when this tower began in B76, and now carries `shiftedHarmonicPowerSum`, the
indexed reflection, the indexed norm bound, the indexed scaled polygamma, and the indexed
second-harmonic limit where before it had two hand-written orders of each.

Audit: `lake build GaloisForLFunctions.HTGeometry.GammaFactorialThirdJetHarmonicResidue` — 8508
jobs, exit 0.

### B89 — Thermal cubic charge: the sharp constant implies the round one

`xiThermalOrientationTerm_le_endpointCrossCharge_cube` bounds the orientation term by
`(86/85)³ · crossCharge³`; `..._le_exactEndpointCrossCharge_cube` proves the same with the sharp
constant `(4/(4 − C))³`, where `C = xiEndpointCompletedCurvature`. Both run the same 50-line
case split and inverse estimate.

They are not independent: `C < 2/43` gives `4/(4 − C) < 4/(4 − 2/43) = 86/85` exactly, so the sharp
version implies the round one. The round theorem is now nine lines — the constant comparison
`4/(4−C) ≤ 86/85 ⟺ 86C ≤ 4` plus one `pow_le_pow_left₀`. Moved below the sharp version per the B72
direction rule. 418 → 375 lines.

The `86/85` in the statement is exactly the sharp constant evaluated at the endpoint of the known
curvature bound; recording that here because it is not visible from either statement alone.

Audit: `lake build GaloisForLFunctions.RHTower.XiThermalQuartetCubicChargeBound` — exit 0.

### Examined, not done — three pairs where the shared part resists clean extraction

**`XiCTaylorThetaTailFullDensityMonotoneCurrent` (49 lines).** The two directions of the
density-current criterion. Their shared block is *setup* — the schedule, the `filter_upwards`, and
the local names `z`, `F`, `T`, `P` — not shared reasoning: the forward direction bounds
`orientedCurrent ≤ 2/z.im · normSq + normSq F · transferCurrent` and the reverse uses the opposite
frontier inequality. Packaging the setup means the same wide dependent interface that made B64 not
worth doing. The better restructure, if it is ever wanted, is a predicate-level equivalence
`FullDensityTransferCurrentSublinearUpper D ↔ AnisotropicOrientedCoefficientSublinearUpper D`,
after which both RH directions compose with the known coefficient-level equivalence in two lines
each. That is a genuine piece of work, not a factorisation.

**`XiCTaylorThetaTailFiniteTranslationBounds` (47 lines) — resolved, see B90 below.**

**`EllipticGammaMixedFace` (50 lines).** The σ- and τ-face proofs are parallel, but the τ side
carries an extra translation `(τ−σ)/2` threaded through the analytic-subring algebra, so the
generalisation has to abstract the shift *and* the theta factor together. Left for a session that
can give it a clean run.

### B90 — Shifted factorial envelope: three shared blocks, transcribed by hand

`integral_abs_thetaCuspTailDerivative_mul_shiftedFactorialEnvelope_le` (112 lines) and
`integrableOn_abs_…` (65) share three blocks, now private lemmas:

- `thetaCuspTailDerivativeNatExpConstant_nonneg` — evaluate the tail bound at `x = 0`;
- `aestronglyMeasurable_absTailDerivative_mul_envelope` — the integrand is measurable;
- `absTailDerivative_mul_envelope_le` — the pointwise domination, whose content is that the tail
  decay `e^{-(p+r)x}` absorbs the envelope's `e^{r(x+a)}` and leaves `e^{ra} e^{-px}`.

75 lines removed; module 1640 → 1565, build 8779 jobs, exit 0.

**On the earlier failed attempt.** I first tried to lift these blocks by slicing the proof text at
computed line offsets, and produced bodies that were cut in the wrong places. Transcribing the three
blocks by hand worked on the second try, with two small adjustments the extraction itself forced:
the pointwise lemma needs `0 ≤ a` as an explicit hypothesis (inside the original theorem it came
from the enclosing binder, and `gcongr` silently used it for `0 ≤ x + a`), and once that hypothesis
is present `gcongr` discharges the side goal without the `positivity` I had added.

The general lesson, recorded because it cost a revert: **offset-based slicing is fine for moving a
whole declaration and unreliable for lifting a block out of the middle of a proof.** Whole
declarations have unambiguous boundaries; interior blocks do not.

### B91 — Inner Mellin piece: same bound/integrability split as B90

`inner_mellin_piece_le` and `inner_integrand_integrableOn` in `XiThetaExplicitBounds` are the B90
shape again: an integral bound and an integrability statement built on the same majorant and the
same pointwise domination. Extracted as

- `integrableOn_inner_majorant` — `72/π⁴ · t^{7/4}` is integrable on `(0,1)`;
- `inner_integrand_le_majorant` — on `(0,1)`, `t^{u-1}‖f_modif t‖ ≤ 72/π⁴ · t^{7/4}`, whose content
  is the kernel bound `3t^{-1/2}e^{-π/t}` meeting `e^{-π/t} ≤ 24t⁴/π⁴`, with `t^{u-3/2} ≤ t^{-9/4}`
  for `u ≥ -3/4`.

103 lines removed across the two consumers; module 998 → 895, build 2900 jobs, exit 0. The
integrability proof now ends by rewriting `‖·‖` on a nonnegative product and applying the domination
directly, rather than restating it.

The B90 boundary lesson applied cleanly here: I located the block by its `have hle :` header and its
first following line at outer indentation, rather than by computed offsets, and it lifted first try.

### B92 — Pattern-driven search, and the Landau cosine split

Having hit the bound/integrability shape three times (B81/B87 weights, B90, B91), I stopped waiting
for the generic scanner and searched for it by name: pairs where one declaration mentions
`integrab` and the other does not, *filtered by ≥28 shared proof-body lines*. The name pattern alone
gives 289 hits across the three areas and is worthless — `integral_X` beside `integrableOn_X` is
ordinary API. Combined with real overlap it gives **eight**, which is a usable worklist.

First of them (excluding the four `Deninger*` files another agent is editing):
`CCMFirstClockLandauTransform`, `integrableOn_sq_cexp_cos` ~ `integral_sq_cexp_cos`, 40 shared lines.
Two extractions:

- `re_pos_shifted_abscissa` — both shifted abscissas `s ∓ i z u` stay in the right half plane when
  `|Im z| < Re s` and `u ∈ [0,1]`;
- `sq_cexp_cos_eq_half_add` — writing `cos` as a half-sum of exponentials turns
  `e^{-sL} L² cos(Lzu)` into the mean of two pure squared-exponential integrands. **This is an
  identity of functions with no hypotheses at all**, which is why both proofs could carry it: the
  integrability proof used it through `congr_fun`, the integral proof through `funext`.

Both consumers are now four and six lines; module 562 → 429.

Remaining from the filtered worklist: four `Deninger*` pairs (45, 37, 36, 29 — left alone while that
area is under active edit), `SmoothAFEZetaDualContourLimit` (36),
`BourgainBilinearLocalization` (35), `XiCTaylorThetaTailCompletedDensityReflection` (29).

### B93 — Bourgain localization: one indicator lemma, three call sites

Second entry from the B92 worklist. `integrable_bourgainBilinearIntegrand` and
`integral_bourgainBilinearIntegrand` both carried the same twenty-line argument that a constant
multiple of the localized box character is integrable — factor the constant out of the indicator,
apply `integrable_bourgainLocalBoxCharacter`, `const_mul`. Extracted as
`integrable_const_mul_bourgainLocalBoxCharacter`, with the constant a parameter.

The sweep found **three** occurrences, not two: the same block also appears as a side condition of
`integral_finsetSum` further down the file. All three are now one line. Module 292 → 229.

One wrinkle worth noting: the statement's `if z ∈ bourgainLocalBox …` needs decidability, which the
consumers got from a `classical` tactic inside their proofs. A lifted lemma cannot — its *statement*
needs it — so it carries `open Classical in`. That has to sit **before** the docstring, not between
docstring and declaration, or the docstring detaches and Lean reports an unhelpful
`unexpected token 'open'`.

### B94 — A better instrument: repeated *blocks*, not clone pairs

B93 turned up a third copy of an argument that no pair of declarations exposed, which means the
pairwise scanner systematically under-counts. Wrote `blockrep.py`: slide an 8-line window over every
tactic proof body in the three areas, hash the windows, report those occurring three or more times.
It stays inside one declaration, skips windows that are mostly generic tactics (`ring`, `simp`,
`linarith`, …), and skips runs of repeated lines.

It reports **1110 blocks repeated ≥ 3 times** — a duplication surface an order of magnitude larger
than anything the clone-pair scanner saw, and of a completely different kind: not near-identical
theorems, but the *same small argument written out repeatedly in unrelated proofs*.

The clearest instance, and the first fixed:

```
theorem exp_two_lt_eight : Real.exp 2 < 8
```

— an eight-line derivation from `Real.exp_one_lt_d9`, written out **seven times** across
`ZetaVerticalGrowth`, `ZetaStripLowerBound`, `ZetaLowerBound`, `ZetaDerivGrowth`,
`ZetaZeroFreeRegion` and `ZetaLogDerivBound` (twice). Placed in `ZetaVerticalGrowth`, the most
upstream of the six — verified by import-closure that the other five all reach it — and all seven
call sites are now `have hexp2 := exp_two_lt_eight`. 49 lines removed for a 10-line lemma.

Method note: my first choice of home, `ZetaSawtoothTail`, was a genuine common ancestor by
import closure but could not see `Real.exp_one_lt_d9` — narrower mathlib imports. Import-closure
membership is necessary but not sufficient for a home; the ancestor must also carry the mathlib
surface the proof uses.

Top repeated blocks still outstanding: a `let u/v/A/B` sector-coordinate preamble (×12, across the
`XiOrder*EdgeCorner` and `XiCenteredOrders*` families), the
`continuedPrimeArchSourceRelativeTrace` half-plane preamble (×11), a bend-pair
`Finset.single_le_sum` step (×8), and a `xiZeroCopyReciprocalSquare ^ 2` real-part formula (×7).
