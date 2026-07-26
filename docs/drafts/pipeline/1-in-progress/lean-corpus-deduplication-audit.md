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

## Census (2026-07-26)

Scanner: `scan2.py` — extracts top-level decls, splits statement/proof at depth-0 `:=`/` by`,
groups by normalised text.

| Metric | Count |
|---|---|
| declarations scanned (3 areas) | 67018 |
| identical statement groups | 1136 (~14234 redundant lines) |
| identical proof groups | 381 (~4926 redundant lines) |
| identical statement **and** proof (exact clones) | 128 (~2063 redundant lines) |

## Work batches

### B1 — `xiDivisorSupport_univ_countable` (14 sites) — DONE
13 `private` verbatim copies + 1 public copy of the same 8-line proof, each followed by a
`noncomputable local instance : Countable XiDivisorSupport` and often
`local instance : Countable XiZeroCopy`.
Fix: single `theorem xiDivisorSupport_univ_countable` + global `instance Countable XiDivisorSupport`
and `instance Countable XiZeroCopy` in `RHTower/XiCanonicalProduct.lean` (where the abbrev lives).
`Countable` is a `Prop`-class so a global instance introduces no diamond.

### B2 — QuietCrossing kernel bounds (6 files × 4 lemmas) — DONE
`qcc_/qtp_/cnd_/gw/kernel_/inv_quad_` variants of the same four Cauchy-kernel estimates in
`QuietCrossingCocycle`, `QuietCrossingCocycleTPoly`, `QuietCrossingConductor`,
`QuietCrossingEscalation`, `QuietCrossingRigidity`, `QuietPathRigidity`.
Fix: new `RHTower/QuietCrossingKernelBounds.lean` carrying the four canonical lemmas; every former
site becomes a one-line `:= quietKernel_*`.

### B3 — MobiusLaplace analytic prerequisites (5–6 sites) — DONE
`analyticAt_zetaResidueUnit*` (5×) and `analyticAt_Gamma_of_re_pos*` (6×).
Fix: canonical pair in `RHTower/MobiusLaplaceAnalyticPrereq.lean` (or the lowest existing common
import), one-line delegations at every former site.

### B4 — Abstract-vs-concrete spectral family hierarchy (~1400 lines) — DONE
`HTGeometry/AbstractSpectralFamily ι` is literally `RHTower/SpectralFamily` at `ι = XiZeroCopy`
with `inv := xiZeroCopyLineConjEquiv`. The whole `RHTower/XiSpectralFamily{,Analytic,Decay,Graded,
Shell,OnLine,GradedOnLine,Lift,RH}` chain re-proves `AbstractSpectral{Family,Decay,Graded,Shell,
Charge,Mass,Defect,Rigidity}`.
Fix: `SpectralFamily.toAbstract` bridge + `simp`-normal field equations; replace every duplicated
RHTower proof by delegation. This is the flagship generalisation, not just a clone removal.
Delivered: `RHTower/XiSpectralFamily.lean` now defines `SpectralFamily := AbstractSpectralFamily
XiZeroCopy` (`abbrev`), so *all* abstract lemmas apply to the Xi family with no bridge at all;
`XiSpectralFamilyAnalytic/Decay/Graded` reduced to re-export shims.

### B5 — Sonin `legacy_*` clones — DONE
`SoninTimeBandHilbertSchmidt.legacy_*` are verbatim copies of `SoninTimeBandIdeal.*`.
Resolved: `SoninTimeBandIdeal` imports `SoninTimeBandHilbertSchmidt`, so the `legacy_` copies are
the *upstream* originals. Removed the four downstream re-proofs in `SoninTimeBandIdeal` and
replaced them with one-line delegations to the `legacy_` originals.

### B6 — remaining ~110 exact-clone groups — 6 landed, rest pending
Landed: `hasDerivAt_log_norm_complex` (HTGeometry/UnitaryReflectionPhaseHalving canonical, delegated
from RHTower/CarrierHorizontalRigidity), `norm_add_sq_complex` (HardyCarrier canonical → RouteBSublevel),
`natCast_cpow_neg_pow` (IntegralFEPolynomial canonical → FinitePrimeSectorDichotomy),
`isAlgebraic_ofReal` (GelfondSchneider canonical → BakerWeldIndependence),
`complex_half_ne_integer` (ConstantFieldQEDGammaClock canonical → ZetaHorizonGammaIntensitySeparation),
`natCast_cpow_conj` (Reflection canonical → MollifiedCarrier/ZetaCarrier).
Pending: mostly 2× pairs and one-file-apart triples; each needs an import-order check to pick the
canonical home.

### B7 — HilbertMetric
46 files, 18041 lines; no exact clones detected in the scan. Structural review still owed
(`SymmetricFockShadow` / `SymmetricFockShadowRigidity` pair is the one flagged clone).

## Log
- 2026-07-26 — created; census complete; B1 started.
- 2026-07-26 — B1 landed: 14 sites → 1 canonical theorem + 2 global instances in XiCanonicalProduct.
- 2026-07-26 — B2 landed: 24 kernel-bound clones → 4 canonical lemmas in QuietCrossingKernelBounds.
- 2026-07-26 — B3 landed: 11 clones → 2 canonical lemmas in MobiusLaplaceAnalyticPrereq.
- 2026-07-26 — B4 landed: `SpectralFamily` is now literally `AbstractSpectralFamily XiZeroCopy`.
- 2026-07-26 — B5 landed: 4 Sonin duplicate re-proofs delegated to their upstream originals.
- 2026-07-26 — B6 first 6 groups landed.
