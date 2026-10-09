# Exact finite paired-log kernel classification

Status: dependency-closed paper proof recorded; implementation pending.

## Objective and corpus evidence

Classify every finitely supported paired-log cancellation, not merely
prove a noninjectivity example. Target for finitely supported coefficients v:

    (∀y, Σ_n v(n) pairedLogKernel(y,n)=0)
      iff v(0)+v(1)=0 and ∀n≥2, v(n)=0.

The target may be proved first for complex coefficients (complexifying the
real kernel), then specialized to real coefficients if needed for the native
receiver. No claim about arbitrary infinite summable coefficients is included.

Only Lean corpus used. Ingredients already inspected:

- `linearIndependent_L2_translates` in
  `HTGeometry/L2TranslationExponentialIndependence.lean` for arbitrary
  distinct real shifts and any nonzero complex L² vector.
- `integrable_riemannAutocorr_complex` in `RiemannKernelSpectralLocalization`.
- `riemannAutocorr_continuous`, `riemannAutocorr_pos`, and
  `riemannAutocorr_le_zero` in the WeilExcess kernel development.
- `MellinL2.additiveTranslationUnitary` is pullback along the
  measure-preserving equivalence y↦y+a. `Lp.coeFn_compMeasurePreserving`
  therefore gives its actual almost-everywhere formula beyond Schwartz inputs.
- Installed Lean `memLp_two_iff_integrable_sq_norm`,
  `Continuous.ae_eq_iff_eq`, and finite-support linear combinations.

## Dependency-closed paper proof

Write K for the actual real autocorrelation. Since 0≤K(y)≤K(0),
|K(y)|²≤K(0)|K(y)|. The existing L¹ theorem and continuity show K belongs
to complex L². Its L² class is nonzero: otherwise continuity upgrades
almost-everywhere zero to pointwise zero, contradicting K(0)>0.

The existing measure-preserving translation definition identifies translated
L² classes with y↦K(y+a) almost everywhere. Consequently arbitrary distinct
literal translates of K are independent: a pointwise finite relation would
give the forbidden L² relation. By finite-subfamily independence, the whole
real-indexed family of literal translates is independent.

For a finitely supported complex coefficient family v on ℕ, push coefficients
forward along n↦log(n), obtaining a finite coefficient family g on ℝ. Every
coordinate of g is nonnegative. The paired potential is synthesis against
the translate coefficient family d(t)=g(t)+g(-t). Translate independence
makes vanishing of the potential equivalent to d=0. Since g is supported
on nonnegative coordinates, d=0 implies g=0: at t>0 the reflected term is
zero, at t<0 g itself is zero, and at t=0 the equation is 2g(0)=0.
The converse is immediate.

The nonnegative logarithmic coordinate has exactly one repeated fibre:
log(0)=log(1)=0. For n≥2, log(n)>0 and its fibre among natural numbers is
the singleton {n}, by strict monotonicity of log on positive reals. Hence
g(0)=v(0)+v(1) and g(log n)=v(n) for n≥2. No other fibres carry mass.
Thus g=0 has exactly the displayed coefficient classification.

This extracts the full finite positive survivor of the alias obstruction:
the quotient by the one-dimensional 0/1 cancellation is faithful.

## Work log / continuation requirements

- [x] Inspect actual kernel, L² translation definition, and relevant corpus APIs.
- [x] Paper proof before implementation.
- [ ] Scratch-verify mathlib/corpus names in the current toolchain.
- [ ] Construct nonzero actual autocorrelation L² class and literal translation bridge.
- [ ] Prove independence/synthesis injectivity for arbitrary finite actual translates.
- [ ] Prove reflected nonnegative-coordinate cancellation classification.
- [ ] Prove exact natural logarithm fibre classification and native finite result.
- [ ] Final direct leaf builds; umbrella wiring; complete axiom audit.
- [ ] Index/lint, exact result log, cleanup owned scratch.

Keep this card in progress until the exact finite classification is proved;
an L² lift alone does not complete the task. Full corpus-research goal remains active.


## Final formalization record — 2026-10-09

Status: FORMALIZED. The finite paired-log synthesis vanishes identically if
and only if v(0) + v(1) = 0 and every coefficient v(n), n ≥ 2, vanishes.
Both real and complex coefficient versions are proved. The intermediate
actual-kernel result proves faithful finite translate synthesis using a
nonzero L² lift of the Riemann autocorrelation.

Lean leaves:
- `formal/GaloisForLFunctions/RHTower/RiemannAutocorrFiniteTranslation.lean`
- `formal/GaloisForLFunctions/RHTower/WeilLogShiftFiniteKernelClassification.lean`

Verification:
- Both direct leaf compilations with output oleans exited 0, without warnings.
- All 13 public declarations audited through `#print axioms`; only
  `propext`, `Classical.choice`, and `Quot.sound` occur.
- Both imports occur exactly once in the RHTower umbrella; both oleans are
  newer than their source files.
- Index refresh exited 0. Module-filtered local lexical searches recover
  all 13 public declarations (plus the three private classification helpers).
- Formal lint exited 1 solely on six unrelated HTGeometry modules missing
  umbrella imports: HankelSliceBirational, HankelSliceChart,
  LinearHypersurface, PaperNativeReesHomogeneousInitial,
  PaperSymmetricPairNormalAction, QKrawtchoukCompanionTriangular.
  No lint error names either new leaf. These unrelated files were not changed.

Only local Lean corpus and installed Lean dependencies were used as
mathematical evidence. No web searches, external papers, or numerics.

Follow-up: `WeilLogShiftFiniteReconstruction.lean` now proves independence
of the actual arithmetic tail, an invertible finite sampling map, and a
native `HasSum` receiver with unique coefficient recovery and inverse-norm
stability. The sample count equals the coefficient count and is minimal.
See [finite Weil packet reconstruction](finite-weil-packet-reconstruction.md)
for its final verification record. Infinite-family injectivity remains
unproved by these finite results. The full corpus-research goal remains active.
