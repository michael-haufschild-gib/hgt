# Faithful compact-polar realization of the complete Xi Weil space

- **ID:** cross-route-10-compact-polar-completion
- **Stage:** 3-formalized
- **Type:** VERIFIED — contribution 10, counted once
- **Source:** whole local Lean corpus; no external novelty claim
- **Statement:** The Fourier evaluations of complex compact C2 tests with both
  polar moments zero inject into, and are dense in, the multiplicity-folded Xi
  divisor Hilbert space. Its reflected Hilbert pairing is exactly the Weil
  pairing and is nondegenerate already on the compact polar test space.

## Goal

Identify the complete spectral carrier of literal compact polar tests, without
RH, simple-zero, spectral-admission, or unknown density premises. This supplies
all folded square-summable zero profiles as limits of actual source tests and
retains faithful source coordinates before completion. This full realization
counts at most once. Mere compact-radical triviality is not a separate result.

## Gates

- [x] Well-posed, source-pure candidate and cross-route mechanism identified.
- [x] Dependency-closed paper argument below; formalization must audit exact APIs.
- [x] Lean leaves compile, public axioms and primary signatures audited.
- [x] Novelty/significance rechecked, umbrellas wired, formal lint recorded.
- [x] All owned obligations closed; count this full realization once.

## Paper proof

Let H = l2(XiZeroCopy), retaining every divisor multiplicity, and let Hfold be
the closed Cauchy core. Existing XiWeilCauchyCoreMultiplicity identifies its
orthogonal complement with vectors whose sum on every multiplicity fibre is
zero. Every square-summable evaluation vector belongs to Hfold.

1. **Absolute spectral convergence.** For a real exponential-first-jet source
   f, existing truncation estimates give, uniformly on |Im z| <= 1/2,
   (1+|Re z|)|FT(f_L)-FT(f)| <= tailBound(L), with tailBound(L) -> 0.
   The same bound with a fixed constant holds for f and every f_L. Since
   |z| <= 1+|Re z| on this strip and sum_q |z_q|^-2 < infinity, all these
   evaluations are l2 and their l2 differences tend to zero. Apply this to
   real and imaginary parts to obtain the complex statement. The two polar
   evaluations converge by the existing strip Fourier convergence theorem.

2. **Exact constraints in the source core.** In H x C^2 take D to be the
   linear image of compact C2 tests under (zero evaluations, polar values).
   Work in closure(D). The finite-observation dense-core theorem applied to
   projection onto C^2 corrects approximants inside D, preserving their
   limit and making both polar values exactly zero. Hence every decaying
   polar-zero source is approximated by compact polar-zero sources in H.

3. **All multiplicity fibres detected.** For each actual centered Xi zero
   a with Re a > 0, the literal theta-divisor cardinal source is even,
   exponential-first-jet, polar-zero, and has transform 1 at +/-a and 0 at
   all other zeros. Every real translate retains the decay and polar zeros;
   its two nonzero spectral values are exp(ita) and exp(-ita). If u is
   orthogonal to all compact polar evaluations, step 2 makes it orthogonal
   to every such translated cardinal source. Its fibre sums A and B obey
   exp(-ita) A + exp(ita) B = 0 for an interval of t (with the conjugation
   dictated by the Hilbert convention). Value and derivative at t=0 give
   A+B=0 and a(A-B)=0. Xi zeros have a != 0 and Re a != 0, so both sums
   vanish, and reflection covers every zero. Thus the annihilator of the
   compact polar image is Hfold-perp. Taking double orthogonal complements
   proves closure(image) = Hfold.

4. **Faithfulness.** A compact continuous test whose evaluations vanish at
   all Xi zeros vanishes identically, by CompactTestXiDivisibilityObstruction:
   its entire transform has exponential type, while the actual simple
   critical zero supply exceeds the linear zero budget of such a function.
   Apply to differences for injectivity. No RH assumption enters.

5. **The full pairing and radical.** Critical-line reflection is an
   involutive isometry J of H and preserves Hfold. Existing polarization
   identity gives W(f,g) = inner(J ev(g), ev(f)), with the precise orientation
   checked in Lean. A compact test in the left/right radical annihilates the
   dense compact image; continuity and J-invariance force its evaluation
   vector to zero. Step 4 forces the test itself to zero. The dense isometric
   evaluation image identifies its Hilbert completion with Hfold, and the
   extended Weil pairing is the bounded invertible fundamental-symmetry form.

## Local-corpus novelty audit

- CHMDFullSpectralNullspace already identifies the radical in the original
  arithmetic graph. Combining that with compact nonannihilation alone is
  too routine for this goal and was rejected as a standalone contribution.
- CHMDCompactOrbitInertia (contribution 2) realizes finite negative blocks in
  graph norm. It does not identify the full absolute l2 spectral completion.
- XiWeilCauchyCoreMultiplicity classifies the resolvent core and multiplicity
  annihilator; XiWeilCauchyPoleExhaustion approximates fibre indicators by
  rational Cauchy packets. Neither supplies compact polar source density.
- WeilPrimeBlindZeroSideIdentity proves scalar Weil truncation convergence;
  the new requirement is strong absolute l2 convergence, including exact
  polar correction, then completeness of literal compact source tests.
- CompactTestXiDivisibilityObstruction supplies injectivity, not density.
- Searches: full-corpus deep radical and compact-Hilbert queries completed
  with partial=false. Last inventory 73,178 files / 1,083,086 declarations.
  Snapshot freshness and semantic-coverage warnings remain; direct sources
  and Lean checks are authoritative. Prose hits are not mathematical evidence.

## Work plan and log

1. Prove absolute l2 truncation convergence and complex compact admission.
2. Prove finite-observation correction inside a closed image.
3. Prove translated-cardinal annihilator completeness and exact density.
4. Prove faithful Weil realization, audit, wire, and count once if significant.

- 2026-10-17 — candidate opened; count remains 9/100. No new Lean code yet.
- 2026-10-17 04:43 UTC — seven candidate leaves written. Targeted builds of
  HTGeometry.ClosedCoreFiniteConstraints and RHTower.XiCompactSpectralSampling
  pass with empty logs. XiCompactSpectralSource is under revision; remaining
  four downstream leaves have not yet been compiled. No count or global pass
  claimed. Full-corpus source-text comparison found no matching compact polar
  completion theorem; XiRelativeCompletionStabilityWall concerns pointwise
  Meyer closability and purity chambers, not this spectral completion.
- 2026-10-17 — XiCompactSpectralSource compiles (two implicit-variable name
  warnings in the compact-test submodule constructor). Complex sampling,
  source linearity and simultaneous spectral/polar truncation convergence
  are verified. Next: exact compact polar approximation.
- 2026-10-17 — XiCompactPolarApproximation compiles with empty log: every
  decaying polar-zero source is approximated in absolute spectral norm by
  compact tests with both polar values exactly zero. Cardinal, density and
  final realization leaves remain unverified. Public source-name audit:
  45 declarations matched, no foreign collisions.
- 2026-10-17 — XiCompactPolarCardinals and XiCompactPolarDensity compile
  with empty logs. Exact closure equals the full multiplicity-folded Cauchy
  Hilbert subspace, with no density assumption. Before the final realization
  check, compile the existing CompactTestXiDivisibilityObstruction dependency
  whose object was absent. The two source-constructor warnings were removed;
  that leaf requires one final targeted rebuild. Count remains 9/100.
- 2026-10-17 05:05 UTC — all seven leaves and the existing compact-test
  injectivity dependency compile with empty final logs. The final scratch
  audit exits 0: all 45 public declarations have exactly `propext`,
  `Classical.choice`, `Quot.sound`; nine primary signatures, nine Mathlib
  APIs and four defining objects checked. Seven imports occur exactly once.
  Generated index and `scripts/formal_tools.py lint --check-generated` exit 0.
  Lint reports only 381 existing large-file warnings. Contribution counted
  once; verified goal count is 10/100 and goal remains active.

## Exact Lean scope and certificate

Primary theorem: `RHTower.compact_polar_weil_faithful_complete_realization`
in `RHTower/XiCompactPolarWeilRealization.lean`. It states injectivity,
exact closure equality, and zero left radical. The right radical and literal
reflected-inner-product identity are also proved. Its statement has no RH,
simple-zero, source-admission, or density premise. The completion is identified
through the exact dense image; no separate Lean `Completion` isometry object
is asserted. All supporting approximation, cardinal and radical results belong
to this single contribution.

Final source SHA256 values (paths relative to `formal/GaloisForLFunctions`):

| Leaf | SHA256 |
|---|---|
| `HTGeometry/ClosedCoreFiniteConstraints.lean` | `3e7317f7d6a9ce3a0aefd99058b8c8ed1d64f5e9c70caa6bfd8ae82f39e56724` |
| `RHTower/XiCompactSpectralSampling.lean` | `28938c5ca54f5a45dbfa2782e052f2e1aa4848fc05e1ba754c82bdc7ab8e3b60` |
| `RHTower/XiCompactSpectralSource.lean` | `4cbe5bb2f7bb028b200a830e3d1e43a03833b2f6a6abd2eaee3ca1bd90a31aa3` |
| `RHTower/XiCompactPolarApproximation.lean` | `b6b8d059e22efba05c60256b881d77bea239ade757221a596e3ce4a45e0692f9` |
| `RHTower/XiCompactPolarCardinals.lean` | `2506fa3b66492b9a70bc3d67116fd708146db17f4fa9b95d18d90560c0e7762a` |
| `RHTower/XiCompactPolarDensity.lean` | `c5d54ffed77244144b812a521e326d933806910e836eeb65d1ddd17a10dc646f` |
| `RHTower/XiCompactPolarWeilRealization.lean` | `47f90a60c93b57cdb60408daf672153ad003acb7248c1893c54aa5e981096798` |

Scratch audit log SHA256:
`ecac84dcbc425fc63b394af06b8456eb23a5a9d224879a5651b97843feda7fbe`.

All seven compiled objects were checked newer than their final sources.
All 21 reviewed contribution-10 temporary files were removed; absence verified.
No owned Lean process remains from this contribution.
