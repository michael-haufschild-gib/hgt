# Constrained prolate stage-3 Lean closure

- **ID:** `constrained-prolate-stage3-lean-closure`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** `../2-fully-proven/new_scientific_knowledge/constrained-prolate/`
- **Statement:** Formalize unconditionally every theorem in all six constrained-prolate stage-2
  cards, including actual classical PSWF identification, fixed-mode Fuchs/Hermite asymptotics,
  radial Dunster transfer, off-diagonal decay, weighted projective convergence, and every existing
  downstream capstone.

## Goal

Move all six source cards to stage 3 only after dependency-closed Lean proofs, umbrella wiring,
per-module checks, axiom audit, formal lint, and final module build.  No asymptotic hypothesis may
remain in any card capstone.

Target cards:

1. `constrained-prolate-two-mode-ground-state`
2. `constrained-prolate-fixed-mode-spectral-ladder`
3. `constrained-prolate-fourier-parity-floor-separation`
4. `constrained-prolate-radial-leakage-divisibility-spectrum`
5. `constrained-prolate-full-radial-prime-charge-law`
6. `constrained-prolate-arithmetic-dilation-operator-limit`

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, dependency audit complete
- [ ] 1 → 2 fully-proven: not applicable; six source cards already carry complete paper proofs
- [ ] 2 → 3 formalized: concrete unconditional Lean capstones, `lake build` green, lint and axiom
  audits pass
- [ ] 3 → 4 publication-ready: outside current goal

## Approach

1. Identify actual finite-Fourier signed modes with simple regular even prolate ODE modes.
2. Construct honest classical even numbering and prove positive `4j` / negative `4j+2` sectors.
3. Prove true fixed-mode Fuchs leakage asymptotics and normalized prolate-to-Hermite coordinate
   limits; instantiate existing secular, ladder, parity, and distance machinery.
4. Prove uniform actual-radial-PSWF to Dunster-leading-model transfer, then weak convergence and
   fixed off-diagonal vanishing.
5. Sum off-diagonal sectors and discharge actual weighted projective convergence; instantiate
   arithmetic trace-class and determinant capstones.

Existing closed infrastructure includes concrete time-band/leakage operators, signed spectrum,
canonical pointwise representatives, exact Slepian kernel scaling, exact joint band/prolate
eigenfunction existence, secular roots/tails/eigenvectors, Fuchs-rate algebra, Hermite contrast
algebra, leading Dunster-model tightness/weak convergence, radial mass transfer, arithmetic
projective/trace-class/determinant consequences.

## No-go closure

- **Exact killing theorem/mechanism:** none; task active.
- **Strongest positive survivor:** not applicable.
- **New insight:** six cards share one upstream analytic bottleneck rather than six independent
  formalization gaps.
- **Status:** active.

## Log

- 2026-08-07 — created directly in stage 1 for explicit user-requested long-running formalization.
- 2026-08-07 — added exact scaled Fourier/Fubini composition and true-mode joint smooth even
  Slepian/prolate eigenfunction existence in
  `formal/GaloisForLFunctions/RHTower/SlepianKernelScaledFubini.lean`.
- 2026-08-07 — proved compact-interior prolate ODE uniqueness, center nonvanishing, and
  one-dimensionality of each regular even separation eigenspace on `[-1,1]` in the same module.
- 2026-08-07 — ruled out equating signed greedy index `n` with classical `4n`: signed greedy order
  is by absolute eigenvalue and interleaves positive `4j` with negative `4j+2` sectors.
- 2026-08-07 — ruled out a global solved-form ODE Lipschitz constant on `(-1,1)`; coefficient
  `1/(1-x^2)` is unbounded at singular endpoints.  Compact subinterval uniqueness is exact.
