# CHMD: primitive cusp escape and compactness

Date: 2026-10-16. Status: formalized. Paper proof and all owned Lean audits complete.

Conjecture tested: the completed signed Doob graph might have a compact
projection into its theta-cosh mass space, allowing a discrete first-mode
argument for primitive positivity.

## Paper obstruction and positive survivor

The original Markov energy is translation invariant: translating both entries
of the Weil autocorrelation leaves it unchanged. For a fixed nonzero compact
C2 real test f, let f_T(x)=f(x-T), v_T=f_T/Θ, and
M(T)=∫ f_T(x)^2 cosh(x/2)/Θ(x) dx. The actual graph has
sourceEnergy(v_T)=markovEnergy(f), source mass M(T), and graph norm squared
sourceEnergy(v_T)+2M(T). Since Θ tends to zero in the positive cusp and
cosh≥1, compact support and ∫f²>0 imply M(T)→∞. Thus normalized v_T have
source norm one, signed energy→0, complete jump energy→1, and graph norm
squared→2. These retain every original prime and the full archimedean source.

Choose f=evenShift(g,4)-cosh(1)g with g=narrowBump(0). Both half-moments
vanish by the existing exact even-shift laws. The bump is supported in
[-1/4,1/4], so f(0)=-cosh(1)≠0. Both half-moments of every translate
also vanish: translation multiplies the positive/negative exponential
half-moments by exp(±T/2). Hence every normalized graph vector lies in
the actual primitive hyperplane.

Choose translates beyond a common threshold, separated by more than the
fixed support diameter. Their mass-space coordinates are orthonormal while
their graph norms are bounded. No subsequence of source coordinates is
Cauchy. Therefore even the compact-core primitive graph has a noncompact
source projection.

Positive survivor: an unconditional primitive sequence with source norm one,
full jump energy tending to one, signed energy tending to zero, bounded
graph norm, and pairwise orthogonal source coordinates. This pins the critical
Rayleigh boundary and rules out a strictly positive uniform signed margin.
It does not establish a spectral Weyl residual, a selfadjoint operator, an
exact essential spectrum, primitive nonnegativity, or RH.

## Lean artifacts

- `formal/GaloisForLFunctions/RHTower/CHMDTranslatedPrimitiveSource.lean`: 216
  lines, 25 declarations. Exact translation invariance, explicit nonzero
  double-primitive profile and mass divergence. SHA256:
  `f526232c72ec226a07393b183a390e2f8ec75a2555b086448ebc0fee7570c878`.
- `formal/GaloisForLFunctions/RHTower/CHMDPrimitiveCuspEscape.lean`: 254 lines,
  34 declarations. `exists_primitive_escape`, `no_cauchy_subsequence`,
  `not_isCompact_primitiveBallImage`, `no_positive_primitive_margin`. SHA256:
  `7e4e23004fc307db07c785cd06c3d24933ffbf56dd58174d280c4929d7fefd8d`.

The failed compactness route and second-pass positive salvage are recorded in
`../5-failed/chmd-primitive-compact-projection-2026-10-16.md`.

## Validation

- Both `lake --old build <leaf>` commands exited 0.
- Final plain `lake env lean <leaf>` audits of both unchanged leaves exited 0
  with empty output. The second direct check preceded its successful build;
  its source hash was verified unchanged.
- Separate 25-name toolchain probe exited 0.
- All 59 declarations passed `/tmp` `#print axioms`: only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Both imports occur exactly once. Scoped whitespace checks passed.
- `scripts/formal_tools.py index` exited 0.
- Global formal lint exited 1 solely for these six other unwired modules:

- `GaloisForLFunctions.RHTower.Deninger.DeningerHasseHilbertOperators`.
- `GaloisForLFunctions.RHTower.Deninger.DeningerHasseHilbertPairing`.
- `GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHasseHilbertAdmission`.
- `GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHasseHilbertDensity`.
- `GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHasseHilbertTopology`.
- `GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHasseMoments`.

No new CHMD lint error was reported. These other modules were preserved.
All owned processes are terminal. All 12 owned scratch files were removed; absence verified. All owned processes
reached terminal exit.

RH remains unproved. Primitive-sector nonnegativity is still open. This result
removes the compact-projection shortcut and supplies an explicit critical
primitive escape sequence in the full original source.
