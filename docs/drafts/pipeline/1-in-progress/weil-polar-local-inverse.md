# Exact local inverse of the Weil pole multiplier

**Status:** compact inverse, uniqueness, and exact constrained-floor criterion pass Lean; first-zero boundary refinement and final integration audit in progress.

**Proof chain:** literal prime–Gamma quadratic form on the two-pole constrained sector → nonnegative constrained ground at every aperture → `riemannHypothesis_of_polarGroundEnergy_nonneg` → RH. This card closes the exact description of the smooth constrained sector; the arithmetic positivity inequality remains open.

## Corpus inputs and conjecture audit

- `CCMRestrictedWeilPolarMultiplier` proves that `Dg = g'' - g/4` kills both exponential moments. Its forward proof supplies the necessary moment constraints; the explicit compact inverse is closed in `CCMRestrictedWeilPolarInverse`.
- `HTGeometry.CompactPrimitive` proves smoothness and support control of zero-mass primitives. `CompactL2FourierRootDivision` independently supplies the modulation–primitive–demodulation construction for real Fourier roots.
- `CCMRestrictedWeilPolarConstrainedSmoothCore` and `CCMRestrictedWeilPolarGroundEnergy` supply constrained smooth density and smooth Rayleigh near-minimizers.
- `CCMRestrictedWeilFiniteNegativeBlock` makes every closed nonpositive subspace finite-dimensional. This suggests strict negativity beyond a null aperture: small translates of an interior null vector would be independent radical directions. The full weighted-form-domain translation and pole-preservation interface has not been proved here. Smooth approximation does not preserve exact zero energy, so it cannot fill that gap.

**Conjecture → proof:** the two moments are exactly the obstruction to solving `Dg=f` with smooth support in the same aperture. Choose `r<a` containing the support of `f` and set

`A_s(x) = exp(s*x) * integral[-r,x] exp(-s*t)*f(t) dt`,
`g(x) = A_(1/2)(x) - A_(-1/2)(x)`.

The moment constraints make both primitives vanish outside `[-r,r]`. Since `A_s' = s*A_s + f`, the two copies of `f` cancel in `g'`, and `g''=g/4+f`. Thus `g` is smooth and compactly supported strictly inside the original aperture. This is the elementary constant-coefficient Green construction; no novelty is claimed for that construction.

**Conjecture → proof:** this inverse is unique among compactly supported smooth functions. If `Dg=0`, then `h=g'-g/2` satisfies `h'=-h/2`. Multiplication by `exp(x/2)` gives a constant, which vanishes outside the compact support. Then multiplication of `g` by `exp(-x/2)` gives a second zero constant.

**Positive consequence:** every smooth constrained source is exactly one multiplier image at the same aperture. Together with smooth Rayleigh near-minimizers, any lower bound on all multiplier images is exactly the corresponding constrained ground bound. This changes the test parametrization without selecting its sign.

**Fail and pivot:** injectivity of `D`, or strict positivity of each smooth nonzero test at a single aperture, does not provide a uniform positive Rayleigh floor. At a first constrained zero, every such test is strictly positive because its compact support fits an earlier positive aperture. Yet smooth near-minimizers, pulled back through the exact inverse, give strictly positive multiplier-image Rayleigh quotients below every positive tolerance. The survivor is an exact description of how zero ground can appear through completion; no smooth null vector may be assumed.

## Verification plan

1. Check required local theorem signatures in a temporary Lean file.
2. Prove the explicit inverse, support control, uniqueness, and exact source-image classification in scratch.
3. Prove the constrained floor criterion on multiplier images and its existing RH landing.
4. Check production leaves, audit all new theorem axioms, run only named leaf builds, wire imports, run formal lint, update current-state frontier and route-independent constraints only where justified.

No numerical experiment or computational proof certificate is used.
