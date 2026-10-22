# Exact local inverse of the Weil pole multiplier

**Status:** formalized. Both production leaves pass named builds; all 21 public theorem dependency audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

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

## Exact Lean surface

- `CCMRestrictedWeilPolarInverse` proves smooth exponential primitives, their exact derivative and exterior support laws, the Green right inverse, a zero compact homogeneous kernel, injectivity, and `isPolarConstrained_iff_existsUnique_polarMultiplier_preimage`.
- `RHTower.le_polarGroundEnergy_iff_polarMultiplier_floor` in `CCMRestrictedWeilPolarMultiplierCriterion` is exact for every real floor `m` at each fixed aperture. The theorem names below are in namespace `RHTower`, rather than a module-named namespace.
- `riemannHypothesis_iff_polarMultiplier_nonnegative` and `riemannHypothesis_iff_polarGroundEnergy_nonneg` prove both directions. `not_riemannHypothesis_iff_exists_negative_polarMultiplier` gives the exact negative-witness counterpart.
- `polarMultiplier_firstZero_no_uniform_positive_floor` gives positive image-core Rayleigh quotients below every positive tolerance at a first zero. `riemannHypothesis_or_polar_firstZero_core_boundary` is a closed, hypothesis-free alternative retaining a normalized constrained null vector and positivity of every nonzero smooth constrained interior test.

The first-zero alternative does not establish the existence of a zero threshold, and no theorem here excludes one. The translation argument above remains an unformalized next conjecture; no claim of strict negativity above a threshold is made.

## Verification

Temporary signature checks and complete scratch proofs used `lake env lean <file>`. The production leaves passed the named commands `lake --old --log-level=error build GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarInverse` and `lake --old --log-level=error build GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarMultiplierCriterion`; each built only its requested leaf. Both are wired into `RHTower.lean`. An importing scratch file audited all 21 public theorems and printed the actual `RiemannHypothesis` definition, retaining zeta zeros, trivial-zero exclusion, the point `1`, and the conclusion `s.re=1/2`. No custom axiom or computational reduction oracle occurs. No umbrella or full build was run. `scripts/formal_tools.py lint` and `git diff --check` passed; lint reported only existing large-file warnings. The adjusted forward-multiplier module documentation also passed a direct Lean check. All owned Lean commands terminated.

No numerical experiment or computational proof certificate is used.
