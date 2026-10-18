# Stability of normalized sixth sieve readouts

- **ID:** biscale-sixth-readout-stability-1810
- **Stage:** 3-formalized
- **Type:** BRIDGE; unconditional polynomial bounds formalized
- **Parent:** [field programme](../1-in-progress/biscale-field-development-1810.md), items 5–6

For a finite real coefficient vector `a`, write `R(a)ᵢⱼ=(aᵢaⱼ)³`. For the actual odd-prime sieve family this is exactly `P⁻⁶ sixthPairReadout`, including zero coefficients. Set `E=Σᵢⱼ(R(a)ᵢⱼ−R(b)ᵢⱼ)²` and `M=Σᵢ(aᵢ⁶+bᵢ⁶)`. There is a common sign `ε∈{1,−1}` such that, with

`T=Σᵢ(aᵢ−εbᵢ)⁶`,

`W=Σᵢ(aᵢ−εbᵢ)²(aᵢ²+bᵢ²)²`,

we have `T²≤512E`, `MT≤32E`, and `MW≤8E`.

These inequalities are unconditional, including empty support and the zero vector. In norm notation the first gives

`minε ‖a−εb‖₆ ≤ 2^(3/4) ‖R(a)−R(b)‖F^(1/6)`.

The constant is an explicit bound, not asserted optimal. The exponent `1/6` cannot increase on any neighbourhood containing zero: on one active mode, distance from zero is `|t|` and observation norm is `|t|⁶`.

When `M≥m>0`, the second bound gives exponent `1/3` with constant `(32/m)^(1/6)`. When also `aᵢ²+bᵢ²≥μ²>0` at every retained mode, the third yields `‖a−εb‖₂≤sqrt(8/m) μ⁻² ‖R(a)−R(b)‖F`. These nondegenerate consequences have stated domain bounds; the primary polynomial inequalities require none.

## Dependency-closed proof

Put `xᵢ=aᵢ³`, `yᵢ=bᵢ³`. Choose `ε` so that `z=Σᵢxᵢ(εyᵢ)≥0`. Let `A=Σxᵢ²`, `B=Σyᵢ²`, and `D=Σ(xᵢ−εyᵢ)²=A+B−2z`. Expanding the Gram discrepancy gives `E=A²+B²−2z²`. Therefore

`2E−D²=(A−B)²+4zD≥0`,

`2E−(A+B)D=(A−B)²+2zD≥0`.

No inverse or nonvanishing argument is used. For arbitrary real `u,v`, the following identities have nonnegative right sides:

`16(u³−v³)²−(u−v)⁶ = 3(u−v)²(u+v)²(3(u+v)²+2(u−v)²)`,

`4(u³−v³)²−(u−v)²(u²+v²)² = (u−v)²(u+v)²(2(u²+v²)+(u+v)²)`.

Summing gives `T≤16D` and `W≤4D`. Combine with the two Gram inequalities to obtain the three claims. Replacing `b` by `−b` leaves `M,E` and coordinate square weights unchanged, so both orientations are covered.

## Boundaries and remaining gates

- This is a stability statement for the complete normalized Fourier readout matrix. A Fourier readout is not one raw lag observation. Raw sampling and its noise amplification remain item 6.
- The generic one-mode scaling and two-mode sign collision are formalized as `one_mode_scaling` and `two_mode_vanishing`. They give the exact powers behind sharpness of `1/6` at zero and `1/3` on a nonzero-mass stratum. Explicit actual-sieve embeddings and the real-exponent impossibility statements remain to be packaged in Lean.
- The scalar inequalities and rank-one Gram argument are classical mechanisms. [Eldar–Mendelson](https://arxiv.org/abs/1211.0872) treats stability of quadratic phase retrieval; this application is not claimed as a new general phase-retrieval principle.
- [Bendory–Edidin–Kreymer](https://arxiv.org/abs/2103.01551) concerns linear measurements of high-order spectra. Its measurement count cannot be substituted for a count of literal individual lag observations.
- Corpus query `sixth readout stability Gram cube Holder exponent` returned exact sixth identities and other Gram estimates, without this estimate among the returned statements. Coverage was a snapshot, semantic completeness unmeasured, background refresh incomplete.
- [x] `SixthReadoutStability.lean`: direct artifact-producing `lake --old env lean -j 1` audit, exit 0 without diagnostics. Actual prime-family normalization and all three polynomial bounds are formalized.
- [x] All five public theorems have no mathematical premise binders; a clean `/tmp` audit prints only `propext`, `Classical.choice`, and `Quot.sound`. Leaf wired without compiling the umbrella.
- [x] Corpus index refreshed. Formal lint checked: no owned wiring or proof-placeholder errors; the global gate fails on concurrent package-root `TransHorizonIncidenceMechanics.lean` placement, outside this component's scope.
- [ ] Actual-sieve sharpness packaging.
- [ ] Extend the stability analysis to the mixed-valuation ambiguity classification.

This component does not close checklist item 5.
