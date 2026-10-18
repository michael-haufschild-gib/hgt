# Stability of normalized sixth sieve readouts

- **ID:** biscale-sixth-readout-stability-1810
- **Stage:** 3-formalized
- **Type:** BRIDGE; unconditional bounds and actual-sieve sharpness formalized
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

- This is a stability statement for the complete normalized Fourier readout matrix. A Fourier readout is not one raw lag observation. `PrimeRawMomentRecovery` now transfers these bounds to a specified `64M²` literal-lag protocol and its indexed raw noise.
- The generic one-mode scaling and two-mode sign collision are formalized in `SixthReadoutStability`. [PrimeReadoutSharpness](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/PrimeReadoutSharpness.lean) now embeds both in actual sieve signals at every cutoff `N+10` and proves the impossibility statements for every real exponent. The prime-family exponents `1/6` at zero and `1/3` on a nonzero-mass stratum are sharp.
- The scalar inequalities and rank-one Gram argument are classical mechanisms. [Eldar–Mendelson](https://arxiv.org/abs/1211.0872) treats stability of quadratic phase retrieval; this application is not claimed as a new general phase-retrieval principle.
- [Bendory–Edidin–Kreymer](https://arxiv.org/abs/2103.01551) concerns linear measurements of high-order spectra. Its measurement count cannot be substituted for a count of literal individual lag observations.
- Corpus query `sixth readout stability Gram cube Holder exponent` returned exact sixth identities and other Gram estimates, without this estimate among the returned statements. Coverage was a snapshot, semantic completeness unmeasured, background refresh incomplete.
- [x] `SixthReadoutStability.lean`: direct artifact-producing `lake --old env lean -j 1` audit, exit 0 without diagnostics. Actual prime-family normalization and all three polynomial bounds are formalized.
- [x] All five public theorems have no mathematical premise binders; a clean `/tmp` audit prints only `propext`, `Classical.choice`, and `Quot.sound`. Leaf wired without compiling the umbrella.
- [x] Corpus index refreshed. Formal lint checked: no owned wiring or proof-placeholder errors; the global gate fails on concurrent package-root `TransHorizonIncidenceMechanics.lean` placement, outside this component's scope.
- [x] `PrimeReadoutSharpness.lean` passes its final artifact-producing named-source audit without diagnostics and is wired. Its four public theorems have no mathematical premise binders.
- [x] All four actual-sieve sharpness theorem axiom closures contain only `propext`, `Classical.choice`, and `Quot.sound`; the audit exits 0. Index refreshed. Final lint reports no owned wiring or placeholder error; unrelated wiring and package-root placement errors remain.
- [ ] Extend the stability analysis to the mixed-valuation ambiguity classification.

This component does not close checklist item 5.

## Actual-sieve sharpness

At every cutoff `N+10`, set all prime coefficients to zero except those at `3` and `5`. The one-mode pair `(t,0)` versus `(0,0)` has sixth-power common-sign distance `T=t⁶` and actual normalized squared readout error `E=t¹²`. The two-mode pair `(1,t)` versus `(1,−t)` has `T=min(64t⁶,64)`, `E=8t⁶`, and total sixth mass `2+2t⁶`. Extra modes at larger cutoffs remain zero; no support enumeration is needed.

The exact power-barrier targets quantify over every real exponent `β`: a uniform bound `T≤C E^β` for `0<t≤1` exists exactly when `β≤1/2` on the first family and `β≤1` on the second. Since `T` is the sixth power of coefficient norm distance and `E` is the square of the observation norm, these are precisely the norm exponents `1/6` and `1/3`.

For completeness, the scalar argument does not rely on a numerical experiment or an unproved asymptotic. If `t^u≤C t^v` on `(0,1]` and `v>u`, take `t=exp(−(|C|+1)/(v−u))`. Dividing by `t^v` would give `exp(|C|+1)≤C`, contradicting `exp(s)≥s+1`. If `v≤u`, the bound holds with constant one. Positive fixed factors such as `64` and `8^β` are absorbed into the constant.
