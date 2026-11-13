# Exponential barriers for confining half-line minimizers

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Target:** B104; regularize the actual arithmetic forcing near the terminal endpoint.
- **Statement:** For every `R>0`, every actual minimizing profile `F`, and every `1/2<β<15/2`, there is `C≥0` with `|F(u)|≤C exp(βu)` almost everywhere on `u<0`. Consequently `∫F²exp(-bu)<∞` for every `b<15`.
- **Status:** Paper argument below; Lean formalization in progress. Not counted. No boundary trace or polar-charge conclusion.

## Corpus connection

`IsHalfLineEnergyMinimizer.weakEquation` allows every actual-domain test.
`TheCompletedWeilRieszVectorsAreBounded` proves a finite-window maximum
principle by positive-level truncation and divergent cutoff Gamma row mass.
Here the actual exponential potential absorbs the complete prime row after
an exponential change of unknown. The finite-window theorem itself does not
apply to the half-line.

`lintegral_archSymbol_mul_normSq_fourier` identifies finite jump energy with
the positive Gamma-symbol energy. `integrable_gamma_add_const_mul` supplies
its linear closure. `integrableOn_mul_archLevyDensity` controls the barrier's
jump energy; `archimedean_tail_integral_unbounded` supplies the divergent
cutoff mass. The Chebyshev bound and
`summable_vonMangoldt_div_rpow` control both prime rows.

## Paper proof

Write `a=a(R)>0`, `λ=λ(R)`, `ω(h)=exp(-h/2)/(1-exp(-2h))`, and
`φ(u)=exp(βu)1_{u<0}`. All profiles are real and vanish on `[0,∞)`.
Fix a minimizing `F` and `1/2<β<15/2`.

**Admissible positive-level tests.** Direct integration gives
`‖φ‖₂²=1/(2β)` and
`‖φ-φ(·+h)‖₂²=(1-exp(-βh))/β≤h` for `h>0`.
The barrier belongs to `L¹∩L²`, and `∫₀∞hω(h)dh<∞`; hence its jump
energy is finite. The extended Lévy–Plancherel identity recovers Gamma
integrability: its nonnegative shifted Gamma-symbol integral is finite,
and adding the constant mass term recovers the absolute full Gamma
integral. The same identity proves that a real contraction fixing zero
preserves this domain.

For `t≥0`, put `G=(F-tφ)₊`. Linear Gamma closure followed by contraction
proves Gamma integrability of `G`. Moreover `0≤G≤|F|`, so ordinary and
eighth-exponential square integrability and `L¹` integrability follow from
those of `F`. Its support and measurability are preserved. Thus `G` is an
actual-domain test. Pointwise,
`FG=G²+t exp(βu)G≥0` on the negative half-line.

**The complete prime row.** For two negative points `u,v`, let
`p=F/exp(β·)` and `q=(p-t)₊`. Monotonicity gives

`F(u)G(u)exp(β(v-u))+F(v)G(v)exp(β(u-v))
 -F(u)G(v)-F(v)G(u)
 =exp(β(u+v))(p(u)-p(v))(q(u)-q(v))≥0`.

When either point is outside the half-line, both cross terms vanish.
Applying the inequality to every prime edge bounds the symmetric prime
mixed form by `∫rβ(u)F(u)G(u)du`, where

`rβ(u)=Σ_{n<exp(-u)}Λ(n)n^(β-1/2)+Vβ`,
`Vβ=Σ_nΛ(n)/n^(β+1/2)<∞`.

Since `β-1/2>0`, the finite sum is at most
`exp(-(β-1/2)u)ψ(exp(-u))≤6exp(-(β+1/2)u)`.
The resulting row times `FG` is integrable, because `β+1/2<8` and
`|FG|≤F²`. One may first sum finitely many edges, then use monotone
convergence for the nonnegative diagonal terms and absolute weighted
summability for the mixed prime form. This proves the complete-series
inequality without a prime cutoff in the conclusion.

**The small Gamma jumps.** Use the strictly positive full exponential
`χ(u)=exp(βu)` in the algebra below, including outside the half-line.
There `F=G=0`, and still `G=χ(F/χ-t)₊`. The identity

`(Fu-Fv)(Gu-Gv)
 =χuχv(pu-pv)(qu-qv)
  +(χu-χv)(FuGu/χu-FvGv/χv)`

and monotonicity show, after integrating with `v=u+h`,

`∫(F(u)-F(u+h))(G(u)-G(u+h))du
 ≥(2-exp(βh)-exp(-βh))∫FG`.

All terms for fixed `h` are integrable by `L²` Cauchy–Schwarz and
translation invariance. The mixed jump integrand is absolutely integrable
against `ω(h)dh` by Cauchy–Schwarz in the product jump measure. Also
`Cβ=∫₀¹(exp(βh)+exp(-βh)-2)ω(h)dh<∞`: on `0<h<1`, the parenthesis lies
between zero and `β exp(β)h`, and the first displacement moment is finite. Thus jumps below
any `0<δ<1` contribute at least `-Cβ∫FG`.

**The large Gamma jumps.** Put
`ρδ=2∫δ∞ω(h)dh` and
`KδF(u)=∫δ∞ω(h)(F(u+h)+F(u-h))dh`.
The cutoff kernel belongs to `L²`, so `|KδF(u)|≤Dδ` for almost every
`u`, with `Dδ` depending on `F,δ`. Fubini and translation invariance give
the large-jump mixed energy exactly as `ρδ∫FG-∫G KδF`.
Including the Gamma mass offset, the complete Gamma mixed form is at least

`(ρδ-C₀)∫FG-Dδ∫G`,

where `C₀=Cβ+2|gammaHardyPhaseRate 0|` is independent of `δ,t`.

**Absorption and vanishing of the truncation.** The polar mixed term is
bounded below by `-P∫exp(-u/2)G(u)du` for a finite `P≥0`, since both
hyperbolic kernels are bounded by `exp(-u/2)` on the half-line. Define

`Aδ(u)=a exp(-8u)+ρδ-C₀-λ-rβ(u)`.

The preceding bounds and the actual weak equation imply

`0≥∫[Aδ(u)F(u)G(u)-(Dδ+P exp(-u/2))G(u)]du`.

Because `β+1/2<8`, exponential dominance gives a finite lower bound on
`a exp(-8u)-rβ(u)-exp(-βu)-exp(-(β+1/2)u)` for `u≤0`.
Since `ρδ→∞` as `δ↓0`, choose `δ` so that

`Aδ(u)≥exp(-βu)+exp(-(β+1/2)u)≥1` for `u≤0`.

Now choose `t>max(Dδ,P)`. The identity for `FG` gives pointwise

`Aδ FG-(Dδ+P exp(-u/2))G≥G²`.

The left side is integrable: `|AδFG|` is bounded by a constant times
`F²exp(-8u)+F²`, and the remaining terms are weighted `L¹` pairings.
Thus `∫G²=0`, proving `F≤t exp(βu)` almost everywhere. The same
argument applies to `-F`, which has the same minimizing energy, and proves
the two-sided bound. Given `b<15`, choose
`max(1/2,b/2)<β<15/2`; then `F²exp(-bu)≤C²exp((2β-b)u)` is integrable.

## Lean status

`ArithmeticHodgeTheoryOfDegenerations/CausalReflection/HalfLineGammaContractions`
passes its final plain source audit without warnings, with exactly
`propext`, `Classical.choice`, and `Quot.sound`. It is wired; its required
olean exists. It proves both directions of the jump/Gamma domain bridge
and closure under zero-preserving real contractions.

Twelve further modules in `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/`
await final source audits:

- `NegativeHalfLineExponentialBarrier`: exact exponential autocorrelation, translation defect, and Gamma integrability.
- `ExponentialBarrierPositiveLevels`: admissibility of positive-level tests in the actual domain.
- `HalfLineGammaMixedEnergy`: absolute integrability and the exact mixed Lévy identity.
- `HalfLineExponentialBarrierJumps`: the integrated exponential correction for each mixed Gamma jump.
- `ExponentialBarrierPrimeEdges`: the support-restricted diagonal comparison for each literal prime term.
- `ExponentialBarrierPrimeRows`: a Chebyshev bound for every finite forward row and convergence of the complete backward row.
- `ExponentialBarrierPrimeComparison`: the integrated complete prime mixed-form comparison, passing from finite edge sums by actual-domain absolute summability.
- `ExponentialBarrierSmallGammaJumps`: a cutoff-independent bound for the integrated small-jump loss.
- `HalfLineGammaCutoffKernel`: square integrability of the cutoff kernel, its bounded action on `L²`, and divergence of its row mass.
- `HalfLineGammaLargeJumps`: the cutoff-kernel realization, both ordinary-mass row bounds, and the exact integrated large-jump identity and lower estimate.
- `ExponentialBarrierPotential`: absorption of the growing prime row and both barrier weights by the eighth-exponential potential.
- `ExponentialBarrierPoleComparison`: both polar terms are bounded below by the test's half-exponential ordinary mass.

The unchecked helper `HTGeometry/HardyBoundary/WeightedPositiveLevelAlgebra`
proves the weighted row inequality and exact relative-jump decomposition.
The additional unchecked helper `HTGeometry/HardyBoundary/TranslationKernelPairing`
justifies Fubini for a nonnegative integrable kernel against arbitrary measurable
`L²` profiles and bounds the mixed pairing by ordinary mass when the kernel is
also `L²`. One of fifteen supporting modules is audited and wired.

The full Gamma comparison and maximum-principle conclusion remain to be
formalized. The complete prime comparison and large-jump Gamma estimate are written but unaudited. No barrier theorem or
contribution is counted yet.

## Boundary implication and limit

Taking `β=1` bounds the complete prime forcing near `u=0`: forward prime
shifts vanish in a sufficiently small terminal interval, and backward
shifts are bounded by a multiple of `ΣΛ(n)/n^(3/2)`. Together with the
existing bounded logarithmic cutoff commutator, this supplies the regularity
needed for a localized Green equation. Identifying that equation, its
normalized trace, and the trace's relationship to the polar source remain
separate obligations. The argument does not show that `exp(-8u)F` is
globally `L²`.

No sharpness at moment order `15` is claimed. The corpus identity
`ArithmeticIncidencePositivity.primeShift_sub_polarDensity_eq_chebyshev`
cancels the leading prime and two-pole densities on smooth compact tests;
their residue is the two-pole Chebyshev defect. Separate absolute row
bounds cannot establish a nonzero leading tail for the actual minimizer.
Extending that compensated identity to its measurable weak equation is a
different obligation.
