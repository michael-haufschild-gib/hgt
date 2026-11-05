# WD — what remains for an unconditional RH proof

**RH open.** The corpus proves the receivers below, not their decisive arithmetic estimates.
Proving **one** complete alternative suffices; the branches need not all be closed.

## 1. Cofinal long-Möbius second moments

For `M_X(s) = Σ_{1≤n≤X} μ(n)n^(−s)`, prove:

> There exists a fixed `K ≥ 0` such that, for arbitrarily large `θ > 0`, some `C_θ ≥ 0` satisfies
>
> `∫_1^T |ζ(½+it) M_floor(T^θ)(½+it)|² dt ≤ C_θ T^K`
>
> for unboundedly many heights `T`.

- **Done:** this estimate implies RH, including exclusion of finite and arbitrarily shallow off-line exceptions.
- **Open:** the actual upper bound, with `K` independent of `θ`. Constants and height subsequences may depend on `θ`.
- **General version:** fixed `B≥1`, `K≥0`; normalized `b₁=1`, `|b_d|≤B`, length `X≤T^θ`, and coefficients of `ζM` vanish for `2≤n≤X₁`, where `X₁≥T^(3θ/4)`. The Möbius specialization already supplies normalization, boundedness and cancellation.
- **Boundary:** dyadic `O(T)` bounds with the stated prefix cancellation give only finitely many zeros of depth `≥1/(2θ)+ε`. This does not control every finite/shallow exception as `θ` varies. The prefix integral `[1,T]` is essential to this receiver.

Source: [TwoSidedThetaMollifierTrap.lean](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/TwoSidedThetaMollifierTrap.lean), `riemannHypothesis_of_cofinal_long_mollifier`, `riemannHypothesis_of_cofinal_moebius_mollifier`.

## 2. Uniform dyadic unit-window bound

Fix `c₀>0` (`c₀=1` suffices). Set `L=2^k c₀ log T`, `n=apertureStage L T` and
`R(γ)=finiteThetaSourceMomentReading (baseTwistTest γ) L 1 n`. Prove:

> `∃ C, ∀ k∈ℕ, ∀ T≥2, min_{γ∈[T,T+1]} R(γ) ≤ C`.

- **Done:** this bound is equivalent to RH. Unit-window mean, supremum or C²-jet bounds are interchangeable alternatives; proving all four is unnecessary.
- **Open:** one constant uniform in both height `T` and dyadic scale `k`.
- **Boundary:** a separate constant at each fixed scale is insufficient.

Source: [UnitWindowMinimumAndOscillation.lean](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/LogScaleHeckeDefect/UnitWindowMinimumAndOscillation.lean), `riemannHypothesis_unitWindow_min_mean_max_finiteTheta_tfae`.

## 3. All-window, all-stage collision sectoriality

Prove positivity of the actual Bessel–Szegő certificate times the centered collision loop on the unit circle:
every Burnol window `m`, every stage selector `S`, every `N≥besselUnitPrefix m S`, and every certificate order satisfying the theorem's explicit remainder bound.

- **Done:** this exact source-sectoriality condition is equivalent to RH.
- **Open:** the source-side sign uniformly through the prescribed growing prefixes and stages.
- **Boundary:** fixed-prefix behavior above its cusp horizon does not supply that uniform sign. Finite-theta purity alone requires the prescribed passage to the ζ source.

Source: [LogStageBesselCertificate.lean](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/SzegoCollision/LogStageBesselCertificate.lean), `riemannHypothesis_iff_unitStage_besselSzego`.

### Port / energy distinction

On a boundary-regular finite-theta window:

- **Uniformly bounded right port** ⇔ all window zeros lie on the critical line.
- **Unweighted right-port L² integrability** ⇔ the window has **no zeros at all**, including on-line zeros. This is not the RH target.
- Weighted window energy `e^(−xt)|𝒵(t)|²` is integrable precisely when `x` exceeds twice the maximal depth. Every positive exponent, not exponent zero, detects purity.

Sources: [RightHalfPortCriticalLineControl.lean](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/WindowPortFlux/RightHalfPortCriticalLineControl.lean), [WindowEnergyLaplace.lean](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/SzegoCollision/WindowEnergyLaplace.lean).

## Density estimates are weaker targets

- Moment `→1` with `log N=o(T)` ⇒ critical-scale clustering.
- Excess `O(1/log T)` with `log N≤T/log T` ⇒ log-free density/occupancy. Length `exp(c log²T)` is a possible sufficient regime, not a constructed mollifier.
- Neither clustering nor `D_win` excludes sparse off-line zeros or proves a critical-line zero proportion.

## Restrictions, with scope retained

- Fixed polynomial length and normalized unit-bounded coefficients cannot give moment `→1`: the proved floor is `1+1/(8+6θ)` in its stated regime. This does **not** refute branch 1's weaker `C_θT^K` bound with unbounded `θ`.
- Excess `K₀/log T` forces `log N≥log²T/(6K₀)−(4/3)log T` eventually. This necessary lower bound proves no attainable optimum.
- Impure-factor-stable upper bounds and generic detector norms do not force the needed arithmetic conclusion. These are scoped obstructions, not bans on every upper-bound or detector method.
- Linear Möbius-taper defect is a CTF receiver; sub-unit cubic trace norm is a TG receiver. Neither is an additional independent WD branch.

Source for moment/occupancy restrictions: [SubexponentialMollifierLengthAndWindowSpikes.lean](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/SubexponentialMollifierLengthAndWindowSpikes.lean).
