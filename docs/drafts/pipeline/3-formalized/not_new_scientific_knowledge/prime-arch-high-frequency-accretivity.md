# Prime--archimedean high-frequency accretivity

- **ID:** `prime-arch-high-frequency-accretivity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / TOP-DOWN HYPOTHESIS DISCHARGE
- **Scientific status:** `[PROVED] [FORMALIZED] [BRIDGE] [NOT AN RH PROOF]`
- **Lean file:** `formal/GaloisForLFunctions/RHTower/PrimeArchHighFrequencyAccretivity.lean`
- **Statement:** The completed prime--Gamma accretivity criterion for RH needs to be checked only
  at countably many Gaussian-rational points of the left critical half-strip with positive height
  greater than `4`; the compact central band is unconditional and negative heights are
  discharged by reflection.

## Result

Write a centered point as

\[
s=\frac12+iz,
\qquad 0<\operatorname{Im}z<\frac12.
\]

The completed endpoint source bound already formalized in the corpus implies

\[
\frac{41}{2}<(\operatorname{Im}\rho)^2
\]

for every Xi zero.  Every centered spectral point
`a = -i(ρ - 1/2)` also satisfies `|Im a| < 1/2`.  The exact imaginary part of the relative-resolvent
atom paired with its critical-line conjugate is

\[
\operatorname{Im}\left[
\left(\frac1a-\frac1{a-z}\right)
+\left(\frac1{\bar a}-\frac1{\bar a-z}\right)
\right]
=
-\frac{2\operatorname{Im}z
\left((\operatorname{Re}z-\operatorname{Re}a)^2
+(\operatorname{Im}z)^2-(\operatorname{Im}a)^2\right)}
{\left((\operatorname{Re}z-\operatorname{Re}a)^2
+(\operatorname{Im}z-\operatorname{Im}a)^2\right)
\left((\operatorname{Re}z-\operatorname{Re}a)^2
+(\operatorname{Im}z+\operatorname{Im}a)^2\right)}.
\]

Consequently, if `0 ≤ R ≤ 4`, then

\[
\operatorname{Im}\operatorname{Tr}_{\Xi}^{\mathrm{rel}}(z)\le0
\qquad
(0<\operatorname{Im}z,\ |\operatorname{Re}z|\le R).
\]

Absolute summability and the multiplicity-exact line-conjugation equivalence justify the pairing.
Taking `R = 4` gives an unconditional rational central band.

The upper-strip involution

\[
z\longmapsto-\bar z
\]

preserves the imaginary part of the analytically continued source trace and reverses its
frequency.  Thus negative frequencies reduce to positive frequencies.  In the original
coordinate, the only remaining open sign is

\[
0<\operatorname{Re}s<\frac12,
\qquad
\operatorname{Im}s>4,
\qquad
\operatorname{Re}\bigl(\mathrm{completedPrimeGammaFlux}(s)\bigr)\ge0.
\]

Continuity of the source flux and density of `ℚ + iℚ` then prove the exact countable criterion

\[
\mathrm{RH}
\iff
\forall s\in\mathbb Q+i\mathbb Q,
\quad
0<\operatorname{Re}s<\frac12,
\quad
\operatorname{Im}s>4,
\quad
\zeta(s)\ne0
\Longrightarrow
\operatorname{Re}\bigl(\mathrm{completedPrimeGammaFlux}(s)\bigr)\ge0.
\]

## Top-down chain

```text
endpoint completed source value
  -> every Xi zero has height squared > 41/2
  -> conjugate-paired relative-resolvent atoms have the correct sign centrally
  -> full source sign is unconditional for |frequency| <= 4
  -> source reflection removes every negative high frequency
  -> only positive high-frequency prime--Gamma accretivity remains
  -> Gaussian-rational density reduces that obligation to countably many values
  -> full source anti-Herglotz criterion
  -> RH.
```

The open problem is now source-pure and one-sided: prove the prime--Gamma flux sign at positive
high Gaussian-rational values without importing Xi divisor locations or an RH-equivalent limiting
measure.

## Literature calibration

Horizontal monotonicity of `ξ` outside the critical line and its equivalence to RH are classical in
the form proved by Sondow and Dumitrescu, [A monotonicity property of Riemann's xi function and a
reformulation of RH](https://arxiv.org/abs/1005.1104).  The present theorem is a formal
source-coordinate localization of that parent criterion using the project's endpoint height gap,
reflection law, and Gaussian-rational source domain.  No novelty claim is made.

## Lean certificate

The principal declarations are:

```text
relativeResolvent_conj_pair_im_formula
xiRelativeResolventTerm_lineConj_pair_im_nonpos
xiRelativeResolventTrace_im_nonpos_lowFrequency
continuedPrimeArchSourceRelativeTrace_im_nonpos_lowFrequency
continuedPrimeArchSourceRelativeTrace_im_nonpos_nine_tenths
continuedPrimeArchSourceRelativeTrace_im_nonpos_four
continuedPrimeArchSourceRelativeTrace_neg_conj_im
ContinuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz
continuedPrimeArchUpperAntiHerglotz_of_positiveHighFrequency
continuedPrimeArchPositiveHighFrequencyUpperAntiHerglotz_iff_riemannHypothesis
CompletedPrimeGammaPositiveHighAccretive
completedPrimeGammaPositiveHighAccretive_iff_centered
CompletedPrimeGammaGaussianRatPositiveHighAccretive
completedPrimeGammaGaussianRatPositiveHighAccretive_iff_riemannHypothesis
```

The module is imported by `GaloisForLFunctions.RHTower`.

## Gates

- [x] 0 → 1 in-progress: source-pure one-sided discharge isolated
- [x] 1 → 2 fully-proven: atomwise identity, summation, reflection, and density proofs complete
- [x] 2 → 3 formalized: placeholder-free Lean module and umbrella import
- [ ] 3 → 4 publication-ready: not proposed; this is an RH bridge theorem
