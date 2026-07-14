# Xi endpoint strong height gap

- **ID:** `xi-endpoint-strong-height-gap`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / UNCONDITIONAL SOURCE BOUND
- **Scientific status:** `[PROVED] [FORMALIZED] [BRIDGE] [NOT AN RH PROOF]`
- **Lean file:** `formal/GaloisForLFunctions/RHTower/XiEndpointStrongHeightGap.lean`
- **Statement:** The completed endpoint source value alone forces every nontrivial Xi zero above
  squared height `41/2`, hence Xi is zero-free for `|Im ρ| ≤ 9/2` and centered Xi is zero-free for
  `|Re z| ≤ 9/2`.

## Result

Let

\[
C=2+\gamma-\log(4\pi)
\]

be the completed endpoint curvature.  The corpus now proves both

\[
0<C<\frac2{43}
\]

and the pointwise inverse-source height law

\[
\frac1C-1\le (\operatorname{Im}\rho)^2
\]

for every Xi divisor copy, with analytic multiplicity retained.  Therefore

\[
\frac{43}{2}<\frac1C
\quad\Longrightarrow\quad
\frac{41}{2}<(\operatorname{Im}\rho)^2.
\]

This propagates from multiplicity copies to divisor support and arbitrary zeros of `xi`.  Since

\[
\left(\frac92\right)^2<\frac{41}{2},
\]

Lean obtains the unconditional bands

\[
|\operatorname{Im}\rho|\le\frac92\Longrightarrow\xi(\rho)\ne0
\]

and

\[
|\operatorname{Re}z|\le\frac92\Longrightarrow\Xi_C(z)\ne0.
\]

No zero enumeration, RH assumption, real-rootedness premise, interval-arithmetic zero
verification, or limiting spectral measure occurs in the proof.

## Top-down consequence

The conjugate-paired relative-resolvent sign is controlled by

\[
(\operatorname{Re}z-\operatorname{Re}a)^2
+(\operatorname{Im}z)^2-(\operatorname{Im}a)^2.
\]

For a centered Xi spectral point, the open critical strip gives
`|Im a| < 1/2`, while the new height law gives `(Re a)^2 > 41/2`.  Hence the paired sign is
unconditionally nonpositive throughout `|Re z| ≤ 4`.  This enlarges the previously formalized
source-sign band and removes every source test of height at most four from the open RH input.

## Literature calibration

Large rigorous zero verifications are classical and vastly exceed height four; for example
[Platt and Trudgian](https://arxiv.org/abs/2004.09765) verify RH through height `3·10^12` by
interval arithmetic.  The theorem here is not
presented as a competitive zero computation.  Its project role is that the zero-free band, and the
radius-four resolvent corollary, follow symbolically from one exact completed source value already
used by the proof architecture.

## Lean certificate

```text
xiZeroCopy_fortyOne_div_two_lt_im_sq
xiDivisorSupport_fortyOne_div_two_lt_im_sq
fortyOne_div_two_lt_im_sq_of_xi_eq_zero
xi_ne_zero_of_abs_im_le_nine_halves
XiC_ne_zero_of_abs_re_le_nine_halves
xi_ne_zero_of_abs_im_le_four
XiC_ne_zero_of_abs_re_le_four
```

The module is imported explicitly by `GaloisForLFunctions.RHTower` and consumed by
`PrimeArchHighFrequencyAccretivity`.

## Gates

- [x] 0 → 1 in-progress: exact endpoint composition isolated
- [x] 1 → 2 fully-proven: scalar inequality and divisor-support propagation complete
- [x] 2 → 3 formalized: placeholder-free Lean module and umbrella wiring
- [ ] 3 → 4 publication-ready: not proposed; the theorem is proof-route infrastructure
