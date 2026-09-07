# CCM-FU: quadratic arithmetic sign-defect mass

- **Stage:** 3-formalized
- **Type:** [BRIDGE], derived arithmetic estimate.
- **Goal:** Complete signed Abel source bound, full CCM-FU chain, RH.
- **Parent:** [complete reserve-extension induction](../1-in-progress/ccm-fu-reserve-extension-induction.md).
- **Proved:** For every `M>=143360000000000`,
  `M^2/2048000000000 <= D_{2}(M) <= 722*M^2`, where D is the literal
  reversed-Möbius-parity energy after selecting 2.

The current induction must compare released quadratic energy with the
newly created geometric defect. The complete first-prime reserve has an
unconditional quadratic lower bound. A claim that the prime-two defect is
lower order would therefore simplify the comparison, but the actual source
has the opposite behavior: its defect itself has quadratic scale. This estimate
does not decide whether the full reserve pays that cost.

The existing analytic cutoff-seven boxes prove
`K_2(7)-K_1(7)>=3/125`. For `M=7d+t`, exact clipped homothety gives

`K_(2d)(M)-K_d(M)=sqrt(d)*(K_2(7)-K_1(7))`
` +(sqrt(M)-sqrt(7d))*(D(3)-D(7))`.

The proved divisor-source bound gives `D(3)-D(7)>=-120`.
If `10000*t<=d`, then `sqrt(M)-sqrt(7d)<=sqrt(d)/10000`.
Hence the channel reversal is at least `sqrt(d)/100` throughout this
entire clipped interval, not only at the exact dilation endpoints.

Put `N=floor(M/7)` and `L=floor(N/100000)`. For `N>=20480000000000`, every
`N-L<d<=N` lies in that interval and satisfies d>=N/2. The complete odd
squarefree mass there is at least L/8: apply the existing coprime window
estimate, density at least one quarter, and `R=floor(L/32)+1`. At the
fixed large threshold, `N<=R^2` and `2R+L/R<=L/8` hold.

Each such d gives a distinct retained prime-factor label and contributes
at least `d/10000` to the actual defect. Thus the complete defect is at least
`N*L/160000`. Since `L>=N/200000` and `M<=8N`, this gives the stated lower
bound. All other defect terms are nonnegative. Initial parity contraction
and the exact good/defect partition put D below the original diagonal,
which is at most `722*M^2`. The coefficient count is analytic, and the
seven-cutoff input is an existing Lean theorem proved from analytic bounds;
no computed values enter this proof.

The exact theorem is
`RHTower.mobiusDivisorParityDefectEnergy_two_quadratic_bounds` in
`formal/GaloisForLFunctions/RHTower/MobiusDivisorQuadraticFirstDefect.lean`.
The other new public theorem is
`RHTower.divisorUnsignedDilationChannel_two_clipped_reversal`.
Scratch and exact-file checks pass; only the new module's olean was emitted.
Both new public declarations were axiom-audited once and depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The module is wired into
`RHTower.lean`; the corpus index is refreshed and formal lint passes, with
the existing large-file warnings. No numerical experiment, full build or
umbrella build was run.
The previously established stale dependency traces prevent a narrow Lake
dependency audit without rebuilding unrelated modules; that audit remains
unperformed.

This settles the quadratic order of the actual first-prime defect. It does
not compare the coefficients of released reserve and geometric cost, or
assert that the first-prime certificate fails. The two-prime ceiling, uniform
signed mixed-state comparison, complete reserve-extension induction and RH
remain open.
