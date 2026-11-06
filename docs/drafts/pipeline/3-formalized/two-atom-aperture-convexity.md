# Two-atom positivity from aperture convexity

- **Stage:** 3-formalized
- **Target:** Obstacles summary §2.5.5, all signed sections of `Θ₁+Θ₂`.
- **Status:** Every literal signed section is positive definite for `0<a<1/2`; determinants and successor Schur coordinates are strictly positive.

## Exact comparison

Set `w_a(r)=sinh(ar)+ar cosh(ar)`, `h=log 2`, `p=exp(-h/2)`.
The established first-atom tail density gives

`F_b(s)=4π^(-1/2) besselFirstAtomTailDensity(b/2,π exp s)>0` for `s≥0`.

For `t=log(nm)`, the positive radial part of the aperture-weighted pair is

`A_b(t)=exp(-t/2)∫_(s>t) w_a(s-t)F_b(s) ds`.

Thus the literal two-atom spectrum is

`A_b(0)+2cos(bh)A_b(h)+A_b(2h)`.

For `a≥0`, the weight is nonnegative, increasing and convex on `[0,∞)`;
it vanishes at zero. Extend it by zero to the negative half-line. For
every `s≥0` and `0≤p≤1`,

`2p w_a(max(0,s-h)) ≤ w_a(s)+p²w_a(max(0,s-2h))`.                 (1)

To verify (1), let `U=w_a(s)`, `V=w_a(max(0,s-2h))`, and
`M=w_a(max(0,s-h))`. Convexity gives `2M≤U+V`, monotonicity gives
`V≤U`, and

`U+p²V-p(U+V)=(1-p)(U-pV)≥0`.

If `s≤h`, then `M=0` and the inequality is immediate. If `s>h`,
the required midpoint inequality follows directly from

`w_a(u+h)+w_a(u-h)-2w_a(u)`
`=2(cosh(ah)-1)w_a(u)+2ah sinh(au)sinh(ah)≥0`, `u=s-h>0`.

Clipping a negative argument to zero only increases the last term.
Monotonicity follows from superadditivity on nonnegative arguments;
expanding the addition formulas leaves a sum of nonnegative terms.

Multiplying (1) by `F_b(s)>0` and using `cos(bh)≥-1` proves

`A_b(0)+2cos(bh)A_b(h)+A_b(2h)`
`≥∫_(0<s<h) w_a(s)F_b(s) ds>0` for `a>0`.                    (2)

The strict reserve comes from the initial center interval, where both
translated terms vanish. No frequency cutoff or numerical estimate enters.

## Literal all-rank bridge

`TwoAtomApertureWeight.thetaCenterTailWeight_two_atom_payment` proves (1).
`TwoAtomApertureSpectrum.twoAtom_apertureSpectrum_pos` proves (2) for
every real frequency and `0<a<1/2`.

Define the center-mixed source by its literal integral

`D_a(t)=∫_(s>0) s sinh(as) (Θ₁+Θ₂)(s/2+t)(Θ₁+Θ₂)(s/2-t) ds`.

The ordered-pair radial identity and triangular Fubini identify
`Re Fourier(D_a)(ξ)` exactly with the four-pair spectrum in (2) at
`b=-πξ`. For each pair, substitution
`u=πnm exp s` makes the complex kernel a real translate of
`firstAtomRadialKernel u z`, weighted by

`4(πnm)^(-1/2) log(u/(πnm)) sinh(a log(u/(πnm)))`.

The existing bound
`‖firstAtomRadialKernel u z‖≤9600 exp(-u/4)exp(-|Re z|)`
on `|Im z|≤π/6` absorbs this logarithmic/power weight. Dominated
holomorphic integration therefore makes `D_a` a Schwartz function and
commutes every derivative with its literal source integral. Fourier
inversion and strict spectral positivity then give, for every `N`,

`PosDef [Re((-i)^(j+k)) D_a^(j+k)(0)]_(0≤j,k<N)`.

## Lean declarations and audit

All modules are in `formal/GaloisForLFunctions/CompletedArithmeticForms/`.

| Module | Exact conclusion |
|---|---|
| `TwoAtomApertureWeight` | Pointwise diagonal payment (1) |
| `TwoAtomApertureSpectrum` | Strict four-pair spectrum (2) at every frequency |
| `ApertureRadialProfile` | Weighted strip envelope, Schwartz profile, radial jets and Fourier integral |
| `ThetaAtomPairComplex` | Entire ordered-pair kernel and exact radial translation |
| `ApertureTailFubini` | Triangular Fubini identity with the aperture primitive retained |
| `ThetaPairApertureJets` | Every literal aperture-weighted ordered-pair jet |
| `ThetaPairApertureFourier` | Exact Fourier identity with the ordered-pair spectrum |
| `TwoAtomAllRankAperture` | Literal two-atom sections, determinants and successor Schur coordinates |

The capstones are `twoAtomApertureMatrix_posDef`,
`twoAtomApertureMatrix_det_pos`, and `twoAtomApertureSuccessorSchur_pos`.
Their only parameters are the rank and `0<a<1/2`; no analytic premise
is added. Every module passed its final direct `lake --old env lean`
check. Transitive audits contain only `propext`, `Classical.choice`,
and `Quot.sound`. All eight modules are wired into the umbrella.

## Corpus anchors

- `ThetaPairCenterTailSpectrum.thetaPairCenterTailSpectrum_eq`: exact pair amplitude and cosine.
- `ThetaPairApertureRemainder`: absolute aperture integrability and exact pair signs.
- `FirstAtomRadialProfile`: complex strip envelope, dominated jets and Schwartz construction.
- `FourierPositiveHankel.signedSchwartzJet_hankel_posDef`: all-rank receiver.

The ordinary two-atom source lacks the full theta reflection identity;
its center integral must be proved directly, not replaced by the
full-source autocorrelation theorem.
