# Physical horizon angular-pair audit

## Question and exact target

The current Lean action identity cancels clock-energy and terminal-square pieces between the physical Einstein current and retained source contact.  The surviving horizon current is a nonzero scalar multiple of

`A = (2*mu-2)*(J0^2+J1^2) + 2*(J0*K0+J1*K1)`,

with `mu=-(gamma^2+1/4)`, `J=(S*S_y,-S*S_x)`, and `K=fullGradientCovector` for the normalized completed Eisenstein scalar `S`.  This audit asked whether that exact surviving face self-extinguishes at zeta-zero heights.

## Results

Symbolic cusp algebra gives, with `u=gamma*log y`,

`A_principal = -8*cos(u)*(cos(u)-2*gamma*sin(u))^2*((2*gamma^2+1)*cos(u)+gamma*sin(u))`.

Its exact logarithmic-phase mean is

`-(8*gamma^4 + 6*gamma^2 + 3)`,

strictly negative for every real `gamma`.  The physical horizon face therefore contains a universal nondecaying/log-periodic background and cannot extinguish by itself at critical-line zeta ordinates.

Numerical checks used the literal completed-Eisenstein Fourier expansion and the exact Lean covectors.  Finite differences converged at second order: successive relative errors were `1.21e-4, 3.03e-5, 7.57e-6` for `J` and `4.19e-6, 1.05e-6, 2.62e-7` for `K`.  Direct and closed principal formulas agreed to floating-point precision, and complementary branches agreed exactly in the implemented algebra.

The natural post-specialization `full - principal` modular-cell integral was negative at all 12 tested zeta zeros and all 12 midpoint controls.  Median normalized magnitudes were `0.692265` for zeta heights and `0.534651` for controls; square and gradient pieces reinforced rather than cancelled.  A scan from `gamma=10` through `50` in steps of `1.25` also found no sign change.  Selected cutoff tests retained sign:

| sample | `(Ymax, order)` | total remainder |
|---|---:|---:|
| zeta 1 | `(3,14)` | `-4.86285e5` |
| zeta 1 | `(4,18)` | `-4.82772e5` |
| zeta 1 | `(5,22)` | `-4.82772e5` |
| midpoint 1 | `(3,14)` | `-1.56246e6` |
| midpoint 1 | `(5,22)` | `-1.55518e6` |
| zeta 4 | `(3,14)` | `-3.38375e8` |
| zeta 4 | `(5,22)` | `-4.32656e8` |
| midpoint 4 | `(3,14)` | `-2.53889e7` |
| midpoint 4 | `(5,22)` | `-2.86903e7` |

This integrated sign is not pointwise positivity.  On 1,089 sampled modular points, the specialized difference had both signs at every tested zeta/control height.  Thus the observed negative integral is a global balance, not a local sign law.

## Interpretation

H1--H4 in `PROTOCOL.md` fail for the isolated horizon face: its principal term has a universal negative mean, actual zeros are not extinguished, neighboring controls behave the same way, and no stable zeta-specific root appeared.  Any viable HB identity must cancel this background through exact outer/cusp faces before attempting arithmetic selection.

More strongly, current Lean specialization no-go theorems show that a pointwise specialized cusp reporter cannot recover the analytic-family finite part in general.  Therefore the numerical `full - principal` integral is deliberately a false-world diagnostic, not the canonical HB landing.  It demonstrates why regularization must precede specialization; it is not evidence about the sign of the canonical family-level finite part.

Landscape consequence: zeta-dependent arithmetic corrections live on top of a larger universal geometric current.  A proof of RH through HB must first identify a complete all-face, family-level regularized action that removes this background without tuning to zero data.  If that exact assembly leaves the displayed mean uncancelled, the matching/extinction proposal is impossible.  Failure of this horizon-face proposal rejects that HB mechanism, not RH.

## Scope

No all-height sign theorem, interval certificate, canonical finite-part computation, outer-face matching, or RH implication is claimed.  Scripts and JSON outputs reproduce every reported number; `PROTOCOL.md` records the frozen 24-method design.
