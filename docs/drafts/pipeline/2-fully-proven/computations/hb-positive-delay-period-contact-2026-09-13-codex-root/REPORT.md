# Positive-delay common-period contact: geometric near-cancellation, not selection

## Result

For the explicit direct common-period contribution in `hb-positive-delay-characteristic-current.md`, set `delta=2*rho-1` and

`A(delta,V)=integral_0^V R_delta(h) * ((CQ(h)+Cjet(h))*J_V(h)-C11(h)*I10(h)) dh`.

This retains all five finite period coefficients through `CQ`, the onset jet, the regular `R_delta(0)=log 2` realization, fixed smooth clock, moving endpoint, and `I10` contact. It does **not** include endpoint-primitive forcing, image sheet, angular cusp face, terminal physical face, or lift/response cross-currents.

At the first 64 zeta ordinates (`delta=2*i*gamma`), the signed complementary response `A(delta,V)-A(-delta,V)` did not vanish:

- At `V=4`, median relative residual was `0.0561285832`, minimum `0.0350261600`, and no sample was below `1e-6`.
- Eight local-spacing-matched height ensembles gave median residuals `0.05559`--`0.05645`; empirical rank `p=0.667`. Zeta heights were not distinguished.
- Terminal-cutoff medians were `0.05603178`, `0.05612858`, and `0.05613011` at `V=2,4,8`.
- Complementary values were conjugates to computed precision, so the signed response is purely imaginary on the critical line. Its relative size falls with height, but its absolute size grows: about `3.26e6` at zero 1 and `5.70e11` at zero 64 for `V=4`.

The falling residual is geometric high-frequency phase alignment. On zeros 33--64, `gamma * relative residual` lies in `[5.95091,5.96593]`; all 512 matched controls give `[5.94928,5.96669]`. A log fit over zeros 1--64 has exponent `-1.0542`, while controls give `-1.0557`. Arbitrary heights at `gamma=200` retain `gamma * residual=5.9477`--`5.9487` across `V=2,4,8`. Attempts at `gamma>=300` lose crossed-order stability and are recorded only as a numerical boundary, not evidence for an asymptotic constant.

Component intervention identifies the mechanism. At order 192, median internal signed cancellation is only `0.66743`, not a delicate many-term extinction. Removing `CQ*J` raises median relative residual to `0.992663`; removing the onset jet changes `0.05612864` to `0.05612948`; removing the retained `I10` contact changes it to `0.07017015`. Median signed magnitudes at order 80 were approximately `6.86e10` (`CQ*J`), `4.68e6` (onset jet), and `1.37e10` (`I10`). The same hierarchy occurs at matched controls. Thus this channel is a dominant period response partially opposed by the lower contact, with negligible onset-jet effect in this tested contraction.

Reverse search strengthens the negative result. Of 256 zeta-neighborhood complex secant starts at `V=4`, 151 converged and deduplicated to six roots. Only the forced root `delta=0` survived order-128 evaluation at `V=2,4,8` (`max relative residual 2.28e-20`). Five nontrivial fixed-`V` roots had local residuals below `9e-8`, but cross-cutoff maxima between `0.286` and `0.845`. A single temporal face therefore manufactures convincing off-line roots that disappear when the face moves.

## Big picture

This direct source layer contains a **critical-line phase law**, not a zeta spectrum. Complementary symmetry makes the critical line special and drives relative branch mismatch toward zero with frequency, while the absolute current remains large and zeta ordinates behave like nearby nonzeros. In the landscape where zeta lives, small high-zero residuals are therefore cheap: geometry alone creates them without arithmetic information.

For HB Identification, this computation evaluates an exact current ingredient but not the complete action. It shows why every face matters: the retained `I10` contact changes the leading response, and fixed-`V` roots move or vanish under terminal displacement. Any claimed physical-action/receiver identity that omits image, endpoint forcing, angular, or physical current faces can generate a false spectrum.

For HB Selection, the direct common-period coefficient is rejected as an independent extinction mechanism. Neither actual zeta heights nor its nontrivial inverse roots survive matched controls and cutoff variation. The structural survivor is useful: branch conjugacy plus an approximately inverse-height phase mismatch explains systematic near-zeros and supplies a future false-positive diagnostic.

For RH, proof space narrows to global arithmetic synchronization of the **complete** direct-minus-image, angular, endpoint, terminal, and lift/response assembly. Symmetry, pure phase, decreasing relative residual, or roots at one cutoff cannot select the zeta divisor. If the literal all-face action stays nonzero at actual Xi occurrences, that falsifies HB extinction as an RH route, not RH. If it vanishes, selection still requires a source-side theorem that excludes off-line occurrences without assuming RH.

## Method and validation

`PROTOCOL.md` froze four hypotheses and mechanically instantiated all 24 conjecture-attack methods before results. Variations include actual/matched heights, `V=2,4,8`, orders 48--192, component removal, inverse roots, arbitrary-height extremes, transition splitting, complementary reversal, and endpoint-aware regularization.

The full landscape used order 128; selected crossed refinements used order 192. Maximum absolute change in relative residual was `3.79e-6`. Component medians at orders 80 and 192 agree within `1.94e-7`. Root validation used three independent terminal cutoffs. Computation used 16 processes per job on both supplied RunPods. This is floating-point evidence for the current analytical formulas, not a Lean proof or interval enclosure.

Repository revision: `9d774a1ea257311ad02f21d521ec31441b980657`.

## Next experiment forced by result

Evaluate Lean's literal `signed_delay_finite_transfer`: complete direct-minus-image finite clock contracted with the original native spin-two trace, then antisymmetrize ordered source branches. Its endpoint currents are already proved zero. Persistence across `(x,y,X,k,V)` can decide whether image geometry adds real coherence or only another family of movable fake zeros before physical/angular faces are attached.
