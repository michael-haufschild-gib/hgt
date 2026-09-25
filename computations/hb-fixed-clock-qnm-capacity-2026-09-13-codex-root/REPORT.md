# Fixed-clock and QNM cancellation-capacity audit

## Outcome

Two apparent extinction mechanisms fail for different reasons.

The literal fixed onset is a powerful generic high-frequency suppressor.  It does not identify zeta heights.  At unit duration, the worst normalized coherence across four physical branch/side channels and overtones `0..8` fell from `0.297675` at zeta zero 1 to `0.00368429` at zeta zero 10.  The neighboring midpoint control at comparable height gave `0.00404877`; synthetic tilts `beta=.2,.8` gave `0.00365463` and `0.00395880`.  At duration 3, corresponding worst coherences were `5.61e-5`, `6.61e-5`, `5.53e-5`, and `6.38e-5`.  Zeta and control medians were indistinguishable at the scale relevant to selection.

The strongest discovered single-channel event is exact but nonselective.  For the synthetic off-line point `rho=.8+49.7738324776723 i`, branch 0 / side 0 / overtone 1 maps to a purely imaginary pulse argument.  Its literal onset vanishes at

`L = 2.764013702173634464298570494968641687076268486047...`.

Direct 80/120-digit quadrature and an independent integration-by-parts formula agree to `2.13e-81` and `3.10e-121`.  At this same duration, all 36 tested channel coherences are below `9.44e-5`, but only one is exactly zero.  Small beta perturbations replace the exact zero by a near-zero.  This is a concrete warning: finite-precision fixed-clock darkness can appear overwhelmingly convincing at an off-line control without common exact extinction.

The QNM experiment exposed a complementary finite-time illusion.  With the exact two BM Jost towers at `beta=.5`, first zeta ordinate, 32 modes can approximate a normalized persistent counterterm on `[0,2]` with held-out maximum error `1.94188e-4`.  The coefficient variation is `1.1746995e10`.  High-precision reevaluation confirms the residual.  A deterministic relative coefficient perturbation of `1e-12` raises maximum error to `0.002822`; `1e-10` raises it to `0.28122`.  The fit is a near-null-space cancellation, not robust extinction.

For comparison, the same 32-mode family on `[0,1]` reached maximum error `1.17e-8` with variation `4.64e5`; at larger height `gamma=49.77`, the best explored `[0,2]` error exceeded one.  No tested regularization produced useful `[0,4]` or `[0,6]` matching.  These last failures are finite numerical observations, not impossibility proofs for every finite packet.

## Exact quantitative obstruction

For `0<beta<1`, every plus-tower mode damps at least at rate `a=1+beta/2`, and every minus-tower mode faster.  Therefore any Jost-supported discrete packet of total variation `V` has magnitude at delay `T` at most `V exp(-a T)`.  Approximating the nonzero normalized AIME counterterm with endpoint error at most `epsilon<1` requires

`V >= (1-epsilon) exp(a T)`.

Persistent matching forces `V` to diverge.  This elementary quantitative bound is the finite-window face of the current Lean arbitrary-finite-variation theorem: a persistent counterterm cannot be carried by the complete strictly damped BM Jost divisor.  Passive stationary mass only increases the nonzero target numerator, so omitting it here gave cancellation its most favorable case.

## Consequences for the two proposed HB steps

Fixed-clock extinction cannot be inferred from small numerical response.  Literal onset smoothing suppresses zeta heights, midpoint controls, and off-line controls alike; a single channel can vanish exactly off-line after clock tuning while every other channel becomes numerically tiny.  Any valid selector must use exact common extinction, retain source independence, and prove that no duration/height tuning entered.

Full temporal/metric/QNM matching cannot be rescued by adding more ordinary damped QNMs or by modewise/all-order frequency renormalization.  Finite packets can manufacture excellent short-window fits with enormous, unstable coefficients, while every bounded finite-variation completion decays and leaves the exact nonzero AIME residue.  A route-wide impossibility theorem now reduces to one concrete identification lemma: prove that every correction allowed by the complete source-retaining metric action is passive stationary data plus finite-variation spectral mass supported on the classified full BM Jost divisor.  Once that is proved, the existing exact no-go theorem kills the entire matching/extinction class.

The only surviving escape sectors are non-polar threshold/peripheral support, zero-damping or growing modes, infinite variation, or additional all-face boundary terms outside the Jost-supported class.  Each is a sharply named physical/mathematical liability rather than generic “missing cancellation.”

Landscape meaning: fixed clocks behave as ordinary filters, and QNM richness behaves as an interpolation basis.  Neither supplies arithmetic selection.  Zeta geometry can enter only through an invariant source-retaining all-face residue whose vanishing is exact and cannot be manufactured by clock tuning or ill-conditioned spectral synthesis.  Failure of these HB mechanisms would reject this route, not RH; falsifying RH still requires a certified off-critical zero of zeta.

## Verification and scope

Pulse results used 320-node quadrature across the full atlas; selected cases agreed with 640 nodes to maximum absolute difference below `3.5e-14`.  Exact single-channel zero used independent high-precision formulas.  QNM fits used 401 training and 2,001 held-out points; the strongest finite-window fit was reevaluated at 80 digits and perturbed.

No claim is made that the complete metric boundary/action correction already satisfies the decisive finite-variation Jost-support hypothesis.  No synthetic off-line point used here is asserted to be a zeta zero.  `PROTOCOL.md` records all 24 method applications and frozen thresholds.
