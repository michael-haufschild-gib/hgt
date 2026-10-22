# FZZ-P: analytic original subtracted screening source

Status: seven public theorems formalized and fully audited, 2026-09-11. Continued Gamma equality, the physical mixed Ward producer and RH remain unproved.

## Proof chain and exact obstacle

Fixed theta/FZZ source → full integrated mixed replica–momentum Ward law in an independently fixed phase frame → balanced external-Gamma vacuum-delay saturation → passivity → RH.

The [whole-plane cutoff audit](../../fzz-p-plane-screening-cutoff-matching.md) identifies the original finite part for two fixed punctures with independently shrinking cutoff disks. To use a continued expression in a marked source response, it must be proved equal to that prescription. This card closes the original source's separate analytic dependence; it does not replace the remaining equality theorem by an assumption.

## Exact source and statements

Set `R=1/2`, `K(alpha,beta,z)=|z|^alpha |z-1|^beta`, and write `E` for its integral outside the two open radius-`R` disks. Let

- `A0 = integral_(ball0 R) |z|^alpha (|z-1|^beta-1)`;
- `A1 = integral_(ball1 R) |z-1|^beta (|z|^alpha-1)`;
- `H = (alpha+2)(beta+2)(A0+A1+E) + 2*pi*(beta+2)*R^(alpha+2) + 2*pi*(alpha+2)*R^(beta+2)`.

`H` is defined by this displayed expression even at `alpha=-2` or `beta=-2`. No division by a vanishing clearing factor occurs in its definition.

The module proves:

1. The original `A0(alpha+delta,beta)` is real analytic at `delta=0` for every `alpha>-3`, using a positive exponential chart in its public statement.
2. For every `beta>-3`, the original `A1(a,beta)` is real analytic at every real `a`.
3. `H(alpha,beta)=H(beta,alpha)`, retaining both collision terms and the exterior.
4. For every `beta>-3`, `H` is real analytic in `alpha` on `-3<alpha<-2-beta`; reflection gives the full right slice. Thus separate analyticity is proved throughout `alpha,beta>-3`, `alpha+beta<-2`.
5. Exact pole-line values: `H(-2,beta)=H(beta,-2)=2*pi*(beta+2)`.
6. For independent first-strip exponents `alpha,beta in (-3,-2)`, `H=(alpha+2)(beta+2)*FP`, where `FP` is the audited original whole-plane finite part.

There are seven public theorems because the two analytic slices are separate declarations. Separate real analyticity is not a claim of joint analyticity or of the physical replica/momentum identification.

## Dependency-closed proof

**Signed exponential integrals.** Split a measurable real source weight into `max(f,0)` and `max(-f,0)`, and weight the original measure by each. Integrability of the actual signed exponential integral implies integrability of both nonnegative parts. An open parameter interval of original integrability therefore lies in both exponential-moment domains. Mathlib's analytic moment-generating-function theorem applies to these actual measures. Their difference is the original integral, with both integrals admitted before subtraction.

**Singular exponent.** Away from the measure-zero puncture, `G0(alpha,beta)*exp(delta*log|z|)=G0(alpha+delta,beta)`. The already proved local subtraction bound admits the right side whenever `alpha+delta>-3`. Openness supplies the required interval. No desired Gamma expression is used.

**Regular exponent.** On the closed disk centered at one, `log|z|` is smooth and avoids its logarithmic singularity. A compact Lipschitz bound gives `|log|z|| <= C |z-1|`. Consequently `|z-1|^beta log|z|` is absolutely integrable for `beta>-3`. The fundamental theorem of calculus proves, for all real `a,X`,

`exp(a*X)-1 = a * integral_(0,1) X*exp(a*t*X) dt`.

Lift to the product of the original disk measure and the fixed interval measure. The variable `t*log|z|` is bounded, so the lifted signed exponential integral is integrable at every real `a`. Fubini is used only after joint integrability is proved. The identity then recovers the original `A1`, whose analyticity follows from the signed exponential construction.

**Exterior and clearing.** The original tail bound admits `K` whenever `alpha+beta<-2`. The same exponential shift gives analytic dependence on the left exponent. The three original source terms and the explicit power terms are combined to prove the left slice of `H`; measure-preserving reflection gives its symmetry and right slice. Evaluation of the explicit definition yields the pole-line values. Away from both poles, field identities give exactly the already audited finite part times its clearing factor.

## What failed and what survived

The first plan used an analytic primitive with a variable integration endpoint. Corpus search did not supply the needed source theorem. The fixed-interval representation above removes that obligation and gives a product measure with an explicitly integrable signed weight. This is now a proved construction, not a source-analyticity premise.

A totalized singular quotient multiplied by its clearing factor would give zero on a pole line. The actual explicitly defined source has value `2*pi*(beta+2)` there, nonzero away from the crossing. The positive survivor is the analytic family retaining these boundary values and its exact relation to the original cutoff prescription.

## Remaining match

Use `a=-alpha/2`, `b=-beta/2`. This card's `H` is four times the cleared source in the [matching card](../../fzz-p-plane-screening-cutoff-matching.md). The proposed partner is

`4*pi*Gamma(a+b-1)*Gamma(2-a)*Gamma(2-b)/(Gamma(a)*Gamma(b)*Gamma(2-a-b))`.

Reciprocal Gamma is already checked to be real analytic everywhere. The next scratch `/tmp/fzzp_plane_gamma_match.lean` now checks cleanly: the partner's left analytic dependence, the exact original power integral, and the zero-collision finite-part equality in the ordinary chamber are proved there. This is an unfinished private prefix. Whole-plane open-region equality and the eventual identity theorem remain distinct from this card's completed result.

For the required first-strip match, two concrete connected slices suffice. First fix `beta in (-2,0)` and use the ordinary-chamber base point `alpha0=-2-beta/2` to extend in `alpha` over `(-3,-2-beta)`. Then fix physical `alpha in (-3,-2)`, use `beta0=-1`, and extend in `beta` over `(-3,-2-alpha)`. This plan must still be checked in Lean. Pole values alone do not supply equality on an open region.

The Gamma match, evaluated continued marked responses, full physical coupling/momentum transport, higher counterterm depths, moving/coalescing punctures, the independent frame and the complete Ward producer remain open.

## Formal artifact and audits

Module: `formal/GaloisForLFunctions/RHTower/FZZCigarSubtractedScreeningAnalytic.lean`, 438 lines. All public theorems take data only. No RH, stationarity, positivity-selector or Ward premise is present.

- Clean scratch: `lake env lean /tmp/fzzp_subtracted_analytic.lean`.
- Final leaf audit: `lake build GaloisForLFunctions.RHTower.FZZCigarSubtractedScreeningAnalytic` passed, 8838 dependency jobs, leaf 124 seconds.
- All seven public theorem axiom closures contain only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint passed; no added axioms, `sorry`, `admit`, `opaque` or `unsafe`.
- Wired into `GaloisForLFunctions.RHTower`; no umbrella build.
- Logs: `/tmp/fzzp-subtracted-analytic-{scratch,build,axioms,lint}.log`.

Search and recent-paper evidence are recorded in the matching card. The decisive tools are the corpus's signed measure/exponential-moment construction, fixed-interval parameter-integral method, original Lipschitz collision bounds and measured Fubini theorem. No paper assertion enters the Lean proof as a premise.
