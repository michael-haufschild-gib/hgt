# BAG covered-source Mellin and positive rational cone cancellation

- **Stage:** 3-formalized

2026-10-06,01ay/02ay. CLOSED in paper and Lean.
ChiCubicCoveredMellinCancellation: 308 lines, API4 at121/183/248/292.
Final production50975/log01 terminal0 empty PASS, lake --old env lean with
explicit leaf olean. Imported axiom76729/log01 terminal0: all4 declarations
use only propext, Classical.choice, Quot.sound. Index93313 PASS; RHT umbrella
import once, no umbrella build. Scoped code/generated diff check PASS.
No admissions, added axioms, heartbeat or recursion increases in this work.

For every fixed positive rho1,rho2, the complete source at cutoff2N divided
bylog(2N), paired with the literal selected normalized Mellin profile at
physicalscaleN and criticalparametersq_(2N), is eventually integrable and
converges to zero inC. Every cofactor, source sector, exclusion and the full
physical exterior remain. This resolves the literal covered-band mismatch.

Proof: compare fullf_N with fullf_(2N) at the SAME q_(2N). Their difference
is local(f_N-f_(2N))+ext(f_N)-ext(f_(2N)). Actual uniform local Cauchy inH5/4
and the complete source difference operator pay the first term. Actual H2
exterior energy atphysicalN is<=B/N^4, while sourceH2 cost at2N is
A sqrt(1+log(2N))<=2AN. Thus the unmatched exterior is admitted and tends0;
matched full/exterior terms follow along the cofinal2N subsequence. Integral
linearity uses actual admission of all four terms.

Exact physical Mellin HasSum identifies the ENTIRE positive rational cone
atP_(2N) acting on the original controlled amplitudeA_N. Its literal scalar
normalization islog(N)^3/(N log(2N)). The ratio log(2N)/logN tends1, so the
covered action has complexnorm o(N/log²N). The eventual series is admitted.
No assumed cancellation, analytic uniformity, Schwartz limit or budget.

Scratch05 audit64398 terminal0 closed integral assembly after explicit
pointwise normalization of integral_add equalities. Four preceding failures
were elaboration/instance/rewrite failures, recorded in the P1 working log.
Completed owned scratch, attachment-template and axiom source removed;
logs and search JSON retained.

Scope: covered POSITIVE EXACT CONE. The complete global defect action still
retains nonzero transverse defects, other sign/zero-coordinate sectors and
actual projectors. P1bag-covered-global-defect-cancellation attacks the full
signed residual, not a conditional receiver. Growing mixed moments, actual
moving cofactors, common-height self-return and RH remain open.

Authoritative lint76722 terminal1:367 warnings,21 unrelated unreachable
modules and1 unrelated proof-debt finding; no owned finding. Global lint is
NOT clean. Exact errors:

error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.BohrOrbitClosureHaar
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.KuznetsovKLWeight
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.KuznetsovOppositeSign
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergCoefficient
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergFactorization
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergForms
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergGcdLog
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergGcdLogForms
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergRatioForms
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergSummability
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionBohrMoment
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionClassLimits
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionFarey
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionOffResonance
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionRatioFibers
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionRatioForm
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionResonantBounds
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionResonantCount
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionResonantSmall
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionSecondMomentExpansion
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionSecondMomentLimit
error: proof debt: formal/GaloisForLFunctions/RHTower/KuznetsovOppositeSign.lean:340: sorry (theorem integrable_and_integral_klWeight_mul_discrete)

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiCubicCoveredMellinCancellation` | `bagCubicSelectedMellin_covered_pairing_tendsto`, `bagCubicCoveredRationalConeAction_summable`, `bagCubicCoveredRationalConeAction_norm_tendsto` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
