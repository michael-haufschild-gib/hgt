# HB exact physical source moment — 2026-09-12, continuation 0912g

Goal active and unproved. Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

Prior work: mem:hawking_bm_normalizable_full_radial_join_2026_09_12_0912f installed full original normalizable temporal radial restoration and exact residue K*normFinitePart(w0)/physicalSlope. Norm and slope nonzero. This continuation attacked the actual remaining fundamentalSourceMoment in K.

## Completed and installed
Five NEW source leaves under formal/GaloisForLFunctions/RHTower, namespace RHTower.D4BMJointSource:
1. ThetaCuspHawkingBMFundamentalMomentPolynomial — exact original source polynomial coefficients, core, smooth coordinate substitution and finite cutoff equality. Final exact audit 71s.
2. ThetaCuspHawkingBMFundamentalMomentCounterterm — endpoint cutoff from admitted subtracted remainder; differentiable endpoint comparison limit. Final exact audit 75s.
3. ThetaCuspHawkingBMFundamentalJacobiMoment — actual core derivatives, compact first derivative bound, moment admission and cutoff limit. Final exact audit 25s.
4. ThetaCuspHawkingBMFundamentalJacobiRecurrence — boundary-preserving IBP recurrence and exact second/fourth reductions. Final exact audit 78s.
5. ThetaCuspHawkingBMFundamentalSourceMomentTransport — actual physical source moment polynomial equality and base-period equality. Final exact audit 134s.

All five passed scratch lake env lean checks and exact lake build Module audits; each final build only two Lake jobs (target leaf + root) against cached dependencies, with no dependency source builds. Five artifacts installed per source. All five wired in RHTower.lean. formal_tools.py lint passed, only existing large-file warnings. NO heartbeat or resource increase, no axiom checks, no mathematical computation, no umbrella/full/dependency build, no Git/launch.sh.

## Exact mathematics now proved
z=x(2-x), x in (0,1], sqrt(1-z)=1-x.
A=(5s²+15s+4)/4.
B=s(s-1)*((s+2)(2s+3)-(w+1)(w+2)/2)/4.
H_n(x)=(1-x)^n*(2-x)^(2s).
I_n=existing firstEndpointMellin(fun _=>H_n,1,w).
Actual original source density times Jacobian =2a²*x^w*(A H_2+B H_4).

The original cutoff is at epsilon(2-epsilon); the transformed cutoff is at epsilon. Their counterterm difference is exactly F(0)/(w+1)*epsilon^(w+1)*((2-epsilon)^(w+1)-2^(w+1)). A slope limit proves zero when Re(w)>-2. Moment admission comes from proved compact derivative bounds, not extra physical hypotheses.

physicalFundamentalSourceMoment_polynomial (source line 73) proves, for every actual q branch side a, M=2a²(A I2+B I4). w=physicalFundamentalFrequency q side, s=D4BMModularCore.physicalRate q branch.

Let d=2s-w, e=w+2s+2.
Primitive=x^(w+1)*(1-x)^n*(2-x)^(2s+1).
Recurrence n I_(n-1)+d I_n-(e+n)I_(n+1)=-0^n.
The n=0 right-hand side is -1, essential.
e(e+1)I2=(e+d²)I0+d.
e(e+1)(e+2)(e+3)I4=[d⁴+(6e+8)d²+3e(e+2)]I0+d(d²+5e+8).

physicalFundamentalSourceMoment_base_period (source line 116) proves unconditional physical denominator-cleared identity:
D M=2a²(P I0+Q),
D=e(e+1)(e+2)(e+3),
P=A(e+d²)(e+2)(e+3)+B[d⁴+(6e+8)d²+3e(e+2)],
Q=d[A(e+2)(e+3)+B(d²+5e+8)].
No division by D or nonvanishing premise needed.

## Hard obstacle and next attack
Need nonvanishing or joint survival of this specific physical P I0+Q, plus actual angular source factors in K. This is NOT proved. I0 is a half-interval finite part, not complete beta.

Physical rates verified from source:
D4BMModularCore.physicalRate q true=q-2; false=-q-1.
physicalFundamentalFrequency q true=-1-q/2; false=-2+q/2.
Matching choices give s=2w+1 or2w+2; other choices s=-2w-4 or-2w-5. Do not confuse D4BMCuspProjection.physicalRate, which is doubled.
Matching common phase = x*(2-x)^4, derivative=(2-x)^3*(2-5x), stationary point x=2/5. Candidate next conjecture: source saddle/Fresnel leading term dominates original endpoint-subtracted remainder throughout actual frequency range, or family joint survival via another exact identity. No dominance proved.

Corpus source inspected: BesselJZeroConstant.lean lines610–684, especially norm_sqrt_mul_besselPhaseIntegral_sub_le at646: explicit Fresnel leading term and remainder via exact quadratic coordinate/Jacobian correction. This is a mechanism to adapt, NOT directly applicable to this source. ArithmeticStationaryReflectedTail offers actual upper bounds. Generic saddle_ne_zero candidates merely assume main-term and error bounds; they do not solve the source problem.
Hand algebra candidate only (not installed): recurrence implies joint I2/I4 obstruction proportional to 2*d*e*(e+1); does not exclude cancellation in fixed A I2+B I4, so do not confuse with source survival.
Full angular/action comparison, physical Peierls identification, Hawking-clock extinction and RH still open.

## Search use and coverage
Used broad incomplete and saddle searches, deep endpoint IBP, stationary nonvanishing/main-term method search, and deep incomplete-period ODE/continued-fraction search. Inspected candidate_lemmas, source_arguments, proof ideas/ingredient sets, declarations/coverage. Last search partial=false but declarations empty; candidate/source results present. Snapshot 57,084 files/735,656 declarations, most compiler metadata pending, semantic coverage not measured. Earlier deep results partial with unfinished auxiliary queries. Continued-fraction and Suzuki beta hits lack applicable complex half-period nonvanishing; do not use them as closure.
Broad own-term arXiv monodromy/holonomic searches opened primary abstracts:
https://arxiv.org/abs/2609.06416 September 6 line-arrangement monodromy.
https://arxiv.org/abs/2608.26087 August 26/revised27 multivariable strong monodromy.
Neither supplies source nonvanishing or is used as premise.

## Lean efficiency notes
No resource increases. Local simp only, change, explicit derivative equality and linear_combination avoid broad elaboration.
- HasDerivAt.scomp at x=0 needs base derivative stated at 2-0, not 2 (arithmetic subtraction not definitional).
- using! with simp only [Function.comp_apply,Pi.sub_apply,id_eq,zero_sub,...] resolves reducible function/instance presentations.
- Under Tendsto congr', normalize composition with an explicit change before rewriting cutoff integral.
- Recurrence hr.congr' goal orientation requires linear_combination hf-hct, not -hf+hct.
- Complex.ofReal_ofNat exists; Complex.ofNat_re does not. For real part w+2, change 0<w.re+2.
- Exact phi derivative: explicit change 1*(2-x)+x*(0-1)=2*(1-x), then ring.
Do not recheck or rebuild these unchanged leaves.

## Documentation and cleanup
Updated only route card docs/drafts/pipeline/1-in-progress/hb-physical-mode-action-contact.md with exact mathematics, audits, search applicability and open target. Frontier map READ ONLY and untouched. Universal STATUS untouched (no new route-independent fact).
Owned exact audit package /tmp/hb-audit-0912g and helper removed. All 0912g scratch files, search outputs and lint log removed. All process handles terminal; final process scan found no owned Lean/Lake processes. No current live process.
Latest user emphatically: optimize Lean code, NO raising heartbeats. Preserve no computations/no axiom-check/no umbrella-build discipline.
