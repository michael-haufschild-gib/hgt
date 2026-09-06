# Exact arithmetic clock first variation — proved 2026-09-06

RH remains unproved. Active unlimited goal stays active. Do not mark complete or blocked because mathematics is hard. Full chain: arithmetic classification covers zeros -> independent unit-remainder constraint -> off-line exclusion -> RH. The unit constraint is still missing. No new radical RH architecture or global literature novelty established.

## Closed result F

Authoritative certificate: docs/drafts/pipeline/3-formalized/arithmetic-clock-first-variation.md. Frozen card retained at 1-in-progress/arithmetic-clock-resonant-first-variation.md and marked proved. Let b(v)=(fract(v)^2-fract(v))/2, q_h(v)=(exp(hv)-1)/h, q_0(v)=v, J_h=integral0..m b(q_h(v))*exp(-(sigma+1)hv)*sin(lambda v)dv. For fixed sigma>=-1, positive integer m, natural K, 0<lambda<2pi, lambda*m=2piK, Lean proves J_h/h -> Q<0 as h->0+. Exact Q=m*((1-sigma)/lambda^3+sigma*cos(lambda/2)/(2lambda^2 sin(lambda/2))-1/(4lambda sin(lambda/2)^2)). This is the full frozen identity, not just a sign estimate for a proposed coefficient.

## Mathematical dependencies

ArithmeticClockResonanceMoments: exact cosine prefix C(lambda,m)=sin(m lambda)*d(lambda), d=cos(lambda/2)/(2lambda^2sin(lambda/2))-1/lambda^3. Differentiate the literal finite integral BEFORE resonance: first sine moment=-m*d; second cosine moment=-2m*d'. Q=-(sigma+2)M1-lambda/2*M2. Let x=lambda/2 and f=x^2+xsinxcosx-2sin^2x; f(0)=f'(0)=0, f''=4sinx(sinx-xcosx)>0 on (0,pi). d<0 and Q=m*(-f/(8x^3sin^2x)+(sigma+1)d)<0.

ArithmeticClockFirstVariation: global Lipschitz b constant1/2; b right derivative fract(v)-1/2 at EVERY v including integers. q_h>=v for h>0 and derivative at0=v^2/2. Exact right integrand derivative D=[v^2/2*(fract(v)-1/2)-(sigma+1)vb(v)]sin(lambda v). For v>=0,h>0,hv<=1, absolute difference quotient <=v^2/2+(sigma+1)v. Finite-interval DCT gives general A>=0 first variation. Right-FTC on v^2/2*b(v)*sin(lambda v) retains every integer slope jump, endpoints vanish for A=m, integralD=Q. J0=0 at resonance. The alternative moving-endpoint proof is not needed.

## Literal-source transfer and exact quantifiers

At positive integer N, clockVariationPrefix sigma lambda (1/N) A = scaledLogarithmicSegment sigma lambda N 0 A exactly. Hence N*S_N(0,m)->Q<0 at integer resonance. Combine with prior ArithmeticLogarithmicPhaseScaling strict negative leading limit at noninteger complete endpoints. For each FIXED sigma>=-1,lambda in(0,2pi),K>0, every sufficiently large N has S_N(0,2piK/lambda)<0. Height t=lambda*N varies with cutoff. No ONE cutoff controlling ALL K is proved. Do NOT exchange forallK existsN0 with existsN0 forallK. No fixed-height/unit-cutoff conclusion follows.

Principal public theorem names in RHTower.DeletionMixedRefinement: resonantClockMomentCoefficient_eq, resonantClockMomentCoefficient_neg, tendsto_clockVariationPrefix_quotient, integral_clockVariationDensity, tendsto_clockVariationPrefix_div_at_resonance, clockVariationPrefix_reciprocal_integer, tendsto_scaledLogarithmic_integer_prefix_first_order, eventually_scaledLogarithmic_complete_prefix_neg, eventually_scaledLogarithmic_turn_prefix_neg.

## Remaining mathematics

B1 (every complete logarithmic turn nonpositive) was formally refuted previous turn at lambda=4pi/3, secondturn, arbitrarily large N. Positive survivor now covers ALL FIXED positive complete prefixes eventually, including integer coincidences. B2 (all weighted complete prefixes at one cutoff), C (all undamped logarithmic prefixes), D1 (all 0<h<=1 clock prefixes), E (layers), R (strict below-threshold whole-tail sign) remain unproved. Even C/R would leave exceptional head and unit remainder at high zero heights unresolved. At a strip zero, Im g_s(1)=t(2sigma-1)/(2|conj(s)(1-conj(s))|^2). Need independent arithmetic input to control it. Do not continue accumulating tail infrastructure while pretending to have attacked that independent RH constraint.

## Audit and process status

Two new leaf modules in formal/GaloisForLFunctions/RHTower/: ArithmeticClockResonanceMoments.lean (16 public declarations:7defs9theorems) and ArithmeticClockFirstVariation.lean (23:4defs19theorems). Both source checks and serialized targeted leaf builds passed. Every scratch was checked with LEAN_NUM_THREADS=1 lake env lean. Final audits LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.<module> rebuilt only respective leaf. Both wired in RHTower.lean after ArithmeticLogarithmicPhaseScaling. All39public axioms audited via /tmp/rh_clock_first_variation_axioms.lean; only propext,Classical.choice,Quot.sound. Output /tmp/rh_clock_first_variation_axioms.txt. No sorry/admit/addedaxiom/opaque/unsafe/native_decide/computational certificates. Index refreshed; research tool retrieves new declarations. lint --check-generated PASS, existing large-file warnings; /tmp/rh_clock_first_variation_lint.txt says formal lint passed. No owned Lean processes remain. No new remote computations were needed; prior Runpod jobs finished. Scratch /tmp/rh_clock_deformation.lean is fully passed but tree modules authoritative. Preserve unrelated worktree changes.

STATUS updated ARITHMETIC-PHASE-003 and clarified002. Related homotopy, phase-block, failed B1, source-scaling cards and two EDQ frontier entries updated. Old memory rh/arithmetic-logarithmic-phase-scaling-2026-09-06 is superseded ONLY regarding F previously open.

## Literature and novelty

Corpus-first derivation; primary literature check after proof found (x/sin x)^2+x/tan x>2 already appears asEq5 in Chen-Cheung2012 Sharpness of Wilker and Huygens type inequalities, https://hub.hku.hk/bitstream/10722/149088/1/content.pdf (there domain0<|x|<pi/2). Our numerator sign on0<x<pi is formally proved, but no novelty claim for ingredient/domain/fullapplication. No forbidden spectral/Gamma/etc RH route adopted. All external sources are background checks, not Lean premises.

## Discipline and technical lessons

Every new turn starts mission+fullchain+plannedhardprogress. Corpus search scripts/formal_tools.py research plus rg, no training-based route claims. One owned foreground Lean process at a time; wait for exit before next. No fullbuild or umbrellabuild. No subagents authorized. Remote math experiments only supplied Runpod if unpredictable by reasoning.

Current mathlib: use mul_lt_mul_iff_of_pos_left, not mul_lt_mul_left on real (latter failsclass). Ne.symm hf needed when hf is bare Not f=0. Spaces around comparisons essential (0<m parses notation!). Parametric partial functions often need explicit change withlambda before unfolding. No abs_add; use abs_sub p(-q),sub_neg_eq_add,abs_neg. slope_def_field only on fullyappliedslope; use explicit Tendsto function target and congr' eventuallyof_forall. Right-FTC intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le avoids partition bookkeeping. Exp Taylor little-o and Real.abs_exp_sub_one_sub_id_le validated in currenttoolchain. Do not rerun passed checks without changes.