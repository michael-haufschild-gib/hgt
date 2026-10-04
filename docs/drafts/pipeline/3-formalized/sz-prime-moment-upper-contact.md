# SZ: upper contact and nonlinear return control

- **ID:** SZ-PRIME-MOMENT-UPPER-CONTACT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** CCMPrimeMomentFirstContact, CCMPrimeMomentPotentialEscape,
  CCMPrimeMomentPotentialLaplace; route SZ joint phase target.
- **Statement:** The actual nonlinear discrepancy and linear Abel potential
  have exactly the same eventual strict finite upper levels.

## Exact theorem and frontier effect

Retain every von Mangoldt prime power and write

    M_n=primeMassHalf(n), m_n=1+M_n/2,
    D_n=m_n^2-psi(n)-1,
    U(T)=exp(T/2)*(1+J(T)/2)-1,
    J(T)=integral_0^T criticalMellinNormalizedChebyshevError(t) dt.

`ccmPrimeMoment_eventual_upper_level_iff A` proves, for every real A,

    (exists N, forall n>=N, D_n<A)
      iff (exists H, forall T>=H, U(T)<A).

There is no RH, eventual-sign, or arbitrary growth premise. The proof
establishes a dynamical comparison of the actual sources. It does not
establish either upper bound. In particular, the positive square in
D=U+(m-sqrt(x))^2 adds no eventual finite-ceiling obstruction, although
it cannot be discarded in a pointwise estimate or amplitude bound.

For eventual sign, the remaining scalar producer reduces to the linear
inequality J(T)<-2+2*exp(-T/2) on a whole tail. That inequality, a uniform
critical normalized forcing bound, and the complete canonical-head
Gamma--prime--polar sign remain open. No new RH receiver was added.

## Dependency-closed paper proof

1. Suppose n>=1 and m_n>=sqrt(n). Some k>=n must have
   m_k<sqrt(k+1). Otherwise every integer potential increment

       U_(j+1)-U_j=(sqrt(j+1)-sqrt(j))*(2*m_j-sqrt(j+1)-sqrt(j))

   is nonnegative on j>=n. This contradicts the already proved actual
   negative potential escape. Choose the first such k.

2. For n<=j<k, m_j>=sqrt(j+1), and the exact admission law gives

       D_(j+1)-D_j=w_(j+1)*(m_j-sqrt(j+1))+w_(j+1)^2/4>=0.

   Positivity of mass increments also gives m_k>=sqrt(k). Hence
   x=m_k^2 lies in [k,k+1), with floor(x)=k and x>=n.
   The exact arithmetic source formula yields

       U(log x)=2*sqrt(x)*m_k-x-psi(k)-1=D_k>=D_n.

   This proves upper contact, including its physical cutoff. It uses
   no estimate of the positive square and no atom-size bound.

3. If D_(j+1)>D_j, its post-entry mass exceeds sqrt(j+1).
   Indeed, m_(j+1)<=sqrt(j+1), together with m_(j+1)=m_j+w/2,
   would give DeltaD<=-w^2/4<=0. Therefore a first upward crossing
   of any level A forces a continuous-potential value >=A at or after
   that crossing. In the exported interval-return theorem the guaranteed
   time is >=log(start); it need not follow the chosen terminal index.

4. Suppose U(T)<A for every T>=H. Actual negative discrepancy escape
   supplies a starting index k with log(k)>=H and D_k<A. Any later
   D_n>=A has a first upward crossing. Upper contact would then give
   U(T)>=A at T>=H, a contradiction. Thus D_n<A eventually.

5. Conversely, the source identity on each literal cell gives

       U(T)=D_floor(exp T)-(1+M_floor(exp T)/2-sqrt(exp T))^2.

   An eventual strict ceiling for D therefore gives the same ceiling
   for U. No moving-cutoff derivative is taken in either direction.

## Corpus investigation and audit

The existing Riccati theorem assumes a tail-wide quadratic barrier;
negative excursions do not supply it. The exact second-grade Selberg
hyperbola law retains an uncontrolled signed future-error pairing.
Those attempted producers were not assumed, and neither was retired
as false. The new upper-contact argument instead uses literal jump
identities and the actual escape theorem proved in the preceding turn.

Search1222417 was partial with reranking deadline and pending/stale
compiler coverage. Search1222462 completed retrieval but its compiler
coverage remained pending/stale. Search1222497 was partial/source-only.
Candidate/source/ingredient sections were inspected; source and Lean
checks determined applicability. No absence or novelty claim follows.

- Scratch3116 failed on natural-index normalization, a case equation,
  a square-root cast, and an untyped intermediate inequality.
- Scratch73279 passed all four theorems and their axiom queries.
- Final production audit73270:
  `lake --old env lean GaloisForLFunctions/RHTower/CCMPrimeMomentUpperContact.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CCMPrimeMomentUpperContact.olean`,
  in `formal`, exit0 with no diagnostics.
- Final all4-public-theorem axiom audit72769:
  `lake --old env lean /tmp/sz_upper_contact_axioms.lean`, exit0;
  each theorem uses only `propext`, `Classical.choice`, `Quot.sound`.
- One RHTower umbrella import; no full or umbrella build, heartbeat
  increase, numerical experiment, subagent, commit, or push.
- Global lint67589 exited1 on14 unrelated unreachable modules; no
  error named this leaf. Global lint is not claimed green.

## Next actual-source attack

The constructed contact is a matched mass/time head: x=(1+M_k/2)^2
and floor(x)+1=k+1. The source identities
`ccmOutgoingPrimeCumulative_succ_eq_primeMassHalf` and
`exp_half_ccmOutgoingPrimeQuantileBoundary` identify its quantile boundary
with log(x). The existing terminal-entropy boundary-mismatch formula
therefore has zero mismatch there. This is a paper consequence of the
read source identities; a dedicated Lean contact-to-entropy export is
not yet supplied. It gives no sign for age, dissipation or the complete
canonical-head pairing. Retain those terms in the next guarded-contact
source comparison, or prove the linear primitive tail sign directly.

Lint67589 errors (unmodified modules):

- owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMApertureChainProfile
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMApertureTranslationChains
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMExponentialRampPrimeMoment
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMExponentialRampSourceDissipation
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMExponentialRampTerminalEntropy
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMRetainedChainKernelLower
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MertensProductDiamondPintz
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MoebiusMollifiedErrorThreeLines
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.RoutePLatePrimeIncrementVariation
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaFinitePairPacketExtension
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaMovingShellFirstOrderPhase
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.CompactMonoidMeasureAlgebra

Closure: all owned processes terminated and all7 exact scratch/search/lint
files removed. Audited production olean retained, unique umbrella import
checked, targeted whitespace clean. Cross-session memory:
`rhtower/sz-prime-moment-upper-contact-2026-10-04`. RH goal remains active;
no proof or falsification of RH is claimed.
