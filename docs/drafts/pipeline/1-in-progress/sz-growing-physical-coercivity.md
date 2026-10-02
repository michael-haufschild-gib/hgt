# Growing physical coercivity of the actual shifted Suzuki form

- **ID:** sz-growing-physical-coercivity
- **Stage:** 1-in-progress
- **Route:** SZ
- **Date:** 2026-10-02
- **Status:** source-based paper argument; Lean implementation under audit
- **Target:** for every L>0, eventually in positive aperture a, every actual
  Ta vector w satisfies L*a*norm(Jw)^2 <= norm(w)^2.

## Why this is the next hard step

The actual matched odd Neumann lift now has Gamma energy O(a*exp(-a))
and exponentially small residual. The response comparison gives physical
mass O(a*exp(-a)). This still does not control the error after multiplication
by the exponentially large prescribed shift. A growing physical coercivity
law would make the response-minus-Neumann physical error o(exp(-a)) in
squared norm, directly addressing that obstruction. This is a new uniform
operator statement, not an optimization of the constants in the old bound.

The complete signed shell/metric Wronskian, its cofinal control, canonical
normalization, shift removal and Xi identification remain separate problems.

## Corpus basis and retrieval limits

Search `Gamma coercivity low frequency multiplier high frequency logarithmic
weight aperture spectral floor`, deep/60s, generation1187787: partial=true,
coverage pending, candidate/source entries source_only, no ingredient sets.
No absence or novelty claim follows from those incomplete search results.
Source inspection supplies these exact ingredients:

- CCMRestrictedWeilSourceContraction:79,
  `eventually_ccmFullLineRemainder_symbol_small`, for every fixed K,epsilon>0.
- Same source:30, private `full_remainder_low_band`, valid for every SoninL2
  vector, with no finite-exponential budget assumption.
- CCMRestrictedWeilRemainderMultiplier:45, actual compression identity;
  :205, `norm_ccmFullLineBoundedRemainder_le`, at most D*exp(a),
  D=norm(kappa)+46.
- CCMRestrictedWeilPolarShiftLower:99,
  `exp_aperture_le_twice_suzukiWeilIntervalShift`: exp(a)<=2*c_a.
- CCMArchimedeanLogWeightEquivalence:101,
  `suzukiLogWeight_le_ccmArchimedeanComparison`: logweight<=C_arch*GammaWeight.
- SuzukiMatchedOddSourceBound: actual shifted quadratic decomposition and
  A_a=c_a I+B_a >= I. These are private helpers; reuse or expose their exact
  statements when needed, without rebuilding unrelated umbrellas.

## Dependency-closed paper calculation to formalize

Let f=Jg, F=norm(f), G=norm(g)_Gamma^2, c=c_a,
A=Re<(cI+B)f,f>, and
T=norm(f-Q_R f), R=exp(K*a), where Q_R is the actual Fourier cutoff.
The prescribed shift gives A>=F^2>=0.

Choose the low-band smallness epsilon=1/4. Exact compression, the full-line
low-band estimate and the global full-line bound give

    norm(B f) <= (c/4)*F + 2*D*c*T.

Here exp(a)<=2c was used in both terms. Cauchy--Schwarz and the symbolic
square (F/2-2D*T)^2>=0 yield

    A >= (c/2)*F^2 - M*c*T^2,    M=4D^2.

For the exact Gamma form vector, the Fourier cutoff norm identity and
logweight<=C_arch*GammaWeight imply

    K*a*T^2 <= C_arch*G.

This uses only |xi|>exp(K*a) on the omitted band and the exact weighted
Fourier norm of g. There is no regularity assumption on an unknown response.

Given L>0, set K=2*C_arch*M*L. Eventually c>=2*L*a, since
c>=exp(a)/2. Multiply the displayed lower bound for A by 2*L*a:

    2*L*a*A >= L*a*c*F^2 - 2*L*a*M*c*T^2.

Since A>=0 and 2*L*a<=c, the left side is at most c*A.
The Gamma inequality gives G>=2*M*L*a*T^2. Adding c*G and
dividing by positive c proves

    norm(w)_Ta^2 = A+G >= L*a*norm(Jw)^2.

Every ingredient is an actual-form or actual-symbol statement. The Fourier
tail inequality for arbitrary Gamma vectors still needs a Lean proof.

## Consequence to test immediately after the coercivity theorem

For the already constructed g_a and z_a=w_a-FromForm(g_a), the exact form
residual identity gives norm(z_a)_Ta^2<=2*norm(r_a)^2+2*norm(g_a)_Gamma^2.
The current source estimates bound this by C*a*exp(-a), with C fixed.
Applying the new floor with arbitrary L would give

    exp(a)*norm(Jw_a-u_a)^2 -> 0.

This is independent of which form lift is chosen, since Jg_a is the literal
canonical Neumann vector u_a. It must then be paired with the actual even
channel and the full signed expression; no Wronskian sign is claimed here.

## Checks

- [x] Corpus search and exact source inspection.
- [x] Paper calculation retains actual shift, compression and both frequency regions.
- [x] Audit arbitrary-Gamma Fourier tail comparison in Lean: final leaf52297 passed.
- [x] Audit uniform growing physical coercivity in Lean: final leaf33070 passed.
- [ ] Audit rescaled physical response-minus-Neumann error.
- [ ] Test signed metric-work cancellation at original common aperture cutoffs.

## Implementation log

2026-10-02 continuation: previous turn classified as progress (actual matched
Gamma admission and physical-decay root audited). Current search1187903 is
partial, with complete source inventory but many compiler records pending or
stale. Its proposed ingredient set concerns smooth Fourier truncations and
does not discharge the arbitrary-Gamma-vector obligation. Direct source
inspection found the existing exact cutoff norm identity and pointwise
logarithmic tail inequality in SuzukiHlogCompactEmbedding.

The existing contraction proof now exposes
`norm_ccmRestrictedWeilBoundedRemainder_le_low_add_tail` for every aperture
vector. The finite-source contraction reuses it. Final leaf audit66319 passed
without warnings. The arbitrary Gamma-tail inequality and growing-floor root
are drafted in scratch. Needed actual-form decomposition/coercivity facts and
the exact matched response-minus-test norm bound are being exposed from their
existing proofs in SuzukiMatchedOddSourceBound; no new assumption is added.

Final SuzukiMatchedOddSourceBound audit81700 passes after exposing the exact
general energy decomposition, shifted coercivity, and Ta residual norm estimate.
SuzukiGrowingPhysicalCoercivity scratch57522 and final leaf33070 pass without
warnings. The actual root holds for every real L, with the nonpositive case
discharged separately, and uniformly for every actual Ta vector. Both new
leaves are wired. Rescaled physical approximation remains under scratch audit.
The next signed source target is recorded in sz-matched-source-metric-balance.md.
