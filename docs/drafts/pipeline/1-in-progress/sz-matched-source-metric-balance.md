# Actual matched-source balance for the signed metric term

- **ID:** sz-matched-source-metric-balance
- **Stage:** 1-in-progress
- **Route:** SZ
- **Date:** 2026-10-02
- **Status:** next source-based paper candidate; no Lean closure claimed

## Hard target

For actual matched odd energy O_a, physical squared norm N_o,a and prescribed
shift c_a, prove c_a*N_o,a-O_a -> 0. Build the same statement for the actual
matched even channel E_a,N_e,a. Then prove the signed cancellation

    c_a*(O_a*N_e,a-E_a*N_o,a) -> 0.

This targets the metric term in the original common-aperture determinant.
It retains the complete signed shell term as a separate open obligation;
it does not claim a cofinal Wronskian bound or shift removal.

## Corpus basis

Current searches1188058 and1188112 are partial/source_only. The first has a
snapshot inventory and proposes an inapplicable Neumann boundary-flux step;
the second has pending coverage and no ingredient set. Actual source hits
include SuzukiMatchedEvenSourceBound and the metric response identity in
CCMSuzukiCrossApertureRieszTransport:361. No absence or novelty claim is inferred.

Source inputs for the odd calculation:

- Actual finite Neumann vector/budget and exponentially small residual:
  CCMRestrictedWeilFiniteNeumannSource.
- Actual Gamma lift and its energy O(a*exp(-a)): CCMFiniteNeumannFormDecay.
- Uniform actual odd energy and exact Ta response-minus-test norm estimate:
  SuzukiMatchedOddSourceBound.
- Growing physical coercivity and the rescaled physical error: the immediately
  preceding target, P1:sz-growing-physical-coercivity. Its final audits are
  recorded there; do not assume a draft has passed.
- Uniform symbol cancellation and arbitrary-vector low-band/tail bound:
  CCMRestrictedWeilSourceContraction.
- Full-line norm bound D*exp(a), D=norm(kappa)+46:
  CCMRestrictedWeilRemainderMultiplier:205.
- Exact physical compression bound:
  CCMRestrictedWeilGroundFrequencyLocalization:293,
  `norm_ccmApertureCompression_le`.
- The literal interval operator is the unitary conjugate of the physical
  remainder (definition located in SuzukiWeilFriedrichsOperator:48).

## Odd-channel paper calculation to audit

Write u for the already constructed canonical Neumann vector, g for its actual
Gamma lift, w for the odd Ta response, z=w-FromForm(g), and f=Jw. Put
C0=2D and K0=2log(C0)+10. The current source estimates give

    norm(u) <= 2M0*exp(-a/2),
    V_u <= 2C0*exp((log(C0)-1/2)*a),
    norm(u-Q_exp(K0*a)u) <= (4C0/pi)*exp(-11a/2).

For every epsilon>0, the actual symbol is at most (epsilon/2)*exp(a)
on that fixed exponential band, eventually. The arbitrary-vector operator
split therefore implies

    abs(Re<B_a u,u>)
      <= 2*epsilon*M0^2 + C1*exp(-5a).

Since epsilon is arbitrary, the complete bounded-remainder quadratic on u
tends to zero. No prime or polar term is discarded individually, and no
infinite Neumann series is substituted for the actual finite vector.

The exact Ta residual norm is O(sqrt(a*exp(-a))), hence tends to zero.
The already proved uniform odd energy bounds norm(w)_Ta; triangle inequality
also bounds norm(FromForm(g))_Ta. Thus the difference of their squared Ta
norms tends to zero. The exact energy identity for FromForm(g) is

    norm(FromForm(g))_Ta^2
      = norm(g)_Gamma^2 + c_a*norm(u)^2 + Re<B_a u,u>.

The Gamma and bounded-remainder terms vanish, so O_a-c_a*norm(u)^2 -> 0.

The new rescaled approximation target gives exp(a)*norm(f-u)^2 -> 0.
Together with the displayed bound for u, the norm-square difference inequality
gives exp(a)*abs(norm(f)^2-norm(u)^2) -> 0. Exact unitary transport and
compression imply

    c_a <= 1+D*exp(a) <= (D+1)*exp(a).

Hence c_a*(norm(f)^2-norm(u)^2) -> 0. Combining the two limits proves
c_a*N_o,a-O_a -> 0.

## Even channel and signed consequence

The actual matched even source is (p_++p_-)/2. Both initial norm and finite
exponential budget obey the same scale exp(a/2). The general budget contraction
already applies to every certified source. Extend the finite recurrence,
canonical test vector, Gamma lift and residual comparison to this literal
source, reusing the common argument where possible. Its energy is already
uniformly bounded by 1/2 in SuzukiMatchedEvenSourceBound.

Only after both actual channel balances are proved, use the exact identity

    c_a*(O_a*N_e,a-E_a*N_o,a)
      = O_a*(c_a*N_e,a-E_a) - E_a*(c_a*N_o,a-O_a).

Uniform energy bounds then give signed metric cancellation. For bounded
aperture increments b-a, the already known lower bound exp(a)<=2c_a and the
proposed upper bound give a bounded ratio abs(c_b-c_a)/c_a. This would pay
the metric term locally. Arbitrary cofinal increments and the complete
signed shell Wronskian remain unproved.

## Checks

- [x] Corpus searches and exact compression/source inspection.
- [ ] Verify interval-to-physical operator norm upper transport.
- [ ] Prove the complete B_a quadratic on actual u_a tends to zero.
- [ ] Prove odd c_a*N_o,a-O_a tends to zero.
- [ ] Construct and audit the actual even-channel analogues.
- [ ] Prove the signed metric cancellation with both actual channels.
- [ ] Attack the retained complete shell Wronskian; preserve normalization and shift obligations.
