# TT: signed centering of the complete differentiated theta packet

- **ID:** tt-parity-packet-centering
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** TT, complete signed theta current
- **Conjecture:** C51, a source-specific nonlocal centering inequality
- **Status:** sign unproved; no Lean theorem or RH claim

## Hard target

Write Phi for the literal complete source, D for the spatial derivative,
f_a(x)=exp(a*x)Phi(x), and psi_a=P(D)f_a. The polynomial P has real
coefficients and contains only even powers or only odd powers. The target is

    integral_R x * psi_a(x)^2 dx >= 0

for every such P and every 0<a<1/2. The intended connection is to the two
parity blocks of the complete signed current. A change of representation
alone is not a qualifying frontier result. The missing work is this
inequality for the actual Phi, retaining arbitrary polynomial coefficients.

## Corpus inputs checked

- ThetaCuspCenterMixedSignedJetCompleteness: the full signed physical jet
  cone is equivalent to RH; odd moments vanish.
- ThetaCuspCenterMixedSeventhRankStrict and ThetaCuspActualOddHeadVariance:
  rank seven is already strict; the actual corrected odd-three head and
  fourteenth-jet border are available. Rank-eight Schur sign remains open.
- ThetaCuspAllOrderGaussianLimit and ThetaCuspAllRankNativeTail: every
  finite native shifted matrix is positive on a rank-dependent far ray.
  There is no fixed ray on which all ranks have been proved positive.
- ThetaDerivativePacketDivisor: all-order source derivatives, exponential
  moments, and source integration-by-parts infrastructure are available.
- ThetaCuspPrimeArchSourceEquation and ThetaPrimeShiftNoetherCurrent:
  literal prime--Gamma--pole source equation and its signed Ward balance.
- ThetaPrimeGammaScalingEnergy: the positive prime-link energy uses a
  Gamma diagonal weight evaluated on Phi. It is not the full nonlocal
  Gamma form on arbitrary differentiated packets.
- ThetaRiccatiGaussianCountermodel: strong log-concavity and the stated
  reflected Riccati inequalities do not give an all-polynomial producer.

## Paper calculation: remove the integrated mixed term, not its sign debt

All functions below are smooth with the decay needed for integration by
parts, from the actual source's tilted Schwartz/exponential-moment laws.
The commutator D*x-x*D=1 gives

    partial_a psi_a = x*psi_a + P'(D)f_a.

If P has parity epsilon in {1,-1}, formal integration by parts gives
P(D)^*=epsilon*P(D), while P'(D)^*=-epsilon*P'(D). The operators commute,
so P(D)^* P'(D) is skew-adjoint. Consequently

    integral_R psi_a * P'(D)f_a = 0,
    partial_a integral_R psi_a^2 = 2 integral_R x*psi_a^2.

This corrects the earlier working-log assessment that the mixed term had
to remain as an independent integrated obstruction. It vanishes for each
parity block, although it need not vanish for a polynomial mixing parities
or pointwise in x. The remaining first spatial moment is signed. A positive
norm, its evenness in a, and the cancellation above do not prove its sign.
These calculations have not been promoted to a formal result.

## First sign attempt: pointwise reflection pairing

For P=c0+c2 D^2 and x>0, set

    u_plus  = (Phi, Phi''+a^2*Phi+2*a*Phi'),
    u_minus = (Phi, Phi''+a^2*Phi-2*a*Phi').

The reflection-paired density of the first spatial moment is the quadratic
form with matrix

    x * [exp(2*a*x) u_plus u_plus^T
         - exp(-2*a*x) u_minus u_minus^T].

Its determinant is exactly -16*a^2*x^2*Phi^2*(Phi')^2. The complete source
is positive and strictly decreasing for x>0, so this matrix is indefinite
there. Thus the proposed *pointwise* square domination cannot prove C51,
already for two even coefficients. This is a paper diagnosis of an attempted
proof, not a falsification of C51: the corresponding integrated low-rank
positivity is already known. Do not spend a new leaf on this elementary
obstruction. Nonlocal integration or a lawful flux remains necessary.

## Second sign attempt: curvature at the neutral aperture

For parity P, put psi=P(D)Phi, eta=P'(D)Phi, zeta=P''(D)Phi. Two
integrations by parts give the exact candidate neutral variation formula

    [partial_a^2 integral psi_a^2]_(a=0)
      = 4 integral x^2*psi^2 - 2 integral eta^2 - 2 integral psi*zeta.

For P=D^n, n>=1, this reduces to

    4 integral x^2*(Phi^(n))^2 - 2*n integral (Phi^(n-1))^2.

Discarding the last two terms would be invalid. The universal weighted
Hardy estimate does not supply the required order-dependent sign; the
actual source must supply it. Even proving this neutral variation at every
order would still require a separate argument for all positive apertures.
No sign assertion or new formal receiver is made here.

## Third attempt: use the literal arithmetic source operator

Let T be the translation-invariant prime--Gamma--pole expression in
literal_complete_theta_source_equation, so T Phi=x Phi, and formally set
T_a=exp(a*x) T exp(-a*x). Commuting a finite differential polynomial through
this expression would give

    T_a psi_a = x*psi_a + P'(D)f_a,
    integral psi_a*T_a psi_a = integral x*psi_a^2.

The derivative exchanges and integral/sum exchanges must be discharged
for this exact packet before treating that displayed operator identity
as formalized. More importantly, its quadratic-form sign is not supplied
by the existing fixed-source Gamma diagonal estimate. Keep the full pole
term and both signed nonlocal terms. The next attempted proof must control
those terms on the complete theta derivative module, not replace T_a by a
positive auxiliary operator.

Follow-up corpus check: `CCMThetaGroundRHCriterion` and
`CCMThetaThreeEnergyComparison` already identify the complete three-energy
form with the Weil form for compact smooth source profiles. That global
bridge is not missing. The tilted differential-packet domain and its sign
remain separate obligations. See
[C52](../../tt-complete-source-charged-poincare.md) for the exact polar variance
and odd-charge payment and the unsuccessful mixed-Ward sign attempt.

## Assessment and continuation

No new signed-current positivity theorem was proved in this pass. C48-S,
the rank-eight integrated Schur sign, and the all-rank compact correction
remain open. C51 is an alternative attack on exactly that sign, with the
integrated parity cancellation now explicit. No generic Schur receiver,
unsigned Gram theorem, tail refinement, or finite-bound optimization was
added to Lean. Continue by constructing and signing the literal nonlocal
arithmetic form, or by returning its exact signed payment to C45/C48.

## Retrieval record

2026-10-02: compact-Schur, differentiated-tilt, source-commutator, odd-four
compact-sign, and parity-centering corpus searches. Detailed coverage and
completion status are recorded in the session working log. Source reads
checked the relevant identities and their scope; no external literature
was used to infer the current frontier. Paper identities above are not
Lean audit certificates.
