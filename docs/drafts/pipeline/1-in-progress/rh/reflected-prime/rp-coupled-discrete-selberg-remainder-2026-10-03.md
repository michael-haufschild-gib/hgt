# RP-61: coupled discrete Selberg remainder

Route RP. RP-60 proved no frontier bound. Hard targets remain the
native history floor (both centroid and square debts), signed high-LCM
work, and negative-work payment at each fixed positive damping.

This trial keeps the exact RP-60 product source and terminal square.
Put X=N^2 and W_N(r)=1/(N*sqrt(r))-1/N^2 for 1<=r<=X.
The corpus identity Lambda*Lambda=mu*log^2-Lambda*log gives

    sum_(r<=X) (Lambda*Lambda)(r)*W_N(r)
      = X^(-1)*sum_(d<=X) mu(d)*S(X/d)
          -sum_(r<=X) Lambda(r)*log(r)*W_N(r),
    S(Y)=sum_(k<=Y) log(k)^2*(sqrt(Y/k)-1).

Conjecture under investigation: the discrete remainder in this coupled
source has a signed payment law at the critical scale when retained
with the original terminal square. A componentwise coarse Selberg
estimate, a transform identity, or an unproved cancellation assumption
does not establish this conjecture.

The first corpus search completed successfully; its candidates include
the exact Mangoldt antidiagonal convolution and Mobius floor inversion.
No candidate supplies the proposed coupled critical bound. Search hits
are source-only and must not be treated as compiler certificates.

Paper work below is not Lean certified. No new theorem is claimed yet.

## Trial 1: keep the logarithmic companions coupled

Let q(d)=mu(d)*log(d), and define, for Y>=1,

    J(Y)=sum_(k<=Y) (sqrt(Y/k)-1),
    P(Y)=sum_(k<=Y) log(k)*(sqrt(Y/k)-1).

From Lambda=mu*log and the logarithmic derivation rule,

    Lambda*Lambda=-(mu.log)*log=-q*log.

Indeed the Lambda.log companion contributes
mu(d)*log(k)*(log(d)+log(k)) at each product d*k; its log(k)^2
part cancels the original source exactly. Thus, with b=Lambda*Lambda,

    R(X):=sum_(r<=X) b(r)*(sqrt(X/r)-1)
         =-sum_(d<=X) q(d)*P(X/d).

The terminal uses the same coefficients at a different cutoff. The
corpus logarithmic convolution identity q=-Lambda*mu implies
q*zeta=-Lambda, so

    Z(N)=sqrt(N)*M(N)-psi(N)=-sum_(d<=N) q(d)*J(N/d).

Consequently the complete RP-60 expression is

    f(N)=-N^(-2)*sum_(d<=N^2) q(d)*P(N^2/d)
         -2log(N)+2gamma+3
         -(1+N^(-1)*sum_(d<=N) q(d)*J(N/d))^2.

This is a coupled two-scale formula, not a payment estimate. The long
linear sum and short quadratic sum cannot be bounded independently
without proving an additional arithmetic cancellation statement.

## Trial 2: retain the fractional endpoint in Euler summation

Write Q(t)=({t}^2-{t})/2, the periodic version of the corpus's local
Bernoulli half. It is continuous, vanishes at integers, has derivative
{t}-1/2 almost everywhere, and is bounded. Define

    a(t)=(1-log(t)/2)*t^(-3/2),   b0(t)=1/t,
    a'(t)=(3log(t)/4-2)*t^(-5/2), b0'(t)=-t^(-2),
    A=4-integral_1^infinity Q(t)*a'(t) dt,
    B=-1+integral_1^infinity Q(t)*b0'(t) dt.

These displayed improper integrals are absolutely admitted by the
bounded Q kernel and the displayed decaying derivatives. In particular
no Lebesgue integral of ({t}-1/2)/t is being used as if absolutely
convergent.

Euler summation for g_Y(t)=log(t)*(sqrt(Y/t)-1), followed by the
corpus's Bernoulli integration by parts, gives the exact paper formula

    P(Y)=Y*(log(Y)-3)+A*sqrt(Y)+B+r(Y),
    r(Y)=-Q(Y)*log(Y)/(2Y)
          +integral_Y^infinity Q(t)*
            [sqrt(Y)*(3log(t)/4-2)*t^(-5/2)+t^(-2)] dt.

Both endpoint values g_Y(1), g_Y(Y) are zero. The surviving boundary
term is Q(Y)*g_Y'(Y), with g_Y'(Y)=-log(Y)/(2Y); deleting this term
at a noninteger Y would change the source. Bounded Q and integration
of the displayed powers give r(Y)=O((1+log(Y))/Y).

The companion calculation for the terminal kernel is

    A0=-3/2-(3/4)*integral_1^infinity Q(t)*t^(-5/2) dt,
    J(Y)=Y+A0*sqrt(Y)+1/2+j(Y),
    j(Y)=-Q(Y)/(2Y)
          +(3/4)*sqrt(Y)*integral_Y^infinity Q(t)*t^(-5/2) dt.

Here the nonzero lower endpoint of sqrt(Y/t)-1 supplies half its
value in Euler summation. The remaining integral is again absolutely
admitted and j(Y)=O(1/Y).

The pointwise decay does not pay the arithmetic remainder. Substitution
of Y=X/d into the long sum gives only the crude absolute upper scale

    X^(-2)*sum_(d<=X) d*log(d)*(1+log(X/d))=O(log X).

The fractional arguments X/d are not integer endpoints. The corresponding
boundary term in the original signed source is exactly

    (1/(2X^2))*sum_(d<=X)
      mu(d)*d*log(d)*log(X/d)*Q(X/d),

together with its integral remainder, the smooth moments, and the
original short terminal square. No critical signed bound for that
complete combination was obtained. This rejects the attempted
componentwise absolute-error proof, not the coupled conjecture.

## Trial 3: test whether the coupling removes the spectral obstruction

This is a paper diagnostic using the corpus's logarithmic-derivative
residue, not an assertion of ordinary integral convergence at a zero.
For Re(s)>1 the admitted Mellin transform of R is

    integral_1^infinity R(X)*X^(-s-1) dX
      = (zeta'(s)/zeta(s))^2 / (2*s*(s-1/2)).

For a single coefficient, integration of sqrt(X/r)-1 from r to
infinity gives r^(-s)/(2*s*(s-1/2)). The source coefficient series
is the square of the Mangoldt series. Equivalently the Mellin
transform of P is -zeta'(s)/(2*s*(s-1/2)), while that of q is
zeta'(s)/zeta(s)^2; this verifies the cancellation from Trial 1.

If rho has positive imaginary part and zeta-zero multiplicity m,
the meromorphic continuation of the displayed transform satisfies

    (s-rho)^2 * Rhat(s) -> m^2/(2*rho*(rho-1/2)) != 0.

This follows by squaring the existing punctured-limit residue theorem.
The double pole survives regardless of the multiplicity of the zeta
zero. It does not prove an off-line zero exists, does not locate zeros,
and does not justify a critical Mellin integral. Nor was it shown that
the transform of the physical terminal square cancels this pole; a
pointwise square cannot be replaced by the square of a transform.

An exact finite rectangle check also prevents claiming extra coercivity.
For a,b<=N, put w_a=sqrt(N/a)-1. Then

    sqrt(N^2/(a*b))-1=w_a*w_b+w_a+w_b.

Since Lambda is nonnegative, expanding R(N^2) gives

    R(N^2)=Z(N)^2+2*psi(N)*Z(N)+R_out(N),
    R_out(N)=2*sum_(b<=N) Lambda(b)*
      sum_(N<a<=N^2/b) Lambda(a)*(N/sqrt(a*b)-1) >= 0.

After substituting in f, the rectangle square cancels. The remaining
asymmetric prime-pair term is the same unpaid future work already
exposed by RP-59/RP-60. Positivity of R_out supplies no critical
upper payment. This is not a new frontier theorem.

## Corpus evidence and search audit

Read source mechanisms used here:

- DirichletLogDerivation.lean: logarithmic convolution derivation and
  exact second-grade identity.
- EulerDeletionLogPrimeForcing.lean: logarithmic_convolution and
  logarithmic_sum, including all dilation compensators.
- EulerMaclaurinSawtooth.lean: Bernoulli half, unit-cell integration
  by parts, trapezoid identity and fractional endpoint convention.
- LogSquaredSummatory.lean: its signed first-order sandwich is too
  coarse for the present coupled payment.
- ZetaLogDerivResidue.lean: neg_logDeriv_zeta_zero_residue.
- RoutePCompensatedMassRiccati.lean: the quadratic Abel barrier is an
  unproved input to its RH receiver, not an unconditional source bound.

The search hit EulerDeletionRemainderMobiusInversion.lean proves
absolutely convergent inversion over positive multiples with a
decaying weighted power error. The present kernel is evaluated at
X/d over a moving finite head. Its summability theorem does not
transfer to this reciprocal-cutoff sum.

Three direct documented deep searches completed, terminal exit 0:

- Coupled Mobius/log-squared/Mangoldt source: query generation
  1215765, coverage=current 1215787, 65030 files.
- Euler/discrete reciprocal remainder: query generation 1215810,
  coverage=current 1215820, 65033 files.
- Mangoldt convolution/logarithmic-derivative pole: query generation
  1215855, coverage=current 1215863, 65037 files.

All reported partial=false, errors=[], no unfinished stages and zero
pending inventory files. Semantic coverage was unavailable/not
measured and refresh remained incomplete because the background
indexer was running. Compiler coverage was predominantly pending,
stale or unavailable; candidate/source-argument hits were source-only.
No generated ingredient set supplied the coupled critical estimate.

## Outcome and next attack

No frontier bound or RH proof/falsification obtained. No Lean source
changed, so there is no new module, umbrella import, build, or axiom
audit to report. Existing global lint failure is not claimed repaired.
The coupled conjecture remains open; this card does not retire RP.

The next attack must bound the signed reciprocal Bernoulli contribution
with the two physical q-cutoffs and terminal square still present.
The new explicit boundary kernels permit testing squarefree-overlap
cancellation directly; their pointwise absolute bounds do not suffice.
