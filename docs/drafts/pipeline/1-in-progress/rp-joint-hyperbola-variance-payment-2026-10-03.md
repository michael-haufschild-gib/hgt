# RP-59: joint hyperbola variance payment

Route RP. RP-58 yielded no frontier theorem. The hard objective remains
an unconditional linear floor for the complete native normalized
history, paying both centroid and square debts. Positive-damping
negative work and signed high-LCM control remain unresolved.

Attack the actual arithmetic null form and the full square-cutoff
Mangoldt hyperbola identity together. Retain the future-error pairing,
harmonic prime error, second-grade discrepancy and physical variance
coefficients. The inverse-source norm estimate from RP-58 did not
remove these terms and is not reused as a lower bound.

First conjecture: their joint signed action admits a critical estimate
after the exact variance coefficients are applied, even though the
individual terms do not have such estimates. Check exact cancellations
before any absolute value. No theorem, sign, or bound claimed yet.

## Trial 1: substitute the full hyperbola law into the actual variance

The corpus's arithmetic null form is H=4A+4q/3-(2psi+e)^2/m-m^3/12.
Here A is the square-root Chebyshev moment, m is critical prime mass,
q is the width-cube prefix, and e is matched-centroid excess. At N=K+2,
put R=psi(N)-N, U=sum_(d<=N) Lambda(d)*R(floor(N^2/d)),
h=sum_(d<=N) Lambda(d)/d-log(N)+gamma, D the second-grade discrepancy,
and F the nonnegative hyperbola floor remainder. The existing exact law
gives the following coefficient-faithful paper substitution:

    m*H = 4*m*A-4*N^2-m^4/12-8*N^2*h-8*U+4*D(N^2)+8*F
             +4*m*q/3-4*psi(N)*e-e^2.

The linear endpoint R cancels. The full signed combination of U, h and
D remains. Substituting the hyperbola identity a second time merely
restores psi(N)^2. No upper estimate for that combination was proved.
The already formalized weighted-credit/two-square-debt decomposition
was read; it is not a new result of this turn.

## Trial 2: test the exact Selberg forcing before absolute values

SelbergSymmetryCore.lean applies |mu|<=1 to the exact Tatuzawa-Iseki
source, losing the signed cancellation. The source is explicitly

    S(k)=floorSummatory(psiDefect)(k)
        =log(k!)-sum_(d<=k) floor(k/d)+2*gamma*k,
    |S(k)|<=24*sqrt(k).

Paper weighted identity: let f(t)=psiDefect(floor(t)), S(t)=S(floor(t)),
I(X)=integral_1^X f(t)/sqrt(t) dt, and
J(X)=integral_1^X log(t)*S(t)/sqrt(t) dt. Extending the exact discrete
identity to real cutoffs adds log(x)-log(floor(x)) times the existing
Mobius floor inversion on both sides. Finite integration and x=n*t give

    I(X)*log(X)-integral_1^X I(t)/t dt
        +sum_(n<=X) Lambda(n)*sqrt(n)*I(X/n)
      =sum_(n<=X) mu(n)*sqrt(n)*J(X/n).

The actual weighted Chebyshev credit differs from -I(X)/2 by only the
explicit bounded-floor and constant contributions, of order sqrt(X).
This identity has no proved critical estimate for its complete signed
right side. Using |S(t)|<=24sqrt(t) separately gives a noncritical
X^(3/2)-scale estimate; it does not supply the required linear payment.

The corpus already disproves a generic inference from the coarse
Selberg bounds: PMSelbergPowerInputBoundary.lean has a comparison
remainder of power 3/4 obeying both unchanged-constant inequalities
while its canonical variance diverges. PMSelbergSublinearPowerBoundary
even tunes its response to o(N). These are not the actual psi remainder
and do not falsify RH. They require using the exact physical source,
not promoting the coarse recursion to a critical bound.

## Trial 3: center the future pairing using the full harmonic tail

The following derivation is on paper, not Lean certified. Use the real
error E(x)=psi(x)-x for x>0 (so E(x)=-x below 1), and extend the exact
second-grade discrepancy to real cutoffs:

    D(x)=sum_(n<=x) (Lambda*Lambda)(n)-x*(log(x)-1-2*gamma).

MertensSecondTheorem.lean supplies the harmonic constant -gamma; the
native prime-error decay admits integral_1^infinity |E(t)|/t^2. Partial
summation therefore gives, with h(y)=sum_(d<=y) Lambda(d)/d-log(y)+gamma,

    h(y)=E(y)/y-integral_y^infinity E(t)/t^2 dt.

Use E(y^2/d), including its fractional-part correction, in the continuous
hyperbola identity. It becomes

    E(y)^2+D(y^2)
      =2*sum_(d<=y) Lambda(d)*E(y^2/d)
          -2*y^2*integral_y^infinity E(t)/t^2 dt
      =2*integral_(0,y] E(y^2/t) dE(t).

Here dE means the locally finite signed measure sum Lambda(n)*delta_n-dt.
This notation keeps both prime atoms and continuous background. The
tail is admitted by the unconditional inverse-square error integral;
no critical square-integrability has been presumed.

## Trial 4: finite Mellin integration and the reciprocal-cutoff term

For 0<alpha<1 and N>=1, define

    A_alpha(v)=integral_0^v E(t)*t^(-alpha-1) dt,
    F_alpha(v)=sum_(d<=v) Lambda(d)*d^(-alpha)
                   -v^(1-alpha)/(1-alpha).

Partial summation gives F_alpha(v)=v^(-alpha)*E(v)+alpha*A_alpha(v).
Integrate the centered identity against y^(-2alpha-1) on (0,N),
substitute u=y^2/t, and keep t<=min(u,N^2/u). The part u<=N is

    integral_0^N E(u)^2*u^(-2alpha-1) du + alpha*A_alpha(N)^2/2.

The remaining part is a genuine reciprocal-cutoff pairing. The identical
square-energy integral on the left cancels, leaving the paper identity

    integral_0^N D(y^2)*y^(-2alpha-1) dy
      =alpha*A_alpha(N)^2/2 + T_alpha(N),
    T_alpha(N)=integral_N^infinity E(u)*u^(-alpha-1)*F_alpha(N^2/u) du.

All interchanges here have a direct unconditional majorant: near zero
E(t)=-t and alpha<1; beyond N^2, F_alpha(N^2/u) is exactly
-(N^2/u)^(1-alpha)/(1-alpha), leaving the admitted |E(u)|/u^2 tail.
The intermediate interval is finite. This establishes paper admission,
not a critical bound.

At alpha=1/2, F_alpha(v) is exactly M(v)-2sqrt(v), the native mass
discrepancy, and

    T_(1/2)(N)=N^(-1)*integral_0^N
        E(N^2/v)*(M(v)-2sqrt(v))/sqrt(v) dv.

Thus the history's mass error is paired with the actual future Chebyshev
error. Neither factor has been replaced by an envelope or an artificial
source. The existing D(x)=o(x) estimate yields only an o(N) scale for
its integrated term at alpha=1/2; it does not control this signed pairing
at the needed critical scale.

One additional exact localization is available on paper. Normalize
T_alpha(N) by N^(2-2alpha). Since F_alpha(v)=-v^(1-alpha)/(1-alpha)
for v<1, the part u>N^2 is

    -N^(2-2alpha)/(1-alpha)*integral_(N^2)^infinity E(u)/u^2 du.

The common far tail cancels in the difference of normalized values at
N and 2N; equivalently, expand F_alpha into its finite prime sum before
subtracting. This leaves a finite signed prime/error integral, with all
continuous terms retained. Its sign and critical estimate remain open.

## Assessment and next attack

No critical lower bound or new frontier theorem proved. No Lean source
changed or build run. The derived identities are kept as paper work,
not promoted as identity-only frontier modules. This does not retire RP
or establish an inverse/hyperbola no-go.

Next conjecture: the finite difference of the normalized reciprocal
pairing has a signed payment law after combining its prime part with
the original second-grade discrepancy and both variance debts. Test
that finite kernel before absolute values. Do not repeat the failed
generic Selberg bootstrap or the already investigated aligned modular
packet signs. Positive-damping negative work, signed high-LCM control,
the complete history floor, and RH remain unresolved.

## Corpus audit and cleanup

Three documented deep searches (budget 300 seconds each) completed with
partial=false, errors=[], and no unfinished stages. Each had zero pending
inventory files but reported an older coverage snapshot, unavailable and
unmeasured semantic coverage, and incomplete background refresh:

- Joint hyperbola: query generation 1215533; coverage 1215557/current
  1215558; 65014 files.
- Weighted Selberg: query generation 1215550; coverage 1215572/current
  1215573; 65015 files.
- Centered future pairing: query generation 1215601; coverage
  1215614/current 1215615; 65016 files.

Candidate lemmas, source arguments, proof ideas and ingredient sets were
inspected. Retrieved evidence was source-only, mostly with pending/stale
compiler coverage. No search hit is treated as a fresh Lean audit.
Relevant exact source statements were read. MertensVonMangoldtEulerConstant
already supplies integrableOn_chebyshevError_div_sq and
integral_chebyshevError_div_sq=-gamma-1; the endpoint-minus-tail identity
also exists in CCMFUSuzukiCriticalRemainderVariation. These are inputs,
not new results. Conditional square-root tail bounds and the unrelated
atomic Stieltjes bounds do not pay the actual future pairing.

RP-24/RP-37 prior signed modular forcing attempts were checked to avoid
repeating their failed aligned-phase-to-moving-cutoff inference. The
present unproved target is the coupled reciprocal-cutoff difference,
not a separate sign for one modular packet. No route is retired.

Owned sessions 14941, 43996 and 33326 all exited zero. Temporary search
JSONs were removed after this record. No owned search/build remains.
No Lean edit, new axiom, numerical experiment, subagent, full build,
resource-limit override, commit or push. Global lint was not rerun with
no Lean changes. Goal active; no external blocker.
