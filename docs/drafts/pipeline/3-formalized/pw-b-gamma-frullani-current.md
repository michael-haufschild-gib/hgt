# PW-B actual Frullani current and signed joint admission

- **ID:** PW-B-GAMMA-FRULLANI-CURRENT-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** The full coefficient derivative is the convergent Frullani integral of the literal weighted-translation response. At zero coefficient parameter this response is globally integrable on both positive rays, Fubini is valid, and its integral is Gamma(3/2), although the original separate atom norm masses are not summable.

## Actual operator and complete source

For positive x keep Q(x)=sqrt(x)*exp(-x), the complete arithmetic family
M_b(x)=sum_n mu(n)*exp(-b*log(n))*Q(n*x), and E_b=partial_b M_b.
The [parameter-generator audit](pw-b-gamma-parameter-generator.md) proves
this actual derivative at every complex b and positive x.
Define the original half-density translation

`T_h f(x)=sqrt(x)/sqrt(x+h)*f(x+h)`, for h>=0 and x>0.

It obeys T_0=id and T_h T_k=T_(h+k) on that ray. Direct evaluation of
the actual Gamma source proves T_h Q(n*x)=exp(-n*h)*Q(n*x) for n>=1.
The arithmetic atom identity also holds at n=0 because mu(0)=0;
Q(0) is not set to zero. No source coefficient is discarded.

Set K_n(h)=(exp(-n*h)-exp(-h))/h. The corpus's convergent Frullani
integral, applied to positive n and 1, gives

`integral K_n(h) dh=-log(n)`,
`integral norm K_n(h) dh=log(n)`.

The norm identity follows from the exact nonpositive sign on h>0.
The separate zero-index kernel is not admitted; its complete arithmetic
atom vanishes. Every actual atom A_b(n,x) therefore satisfies

`integral K_n(h)*A_b(n,x) dh=-log(n)*A_b(n,x)`,
`integral norm(K_n(h)*A_b(n,x)) dh=norm(-log(n)*A_b(n,x))`.

For every fixed x>0 and complex b, the current's polynomial Gamma
majorant makes these norm integrals summable. Full series/integral
interchange is consequently valid. With the response defined directly by

`F_b(x,h)=(T_h M_b(x)-exp(-h)*M_b(x))/h`,

this proves F_b(x,.) in L1(dh) and integral F_b(x,h) dh=E_b(x).
It identifies the complete nonlocal source, not an abstract operator
applied under an unproved domain premise. The original atomwise global
norm-integral series converges exactly when Re(b)>0, by the
[absolute-admission theorem](pw-b-gamma-global-absolute-admission.md).

## Signed product admission at zero

The absolute atom test fails at b=0. A different, exact signed assembly
admits the literal F_0 jointly on (h,x) in the two positive rays.
Let S(n)=sum_{j<=n}mu(j), and let B_Q(n,x) be the previously admitted
source Abel atom. Retain

`B_n(h,x)=S(n)*(K_n(h)*Q(n*x)-K_(n+1)(h)*Q((n+1)*x))`.

Its exact split is

`B_n=K_n*B_Q(n,.)+S(n)*(K_n-K_(n+1))*Q((n+1)*.)`.

For n>=1 the kernel increment is nonnegative on h>0, with norm integral
log(n+1)-log(n)<=1/n. The admitted Gamma dilation has norm mass
Gamma(3/2)/(n+1). Product integrability of both factors, the earlier
adjacent-source estimate and the increment bound prove

`integral integral norm B_n dh dx`
`<= (Gamma(3/2)+Gamma(5/2))*abs(S(n))*log(n)/n^2`
`   +Gamma(3/2)*abs(S(n))/n^2`.

Both complete majorant series converge by unconditional corpus theorems.
Thus all Abel atom norm integrals are summable on the product measure.
At every fixed positive h,x, norm K_n(h)<=exp(-h)/h and the original
Gamma inverse-square bound also admit the pointwise Abel sum.
Finite summation by parts retains exactly the terminal

`sum_{n<N} B_n(h,x)`
`=sum_{n<=N} K_n(h)*mu(n)*Q(n*x)-S(N)*K_N(h)*Q(N*x)`.

The kernel bound times the previously proved source terminal decay
sends this terminal to zero. Both complete pointwise sums exist;
the finite identity therefore proves F_0(x,h)=sum_n B_n(h,x).
This identifies the admitted assembly with the literal response.
No summation convention or replacement definition supplies the equality.

## Surviving mass and route scope

The full response is L1(dh dx). Fubini now legitimately exchanges its
two integrations. The actual source identity and the already proved
mass of E give

`integral integral F_0(x,h) dh dx`
`=integral integral F_0(x,h) dx dh=Gamma(3/2)`.

The product integral has the same mass, and its L1 norm is strictly
positive. The original separate atom norm integrals remain nonsummable
at zero. This proves a positive signed joint-domain survivor, while
retaining the nonzero contribution required in a complete balance law.

PW-B remains active and RH unproved. The proof chain is literal PW
response -> FE imbalance -> positive Deninger Ward transmutation ->
independently source-forced fixed-grade balance -> RH. The present
result supplies an actual nonlocal arithmetic generator and its signed
global domain. It does not identify a physical spectral label, establish
a self-adjoint realization or force the required balance.

## Search and method audit

Deep method searches cover the Frullani source identity, absolute kernel
mass and signed product admission. Results report partial indexed
coverage; complete candidate, source-argument, method and freshness
metadata are retained in the [search artifact](../1-in-progress/pw-b-gamma-frullani-searches.json).
The first search locates the applicable convergent Frullani formula.
The second gives generic logarithmic derivative results, not the required
absolute estimate. The third suggests product norm control and Abel
summation; the actual two-variable estimate is proved here. A fourth reflection/commutator search suggests a trace-zero/positive-kernel
argument. Its nuclear-operator and bounded-partner hypotheses, and equality
of that trace to this literal response, are not supplied. The separate
positive heat-pair formula describes different prescribed squared distances.
Neither result transfers to the actual source without those missing data.
The exact Gamma mass prevents identifying this integral with an ordinary
zero commutator trace without accounting for a compensating contribution.
The four searches cover respectively 723356, 723356, 723371 and 723387
indexed declarations; candidate applicability was checked in the source
and, for used ingredients, in the actual Lean proof.

Broad relaxation, mixing and damping searches were also attempted;
direct arXiv searches encountered timeouts. Primary abstracts read include
[the Georgi–Machacek phase-transition analysis](https://arxiv.org/abs/2609.06139)
(September5) and [uncertainty quantification in art](https://arxiv.org/abs/2608.04038)
(August3). Their thermal approximations and empirical video-generation
methods supply no proved transfer to this arithmetic source. A search
snippet associated with the former did not match its primary abstract;
no claim relies on that snippet. No external theorem is a Lean premise,
and no numerical experiments were run.

## Lean audit

The source leaf is ThetaCuspHawkingParikhWilczekGammaMobiusFrullaniCurrent.lean
(250 lines, 24 public theorems and four definitions). The joint leaf is
ThetaCuspHawkingParikhWilczekGammaMobiusFrullaniJointAdmission.lean
(284 lines, 21 public theorems and two definitions), both under
formal/GaloisForLFunctions/RHTower. Their closed capstones are
pwGammaMobiusFrullaniCurrent_closed and pwGammaMobiusFrullaniJoint_closed.
Scratch `lake env lean` checks passed; both direct leaf checks passed
without warnings.
Both targeted leaf builds passed. The joint build replayed existing
upstream style warnings. All 51 public declarations passed the scratch
axiom audit, using only `propext`, `Classical.choice`, and `Quot.sound`.
All public names have unique source declarations. Both modules are wired
into RHTower. No full or umbrella build, numerical experiment, commit or
push ran.

The formal lint command failed on one unrelated shared-worktree module,
FokasLenellsCausalFrequencyBessel, unreachable from its umbrella; it reported
no error in these PW-B leaves. That unrelated module was left untouched.
Index and documentation verification are recorded in the attack ledger.

One premature joint scratch check overlapped the still-running core build
and failed on the missing core olean. This was acknowledged and corrected:
the core build completed before the successful joint scratch check, direct
check, targeted build and axiom audit ran in sequence. All owned Lean
processes completed. RH remains unproved; the goal remains active.
