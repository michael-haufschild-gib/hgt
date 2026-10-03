# TG C9.11t — faithful native ground recovery

- **ID:** tg-prime-polar-ground-recovery
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** P1 `tg-principal-polar-operator-cancellation`; route TG
- **Statement:** One fixed bounded physical map recovers every native symmetric prime–polar ground tail from an actual narrow input column of the square Fourier time-band operator.
- **Status:** both affected production leaves and all fourteen public axiom queries pass; wired and indexed; global lint reports eleven unrelated unwired leaves and no finding in these two modules.

## Hard question and result

C9.11s gave only a sufficient condition for native nuclear admission. Could
time-band smoothing conceal a ground source that fails to converge? It cannot.
For every a>0 there are 0<b<=a and a bounded operator V on full SoninL2 such
that, for every original symmetric prime–polar tail K,

`V(K H_a f_b) = K f_a`,

where `f_r=1_[−r,r]` and `H_a` is the literal square time-band Fourier
operator. The same b and V work for all finite prime sets and positive lower
polar endpoints, with arbitrary upper endpoints. The prime coefficients,
polar density and both dilation directions are unchanged.

Consequently a fixed C>0 satisfies

`‖K f_a‖ <= C ‖K H_a‖_(S1)`.

Together with C9.11s this is comparison in both directions between the native
ground norm and the genuine nuclear norm. Their cofinal Cauchy criteria are
therefore equivalent. These finite-tail estimates are the formalized result;
no arithmetic ground-tail convergence is asserted.

## Dependency-closed paper proof

1. Use the verified full-carrier transfer `f_n=a^n S_n T_n f_a`, where S_n is
   the isometric parity multiplier and `T_n=I−n R_(n+1/2)` is contractive.
   Let `L_n=S_n T_n`; then `L_0=I` and `‖L_n‖<=1`. Each L_n commutes with
   every original positive dilation.

2. Define `mu_n=(1+(-1)^n)/(2(n+1))` and
   `A(z)=sum_n ((n!)^-1 z^n mu_n) L_n`. We have `mu_0=1`, `|mu_n|<=1`.
   For |z|<1, the series converges in operator norm and
   `‖A(z)−I‖ <= |z|/(1−|z|)`. Thus A(z) is invertible when |z|<1/2.
   This uses an actual convergent operator series and the Banach-algebra
   inverse theorem; invertibility is not an input.

3. The actual Taylor coefficient of the rectangular Fourier operator on f_b
   is obtained from its L2 pairing, not from a supplied coefficient formula.
   Pull the cutoff to the interval subtype; its representative is one there.
   Integrating the monomial gives
   `integral_-b^b y^n dy = 2 b^(n+1) mu_n`.
   The corpus's literal Taylor output identity and step 1 identify each
   coefficient. Continuity of evaluation and uniqueness of the known Fourier
   Taylor sum then give
   `H_(a,b) f_b = 2b A(-2pi i ab) f_a`.

4. Choose b>0 below both a and a sufficiently small reciprocal of a. Since
   the actual input is supported in [-b,b], its square and rectangular
   Fourier columns agree. Every term L_n commutes with the dilation action,
   hence so does A. Pass this through the native finite prime sum and strong
   polar integral, retaining the signed source. Therefore
   `K H_a f_b=2b A(-2pi i ab) K f_a`.
   Set `V=(2b)^-1 A(-2pi i ab)^-1` to obtain exact recovery.

5. Apply V's operator norm, evaluate K H_a at f_b, and use the contractive
   embedding of the genuine Schatten-one Banach space into bounded
   operators. For example `C=1+‖V‖‖f_b‖>0` gives the reverse nuclear
   estimate uniformly in all native source cutoffs.

## Lean evidence

`SoninPrimePolarGroundRecovery.lean` formalizes the operator series,
invertibility, actual Fourier-column identity, native exact recovery and
reverse nuclear estimate. `SoninPrimePolarGroundTransfer.lean` now also
exposes its already-proved monomial/dilation and native source commutations.
The new leaf is wired into `formal/GaloisForLFunctions/RHTower.lean`.

Both affected leaves passed final foreground `lake --old env lean <leaf>
-o <olean>` with empty diagnostics. Logs:
`/tmp/tg-c911t-ground-final.log` and `/tmp/tg-c911t-recovery-final.log`.
No full or umbrella build, numerical experiment, proof hole, heartbeat
increase or added axiom was used.

## Remaining hard mathematics

The actual critical arithmetic ground energy remains unbounded by the new
result. The next attack must control the signed cumulative prime–polar error
with its terminal square retained; time-band smoothing cannot replace that
work. Fourier-channel/full-response transport, Gamma completion, Hardy cubic
compatibility and the strict sub-unit law also remain open. RH has neither
been proved nor falsified.

Public axiom audit `/tmp/tg-c911t-axioms.lean` passed with exit 0. All fourteen
public declarations in the two affected leaves use only `propext`,
`Classical.choice` and `Quot.sound`. Index refresh passed and updated the
generated Lean API, overview, gap registry and search database. Evidence:
`/tmp/tg-c911t-axioms.log`, `/tmp/tg-c911t-index.log`.

Global lint exited 1 with eleven unrelated modules unreachable from their
umbrella; neither affected module has a lint finding. See
`/tmp/tg-c911t-lint.log`. All fourteen public names are present in
`formal/LEAN_API.md`. Owned build/search/index/lint processes terminated.
