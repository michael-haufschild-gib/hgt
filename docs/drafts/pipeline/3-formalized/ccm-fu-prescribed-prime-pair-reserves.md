# CCM-FU: prescribed-prime inclusion and uniform pair source profile

- **Stage:** 3-formalized; scratch and exact-file checks, new-closure axiom audit and global formal lint passed. Lake packaging audit remains pending.
- **Proof chain:** Actual divisor source → renewable signed reserve → exhaustive prime selection → uniform signed Abel bound → RH.
- **Closed:** Every sufficiently large prescribed prime has a reserve-producing partner after any nonempty even prime core. Complete pair changes have a uniform source profile on the entire ordered prime-ratio ray. A common far-ratio window gives opposite pair changes before and after a prescribed prime.
- **Open:** Prescribed primes below the changing core threshold; intermediate payment; uniform physical cutoff and successor-envelope control through exhaustion; RH.

## Statements about the actual source

Use the existing literal definitions

W_P(Y)=integral_(x>1) G_P(Y*x)G_P(x)/x^3,
rho_P=squarefreeDensity*product_(r in P) r/(r+1),
kappa_P=sum_n fixedCoreBlockMass(P,n),
Q_P(M)=mobiusDivisorSelectionEnergy(M,P).

For every nonempty finite prime core P there is C_P>=0 such that all
distinct unprocessed primes q>=p satisfy

|p*(kappa_(P+p+q)-kappa_P)
 -2*rho_P*(p/q)*sqrt(p/q)*W_P(q/p)| <= C_P/sqrt(p).

The constant is independent of both primes and their ratio. The first
merger and both density changes are included. No separate enlarged-core
limit replaces the uniform estimate.

If P is even, there are c>0 and T such that **every prime r>=T** has a
prime partner p<r, both outside P, with

kappa_P-kappa_(P+r+p)>=c/r.

The enlarged core is even. There are also c>0 and T such that every
prime r>=T has such a partner with

Q_P(M)-Q_(P+r+p)(M)>=c*M^2/r

for every sufficiently large integer M. The onset in M can depend on r
and its partner. This strengthens unbounded pair existence to inclusion
of every prescribed prime beyond a single threshold for the fixed core.

There is a separate compatibility constraint. For every nonempty prime
core P there is L0>=1 such that every L>=L0 admits c>0 and T with

(-1)^card(P)*(kappa_P-kappa_(P+p+q))>=c/p

whenever the distinct unprocessed primes satisfy p>=T and
L*p<=q<=(L+1)*p. Because L is freely selectable, apply this statement to
an even P and P+r using a common window. For every prescribed prime r
outside P, some common L,c,T give simultaneously

kappa_P-kappa_(P+p+q)>=c/p,
kappa_(P+r+p+q)-kappa_(P+r)>=c/p.

Such pairs exist beyond every lower prime cutoff. Consequently their
insertion raises the prescribed prime's coefficient debt
kappa_(P+r)-kappa_P by at least 2c/p. A reserve in the current core
cannot be transferred unchanged to a future required source state.
This is a constraint on these far-ratio pairs, not a rejection of other
ratios, prescribed-prime repair, or CCM-FU.

## Dependency-closed paper proofs

Take B>=0 with |W_P(Y)|<=B on Y>=1 and D>=0 with
|W_(P+p)(Y)+sqrt(p)W_P(Y/p)|<=D, uniformly over unprocessed p and Y>=1.
These are proved actual-source bounds. Write t=sqrt(p),
k=p*sqrt(q)/q^2, z=W_P(q/p), e=W_(P+p)(q)+t*z. Then |e|<=D,
|z|<=B, k<=1/t and t*k<=1. The density identities give
rho_(P+p+q)<=rho_(P+p)<=rho_P and
rho_P-rho_(P+p+q)<=2*rho_P/p.

The exact discrete release formula yields

p*(kappa_(P+p+q)-kappa_P)-2*rho_P*t*k*z
 =-p*(kappa_P-kappa_(P+p))
  -2*rho_(P+p+q)*k*e
  -2*(rho_P-rho_(P+p+q))*t*k*z.

The three terms have magnitudes at most 2*rho_P*B/t,
2*rho_P*D/t and 4*rho_P*B/t respectively. Since
t*k=(p/q)*sqrt(p/q), choose C_P=2*rho_P*(3B+D).

For the signed tail statement put s=(-1)^card(P) and let R_P be the
proved residue limit of W_P. Its proved orientation gives s*R_P<0.
Choose a=-(s*R_P)/4>0; eventually s*W_P(lambda)<=-2a. For any bounded
window [L,L+1] in that tail,
(p/q)*sqrt(p/q)>=1/(L+1)^2. Set c=rho_P*a/(L+1)^2.
The oriented main term is at most -4c. At p>=(C_P/c+1)^2 the error
is less than c, proving the stated release. Choosing the maximum of
the two tail thresholds, then the minimum margin and maximum prime
threshold, gives the simultaneous P and P+r comparisons. The corpus
prime interval theorem supplies pairs beyond every finite exclusion.

For direct prescribed-prime inclusion, use the already proved even-core
reserve window L*p<=q<=(L+1)*p with margin c/p. The corpus theorem
prime_between, with relative width 1/L and x=r/(L+1), supplies

r/(L+1)<p<(1+1/L)*r/(L+1)=r/L

for every sufficiently large r. Increase the r threshold so this partner
exceeds the reserve threshold and every member of P. Thus p<r, both
primes are unprocessed, and the complete pair reserve applies with q=r.
Its margin c/p is at least c/r. Commuting the finite-set insertions
places the prescribed prime first in the displayed final core. Two new
primes preserve evenness; no claim about the intermediate energy follows
from this commutation.

Finally subtract the two proved normalized energy limits Q(M)/M^2→kappa.
Half the strict coefficient margin holds for all sufficiently large M;
multiplication by M^2 gives the physical energy statement. No numerical
result or analytic sign assumption is an input to these arguments.

## Lean implementation and validation

- `MobiusDivisorPrimePairRatioProfile.lean`: one public uniform profile theorem.
- `MobiusDivisorPrimePairSourceOrientation.lean`: three public theorems for arbitrary tail windows, simultaneous source states and arbitrarily large debt-increasing pairs.
- `MobiusDivisorPrescribedPrimePairReserve.lean`: two public theorems for every sufficiently large prescribed prime, at coefficient and actual energy level.

All three imports are wired into RHTower. Each leaf passed a foreground
scratch check and its exact source-file check with leaf olean emission.
One external audit of these six new theorem closures found only
propext, Classical.choice and Quot.sound; no old declaration was
re-audited. Global formal lint and the scoped whitespace check passed.
No umbrella or old prerequisite was built. The known Lake packaging
audit remains pending because its prerequisite graph would trigger a
broad stale rebuild. No computation was used as a proof premise.

## Remaining coverage problem and independent experiment

The prescribed-prime theorem covers all large primes for each fixed
core. Its threshold changes when the core changes; it does not prove
that the least omitted prime ever lies beyond that threshold. Nor does
it pay every intermediate merger or bound every immediate successor.
Those remain mathematical obligations, not assumed premises.

The separate [bounded RunPod screen](../2-fully-proven/computations/ccm-fu-forced-prime-repair-2026-09-08/README.md)
tested exact-successor-envelope repair at all saved cutoffs through 32:
39,220 prescribed-prime choices, with no failure of restoration in at
most two mergers. This remains finite numerical evidence. The general
repair statement requires the full three-prime source interaction and
one bound at every cutoff; neither is proved by that screen or the
asymptotic results above.
