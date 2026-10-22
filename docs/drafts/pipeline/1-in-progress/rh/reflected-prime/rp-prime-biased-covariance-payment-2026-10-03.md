# RP-63: prime-dependent covariance at the physical cutoff

Route RP. RP-62 supplied no frontier bound. Hard targets remain fixed
positive-damping negative work, signed high-LCM control, and payment
of both native history debts. The previous scalar Bernoulli regrouping
returned the existing source after its compensator canceled.

This trial keeps the literal channel
c_d=mobiusDivisorDilationChannel(M,d), its original cutoff d<M, and
all residual prime-label fibres. Let theta_p=1-1/p and
theta(d)=product_(p|d)theta_p. Select primes independently with these
probabilities, and average the existing retained-fibre energy.
Conjecture under investigation: its full covariance has a critical
payment bound that does not assume the native mean-head square bounded.

## Exact finite covariance calculation (paper, not Lean certified)

Write E_theta(M) for the averaged energy and I for the squarefree
indices 1<=d<M. The corpus's exact pair formula gives

    E_theta(M)=sum_(d,e in I) c_d*c_e*
       product_(p in primeFactors(d) symmetricDifference primeFactors(e))theta_p
      =sum_(d,e in I) c_d*c_e*theta(d)*theta(e)/theta(gcd(d,e))^2.

Put beta(r)=product_(p|r)(theta_p^(-2)-1) for squarefree r and
F_r(M)=sum_(d in I,r|d)c_d*theta(d). Expanding the finite divisor
product of theta(gcd)^(-2) gives

    E_theta(M)=sum_(squarefree r<M) beta(r)*F_r(M)^2,
    E_theta(M)-F_1(M)^2=sum_(squarefree 2<=r<M)beta(r)*F_r(M)^2>=0.

This retains the mean-head square with coefficient exactly one. It
has not produced an upper bound. The full-selection event also gives

    (product_(p<M,prime p)theta_p)*(sum_(d in I)c_d)^2<=E_theta(M).

Every identity is finite and uses the actual source coefficients. No
critical integrability, uniformly bounded fibre, or missing covariance
term is assumed.

## Projection cost cancels the proposed contraction (paper)

For squarefree r put gamma(r)=product_(p|r)(1-theta_p^2). The exact
covariance also reads

    E_theta(M)=sum_(squarefree r<M) gamma(r) *
      [sum_(k<M/r,(k,r)=1) mu(k)*theta(k)*A(M,r*k)]^2,

where A is divisorUnsignedDilationChannel. Exact continuous homothety
turns the inner square into r times a prime-deleted head at time M/r;
the real cutoff remains clipped as in the corpus theorem.

At that smaller time, Boolean inversion recovers the prime-deleted
head from the divisor fibres F_s by sum_(s|r)mu(s)*F_s. Weighted
Cauchy therefore costs sum_(s|r)1/beta(s). Whenever all these divisor
coordinates are active, this equals

    product_(p|r)(1 + 1/(theta_p^(-2)-1)) = 1/gamma(r).

It cancels the gamma(r) in the covariance exactly. Thus this independent
cofactor estimate supplies no rare-selection contraction. This does
not exclude a bound using joint relations between different cofactors.

## Native sharpness and positive survivor

Let a=A(M,1), b=A(M,p), theta=1-1/p for a prime p. The signed native
coefficients are c_1=a and c_p=-b. Their two-channel covariance is

    E_p=(1-theta)*(a^2+b^2)+theta*(a-b)^2
       =(b-theta*a)^2+(1-theta^2)*a^2.

This exact nonnegative remainder is the positive survivor. In
particular (1-theta^2)*a^2<=E_p. The fixed-channel profile theorem
gives a/sqrt(M)->c_0 and b/sqrt(M)->c_0, with c_0>0 already proved
in the corpus. Consequently E_p/M->2*c_0^2/p, and

    [(1-theta^2)*a^2-k*E_p]/M
      -> c_0^2*(2*(1-k)*p-1)/p^2.

For every k<1 and every prime lower threshold B, choose a prime
p>=B with 2*(1-k)*p>1. The limit is strictly positive. Thus eventually
in the original physical cutoff M,

    k*E_p < (1-theta^2)*a^2.

No uniform factor k<1 improves the projection inequality for these
native compressions, even after deleting any finite prime prefix
and any finite cutoff prefix. The limit order is: choose a fixed
prime, then let M grow. No joint-limit interchange is used.

Scope: this is sharpness for the native two-channel compression,
not a lower bound on the complete covariance, not a no-go theorem
for the RP route, and not an RH proof or falsification. The hardest
payment problems remain open. A further attack must retain relations
between prime-deleted heads, rather than paying them independently.

Lean implementation audited:
`formal/GaloisForLFunctions/RHTower/RoutePBiasedPrimeProjection.lean`.

Final foreground audit `lake --old env lean` on this leaf with explicit
olean output passed, exit 0, no diagnostics. Five public theorems were
audited using `#print axioms` in `/tmp`: only `propext`,
`Classical.choice`, and `Quot.sound`. The leaf is wired into RHTower;
no umbrella build ran. Global `scripts/formal_tools.py lint` exited 1
on 12 other unreachable modules: the previous ten plus
MertensProductDiamondPintz and HTGeometry.CompactMonoidMeasureAlgebra.
No error named the new leaf. The global gate remains failing.

The independent projection-contraction conjecture is retired with
the exact square decomposition and native sharpness as its audited
positive survivor. The full joint covariance payment conjecture
remains open; this card does not retire Route RP.

## Corpus audit

Three deep searches used the literal covariance, cofactor projection,
and fixed-channel profile mechanisms. Query versions 1216168,
1216201, and 1216218; coverage versions 1216171, 1216204, and
1216219 respectively. The middle search reported partial output
because filter_and_judge returned malformed/incomplete JSON; its
available candidates were inspected. Other searches reported no
errors or unfinished sections. Semantic coverage was unavailable,
refresh remained incomplete, and compiler states were predominantly
pending/stale/unavailable; source claims were checked against files.
The new native theorem receives its own Lean audit.
