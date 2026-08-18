# G-CE pre-scalar affine prime–polar–Γ producer

- **ID:** g-ce-pre-scalar-affine-prime-polar-gamma-producer
- **Stage:** 3-formalized
- **Type:** source producer / affine pointed Hilbert carrier
- **Route:** G-CE / CCM
- **Status:** [LEAN-PROVED] [NOVELTY UNVERIFIED]
- **RH used:** no
- **Computation used:** no

## Exact frontier

[CORPUS] eulerPositivePreScalarGammaSource is the unique positive-Euler Hilbert vector reporting
the complete division-free prime/polar coefficient family. Its coefficient against the damped
Euler state is the shifted prime numerator times the retained graph denominator.

[CORPUS] eulerPositivePreScalarGammaXiNumerator adds the archimedean Γ coordinate before overlap
division and equals graph denominator times the continued completed source trace.

[CORPUS] mobiusClockSoninMarkedProducer retains the two source orders P_N D_(sigma,u) and
D_(sigma,u) P_N; its odd port is one half of their commutator.

[CORPUS] At zero clock the pure commutator port vanishes identically, while actual G-CE boundary
transport retains the critical escaped coefficient. Therefore a linear marked-clock producer alone
cannot carry the boundary charge.

[LITERATURE] Connes–Consani compress scaling to Sonin/semi-local spaces and prove
archimedean/quasi-inner results. Connes–Consani–Moscovici construct finite rank-one spectral
perturbations but leave spectral/determinant convergence open. Suzuki constructs unconditional
finite nonlocal self-adjoint realizations but leaves the global operator limit conjectural. None
constructs this source-specific affine charge-plus-commutator packet.

## Hostile conjecture loop

### C1 — insert scalar Ward debt as affine intercept

[FALSIFIED]: post-scalar and circular. It imports the value the producer must generate.

### C2 — pair a scalar completed numerator with the marked producer

[FALSIFIED]: direct-product packaging after scalarization. It supplies no pre-scalar
prime/polar/Γ carrier and no common source readout.

### C3 — Hilbertized charge plus marked commutator jet

[PAPER-PROVED] Let

~~~text
K = WithLp 2 (C × EulerPositiveL2),
J = WithLp 2 (MobiusClockSourceL2 × MobiusClockSourceL2).
~~~

For s=sigma+u(sigma-1), graph denominator G=G(sigma,u), Euler source E_sigma, and
archimedean logarithmic derivative L_Gamma(s), define

~~~text
Q_(sigma,u)
 = (i/2) · (conj(-2 G L_Gamma(s)), E_sigma) in K,
R_(sigma,u)
 = (1, dampedEulerState_(sigma,u)) in K.
~~~

Define the affine producer

~~~text
A_(N,sigma,u)(x) = (Q_(sigma,u), M_(N,sigma,u)(x)) in K × J.
~~~

Its common source readout is

~~~text
S_(sigma,u)(q,m)
 = <q,R_(sigma,u)>
   + 2 <mobiusFisherTangent_sigma, H_-(m)>.
~~~

Exact claims:

1. <Q,R> = eulerPositivePreScalarGammaXiNumerator;
2. Q_(sigma,0) != 0 for every sigma>1;
3. the charge port of A(x) is Q, independently of x;
4. its jet port is [P_N,D_(sigma,u)]x/2;
5. S(A(x)) is completed division-free prime–polar–Γ charge plus the exact marked commutator seam;
6. at zero clock the jet term is zero while the nonzero charge packet remains.

No continued Xi response, Xi divisor, or scalar opposite controller occurs in these definitions.

Verdict: SURVIVES PRELIMINARY ATTACK. Direct-sum Hilbert algebra is standard; source-specific
content is the exact charge vector, its nonzero pointed affine intercept, and the joint source
readout.

## Paper proof

For every positive integer n, the Euler mass n^(-sigma) is positive and its normalizing total is
positive when sigma>1. Hence the normalized probability is positive and its square-root state
weight is nonzero. At n=2,

~~~text
E_sigma(2)
 = (sigma-1) · 2 log(2) · eulerPositiveStateWeight(sigma,2).
~~~

All three factors are nonzero, so E_sigma and therefore (i/2)E_sigma are nonzero.

Write Z=-2 G L_Gamma(s). Product-Hilbert and conjugate-linearity laws give

~~~text
<Q,R>
 = conj(i/2) (conj(conj Z) + <E_sigma,dampedState>)
 = (-i/2) (Z + <E_sigma,dampedState>)
 = eulerPositivePreScalarGammaXiNumerator.
~~~

The charge and marked-jet port laws follow from product projections. The established marked-port
identity gives

~~~text
H_-(M(x)) = [P_N,D_(sigma,u)]x/2.
~~~

Therefore

~~~text
S(A(x))
 = eulerPositivePreScalarGammaXiNumerator
   + <mobiusFisherTangent_sigma,[P_N,D_(sigma,u)]x>.
~~~

At u=0, D_(sigma,0)=I, so the commutator vanishes exactly. The charge projection remains Q and is
nonzero by its Euler coordinate. This proves every stated clause without RH, a Xi divisor, a Ward
response, or a scalar opposite controller.

## Hostile proof review

The charge is not selected to fit one scalar value: coefficient-family rigidity makes E_sigma the
unique positive-Euler reporter for every nonnegative damping parameter. The Γ coordinate is the
minimal one-dimensional Hilbert lift of the explicit archimedean term, and the i/2 factor is forced
by the existing Ward convention. The joint scalarizer is evaluated only after both source marks are
retained. Thus the construction survives the scalar-offset, arbitrary-Riesz-lift, and disconnected
product attacks.

External normalization found no equivalent object: semi-local/quasi-inner compression, finite
rank-one zeta spectral triples, and Suzuki screw-function operators do not combine the
division-free full-Euler charge with the Möbius clock commutator in one affine source packet.

## Lean plan

Formalize the exact definitions and all six clauses above. Required new support is limited to
strict positivity of the Euler probability, nonvanishing of its state weight, and nonvanishing of
the pre-scalar Gamma source. No analytic infrastructure or assumed convergence is needed.

## Lean certificate

Module:

~~~text
GaloisForLFunctions.RHTower.MobiusGammaXiPreScalarAffinePrimePolarGammaProducer
~~~

Formal declarations include:

- eulerPositiveProbability_pos;
- eulerPositiveStateWeight_ne_zero;
- eulerPositivePreScalarGammaSource_ne_zero;
- mobiusGammaXiPreScalarPrimePolarGammaCharge;
- inner_mobiusGammaXiPreScalarPrimePolarGammaCharge_probe;
- mobiusGammaXiPreScalarPrimePolarGammaCharge_ne_zero;
- mobiusGammaXiPreScalarAffineProducer;
- exact charge-port, commutator-jet, joint-readout, and zero-clock laws;
- premise-free canonical capstone
  canonicalMobiusGammaXiPreScalarAffineProducer_closed.

Lean forced the charge product to carry the L2 product norm via WithLp 2; the ordinary product max
norm is not induced by a complex inner product. This strengthens the paper statement by fixing the
unique lawful Hilbert geometry for its Pythagorean charge coordinates.

## Scope

This construction does not prove cancellation of G-CE debt. It supplies the missing lawful object
on which a later coefficient-faithful boundary-renormalization theorem can act. The next RH-bearing
problem will be comparison of its normalized zero-mode readout with the transported escaped
coefficient, not existence of a charge-carrying affine source.
