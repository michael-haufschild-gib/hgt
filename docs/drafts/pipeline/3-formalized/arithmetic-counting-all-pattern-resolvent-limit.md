# Full actual resolvent for every prime pattern

- **ID:** ACP-ALL-PATTERN-RESOLVENT-LIMIT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Lean target:** EveryPrimePatternHasItsFullArithmeticResolvent.lean
- **Input:** ../3-formalized/arithmetic-counting-all-pattern-bounded-spectral-mass.md

## Exact endpoints

For every prime pattern P and 0<s<g0=2 log 2, the full
actual scalar reciprocal reading

R_P(N,s)=sum_i |<v_(P,N),e_(i,N)>|^2/(E_(i,N)-gamma-s)

converges along horizons N+1 to

F_P(s)=sum_(m>=1)a_P(m)^2/(E_m-gamma-s).

The two endpoints are absolute summability of this normalized conductor
series and convergence of the complete actual finite reading to it. They
cover every P without a positive-density or summability assumption.

## Absolute summability

The coefficient mass theorem gives sum_(m>=0)a_P(m)^2 equal to zero or
one. The m=0 coefficient is zero. For every m>=2,
E_m-gamma-s>=g0-s>0. Thus the absolute positive-conductor series is
bounded termwise by a_P(m)^2/(g0-s), a summable series. The ground is
one finite term with denominator -s. This proves absolute summability.

## Common denominator separation

Use relative actual energies D_(i,N)=E_(i,N)-gamma and choose the actual
ground index j_0(N) supplied by the conductor-coordinate theorem. Its
energy tends to zero. Put eta=(g0-s)/2>0. Since 0<s+eta<g0, the existing
exact spectral count gives exactly one actual eigenline below
gamma+s+eta eventually. The selected ground is eventually there; every
other index therefore satisfies D_(i,N)-s>=eta.

The selected ground also eventually has D_(j_0,N)<s/2. Consequently its
denominator has absolute value greater than s/2. With
rho=min(s/2,eta)>0, every actual denominator has absolute value at least
rho eventually. No reciprocal convention at a zero denominator is used
in either limiting argument. Parseval and the actual horizon norm give
sum_i |<v_(P,N+1),e_(i,N+1)>|^2=1 for every N.

## Positive density: unit packets exhaust the resolvent

At c_P>0, the normalized conductor mass is one. Choose the actual
eigenline sequences for every positive conductor. Distinct arithmetic
energies imply eventual distinctness on every finite conductor packet;
the squared difference of each pair of energy sequences has a strictly
positive limit. Each selected reciprocal term converges because its
limiting denominator is nonzero.

Take the packet m=1,...,K+1, which contains the ground. Its actual
reciprocal sum lies below the full sum, since all omitted denominators
are positive. The difference is at most the omitted squared mass divided
by eta. For fixed K, the packet mass and reading converge termwise.
Then K tends to infinity: the packet mass tends to one and its reciprocal
sum tends to F_P(s). These lower and upper bounds have the same limit.
This is precisely the already proved generic unit-mass packet lemma;
every one of its hypotheses is supplied by the present counted data.

## Zero density: escape and reciprocal decay

At c_P=0, every a_P(m) is zero, hence F_P(s)=0. The bounded spectral-mass
classification proves vanishing mass below every fixed relative threshold
T, including nonregular ones. For T>s and sufficiently large N, the
triangle inequality and the denominator separation give

|R_P(N+1,s)| <= M(P,N+1,gamma+T)/rho + 1/(T-s).

Indeed each term below T is bounded by its squared coefficient divided
by rho. Every term above T has denominator at least T-s; its total
squared mass is at most one. For an explicit epsilon proof, choose
T=s+2/epsilon. The second term equals epsilon/2 and the first tends to
zero, so the reading is eventually smaller than epsilon in absolute
value. This proves the zero-density case without pretending that the
zero limiting coefficient profile has unit mass.

## Dependency and novelty audit

The finite-prime full-resolvent source and generic packet proof were read.
The all-pattern coordinate and zero/unit mass leaves are already checked.
The bounded spectral-mass leaf has passed its scratch, transitive axiom
and canonical installed-source audits. A corpus search for escape
of reciprocal spectral mass found no matching unconditional actual-prime
endpoint. No literature-wide priority claim is made.

The new contribution is the complete actual spectral transfer for arbitrary
prime support, with separate proofs on both sides of the Euler-density
boundary. It establishes a full finite-matrix reading, not merely a formal
arithmetic series or selected-mode limit.

## Boundary

An absolute resolvent limit of zero does not determine its eventual sign,
so it does not determine the greatest gap at zero Euler density. The
relative ground/positive-tail balance remains open. Divergence of the
unnormalized conductor mass alone does not establish divergence after
energy weighting. Whether zero-density patterns can retain a positive gap
is a separate question, not a conclusion here.

Positive-density secular normalization and exact gap classification should
follow only after the actual full-resolvent transfer. No complete Weil
positivity producer or RH conclusion is claimed.

## Immediate formalization

The matching two-endpoint draft is
/tmp/acp-all-pattern-resolvent-limit-check.lean. It contains the full
epsilon proof of reciprocal decay under mass escape and the actual
denominator/counting application. It imports the new bounded-mass leaf
and the existing finite-prime full-resolvent leaf. The latter olean exists
and must be preserved; the former passed its first required olean in
session 84622, without rebuilding any existing artifact.

- [x] Complete paper proof for every prime pattern.
- [x] Immediate full Lean draft with matching endpoints.
- [x] Scratch and transitive axiom audit.
- [x] Canonical source check, umbrella and durable evidence.

## Lean endpoints and audit

EveryPrimePatternHasItsFullArithmeticResolvent.lean proves
summable_primeSetConductorResolvent and tendsto_primeSetFiniteResolvent.
Scratch 37381 and canonical 79210 exited zero without diagnostics. Both
transitive audits use only propext, Classical.choice and Quot.sound. The
adjacent audit preserves commands, source SHA256 and actual output.
