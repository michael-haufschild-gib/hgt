# Rank-one cofactor moduli are Archimedean

- **ID:** rank-one-cofactor-moduli-are-archimedean
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Q-III](../1-in-progress/q-iii-escape-state-classification.md)
- **Statement:** Every one-dimensional actual cofactor module has either the
  augmentation character or cofactor character magnitudes `n^(-s)` for one
  real s>=1/2.

## Lead

In one complex dimension the commuting unital action is scalar. With the
unit cyclic vector, K(n,n)=|chi(n)|^2 and chi is completely multiplicative.
The new actual energy-ratio invariant makes r(n)=n*|chi(n)|^2 nonnegative,
completely multiplicative and nonincreasing in the ordinary integer order.
The elementary classification is: either r(n)=0 for all n>=2,
or r(n)=n^(-alpha) for alpha>=0. Comparison of integer powers through their
logarithms forces the latter form. If any r(n)=0, monotonicity and
multiplicativity force r(2)=0 and then every positive integer above one.

The character is real and its signs are multiplicative. The theorem does
not select those signs, put the character on the Kronecker curve, or identify s with
a zeta real part. A global polynomial energy upper bound alone does not
justify a bound on local subsequence escape exponents; do not add one.

## Gates

- [x] Corpus search for the monotone multiplicative classification.
- [x] Exact scalar extraction from actual rank one on paper.
- [x] Dependency-closed paper proof.
- [x] Lean verification and transitive axioms.

## Dependency-closed paper proof

Let xi=v_1 be the unit cyclic vector. In complex dimension one each v_p is
z_p xi. Pairing with xi gives z_p=K(p,1), hence z_p is real. Applying D_p to
v_q gives z_(pq)=z_p z_q. Thus K(p,q)=z_p z_q and
r(p)=p*z_p^2 is a nonnegative multiplicative function with r(1)=1.
The actual contracted-energy identity makes r antitone in the ordinary
integer order.

If r(2)=0, then r(p)=0 for every p>=2, giving augmentation. Otherwise r(2)>0.
For every p, choose k with p<=2^k. Antitonicity gives
r(p)>=r(2)^k>0. Define g(p)=-log r(p). It is nonnegative, monotone, and
logarithm-additive: g(pq)=g(p)+g(q).

For positive integers n,m with m>1, compare n^k with
m^ceil(k*log(n)/log(m)). Monotonicity and logarithm-additivity imply

    k*g(n) <= k*g(m)*log(n)/log(m) + g(m).

If g(n)>g(m)*log(n)/log(m), choose k larger than g(m) divided by that
positive gap; contradiction. Interchanging n and m gives equality. Taking
m=2 yields g(n)=alpha*log(n), alpha=g(2)/log(2)>=0, including n=1.
Therefore r(n)=n^(-alpha), z_n^2=n^(-(alpha+1)), and
|z_n|=n^(-s) for s=(alpha+1)/2>=1/2.

This also proves reality of the character and the product formula for the
entire rank-one Gram. In the positive branch each sign z_n/|z_n| lies in
{−1,1} and is multiplicative. The argument does not select those signs.

## Current verification status

The generic power classification and actual rank-one character, Gram product,
and magnitude classification passed `/tmp/qiii-diagonal-energy-retry-check.log`
with standard axioms. Their canonical leaves are installed and wired:
`HTGeometry/MonotoneMultiplicativeProfilesArePowers` and
`ArithmeticDefectRigidity/RankOneCofactorMagnitudesArePowers`. Both final
canonical source audits passed in session `90975`, with standard axioms.
`ArithmeticDefectRigidity/RankOneCofactorSignsAreMultiplicative` proves
`ActualCofactorLimit.rankOneCharacter_eq_augmentation_or_signed_rpow`:
the nonaugmentation branch has a multiplicative sign η valued in {−1,1},
with χ(p)=η(p)*p^(-s). Scratch check `45147` and canonical source-only audit
`87736` passed. The canonical leaf is wired into the programme umbrella;
its transitive axioms are only `propext`, `Classical.choice`, `Quot.sound`.
Final audit output: `/tmp/qiii-rank-one-sign-canonical-final.log`.
