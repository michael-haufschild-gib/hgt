# Exact greatest gaps for finite sets of prime flips

- **ID:** ACP-FINITE-PRIME-SECULAR-GAP
- **Stage:** 3-formalized
- **Type:** THEOREM; synthesis of audited finite-set leaves
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Statement:** Every finite prime set has an attained positive greatest hyperplane gap, determined by its explicit arithmetic secular function. Under proper inclusion, equal gaps occur only at the dyadic maximum.

## Exact classification

For a finite prime set F put `c_F=prod_(p in F)(p-1)/(p+1)`. The normalized
squared conductor weights are `w_F(m)=4^omega(m)/phi(m)` when every prime
factor of the positive conductor m belongs to F, and zero otherwise.
The actual limiting squared coefficients are `c_F^2 w_F(m)` and sum to one.
Write `D_m=log m+tameDifferent(m)` and

`Phi_F(s)=-1/s+sum_(m>=2) w_F(m)/(D_m-s)`.

For every real g,

`HasHyperplaneGap(omega_F,g) iff g<=2 log 2 and
  forall s, 0<s<g implies Phi_F(s)<=0`.

The greatest gap delta_F is attained, and
`0<(2 log 2)c_F^2<=delta_F<=2 log 2`. Every real gap is exactly a value
at most delta_F. The function Phi_F is continuous and strictly increasing
on (0,2 log 2). If delta_F is below the ceiling it is the unique zero there;
conversely every zero in that interval equals delta_F. If there is no
interior zero, delta_F equals the ceiling. No root above that ceiling is
needed for the exact classification. The empty set is included.

For F subset G, weights and secular functions increase and greatest gaps
decrease. For proper inclusion,

`delta_G<delta_F iff delta_G<2 log 2`.

Thus equality under proper inclusion is confined to the maximal plateau.

## Proof and formal sources

1. Finite-prime signed counts give the product mean c_F. Möbius inversion
   gives the conductor coefficients; local geometric series and the finite
   Euler product prove their exact support and unit squared mass.
   See `arithmetic-counting-finite-prime-spectral-mass.md`.
2. Mixed harmonic counts and Ramanujan quasimode projection identify every
   fixed conductor coefficient on an actual eigenline. See
   `arithmetic-counting-finite-prime-spectral-coordinates.md`.
3. Distinct conductor energies separate each finite packet. The unique
   ground count bounds every omitted reciprocal denominator below by a
   positive constant; unit mass exhausts the remainder. This proves full
   actual resolvent convergence to c_F^2 Phi_F. See
   `arithmetic-counting-finite-prime-resolvent-limit.md`.
4. The exact finite Hermitian reciprocal criterion gives necessity of the
   secular signs. For sufficiency, strict increase makes the reading at s
   negative by testing the assumed nonpositive sign at a slightly larger t.
   The epsilon in the gap definition includes the endpoint. A supremum
   argument proves attainment; supported weights give inclusion comparison.
   See `arithmetic-counting-finite-prime-gap-criterion.md` and
   `TheFinitePrimeSecularSignsDetermineTheGap.lean`.
5. A summable majorant uniform on each half-line below the ceiling proves
   continuity. An interior greatest gap can have neither a positive nor a
   negative reading, so it is a zero. Every newly flipped prime contributes
   a strictly positive reciprocal term. Two equal submaximal gaps would
   therefore give contradictory zero values. See
   `arithmetic-counting-finite-prime-root-rigidity.md` and
   `InteriorSecularRootsForceStrictPrimeGapDecrease.lean`.

The final two leaves have thirteen public endpoints, all with transitive
standard-axiom audits and successful canonical source checks. The preceding
three leaves have their own source and audit records. This synthesis adds
no new declarations; its verification evidence is in those five adjacent
`-audit.txt` files. No placeholder or unproved analytic premise occurs.

## Source audit and scope

[Borwein–Choi–Coons (2008)](https://arxiv.org/abs/0809.1691) study generalized
Liouville signs and their means. [Coppola–Ghidelli (2020)](https://arxiv.org/abs/2009.14121)
study multiplicative Ramanujan coefficients and finite Euler factorizations.
Those ingredients are established background. The contribution here is the
exact constrained gap of the actual prime matrices and its rigidity under
joint flips. This is a scoped source audit, not exhaustive literature novelty.

Qualitative cutoff-gap collapse is formalized in
`arithmetic-counting-prime-tail-gap-collapse.md`: above every fixed prime
cutoff, joint greatest gaps tend to zero. Individually maximal prime flips
can therefore have an arbitrarily small positive joint gap.
The first energy moment and quantitative decay rate remain in
`../2-fully-proven/arithmetic-counting-finite-prime-energy-moment.md`.
Pointwise convergence to a cofinite zero-gap gauge alone does not imply
convergence of finite-stage greatest gaps. Infinite-prime transfer needs
its own horizon-uniform estimate. Complete Weil positivity remains open.
