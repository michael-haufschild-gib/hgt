# Arithmetic square payment for the complete Haar prime source

- **ID:** acs-haar-prime-ground-state
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** ACS: full-source effectivity → Hodge index → RH.
- **Parent:** [signed Haar head payment](../1-in-progress/acs-low-haar-head-payment.md)
- **Target:** Preserve the exact proper-divisor charge and a nonnegative
  square remainder in the actual signed Haar prime form, including index one.

## Source and identity

Write n_a=2a+1 and M_a=haarMass(a). The checked incidence formula retains
exactly the edges n_a m=n_b, with a,b in [1,X] and 2≤m≤2X+1.
For these actual edges define

`Q_X(d)=sum Lambda(m) M_b (d_a/sqrt(m)-d_b)^2`,

`O_X(a)=sum_(m,b: n_a*m=n_b) Lambda(m) M_b/m`.

The exact identity is

`haarPrimeEnergy(d,X)+Q_X(d)
 =sum_a [(log(n_a)-Lambda(n_a))*M_a+O_X(a)]*d_a^2`.

The missing odd root n=1 removes the full Lambda(n_a) term from the
incoming divisor identity. This subtraction and the edge squares must not
be discarded when comparing with the actual Gamma and polar terms.

## Dependency-closed paper proof [PROVED HERE]

Fix b in [1,X]. Each incoming multiplier m is a divisor of n_b, satisfies
m≥2, and has odd quotient n_b/m≥3. Conversely, every divisor m of n_b with
2≤m<n_b has odd quotient k≥3. The unique index a=(k−1)/2 lies in [1,b]
and satisfies n_a*m=n_b. Also m≤n_b≤2X+1. Thus every proper divisor except
one occurs exactly once. Since Lambda(1)=0 and the checked von Mangoldt
divisor identity is `sum_(m|n_b) Lambda(m)=log(n_b)`, the incoming coefficient
is exactly `M_b*(log(n_b)-Lambda(n_b))`.

On each edge, expand

`Lambda(m)*M_b*(d_a/sqrt(m)-d_b)^2
 =Lambda(m)*M_b*d_a^2/m + Lambda(m)*M_b*d_b^2
  -2*Lambda(m)*M_b*d_a*d_b/sqrt(m)`.

Here m≥2, so sqrt(m)^2=m and every division is legitimate. Summing the
three terms gives respectively O_X, the exact incoming coefficient, and
the original Haar prime energy from `haarPrimeEnergy_eq`. This proves the
identity for arbitrary signed real coefficients, with no discarded edge.
Every square has nonnegative coefficient, so Q_X≥0.

For a fixed a,m there is at most one b. The checked mass contraction is
`m*M_b≤2*M_a` on an actual edge. Therefore

`O_X(a)≤2*M_a*sum_(m=2..2X+1) Lambda(m)/m^2`.

This keeps the summable exponent two in the outgoing charge, while the
incoming charge is the exact proper-divisor logarithm.

The square remainder vanishes exactly when `d_b=d_a/sqrt(m)` on each
edge with Lambda(m)>0. Equivalently the rescaled coefficients
`sqrt(2a+1)*d_a` agree along every such edge. This identifies the actual
arithmetic alignment rather than replacing the signed matrix by absolute
row sums.

Restoring the missing-root term gives the source-derived defect

`D_X(d)=sum_a [log(n_a)*M_a+O_X(a)]*d_a^2−haarPrimeEnergy(d,X)
        =Q_X(d)+sum_a Lambda(n_a)*M_a*d_a^2`.

This defect is positive definite at every finite horizon, including the
whole low-index head. To prove its zero kernel, first every nonnegative
summand must vanish. Induct on b. Choose a prime p dividing n_b. If p=n_b,
the root charge has strictly positive coefficient log(p) M_b and forces
d_b=0. Otherwise n_b/p is an odd integer at least three, giving an edge
from a<b. Induction gives d_a=0, and its edge square with positive
coefficient log(p) M_b forces d_b=0. Conversely all coefficients zero
annihilate every term. Hence D_X(d)>0 for every nonzero coefficient vector.

The outgoing charge is independent of coefficient signs and has the
inverse-square budget above. This is a positive arithmetic source payment
at every horizon, with no removed head or assumed spectral sign. It is
not the full Weil payment: its exact diagonal requires a joint comparison
with the original Gamma and polar terms.

### Uniform floor on the entire signed coefficient space

For each b choose a prime p_b dividing n_b, and write n_b=(2a_b+1)p_b.
Then 0≤a_b<b. Set `T_b=d_(a_b)/sqrt(p_b)` when a_b≥1 and T_b=0 when
a_b=0. The selected prime edge or root term belongs to D_X exactly once,
because its receiving index is b. Hence

`D_X(d) ≥ log(2) sum_b M_b*(d_b−T_b)^2`.

Fix a≥1. Distinct selected children have distinct multipliers p_b, all
odd and at least three. The actual mass contraction therefore gives

`sum_(b:a_b=a) M_b/p_b
 ≤ 2 M_a sum_(k≥1) 1/(2k+1)^2 ≤ M_a/2`.

For the last inequality, `(2k+1)^2≥4k(k+1)` and
`sum_(k=1..N) 1/(k(k+1))=1−1/(N+1)≤1`; no analytic estimate is assumed.
Consequently `sum_b M_b*T_b^2≤(1/2)sum_b M_b*d_b^2`.
The scalar identity

`3(d−T)^2+(3/2)T^2−d^2=(1/2)(2d−3T)^2≥0`

now yields `sum_b M_b*d_b^2≤12 sum_b M_b*(d_b−T_b)^2`. Thus

`D_X(d) ≥ (log(2)/12) sum_b M_b*d_b^2`,

uniformly in horizon and with every low-index coefficient retained. This
is a uniform arithmetic floor, not merely finite-dimensional strict
positivity. The floor is formalized in
`TheHaarPrimeDefectHasAUniformMassFloor.lean`.

## Scope and formalization

Both exact modules passed clean direct `lake --old env lean` checks:

- `ArithmeticCastelnuovoSeveri/TheHaarPrimeSourceRetainsItsDivisorSquares.lean`
  proves `haarPrime_incoming_divisor_charge`,
  `haarPrimeEnergy_add_divisorSquares`, `haarPrimeLogDefect_eq`,
  `haarPrimeDivisorSquares_eq_zero_iff`, `haarPrimeLogDefect_eq_zero_iff`,
  `haarPrimeLogDefect_pos_iff`, and `haarPrimeOutgoingCharge_le`.
- `ArithmeticCastelnuovoSeveri/TheHaarPrimeDefectHasAUniformMassFloor.lean`
  proves `haarPrimeLogDefect_ge_mass`, retaining every signed coefficient
  with the common floor log(2)/12, independently of horizon.

The first module's olean was built only for the importing second module;
the second was built only for the importing pole-payment module.
Both are wired into the owning umbrella; the umbrella was not compiled.
No assertion of full Weil positivity follows from this identity alone.
The signed Gamma–prime–pole comparison remains the parent target; the
identity retains a positive arithmetic remainder available for that joint
comparison.

The [original pole payment](acs-haar-prime-defect-pays-poles.md) now proves
`D_X+P≥D_X/8≥mass/144` on every signed section, retaining the whole head.
The actual Gamma/central-mass comparison with the exact diagonal remains open.

No web search, novelty checks, numerical experiments, or axiom checks.

## Log

- 2026-10-29 — Exact divisor squares and uniform mass floor formalized;
  both direct module checks passed.
