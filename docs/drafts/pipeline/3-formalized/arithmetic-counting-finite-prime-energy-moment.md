# The first conductor moment bounds every finite-prime gap

- **ID:** ACP-FINITE-PRIME-ENERGY-MOMENT
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** arithmetic-counting-finite-prime-secular-gap.md
- **Lean:** `FinitePrimeConductorMomentsBoundTheGreatestGap.lean`
- **Audit:** `arithmetic-counting-finite-prime-energy-moment-audit.txt`

## Exact statement

For every finite prime set F, the counted probability weights satisfy

`sum_m a_F(m)^2 D_m = M_F = sum_(p in F) 4p log p/(p^2-1)`.

For nonempty F, `0<c_F<1` and the attained greatest gap obeys

`delta_F <= c_F^2/(1-c_F^2) * M_F`.

Here D_m is the conductor energy above the ground, and c_F is the harmonic
density. The identity includes the empty set. The upper bound complements
the previously proved lower bound `g0*c_F^2<=delta_F`.

## Arithmetic moment proof

Write D_m=log m+tameDifferent(m) and w_m=b_F(m)^2/phi(m). The dual number
`u_m=w_m+epsilon*w_m D_m` is multiplicative on coprime positive inputs,
since both energy terms are additive there and epsilon^2=0. At conductor
one it equals one. For p in F its local mass and moment are

`L_p=1+4p/(p-1)^2`,
`M_p=4p(p+1) log p/(p-1)^3`.

The geometric first-moment series proves summability of both components;
the L1 norm makes the dual local series norm-summable. The finite Euler
product therefore sums all supported conductors to the product of
`L_p+epsilon M_p`. Its second component is
`(prod L_p)*sum(M_p/L_p)`. The identities

`c_F^2 prod L_p=1`,
`M_p/L_p=4p log p/(p^2-1)`

give the claimed mean energy. Off-support weights vanish, so extending the
supported sum to all natural conductors adds nothing.

## Gap bound proof

For nonempty F, one density factor lies strictly below one and all factors
are positive and at most one. Thus A=1-c_F^2>0. Fix 0<s<delta_F<=g0 and,
for conductors m>=2, put x_m=a_F(m)^2 and d_m=D_m-s>0. The proved mass,
moment and full secular identities give

`sum x_m=A`,
`sum x_m d_m=M_F-s A`,
`R_s=sum x_m/d_m=c_F^2(Phi_F(s)+1/s)<=c_F^2/s`.

Finite weighted Cauchy-Schwarz followed by convergence of all three partial
sums gives `A^2<=R_s(M_F-s A)`. The second factor is nonnegative. Consequently
`A^2<=(c_F^2/s)(M_F-s A)`. Multiplication by s>0 and A+c_F^2=1 yield
`s A<=c_F^2 M_F`. Letting s increase to delta_F proves the gap bound,
including a maximal gap. No convergence of the full arithmetic vector's
energy is assumed.

## Lean closure and scope

The three audited public endpoints are
`hasSum_finiteFlipConductorEnergy`, `finiteFlipHarmonicDensity_lt_one`, and
`finiteFlipGreatestGap_le_energyMoment`. Scratch and canonical source checks
passed without diagnostics; all transitive axiom lists contain only
`propext`, `Classical.choice`, and `Quot.sound`. Exact commands, source hash
and actual output are retained in the adjacent audit.

This is a quantitative statement for finite prime sets. It asserts neither
complete-source positivity nor transfer to arbitrary infinite gauges.
The prime-cutoff rate is developed separately in
`arithmetic-counting-prime-tail-gap-rate.md`.

- [x] Dependency-complete arithmetic moment and gap-bound paper proof.
- [x] Exact Lean endpoints and transitive axiom audit.
- [x] Canonical installed-source check, umbrella, durable evidence, cleanup.
