# Moving-horizon Darboux/Cayley rigidity (2026-08-26)

## Falsification
The former finite-mass interpretation of fixed `u=1` was false. Birmingham–Mokhtari horizon equation gives `u_h=1+x_h`. The old fixed-radius results were renamed `FixedUnitRadius`; no false horizon API remains.

## Exact moving-horizon law
For `A=Q+2`,
`G_H(A,x)=6*x*(2+3*x)/(A+3*x)`.
For Xi reflected shifts `A=a(3-a)`, `B=(1-a)(2+a)`, its reflected defect is `(1-2a)` times a strictly positive susceptibility, hence vanishes iff `a=1/2`.

Darboux superpotential
`W(Q,s,x)=Q(Q+2)/6 + 3(s-x^2-x^3)/(Q+2+3x)`
is constant on moving horizon `s_h=x^2+x^3`. Existing fixed-scale derivative `partial_x W=-(B_S-B_V)/2` combines with `s_h'=2x+3x^2` to give exact projected shape-flux decomposition:
`-(B_S-B_V)/2 + s_h' * 3/(Q+2+3x)=0`.

Moving-horizon third mass jet:
`J_H(Q)=-324 Q/(Q+2)^3 = d4ThirdMassParityJet Q 1 + 108/(Q+2)^2`.
It is negative for physical `Q=1/4+xi^2`, positive for virtual `-2<Q<0`. Xi-reflected third-jet defect also vanishes iff line.

## Exact horizon Cayley S-matrix
New literal absorbed-horizon BM Darboux phase:
`S_H=(Q(Q+2)+12 i |A_H|^2 omega)/(Q(Q+2)-12 i |A_H|^2 omega)`.
On Xi mediator `Q in (-2,0)`, algebraic weight is negative, so `S_H` is regular and unitary. At nonzero amplitude/frequency, reflected phase equality holds iff `Re rho=1/2`. Frequency reversal gives exact inverse phase.

## Files
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskyThirdMassParityJet.lean`
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskyFiniteMassReflectionRigidity.lean`
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingDarbouxHorizonCayleyReflectionRigidity.lean`
- import added to `formal/GaloisForLFunctions/RHTower.lean`

All targeted modules compile. New theorem axiom audits show only `propext`, `Classical.choice`, `Quot.sound`. Scratch files removed. No docs/git touched.

## Open core
Need derive, from total gauge-fixed nonlinear Einstein/Teukolsky boundary dynamics, either:
1. coherent reflected horizon phases are equal, forcing RH via new theorem; or
2. discrepancy is exactly positive orthogonal-helicity/continuum flux.
Generic KMS/passivity cannot provide this. Nonlinear Einstein contact freedom changes total section value; causal or projected boundary structure must remove it.