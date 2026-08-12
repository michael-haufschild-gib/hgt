# Mass-shifted projective arithmetic surplus (2026-08-12)

New module `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionProjectiveArithmeticSurplus.lean`, umbrella-wired.

## New law

For positive degree n, c=2n+1, current cumulative Jacobi flux F, dissipation D, admitted norm h, current alpha, and literal adaptive mixed/completed source S^sharp,

[
\mathfrak S=c(S^\sharp/h-\alpha F-2n\alpha^2)-F^2=cD-F^2>0.
]

This is source-first nonlinear work, not orientation or fixed reporting. Completing the alpha square proves drift-free coercivity

[
(6n-1)F^2<8n(2n+1)S^\sharp/h.
]

With U=F/c, reciprocal projective clock C=U^{-1}-y has exact derivative
[
C'=\mathfrak S/F^2>0
]
where F is nonzero. In normalized reciprocal-mass gauge, fixed-degree arcsine recession gives
[
\widehat{\mathfrak S}\to c^2/4,qquad
\widehat{\mathfrak S}/\widehat F^2\to1.
]

## Meaning

Absolute monic source collapse is norm collapse; source cannot vanish independently of projective flux. Every fixed-degree terminal chamber has asymptotically one unit of arithmetic projective work per mass. Generic coordinate dilation no longer kills the invariant. Remaining exact obstruction is cross-degree transport/diagonal shape control: pointwise positivity has no generic uniform rate near degenerate Jacobi shapes, and fixed-degree limits do not synchronize with cofinal terminal frontiers.

## Verification

Direct `lake env lean` passes. Targeted `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveArithmeticSurplus` passes (11788/11788). Eight capstone axiom audits report only `propext`, `Classical.choice`, `Quot.sound`. Forbidden scan and diff check clean. Full lint fails only unrelated concurrent umbrella reachability debt; new module is reachable.

Report equations (9.3.618)-(9.3.622). Stage3 card `mass-shifted-projective-arithmetic-surplus.md`.