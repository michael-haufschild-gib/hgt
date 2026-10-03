# RN: canonical coordinate-current boundary at every positive spacing

Status: formalized and audited 2026-10-02 in
`formal/GaloisForLFunctions/RHTower/ThetaCoordinateCanonicalBoundary.lean`.

Write p for the literal theta decay slope, c=p', and q=c(0). For t,y>0,
define

    C(t,y)=t[p(t+y)−p(t)]/y−p(t),
    λ(t,y)=[p(t+y)−p(y)]/[p(t)+p(t+y)],
    J(t,y)=∂y C−λ∂t C−(∂t λ)C.

The negative sign on the last term is essential. This is the literal
differential current; its weighted improper-integral application has not
been established by this leaf.

## Exact reduction and boundary proof

For a=p(t), b=p(t+y), r=p(y), u=c(t), v=c(t+y), put

    Q=(b²−a²)[t(a+b)+y(b−r)]
       −y(2t+y)[a(a+r)v+b(b−r)u].

Lean proves `J=−Q/[y²(a+b)²]`. At t=0, Q=0 and

    ∂t Q(0,y)=p(y)E_y,
    E_y=p(y)²+y p(y)c(y)−2q y²c(y)>0.

The global endpoint sign follows from the previously proved source chord
reserve. With A=c(y)+2q, B=q y(2c(y)+q), F=p(y)A−B>0,

    A²E_y=F[A p(y)+B+y c(y)A]+q²y²(c(y)−q)²>0.

All factors in the first term are positive. The derivative limit therefore
gives the actual theorem, with no unproved source-sign assumption:

    ∀ y>0, ∀ᶠ t in 𝓝[>] 0, J(t,y)<0.

The neighborhood may depend on y. This does not assert J<0 on the whole
positive quadrant or positivity of the global coordinate residual.

## Validation

Targeted `lake --old build` and final direct `lake env lean` passed without
leaf diagnostics. All six public theorem axiom audits report only propext,
Classical.choice and Quot.sound. The leaf is wired into RHTower. No full
or umbrella build ran. Formal lint reports twelve unrelated unreachable
modules, listed in the working log; no violation in this leaf.

## Remaining hard RN obligations

Prove or falsify the interior margin Q>0, or directly prove its required
weighted integral sign. Audit the parameter derivative and vanishing
canonical flux before inferring global B_*(y)>0. Schur compensation and
propagation, arbitrary rank, and the retained arithmetic RH transfer remain
separate open problems.
