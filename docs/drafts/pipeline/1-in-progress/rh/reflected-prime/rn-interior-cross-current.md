# RN-P-7p: interior cross term of the canonical coordinate margin

Status: full global margin Q>0 and current J<0 are formalized and directly audited.
All 24 public theorem axiom audits contain only the standard logical baseline.
Certificate: P3 `theta/rn-global-canonical-current.md`.
The weighted-integral transfer is also formalized and audited; see P3
`theta/rn-global-confluent-coordinate-residual.md`. This working derivation
is complete. The active successor is `rn-center-schur-coordinate-row-flow.md`.

For 0<x<z, put a=p(x), b=p(z), u=c(x), v=c(z). The exact decomposition
of the canonical margin at t=x, y=z−x is

    Q=Q_base+y[b−a−p(y)]Q_cross,
    Q_base=(b²−a²)[x(a+b)+ya]−y(x+z)ab(u+v),
    Q_cross=b²−a²−(x+z)(bu−av).

Convexity of p makes the bracket strictly positive. The interior task here
is Q_cross>0, leaving Q_base and the full compensation explicit.

## Actual curvature mechanism

The corpus gives b_c=c''−4c>0 on the nonnegative ray. An initial attempt
to differentiate exp(−2t)(c'−2c) was wrong: its derivative is not b_c.
The correct current is exp(2t)(2c−c'), with derivative −exp(2t)b_c<0.
The actual first-atom formulas and scaled likelihood remainder imply

    S(2c−c')→24>0.

Indeed atom curvature is 4S+6S/q_a², its derivative is
8S−12S/q_a²−36S/q_a³, and q_a=S−3/2; the atom difference times S is
24(S/q_a)³→24. The likelihood errors times S vanish by the corpus's
fixed spectral gap estimates. Eventual positivity propagates through the
strictly decreasing current to every t≥0. Thus 0≤c'<2c and

    Q_c=cc''−c'²=c(c''−4c)+(2c−c')(2c+c')>0.

This proves global log-convexity of the actual curvature, not of an
arbitrary source satisfying only projective descent.

## From curvature to the interior cross term

Let M=pc+tpc'−tc². Then M(0)=0 and

    (M/c)'=pc'/c+tpQ_c/c²>0   (t>0).

Therefore the slope elasticity ρ(t)=tc/p has ρ'=M/p²>0. Also ρ>1,
since (tc−p)'=tc'>0. For fixed x>0 write n=ρ(x), R=p(z)/p(x), s=z/x.
Both p/t and ρ strictly increase, so R≥s≥1 and ρ(z)≥n. For

    F(z)=R−1/R−n(s−1/s),

F(x)=0 and

    F'(z)=ρ(z)(R+1/R)/z−n(s+1/s)/z>0  (z>x).

Here R+1/R≥s+1/s follows from
(R−s)(Rs−1)/(Rs)≥0. Finally

    Q_cross/(ab)=R−1/R−(x+z)[c(x)/a−c(z)/b]
                 ≥R−1/R−n(s−1/s)=F(z)>0.

Every inequality is on the actual source. This cross-term decomposition alone
does not determine the Q_base sign. The source-potential argument below now
proves that exact remaining compensation.

## RN-P-7q: global base sign from source-potential trapezoids

The base term now has a complete paper proof from the actual projective
reserve. Put U'=p and V=c c'−p c''>0. The derivative ratio c'/p strictly
decreases, so c is strictly concave as a function of U. Let

    K=3t c²−3pc−tpc'.

Then K(0)=0 and K'=tV+4c'(tc−p)>0. For g=t/p,

    dg/dU=−(tc−p)/p³,
    d²g/dU²=K/p⁵>0.

Thus g is strictly convex as a function of U. For 0<x<z and
A=U(z)−U(x)>0, the two strict trapezoid inequalities are

    p(z)²−p(x)²>A[c(x)+c(z)],
    A[x/p(x)+z/p(z)]>z²−x².

Their combination gives Q_base>0. The already paper-proved positive
cross term then gives the FULL Q>0 on t,y>0, hence J<0 globally.
Lean proves both trapezoids by differentiating the endpoint gaps and
applying strict derivative-ratio descent; no inverse U construction or
integration substitution is needed. The global leaf and its dependencies
passed targeted builds, direct Lean checks and axiom audits. The weighted
improper-integral transfer to B_* is now separately audited as well.
