# Coupled odd-four seam direction: obstruction and exact repair

Route TT, conjecture C61. Candidate: the literal coupled source with
canonical C3, direction eta(x)=168*q(x)-56, and one load
0<=C4<=10^13 is positive for every x>=0. This candidate fails at zero.
The coupled route and RH remain open.

## Exact source obstruction

Let Phi be the complete theta-cusp source, J_k its signed reflected
moments, H2 the positive leading odd plane determinant, D3 the negative
third odd seam determinant, D4 the fourth native seam determinant,
B the (2,3) cofactor, and G(0)=3*Phi(0)^2. The actual canonical C3 obeys

    C3*G(0)*H2 = -3*D3.

With eta(0)=168*pi-56 and C4=10^13 the corrected determinant is strictly
negative. A nonzero native coefficient vector makes the literal coupled
energy strictly negative. The same vector remains negative for every
C4<=10^13 since G(0)>0. This excludes the whole coefficient interval
proved admissible on the adverse ray; it does not exclude larger loads
or different coupled directions.

## Dependency-closed paper proof

The actual modular seam scale X lies in [191/10,96/5], and pi lies in
[157/50,63/20]. Source jets through order fourteen identify all seven
odd signed moments with exact mass-normalized polynomials. The leading
head H2 is positive. The canonical coefficient is retained exactly.
Jacobi's identity and the rank-one determinant update give

    H2*Dcanonical(t,C4)
      = -2*H2*(D4+C4*G*D3)-3*(D3*t+B)^2.

For t=168*q-56 and C4=10^13 the cleared expression is a polynomial of
homogeneous degree32 in the seam scale coordinates. Each of its three
quadratic Bernstein controls in q has strictly negative coefficients
on X=(191*u+192*v)/10, b=u+v with u,v>=0,u+v>0. The actual point has b=1.
Thus its sign is strictly negative throughout the full source enclosure.
No numerical source evaluation or truncation premise is used.

The literal coupled matrix is Hermitian. If all coefficient-vector
energies were nonnegative its determinant would be nonnegative, a
contradiction. Monotonicity in C4 at the seam gives the common vector.

## Strongest positive survivor

The identity above gives the exact source-selected direction penalty.
The unique zero-penalty direction is

    t_opt=-B/D3.

It maximizes the determinant. At this direction the determinant is
positive exactly when D4+C4*G*D3<0. For the SAME C4=10^13, a strictly
positive homogeneous certificate proves that inequality over the
actual seam scale interval. The first three leading minors are already
positive: native first/second minors, and corrected third minor -2D3.
Exact four-square completion therefore proves the entire optimal-direction
seam matrix positive definite. The failure is a direction defect,
not an impossibility of repair at this load.

## Lean status

Production leaves are wired into RHTower:

- ThetaCuspCoupledOddSeamDirection: actual source square penalty,
  sharp determinant criterion, optimality, strict-form criterion.
- ThetaCuspCoupledOddSeamModel: canonical homogeneous source model.
- ThetaCuspCoupledOddSeamSigns: original-direction negative controls
  and optimal-direction positive reserve.
- ThetaCuspCoupledOddSeamObstruction: actual determinant/energy
  obstruction, common negative vector, optimal-direction PosDef.

All four production --old leaf builds and final direct lake env lean
leaf audits passed. Scratch source obstruction/energy and optimal
polynomial audits use propext, Classical.choice, Quot.sound only.
Current-production axiom reports for every capstone show only those
same three standard axioms (tt_c63_gap_derivative.audit.log). That
combined run exited1 solely on the unfinished C63 derivative proof;
all C61/C62 leaf direct audits exited0. Index refresh passed. Current lint reports13 unrelated umbrella
omissions, with no C61/C62 module errors. Superseded owned C61/C62 scratch sources
and .olean files were removed.

## Surviving hard problem

C62 on the [working card](../1-in-progress/tt-actual-odd-border-primitive.md)
constructs a source-dependent direction from

    C3*x*Phi^2*H2*eta' = D3*eta+B.

This cancels the complete Schur residual and forces eta(0)=t_opt.
The actual continuous regular solution and exact residual cancellation
are constructed; the source-transport production direct audit passed.
The exact determinant split, determinant-sign equivalence and positive
initial gap also passed their production direct audit and axiom reports. Positive scalar Schur gap across
the compact region, controlled join to the proved q>=5 direction, exact
flux integration, and all-rank closure remain open. No source-sign
hypothesis is supplied.
