# Inherited odd diagonal extension: obstruction and sharp positive capacity

Route TT. Closed candidate: extend the canonical globally positive
odd-three block to odd-four by leaving its correction on the old
diagonal and adding a nonnegative scalar correction on the new diagonal.
RH and general matrix-flux positivity remain open.

## Source statement

Write q(x)=pi*exp(2x), J_k(x)=(-1)^k*Phi_reflected^(2k)(x),
G(x)=3*Phi(x)^2+2*x*Phi(x)*Phi'(x), and let C3 be the source-selected
canonical odd compensation coefficient. Its existing unconditional
bounds are 10^9<C3<3*10^9.

There is no C4>=0 for which

    [J_(i+j+1)(x)]_(0<=i,j<4)
      + C3*G(x)*e2*e2^T + C4*G(x)*e3*e3^T

is positive semidefinite for every x>=0. The explicit obstruction is

    x7=log(7/pi)/2,
    c=(107472/7,-2737/10,1,-1/1120).

For E7=c^T*[J_(i+j+1)(x7)]*c, the complete source satisfies

    0<E7,       G(x7)<0,       E7+C3*G(x7)<0.

Every additional C4>=0 decreases this quadratic further.

## Dependency-closed paper proof

All four ordered pairs of the first two atoms are retained in the
exact radial recurrence. Their energy lies strictly between
20,000,000*f1(x7)^2 and 4,000,000,000*f1(x7)^2. The complete remaining
likelihood source uses the all-order affine derivative estimate,
combined with the Gaussian jet recurrence through order fourteen.
Leibniz retains both mixed terms and the tail square; its contraction
with c bounds the entire omitted-source energy by 10,000,000*f1(x7)^2.

The source likelihood derivative is nonpositive. At q=7 the first-atom
logarithmic slope equals -197/22, so Phi'<=-(197/22)*Phi. Exact
exponential bounds give x7>=2/5, and Phi>=f1>0. Hence
G(x7)<=-(229/55)*f1(x7)^2. The canonical coefficient's lower bound
now makes the full corrected energy negative. No numerical source
evaluation, atom truncation assumption, or unproved sign is used.

## Strong positive survivor

The exact source capacity

    B7=E7/(-G(x7))

satisfies 0<B7<C3. For every real C,

    E7+C*G(x7)>0  iff  C<B7.

This is a sharp admissible interval for the actual complete-source
direction. The native source is positive there; adjoining degree seven
lowers its admissible compensation below the inherited coefficient.

Paper status: dependency-closed. Lean source:
`formal/GaloisForLFunctions/RHTower/ThetaCuspInheritedOddCompensationBoundary.lean`.
Lean status: formalized, including the matrix no-go and exact positive
capacity. Direct `lake env lean` on the saved leaf exits zero without
warnings. Targeted `lake build --old +GaloisForLFunctions.RHTower.ThetaCuspInheritedOddCompensationBoundary`
passes. The six exported theorem axiom audits, run from a separate
`/tmp` file, contain only `propext`, `Classical.choice`, and `Quot.sound`.
The leaf is wired once into the RHTower umbrella; generated indexes
were refreshed and all six theorem API rows verified.

Repository lint was run and fails on thirteen unrelated unreachable
modules; this leaf has no reported lint error. No full or umbrella
build, new axiom, heartbeat increase, numerical computation, subagent,
commit or push was used.

## Surviving research

The in-progress [odd-border card](../1-in-progress/tt-actual-odd-border-primitive.md)
records C56: differentiate a coupled flux along the existing central
coordinate c2+(168*q-56)*c3. That flux vanishes quadratically on the
obstructing vector at q=7. Its derivative cross term remains essential;
global positive definiteness has not been proved. General coupled-flux
positivity, rank-eight integration, and all-rank RH closure remain open.
