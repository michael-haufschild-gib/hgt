# BAG cubic regular source and intersection mass

- **ID:** BAG-C28.56z, source regularity and intersection summand only.
- **Stage:** 3-formalized for the exact source and intersection statements below.
- **Route:** BAG, complete signed arithmetic cubic boundary.
- **Continuation:** `../1-in-progress/bag-critical-cubic-finite-part.md`.
- **Lean namespace:** `RHTower.BAGTrace`.
- **Leaves:** `ChiRamanujanCubicRegularSource`, `ChiRamanujanCubicIntersectionMass`.

## Exact source theorem

Use the corpus entire residue factor F(s)=(s-1)zeta(s), with F(1)=1, and set
J(sigma,alpha)=F(sigma+alpha)F(sigma-alpha). For sigma>=1 and imaginary
alpha,beta, every denominator J below is nonzero, by the proved closed
Re(s)>=1 zeta nonvanishing theorem, with the pole filled by F(1)=1.

    A(sigma,alpha,beta) = J(sigma,alpha)J(sigma,beta)H/J(sigma,alpha-beta)
    T(sigma,alpha) = J(sigma,alpha)K.

The actual source A and contraction source T are jointly smooth through
every point of the critical plane, including the intersection. Joint
holomorphy of K, not only frequency-slice holomorphy, is also formalized.
Both A axes are exactly J(sigma,0), and A(1,0,0)=1.

With real frequencies u,v, epsilon=sigma-1 and D_u=epsilon^2+u^2, the
COMPLETE directed prime-coordinate trace after literal two-axis masking is

    (A(u,v)-T(u))/D_u + (A(u,v)-T(v))/D_v
      - epsilon^2*A(u,v)/(D_u*D_v)
      - 2*u*v*A(u,v)/(D_u*D_v) + 1.

No signed sector is removed. This is an exact equality of the previously
proved trace limit, not a replacement definition of the source.

## Exact intersection theorem

For EVERY continuous compactly supported complex test Phi on R^2,

    lim_(epsilon -> 0+) integral_R^2
      -epsilon^2*A(1+epsilon,u,v)*Phi(u,v)
        / ((epsilon^2+u^2)*(epsilon^2+v^2)) du dv
      = -pi^2*Phi(0,0).

The moving source is retained. The literal tested kernel is integrable for
every epsilon>0. The limit has no unproved arithmetic or analytic premise;
continuity and compact support specify the permitted test class.

## Paper proof and the critical distinction

On [1,2] times the compact support of Phi, source regularity bounds A*Phi
uniformly. Outside that support the tested source is zero. Scale both real
frequencies at once by epsilon. The two-dimensional Haar Jacobian cancels
the literal epsilon-squared numerator and both rescaled denominators,
leaving ((1+x^2)(1+y^2))^-1 times the moving tested source. This density is
integrable, its integral is pi^2, and the source tends pointwise to
A(1,0,0)*Phi(0,0)=Phi(0,0). One product-space dominated-convergence theorem
proves the claim. Exact scalar/cast identification supplies the negative
summand of the original complex-valued trace.

The epsilon-squared numerator therefore CANNOT be discarded just because
it tends to zero pointwise away from the axes. The positive result is the
exact intersection boundary action above. This is a statement about that
summand, not yet a claim excluding further contributions in the other terms.

## Frontier left open

The two symmetric finite parts and product principal-value action are now
formalized in C28.56aa, P3 `bag-cubic-critical-boundary.md`. That result uses
direct uniform second/mixed cancellation, exact reflection and dominated
convergence for the actual source. Physical transfer remains open.

Beyond it: rational reindexing/orthogonality, physical contraction matching,
physical-profile growth, finite-height near-resonances, coupled damping/band
limits, growing moments, moving cofactors and positive common-height return.
No unconditional RH conclusion is claimed.

## Audit

- Regular source: 26 public theorems; direct production audit3941 exit0,
  no diagnostics, using `lake --old env lean`.
- Intersection: 9 public theorems; production52688 exit0 with no diagnostics,
  using `lake --old env lean`.
- All35 public theorem axiom queries2309 exit0; only propext, Classical.choice,
  Quot.sound. Every expected theorem was checked. No tree #print command.
- Both leaves wired into RHTower; no full/umbrella build.
- No added axiom, sorry/admit, numerical experiment, subagent or heartbeat increase.

- Index70100 exit0; generated API/overview/gaps refreshed. All35 public
  theorem names checked in the generated API.
- Lint1295 exit1 solely on14 unrelated unreachable modules; no new-leaf,
  proof-debt or generated-freshness error.
- Scoped whitespace checks passed. Evidence logs are
  /tmp/bag-critical-{source-production,intersection-production,axioms,index,lint}-01a0.log.
