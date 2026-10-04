# BAG complete compact-test cubic boundary

- **ID:** BAG-C28.56aa.
- **Stage:** 3-formalized for the complete arithmetic boundary below.
- **Route:** BAG. Physical prime-correlation transfer remains open.
- **Namespace:** `RHTower.BAGTrace`.
- **Leaves:** `ChiRamanujanCubicBoundaryCancellation`,
  `ChiRamanujanCubicCompensatedBoundary`, `ChiRamanujanCubicCriticalBoundary`.
- **Source basis:** C28.56y complete weighted six-zeta trace and C28.56z actual
  regular source and signed intersection mass.

## Exact new result

For EVERY smooth compactly supported complex test Phi on R^2, the COMPLETE
connected arithmetic kernel has a boundary as epsilon tends to zero from
above. Its integral is a genuine Bochner integral for every epsilon>0.
Every signed valuation sector is retained. The finite-prime trace limit is
explicitly identified with this kernel by
`complete_weighted_offAxes_connectedKernel`.

Write A_sigma(u,v) for the actual pole-removed six-zeta source and T_sigma(u)
for its actual contraction source. Put D_u=epsilon^2+u^2, sigma=1+epsilon.
The tested kernel is exactly

    [(A-T(u))/D_u + (A-T(v))/D_v
      - epsilon^2*A/(D_u*D_v) - 2*u*v*A/(D_u*D_v) + 1] * Phi(u,v).

For any R>=0 containing support(Phi) in [-R,R]^2, define

    f_sigma(u,v) = A_sigma(u,v)*Phi(u,v)
    g_sigma(u,v) = (A_sigma(u,v)-T_sigma(u))*Phi(u,v)
    Delta f_sigma(u,v) = f_sigma(u,v)-f_sigma(-u,v)
                           -f_sigma(u,-v)+f_sigma(-u,-v).

The full-plane limit is

    integral_[0,R]x[-R,R] [g_1(u,v)+g_1(-u,v)]/u^2
    + the same first-axis integral with Phi(u,v) replaced by Phi(v,u)
    - pi^2*Phi(0,0)
    - 2*integral_[0,R]^2 Delta f_1(u,v)/(u*v)
    + integral_[-R,R]^2 Phi.

Division is totalized on the zero-measure axes. This is the explicit
`cubicCriticalBoundaryValue`; the value is proved independent of R. No test
symmetry is assumed. The theorem `exists_cubicCriticalBoundary` supplies
such an R for every smooth compact test; there is no unproved source-bound,
arithmetic cancellation, zero-free-region or RH premise.

## Dependency-closed proof

The corpus already proves joint smoothness of the actual A and T at every
sigma>=1, exact source-axis cancellation and A(1,0,0)=1. This cycle proves
the full Euler correction and A symmetric under interchange of frequencies.

Apply the mean value theorem to the Frechet derivative of f, then to
t |-> f(x+t*k+h)-f(x+t*k). A uniform second derivative bound gives

    norm(f(x+k+h)-f(x+k)-f(x+h)+f(x)) <= C*norm(h)*norm(k).

Compactness supplies one C across sigma in [1,2] and the frequency box.
Opposite rectangle corners yield norm(Delta f)<=C*u*v. For the first axis,
use two increments in the same coordinate: exact g_sigma(0,v)=0 leaves
norm(g_sigma(u,v)+g_sigma(-u,v))<=C*u^2. The second axis follows by source
symmetry and swapping the test, without assuming Phi is symmetric.

The totalized quotients are bounded and measurable. Their damped versions
multiply by u^2/(epsilon^2+u^2), and by the corresponding v factor for the
mixed term. Both multipliers lie in [0,1]. Parameter continuity of the
actual source and dominated convergence give all three reflected limits.
A separate smooth extension of either quotient is unnecessary.

Exact Fubini and interval reflection identities identify these integrals
with the ORIGINAL whole symmetric-box kernels, including all four mixed
quadrants. C28.56z supplies the actual moving-source intersection mass.
Linearity assembles every term. Zero outside the test support gives the
full-plane result, compactness supplies the containing box, and uniqueness
of the full-plane limit proves box independence.

## Audit

Direct foreground production audits, with `lake --old env lean <leaf> -o
<olean>`, passed without diagnostics: cancellation48689,
compensated29471, critical11675. All three leaves are wired into RHTower;
no umbrella/full build was run. All30 public-theorem axiom queries passed
in58033, using only propext, Classical.choice and Quot.sound. Index67141 passed and all30 names are present in LEAN_API. Lint48319 reports
19 unrelated unreachable modules, no new-leaf, proof-debt or freshness error.

## Hard frontier still open

This closes the fixed compact-test ARITHMETIC boundary. It does not exchange
the finite-prime net with integration or identify the result with the
physical prime cubic. C28.56ab now proves balanced rational reindexing and
fixed-dilation orthogonality; C28.56ac proves weighted rational/tested
identification and termwise rational-series integration. Remaining: physical contraction matching,
actual-profile growth for noncompact/growing tests, finite-height
near-resonances with coupled damping/band limits, growing moments, moving
cofactors, and positive common-height self-return. RH remains unproved.
