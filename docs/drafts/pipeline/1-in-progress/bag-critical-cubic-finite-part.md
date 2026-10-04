# BAG critical cubic finite part

- **ID:** BAG-C28.56z / BAG-C28.56aa.
- **Stage:** compact-test boundary formalized; physical transfer in progress.
- **C28.56ac checkpoint:** weighted rational/tested identification, including
  termwise series integration, is formalized in P3 bag-weighted-rational-critical-boundary.
  Global actual-source control for Schwartz/growing tests and physical transfer remain.
- **C28.56ab checkpoint:** full balanced rational reindexing and fixed-dilation
  orthogonality are proved in P3 bag-complete-rational-cubic-orthogonality.md.
  Its frequency-weighted extension is now C28.56ac; do not repeat either problem.
- **Route:** BAG, full signed cubic boundary before physical near-resonance transfer.
- **Prior progress:** C28.56y complete weighted six-zeta trace, normal joint H,
  complete contractions K and K'(0)=0. These are audited Lean results.

## Current conjecture and source basis

**C28.56aa resolution:** the complete compact-test boundary is formalized in
P3 `bag-cubic-critical-boundary.md`. The derivation below records its source
and earlier conjecture cycle. Open work now begins at physical transfer,
not the finite parts or product PV.

Prove the critical compact-test boundary of the ACTUAL connected weighted
trace. ZetaResidueFactorDerivative supplies the entire F(s)=(s-1)zeta(s),
with F(1)=1. ChiRamanujanWeightedCubicTrace and Contractions supply the
complete source and H/K. The current corpus search for smooth quotients
is nonpartial (inventory65413/65413); scalar Hadamard and analytic-slope
lemmas exist, but no claimed parameterized cubic boundary theorem was found.

Use J(sigma,alpha)=F(sigma+alpha)F(sigma-alpha), and
A=J(sigma,alpha)J(sigma,beta)H/J(sigma,alpha-beta).
On sigma>=1 and imaginary frequencies, J never vanishes. A extends smoothly
through the critical plane locally and equals a=J(sigma,0) on BOTH axes.
Let T_sigma(u)=J(sigma,i*u)K(sigma,i*u), epsilon=sigma-1,
D_u=epsilon^2+u^2. The exact connected source should equal

    (A(u,v)-T(u))/D_u + (A(u,v)-T(v))/D_v
      - epsilon^2*A(u,v)/(D_u*D_v)
      - 2*u*v*A(u,v)/(D_u*D_v) + 1.

Each of the first two numerators vanishes on its singular axis. This is
algebraically equivalent to the earlier B/M decomposition and retains the
same full trace, without first needing division by uv at the axes.

The limit is the sum of the two corresponding finite parts, minus the
pi^2 intersection mass and twice the product principal-value action of
A_1 times the test, plus the ordinary test integral. Symmetric reflection
on a fixed compact box cancels the linear term for each finite part and
cancels both constant axes for the product PV. Dominated convergence then
needs actual uniform source derivatives on that compact box, not a pointwise
zero or a bare epsilon^2 factor. Both kernels and source regularity must be
proved and joined; a generic conditional receiver alone is not closure.

Beyond this boundary, physical-profile growth, arithmetic/physical diagonal
matching, near-resonances, coupled damping/band limits, growing moments,
moving cofactors and positive common-height self-return remain open.

## Joint intersection proof (current cycle)

Conjecture/proof refinement: do not tensor two pointwise approximate-identity
limits. Scale BOTH frequencies by the same epsilon. The Jacobian cancels
exactly against the literal epsilon-squared numerator and both denominators,
leaving density ((1+x^2)(1+y^2))^-1, whose integral is pi^2. The actual source
A(1+epsilon,epsilon*x,epsilon*y) tends to A(1,0,0)=1. For an arbitrary
continuous compactly supported test Phi, compactness of
[1,2] times tsupport(Phi) bounds A*Phi uniformly. One product-space dominated
convergence theorem therefore gives pi^2*Phi(0,0); the signed trace contributes
its negative. This handles the moving source and the simultaneous limit.

The corpus kernel search completed nonpartially, inventory65441/65441.
Its proposed Cauchy-sequence/filtration ingredients do not prove this claim.
The useful actual APIs are product Bochner integrability, Haar scaling, the
exact integral of (1+x^2)^-1, and filter dominated convergence. The proof is
being checked directly against these APIs; mixed finite parts remain next.

## Remaining cancellation proof, fixed compact test

Fix a C-infinity compactly supported complex test Phi and choose R>0 with
support inside (-R,R)^2. Write f_sigma(u,v)=A_sigma(u,v)*Phi(u,v),
g_sigma(u,v)=(A_sigma(u,v)-T_sigma(u))*Phi(u,v), and
h_sigma(u,v)=(A_sigma(u,v)-T_sigma(v))*Phi(u,v).
Joint source smoothness on the closed sigma>=1 locus gives uniform second
frequency derivative bounds for these three functions on
[1,2] times [-R,R]^2. Crucially g_sigma(0,v)=0 and h_sigma(u,0)=0.

For u>0 the first reflected quotient is

    r_sigma(u,v) = [g_sigma(u,v)+g_sigma(-u,v)]/u^2.

Taylor's integral remainder identifies it with

    integral_0^1 (1-t) * [partial_uu g_sigma(t*u,v)
                          + partial_uu g_sigma(-t*u,v)] dt.

The linear terms cancel exactly. Thus r is uniformly bounded and extends
continuously to u=0. Reflection rewrites the FIRST full finite-part pairing
as integral_(0,R)x(-R,R) r_(1+epsilon)(u,v)*u^2/(epsilon^2+u^2).
The multiplier is in [0,1] and tends to one away from u=0; dominated
convergence gives the integral of r_1. The second pairing is identical with
u/v and g/h exchanged. These are symmetric finite parts, not ordinary
absolutely convergent integrals of g_1/u^2 near its possible linear term.

For the mixed term define

    Delta f(u,v)=f(u,v)-f(-u,v)-f(u,-v)+f(-u,-v).

Two fundamental-theorem-of-calculus applications give, for u,v>0,

    Delta f_sigma(u,v)/(u*v)
      = 4*integral_0^1 integral_0^1
          partial_uv f_sigma((2*t-1)*u,(2*s-1)*v) ds dt.

This quotient has a uniform bound and a continuous extension to both axes.
The FULL original mixed pairing, reflected into (0,R)^2, equals the
integral of that quotient times
[u^2/(epsilon^2+u^2)]*[v^2/(epsilon^2+v^2)]. One dominated convergence
argument gives its product principal value. This also supplies the needed
uniform distribution bound; a pointwise limit or a bare epsilon^2 factor
would not. Combined with the intersection theorem and ordinary test
integral, this is the complete compact-test boundary proof mechanism.

At the C28.56z checkpoint, Lean work still required these parameterized remainder
identities, their actual-source uniform bounds, reflection identities and
DCT assembly. Scalar Hadamard quotient and analytic-slope corpus leaves do
not supply joint parameter regularity by themselves. One implementation
option is to clamp only sigma to max(1,sigma) before forming the frequency
remainders; this gives global continuity for parameter-integral APIs while
agreeing with the literal source for all epsilon>0. No clamp of frequencies,
mode omission or change to the source pairing is permitted.

A further targeted corpus search for Sokhotski/Plemelj/PV boundaries was
nonpartial, inventory65452/65452; candidate/source/proof/ingredient sections
were inspected. It did not identify the joint moving-source result. Its
unrelated derivative-at-zero proposed ingredients cannot justify this limit.

## Audited checkpoint

Source regularity and the literal signed intersection mass are complete in
ChiRamanujanCubicRegularSource and ChiRamanujanCubicIntersectionMass:35
public theorems, both direct production audits clean, all axiom queries
standard only, umbrella wired, index current. Lint's14 unreachable-module
errors are unrelated. P3 bag-cubic-regular-source-intersection-mass records
the exact completed subset. This card remains open for the two reflected
finite parts and mixed-PV assembly above, then the physical transfer.

## C28.56aa — direct cancellation cycle

Previous cycle was progress: source regularity and actual intersection mass
are production/axiom audited. Current target is the other three boundary
terms, preserving the full connected trace.

The quotient-extension construction is unnecessary for dominated convergence.
A stronger direct route now has a checked production proof: apply the mean
value theorem first to fderiv(f), then to the difference
f(x+t*k+h)-f(x+t*k). A uniform second derivative bound C gives

    norm(f(x+k+h)-f(x+k)-f(x+h)+f(x)) <= C*norm(h)*norm(k).

For the actual A*Phi, take opposite corners of the frequency rectangle.
Compact joint source smoothness gives ONE bound for every sigma in[1,2],
and the exact four-reflection numerator is bounded by C*u*v on[0,R]^2.
For the actual (A-T(u))*Phi, take both increments in the first coordinate;
the center value is exactly zero by the proved source axis law, leaving
norm(g(u,v)+g(-u,v))<=C*u^2. The COMPLETE Euler correction and A are proved
symmetric under frequency interchange, so the second axis follows with
the reflected test; no symmetry of Phi is assumed.

Production ChiRamanujanCubicBoundaryCancellation passes direct audit48689
with no diagnostics. Its axioms/index/umbrella audit will be batched after
the current limit leaf. The next checked statement being built is DCT for
the actual totalized quotients, multiplied by u^2/(epsilon^2+u^2) (and its
v counterpart). These multipliers lie in[0,1]; values on the axes are zero
by totalized division. This avoids a separate smooth extension theorem,
without changing the literal source or weakening the desired boundary.

Corpus search remainders-search was nonpartial, inventory65454/65454; all
candidate/source/proof/ingredient sections inspected. Existing Taylor
bounds apply to scalar slices; the direct two-MVT proof is built from the
current corpus MeanValue APIs and the actual jointly smooth source.


## C28.56aa completed boundary

The COMPLETE fixed compact-test boundary is now production- and axiom-audited
in ChiRamanujanCubicBoundaryCancellation, ChiRamanujanCubicCompensatedBoundary
and ChiRamanujanCubicCriticalBoundary. All30 public theorems use only standard
logical axioms. P3 bag-cubic-critical-boundary gives the exact formula and proof.

Both finite parts, all four mixed quadrants, the actual intersection mass,
and the ordinary test term survive the final assembly. The finite-prime
trace limit is explicitly identified with the kernel. Every positive-damping
full-plane integral is integrable and the boundary is independent of the
containing box. Smooth compact test regularity is the test class; there is
no assumed arithmetic bound or RH premise.

Next hard problem: rational reindexing/fixed-dilation orthogonality and
physical contraction matching, followed by the actual-profile and finite-height
near-resonance transfer with coupled damping/band limits. A fixed compact-test
boundary alone does not exchange the prime net with integration or prove the
physical cubic. Do not redo the now-closed boundary. RH remains unproved.
