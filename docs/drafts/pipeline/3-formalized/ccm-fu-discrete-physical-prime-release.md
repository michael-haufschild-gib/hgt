# CCM-FU: discrete prime release equals the signed physical average

- **Stage:** 3-formalized; three leaves passed foreground scratch and exact-file checks. Lake packaging audit remains pending.
- **Parent:** [literal fixed-core prime correlation](../1-in-progress/ccm-fu-fixed-core-prime-correlation.md).
- **Proof chain:** Actual divisor source → renewable signed reserve → exhaustive selection → uniform signed Abel bound → RH.
- **Closed:** Real head block coefficients, physical block integrals, complete countable integral assembly, exact discrete-to-physical release identity, strict distant-prime release orientation for each fixed nonempty core.
- **Open:** Uniform control under changing cores and cutoffs, renewable reserve, exhaustive selection and RH.

## Exact source theorem

Let P be a finite prime core, p a prime outside P, and kappa_P the
already proved complete limiting energy coefficient, defined as its
actual nonnegative quotient-block mass series. Let

`rho_P=squarefreeDensity*product_(q in P) q/(q+1)`

and let G_P be the actual continuous processed head, with

`W_P(Y)=integral_(x>1) G_P(Y*x)*G_P(x)/x^3 dx`.

Lean proves the exact identity

`kappa_P-kappa_(P+p)=2*rho_(P+p)*p^(-3/2)*W_P(p)`.

All infinite tails, density factors, square-root factors and the dilation
Jacobian are included. Neither side is defined to equal the other.

For every fixed nonempty finite prime core P, Lean also proves

`eventually in p:Natural, p prime and p outside P imply`

`0 < (-1)^(card(P)+1)*(kappa_P-kappa_(P+p))`.

Thus sufficiently distant unprocessed primes strictly decrease the
limiting coefficient for odd-sized cores and strictly increase it for
even-sized cores. The threshold depends on P. This is a statement about
the limiting coefficient, not an every-cutoff energy inequality.

## Dependency-closed paper proof

Write a_n,b_n for the discrete head's square-root slope and intercept.
For every real u in [n,n+1], finite Mobius dilation gives

`G_P(u)=a_n*sqrt(u)+b_n`.

Indeed, for each positive divisor d of product(P), the interval u/d lies
inside [floor(n/d),floor(n/d)+1]. The unit source's exact square-root
interpolation therefore gives an affine expression in sqrt(u). If the
quotient is zero, the whole unit source is zero. Summing the signed finite
dilations preserves affinity. Its two endpoint values are the actual
integer heads, so its coefficients equal the existing discrete a_n,b_n.
The same argument gives

`sqrt(p)*G_P(u/p)=a_(n/p)*sqrt(u)+sqrt(p)*b_(n/p)`.

Both identities include every clipping endpoint and the inactive block.

Define the physical kernel

`K_(P,p)(u)=2*sqrt(p)*G_P(u)*G_P(u/p)/u^3`.

Its absolute integrability on u>1 follows from the already proved
integrability of the dilation average at Y=1/p, multiplied by 2*sqrt(p)
and with the two real factors exchanged.

The existing arithmetic correlation primitive is

`Phi_n(t)=2*[a_n*a_(n/p)*t`

`+(2/3)*(a_n*sqrt(p)*b_(n/p)+b_n*a_(n/p))*t*sqrt(t)`

`+b_n*sqrt(p)*b_(n/p)*t^2/2]`.

The derivative of t*sqrt(t) is (3/2)*sqrt(t). Apply the product rule and
sqrt(t)^2=t, then compose with inversion. The exact head identities give

`d/du[-Phi_n(1/u)]=K_(P,p)(u)`

throughout the closed block for n>=1. The fundamental theorem of calculus
therefore identifies the kernel integral on (n,n+1] with
Phi_n(1/n)-Phi_n(1/(n+1)). This is precisely the existing arithmetic
correlation mass divided by rho_(P+p).

The intervals (n+1,n+2], n>=0, are pairwise disjoint and cover (1,infinity).
Countable integration of the absolutely integrable kernel joins every
block. The original zero-index mass is zero, so the resulting full mass
series is rho_(P+p)*integral_(u>1) K_(P,p)(u) du. Uniqueness of the already
proved arithmetic series sum identifies this with kappa_P-kappa_(P+p).

Extend the kernel integral to u>0: the original head G_P(u) vanishes
below one. Set u=p*x. The square-root multiplier, cubic denominator and
Jacobian give 2*sqrt(p)/p^2=2*p^(-3/2). The second head G_P(x) vanishes
below one, so the remaining integral is exactly W_P(p). This proves the
discrete-to-physical identity.

The preceding source theorem proves the strict eventual sign
(-1)^(card(P)+1) for W_P(Y). Compose its real dilation limit with the
natural-number inclusion. The exact density and p^(-3/2) factors are
strictly positive. The displayed discrete orientation follows.

## Lean implementation

- `MobiusDivisorContinuousHeadBlocks.lean`: two public theorems identifying the literal continuous head and its integer dilation with the existing discrete block coefficients.
- `MobiusDivisorPrimeCorrelationBlockIntegral.lean`: kernel definition, absolute integrability and exact block integral theorem. The differentiated source is the existing arithmetic primitive.
- `MobiusDivisorPrimeCorrelationPhysical.lean`: complete kernel scaling, full mass-series integral, exact release coefficient identity and eventual discrete orientation.

The three leaves are wired into RHTower. Each passed `lake env lean`
scratch and exact-file checks and emitted its leaf olean. No full,
umbrella or large build was run. No numerical experiment or computed
premise is used. The known Lake packaging audit remains pending because
of its broad stale prerequisite rebuild.

All nine new public declarations (eight theorems and one definition) passed
one external axiom audit. Every closure uses only propext, Classical.choice
and Quot.sound. No old declaration was re-audited, and no old prerequisite
olean needed rebuilding. Global formal lint passed, the declaration index
was refreshed and the scoped whitespace check passed.

## Uniform source obligation

The fixed-core contour, physical mean, scalar orientation and discrete
identification are closed. A new argument must control actual transitions
while the processed core and cutoff change. Strict signs after separate
core-dependent thresholds do not provide one reserve budget at every
cutoff. The [reserve-induction quantifier requirement](../1-in-progress/ccm-fu-reserve-extension-induction.md)
requires one common bound for all earlier cutoffs, or a proved propagation
law supplying that bound. The [changing-core pair theorem](ccm-fu-changing-core-pair-reserves.md)
now supplies a uniform ratio profile and positive pair reserves after
every even nonempty core, along with the opposite comparable-pair cost.
Its core-dependent thresholds, intermediate costs and lack of exhaustive
prime inclusion leave the common every-cutoff bound open. RH remains
unproved.
