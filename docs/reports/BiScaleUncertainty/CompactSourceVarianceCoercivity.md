# Compact-source graph variance coercivity and rigidity

## Exact statement

Let ψ be any real continuous compact source, let B>0 be its constructed support
radius, and let λₙ be arbitrary finite nonnegative atom coefficients. Use the
actual mixed graph κ from `CompactSourceGraphAdmission.md`. For an actual physical
L² velocity q and any constant c put

    f(x)=c+∫₀^{exp x}q(t)dt,
    M=∫ψ²,    A=∫ψ²f,    Q=∫ψ²f²,
    J=∫|f(u+h)−f(u)|²dκ(h,u).

Then all these quantities are finite and

    0 ≤ M Q − A² ≤ sinh(2B) J.

No nonzero-source, positive-mass, connected-support, atom-summability or energy
admission hypothesis is needed. In addition,

    J=0  iff  f(u)=f(v) whenever ψ(u)≠0 and ψ(v)≠0.

Thus separate nonzero source regions belong to one zero-energy class under the
diffuse jump graph. No assertion is made about values inside holes where ψ=0.

## Paper proof [PROVED HERE]

The following variance identities hold for every continuous state f, independent
of its Sobolev origin. Define

    P(u,v)=ψ(u)²ψ(v)²(f(v)−f(u))²,
    L(h,u)=P(u,u+h),     H(h)=∫L(h,u)du.

P is continuous, nonnegative and supported in [-B,B]². L is continuous,
nonnegative and supported in [-2B,2B]×[-B,B]. Both are therefore integrable.
The one-variable moment integrands ψ², ψ²f and ψ²f² are continuous and
compactly supported too. Expanding P and applying Fubini gives

    ∫∫P(u,v)du dv = 2(MQ−A²).

Translation v=u+h, justified by the established integrability, gives
`∫H(h)dh=∫∫P`. Replacing u by u−h and using symmetry of P gives H(-h)=H(h).
Consequently

    ∫_{h>0}H(h)dh = MQ−A² ≥0.

Whenever L(h,u)≠0 and h>0, both endpoints are in [-B,B], so h≤2B.
Monotonicity of sinh and exp gives

    1 ≤ sinh(2B) exp(h/2)/sinh h.

Multiplying by L and integrating on h>0 proves

    MQ−A² ≤ sinh(2B)∫_{h>0}∫w_arch(h)L(h,u)du dh.

The integral on the right is exactly the diffuse part of the constructed graph
energy. Every arithmetic term is nonnegative, so adding the entire countable
atomic measure proves the stated bound. For the actual q, compact-source
admission already proves finite total graph energy; hence passage between
nonnegative extended integrals and ordinary finite values is justified.

If J=0, coercivity forces MQ−A²=0. The exact pair identity gives ∫P=0.
Nonnegativity gives P=0 almost everywhere, and continuity together with full
support of two-dimensional Lebesgue measure upgrades this to P=0 everywhere.
At nonzero source endpoints its positive source factor forces f(u)=f(v).
Conversely, that equality makes every source-weighted pair difference zero,
including every diffuse edge and every arithmetic atom. Thus J=0.
The argument also covers ψ=0 without dividing by M.

The previous compact admission bound is `J ≤ C D`, where C is constructed
resistance mass and D is source-local additive Dirichlet mass. Both are finite.
Combining the two inequalities gives `MQ−A² ≤ sinh(2B) C D`. This explicitly
couples source variance and mixed multiplicative jumps to additive regularity.

## Significance and boundary

Compact-source admission supplied an upper energy bound from additive regularity.
This result supplies the complementary lower bound in terms of weighted state
variance, and determines the whole continuous zero-energy class. Positivity of
long diffuse jumps links source regions even when the local source support is
disconnected. The coefficient depends on the actual support radius; no uniform
bound over expanding sources, sharp optimal coefficient, closed operator domain,
or unitary affine representation is asserted.

The variance identity and positive-kernel comparison are classical ingredients.
The field-specific contribution is their premise-free application to the actual
singular diffuse/arithmetic graph and its previously constructed rough states.
The focused corpus search found hyperbolic-multiplier variance identities and
compact admission, but no matching graph coercivity theorem. Coverage remains
semantic-unmeasured; this is not an exhaustive novelty claim.

[Barlow–Bass–Chen–Kassmann, Non-local Dirichlet Forms and Symmetric Jump Processes](https://arxiv.org/abs/math/0609842)
provides background on squared-jump forms and kernel bounds. Only its abstract
was inspected; no theorem from it is used in this proof.

## Lean certificate

`CompactSourcePairVariance.lean` proves the general continuous pair/lag identities
and zero-variance classification. `CompactSourceGraphCoercivity.lean` proves the
actual mixed-graph bound, additive Dirichlet consequence and zero-energy rigidity.
Both final direct leaf checks passed without diagnostics. All 27 public
declarations use only `propext`, `Classical.choice`, `Quot.sound`. Both imports
are wired and all 21 public theorem names are indexed. Repository lint reports
seven unrelated concurrent modules missing umbrella imports; no error concerns
either leaf. Exact evidence is recorded in `ContinuumCoprimeShear-FACTS.md`.

Certified as one connected contribution, package 5 of the active 100-package goal.
