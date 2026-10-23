# Can ordinary Möbius window bounds control a balanced product pullback?

- **ID:** goldbach-balanced-product-smoothing
- **Stage:** 5-failed
- **Type:** FALSE transfer candidate; exact positive survivor formalized
- **Parent:** [Goldbach target](../1-in-progress/goldbach-unconditional-2026-10-23.md), Cycle 11
- **Source:** BVI's actual-row short-window mean-square mechanism

## Exact candidate before proof

Let I_X be the integers in (X,2X], and let

    d_X(v)=#{(m,n)∈I_X² : mn=v}.

Extend d_X by zero on all integers. For an integer H≥1 let

    A_H d_X(v)=H⁻¹ Σ_(0≤h<H) d_X(v+h).

The balanced bilinear sum can be pushed to the residual coordinate:

    Σ_(m,n) α_m β_n μ(T−mn)
      =Σ_v μ(T−v) Σ_(mn=v) α_m β_n.

The flat choice α=β=1 is already a necessary test for transferring BVI's
small smoothing cost to arbitrary bounded product coefficients.

**Candidate S:** for fixed 0<η<1 and H=floor(X^η),

    ||d_X−A_H d_X||²_(ℓ²(ℤ)) = o(X²).

This is a falsifiable proposed transfer, not an assumed analytic input.
If true with adequate quantitative precision and weighted variants, it
would allow ordinary Möbius short-window means to enter the balanced
Goldbach sum. The first open step is this smoothing cost itself.

## Attack: retain the zero-shift collision

Set C_X(h)=Σ_v d_X(v)d_X(v+h). At h=0 this counts
m₁n₁=m₂n₂. At h≠0 it counts a nonzero determinant. The primitive-row
decomposition m₁=ga, m₂=gb forces g|h in the latter case and leaves a
one-dimensional progression of cofactor solutions. At h=0 the common
divisor g is unrestricted. Thus the diagonal may exceed every averaged
nonzero-shift contribution by a logarithmic factor.

The nonzero-determinant count is pursued in the separate
[compensated collision audit](goldbach-compensated-product-collision-cost.md).
The positive survivor formalized in this cycle is the complete residue
profile and exact smoothing-energy accounting below. No short-interval
estimate is supplied as a premise.

## Status

Candidate S already fails at the parity mode. If X and H are even, then

    Σ_v (−1)^v d_X(v)=X²/2,
    Σ_v (−1)^v A_H d_X(v)=0.

The first identity counts the odd-odd pairs (X²/4); the second is the
vanishing alternating sum of an even averaging window. The difference
is supported on at most 4X²+H integers, so Cauchy gives

    ||d_X−A_Hd_X||² ≥ X⁴/[4(4X²+H)].

For η=1/2, choose X=(2j)² and H=2j. This contradicts Candidate S.
The contradiction is a coherent residue bias, not evidence of random
collision noise. Discarding that mode by an absolute norm would lose
information which the actual Möbius row can cancel. The correct next
object is therefore the full residue profile before estimating the
remaining signed pairing.

## Positive survivor: the exact local product profile

For q≥1 let ν_q(r) count ordered pairs of residues a,b modulo q with
ab=r. Group a by g=gcd(a,q). Such a exists in φ(q/g) classes. Its
multiplication fibre has g elements exactly when g|r, and is empty
otherwise. Hence

    ν_q(r)=Σ_(g|q, g|r) g φ(q/g).

Equivalently, if c_d is the Ramanujan sum,

    ν_q(r)/q=Σ_(d|q) c_d(r)/d.

To verify the Fourier statement directly, use the canonical additive
character ψ_q. Character orthogonality gives

    Σ_(a,b mod q) ψ_q(hab)=q gcd(h,q).

Fourier inversion groups h by additive order d=q/gcd(h,q), giving the
displayed Ramanujan expansion. Period orthogonality then proves the
exact centered energy

    q⁻¹ Σ_(r mod q) (ν_q(r)/q−1)²
      =Σ_(d|q, d>1) φ(d)/d².

For prime q this is (q−1)/q². For squarefree q it is
∏_(p|q)(1+(p−1)/p²)−1. These are positive coherent contributions, not
signed cancellation estimates.

When q|X, each row interval has X/q representatives of every residue,
so the physical product row has residue masses (X/q)²ν_q(r). If q|H,
averaging replaces these masses by the uniform value X²/q. This
identifies every rational mode erased by the proposed transfer, not
only parity. The sharp orthogonal projection onto residue-constant
vectors gives its unavoidable error and the exact surviving residual.

The exact gcd Fourier reconstruction, local energy and its vanishing
classification, actual balanced product masses, smoothing energy and signed
pairing are now formalized in
[ProductResidueProfile.lean](../../../../formal/GaloisForLFunctions/goldbach/ProductResidueProfile.lean).
The totient/Ramanujan expressions above remain paper corollaries of the
certified gcd spectrum. No signed estimate or scientific novelty claim.
The original all-even target is unchanged.

## Exact projection accounting

For a positive integer L and any real row u on L positions, write
`m(u)=L⁻¹Σ_j u_j`. Expanding the product and using `Σ_j u_j=L m(u)`
gives, without any hypothesis on either row,

    Σ_j u_j v_j = L m(u)m(v) + Σ_j (u_j−m(u))(v_j−m(v)).

Apply this independently on each residue class of a window containing L
positions per class. For `f=d_X−A_Hd_X`, where q divides both X and H,
the class masses are `Δ_r=(X/q)²(ν_q(r)−q)`. Thus

    Σ_v f(v)² = L⁻¹ Σ_r Δ_r²
                + Σ_r Σ_(v≡r) (f(v)−Δ_r/L)².

The first term is the complete periodic obstruction. Equality in its lower
bound holds exactly when each residual is zero. For a second real row g,
the corresponding signed pairing is

    Σ_v f(v)g(v) = Σ_r Δ_r m_r(g)
                    + Σ_r Σ_(v≡r) (f(v)−Δ_r/L)(g(v)−m_r(g)).

Consequently a Möbius mean estimate controls only the first term; the
second is the compensated product-pullback correlation and remains open.
No mean estimate is being substituted for that correlation. The window
`(-H,4X²]` has L=(4X²+H)/q positions per class and contains the full
support. This recovers the sharp projection formula with K=qL.

The local centered energy vanishes exactly for q=1. Indeed, zero energy
would force ν_q to be the constant q. For q>1 its Fourier coefficient
at frequency 1 would then vanish, whereas the proved gcd formula makes
that coefficient q. At q=1 the single fibre has size one. Thus every
nontrivial modulus contributes a nonzero periodic obstruction.

## Finite model with the actual product counts

For q,L,h positive and k natural, put X=qk and H=qh. Encode an integer
n by `(n mod q, floor(n/q) mod L)`. Let D_c(r,t) count ordered pairs
m,n in `(X,2X]` whose product plus c has that label. Define

    F(r,t)=D_H(r,t)−H⁻¹Σ_(0≤j<H)D_(H−j)(r,t).

Every product contributes exactly once to its residue fibre, independently
of L. Hence `Σ_t D_c(r,t)=k²ν_q(r−c)`. The complete H-step average has
mass k²q in every residue, while H is zero modulo q. Thus

    Σ_t F(r,t)=k²(ν_q(r)−q).

The projection identity proved above now gives the unconditional exact law

    Σ_(r,t) F(r,t)² = (k⁴/L) Σ_r(ν_q(r)−q)²
                       + Σ_(r,t)(F(r,t)−mean_t F(r,t))².

Taking L=4qk²+h+1 ensures `qL>4X²+H`. All shifted products lie between
0 and `4X²+H`, so their encoding does not wrap. The finite row is then
exactly the translate by H of the ordinary integer smoothing difference.
This model keeps every actual product multiplicity; no residue-mass
assumption is supplied as a premise.

## No-go closure

- **Killing mechanism:** complete-period smoothing erases nonzero periodic
  multiplication modes. The checked finite square-root-window family has
  squared error at least `(E_2/34)X²`, with E_2 proved positive.
- **Strongest positive survivor:** full gcd Fourier reconstruction and
  centered energy; exact realization by the balanced integer products;
  sharp orthogonal projection energy and the surviving signed covariance.
- **New insight:** periodic bias must be retained as a signed mean pairing.
  Removing it leaves a specific covariance, not an automatic smoothing
  estimate. The follow-up collision audit attacks that attempted repair.
- **Status:** dependency-closed paper proof and exact finite Lean theorems
  recorded on the [formalized survivor card](../3-formalized/not_new_scientific_knowledge/goldbach-product-residue-profile.md).
  Leaf compilation and eleven closure audits passed without warnings.
  Only standard Lean foundations occur. The ordinary infinite ℓ² notation
  and asymptotic contradiction are paper corollaries of the finite theorem.

No external novelty claim or web novelty audit; this is elementary arithmetic
salvage within the requested RH-to-Goldbach transfer audit.
