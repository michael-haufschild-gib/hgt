# Can ordinary Möbius window bounds control a balanced product pullback?

- **ID:** goldbach-balanced-product-smoothing
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; transfer audit for the actual signed estimate
- **Parent:** [Goldbach target](goldbach-unconditional-2026-10-23.md), Cycle 11
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

The proposed positive survivor is an explicit nonzero-determinant count,
together with the exact smoothing-energy accounting. Establish its
constants and scope before formalization. A generic Cauchy bound or an
assumed short-interval estimate will not be used as its proof.

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

Paper derivation recorded; exact Lean dependencies and the general-modulus
certificate are in progress. No route is retired before this positive
survivor is formalized. No signed estimate or scientific novelty claim.
The original all-even target is unchanged.
