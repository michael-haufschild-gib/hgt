# Centered prime-dilation dispersion for the flat balanced product row

- **ID:** goldbach-flat-prime-dilation-dispersion
- **Stage:** 2-fully-proven
- **Type:** Classical analytic bridge; paper proof, no external novelty claim
- **Parent:** [prime-dilation candidate](../1-in-progress/goldbach-prime-dilation-dispersion.md)
- **Dependency:** [composite Kloosterman budget](goldbach-composite-kloosterman-budget.md), proved on paper from checked prime Weil and finite arithmetic
- **Lean status:** Not formalized. No dispersion premise, placeholder or conditional Lean capstone added.

## Statement

Let X be a positive integer, 5X²≤T≤6X² an integer, and put

    d_X(v)=#{(m,n)∈(X,2X]²∩ℤ²:mn=v},
    ρ_X(v)=log(v/X²)       on [X²,2X²],
           log(4X²/v)     on (2X²,4X²],
           0              elsewhere,
    Q=floor(exp(sqrt(log X))),
    R_Q(v)=Σ_(d≤Q)c_d(v)/d,
    a(v)=d_X(v)−ρ_X(v)R_Q(v).

Here d_X is zero outside the integer product range, and
`c_d(v)=Σ_(e|gcd(d,|v|)) e μ(d/e)` is the Ramanujan sum. Let P contain
all primes at most exp((log X)^(1/4)) that do not divide T. For p≠q in P set

    Γ(p,q)=Σ_(1≤r≤6X²) r 1_(gcd(r,pq)=1) a(T−pr)a(T−qr).

There are absolute C,X₀ such that, for X≥X₀ and every displayed T,

    Σ_(p,q∈P,p≠q)|Γ(p,q)|
      ≤C X⁴ exp(−sqrt(log X)/10).                    (1)

The lower prime cutoff in Candidate D is therefore unnecessary for its
off-diagonal estimate. It is still needed to pay the amplifier's diagonal.
This statement concerns the actual flat product count. Arbitrary Type II
coefficients and predecessor marks are not included.

## 1. Finite modular-inverse discrepancy

For M≥1, integer c, and integer intervals U,V of cardinalities L_U,L_V,
write

    H_M(c;U,V)=#{(u,v)∈U×V:gcd(u,M)=1, uv≡c mod M}.

Let Δ=gcd(c,M). The composite budget gives

    H_M(c;U,V)=φ(M)L_U L_V/M² + E,

    |E|≤C τ(M)(1+log(2M))²
      [M^(2/3)Δ^(1/3)+(L_U Δ+L_V)/M].               (2)

Proof: Fourier expansion of both interval multiplicities on Z/M gives
`M^(-2)Σ_(a,b) Û(a)V̂(b)S(a,bc;M)`, up to harmless signs.
The zero-zero term is the displayed main term. For a nonzero residue a,
the geometric-series formula gives

    |Û(a)|≤C M/min(a,M−a),

independently of the number of complete periods in U. For every d|M,

    M^(-1)Σ_(a≠0,d|a)|Û(a)|≤C(1+log(2M))/d.        (3)

The cubed Kloosterman bound implies
`|S(a,bc;M)|≤8τ(M)M^(2/3)Δ^(1/3)gcd(a,b,M)^(1/3)`.
Use `gcd(a,b,M)^(1/3)≤Σ_(d|a,b,M)d^(1/3)` and (3) twice.
The resulting divisor sum is bounded by Σ_(d≥1)d^(-5/3), giving the
first term of (2). When exactly one frequency vanishes, use the exact
Ramanujan sum and

    |c_M(bc)|≤gcd(bc,M)≤Δ gcd(b,M),
    gcd(b,M)=Σ_(d|b,M)φ(d).

Equation (3) bounds these two terms by
`Cτ(M)(1+log(2M))(L_U Δ+L_V)/M`.
The case M=1 has zero discrepancy. All interval lengths and residue
multiplicities in this calculation are exact integers.

The Ramanujan bound used here follows prime-power by prime-power from
`c_(ℓ^j)(v)=φ(ℓ^j)` if ℓ^j|v, `−ℓ^(j−1)` if
ℓ^(j−1)|v but ℓ^j∤v, and zero otherwise; CRT multiplies the values.

## 2. The actual determinant count

Fix distinct primes p,q with gcd(T,pq)=1, and set D=T(q−p)≠0.
For h∈{1,p,q,pq}, let N_h(R) count the quadruples of integers in
(X,2X]⁴ for which

    mn=T−pr,   m'n'=T−qr,   0<r≤R,   h|r.

For every ε>0, uniformly in R≥0,

    N_h(R)=(σ_(-1)(|D|)A_h/h)
       ∫_0^R ρ_X(T−pt)ρ_X(T−qt) dt
       +O_ε((pq)^4(1+|D|)^ε X^(11/6+ε)),           (4)

where

    A_1=ζ(2)^(-1) p/(p+1) q/(q+1),
    A_h=A_1∏_(ℓ|h)(1−1/ℓ).

If p/q is outside [1/4,4], both sides' unweighted main/count terms
vanish: the two product arguments cannot lie in [X²,4X²] for the same
positive t. Otherwise all boundary slopes below are bounded absolutely.

### Exact congruence

Fix y=m'. The equations give

    qmn−pyn'=D,   mn≡T mod ph.

There is no solution if q|y. If p|h and p|y, reduction modulo p also
excludes a solution. In all other cases gcd(y,qh)=1, and CRT combines
the product congruences into

    mn≡A mod L,   L=phy,   gcd(A,L)=gcd(D,y).        (5)

For h=1 the first congruence determines A modulo py. Adding the second
congruence is compatible exactly when gcd(y,h)=1: its compatibility
divisor is p gcd(y,h), and D−qT=−pT is coprime to any extra prime
of h. This proves (5), including its stated exclusions.

The remaining n' constraint is the hyperbolic strip

    (D+pyX)/q < mn ≤ (D+2pyX)/q,

intersected with mn≥T−pR and the original square. Its continuous
area will be denoted F_R(y).

### Summing the discrepancy, with all nonunit fibres

Partition the m-interval into K intervals of width at most X/K+1.
On each, upper and lower rectangles bracket the strip. In the relevant
square every boundary is n=c/m with |c|≤4X², or a constant; the total
area between the two rectangular brackets is O(X²/K+X).

For each rectangle split m by g=gcd(m,L). Only g|gcd(D,y) contributes.
Write y=gt, m=gu. Then

    M=L/g=pht,   gcd(u,M)=1,
    un≡A/g mod M,
    gcd(A/g,M)=gcd(D/g,t).

Apply (2) to U=(the m interval)/g and V=(the n interval). Its main
density in the original (m,n) coordinates is

    (1/(phy)) Σ_(g|gcd(D,y)) φ(phy/g)/(phy/g).       (6)

Rounding the real endpoints in U,V changes the main term by quantities
bounded by the one-zero-frequency allowances in (2).

For completeness, the bounds summing its errors are elementary. Put
Y=X/g; only g≤2X occurs, so Y≥1/2. For any positive integer B,

    Σ_(Y<t≤2Y)t^(2/3)gcd(B,t)^(1/3)
      ≪Y^(5/3)τ(B)+Yτ(B),
    Σ_(Y<t≤2Y)gcd(B,t)/t ≪τ(B)(1+log(2Y)).

Expand the gcd by divisors for the first inequality and use
`#{t≤2Y:d|t}≤2Y/d+1`; expand `gcd(B,t)≤Σ_(d|B,d|t)d`
for the second. The plain reciprocal sum is O(1+log(2Y)).
Use τ(n)≪_η n^η, allocate η small relative to ε, and sum
`Σ_(g|D)g^(-5/3)≤Σ_(g≥1)g^(-5/3)`.
The discrepancy over all y and all g, for K rectangles, is therefore

    O_ε(K(ph)^2(1+|D|)^ε X^(5/3+ε)).

The area bracket contributes
`O_ε((1+|D|)^ε(X²/K+KX))`; the extra KX allows all endpoint
roundings. Choose K=max(1,floor(X^(1/6))). Both costs fit the error
in (4), since ph≤p²q. The divisor bound used here has the elementary
proof: for large primes ℓ, k+1≤ℓ^(ηk); for the finitely many remaining
primes the ratios (k+1)/ℓ^(ηk) have finite suprema. Multiplying the
prime-power bounds proves the claimed uniform constant.

### Averaging the exact arithmetic row density

Put

    β_h(y)=Σ_(g|gcd(D,y)) φ(phy/g)/(phy/g).

For every Y≥1,

    Σ_(y≤Y,gcd(y,qh)=1)β_h(y)
       =Y σ_(-1)(|D|)A_h + O(τ(|D|)(1+log(2Y))).  (7)

To prove this, put y=gt with g|D. Such g is coprime to pq. Expand

    φ(pht)/(pht)=φ(ph)/(ph)
        Σ_(d|t,gcd(d,ph)=1) μ(d)/d.

Coprimality of t with qh removes all d sharing a prime with pq and is
then imposed by the at most four divisors of rad(qh). Each floor error
is at most one. Summing 1/d costs at most 1+log(2Y) for each g.
Extending the d-sum to infinity costs O(1) per g, and adding g>Y
to the main term costs at most τ(|D|). The remaining absolutely
convergent product is exactly A_h.

The function F_R(y)/y on [X,2X] has supremum and total variation O(X),
uniformly in R. Indeed the strip is between two product thresholds
affine in y; the derivative of product area at a threshold is ρ_X,
which is bounded by log 2. The threshold derivatives are O(X) when
p/q∈[1/4,4]. Intersecting with the fixed R threshold preserves the
same variation bound. Partial summation in (7) therefore replaces
the row factor by its mean at cost O(Xτ(|D|)(1+log(2X))).

Finally, integrating first in y gives

    (1/(ph))∫_X^(2X) F_R(y) dy/y
       =(1/h)∫_0^R ρ_X(T−pt)ρ_X(T−qt) dt.

This follows by putting v=mn, w=(qv−D)/p and then v=T−pt;
`∫_X^(2X)1_(X<w/y≤2X)dy/y=ρ_X(w)`.
Together with (6) and (7), this proves (4).

## 3. Masked product-product main term

Inclusion–exclusion over h=1,p,q,pq removes p|r and q|r.
Partial summation weights the count by r. Its range is contained in
[0,6X²], so the error in (4) is multiplied by at most 12X².
Writing I=∫_0^(6X²)tρ_X(T−pt)ρ_X(T−qt)dt, the result is

    Σ_r r 1_(gcd(r,pq)=1)d_X(T−pr)d_X(T−qr)
      =S I+O_ε((pq)^4(1+|D|)^ε X^(23/6+ε)),        (8)

    S=ζ(2)^(-1)σ_(-1)(|D|)
      ·(p²−p+1)/(p(p+1))·(q²−q+1)/(q(q+1)).

No signed Möbius estimate is used in (8).

## 4. Exact conductor support of the coherent kernel

Let K(d,e) be the complete-period mean of
`1_(gcd(r,pq)=1)c_d(T−pr)c_e(T−qr)`.
Put u_0=1,u_1=−1 and t_(ℓ,0)=1−1/ℓ,t_(ℓ,1)=1/ℓ.
CRT and primitive additive-character orthogonality give

    K(d,e)=c_k(D)u_α t_(p,γ)t_(q,β)u_δ             (9)

when d=kp^αq^β, e=kp^γq^δ, gcd(k,pq)=1 and all four exponents are
0 or 1; K(d,e)=0 in every other case.

Outside pq, distinct prime-power conductors cannot cancel their
frequencies. Equal conductors pair the second primitive frequency
with −p/q times the first, leaving c_(ℓ^j)(D). At p the first argument
is always a unit, so its Ramanujan values are 1,−1,0 at exponents
0,1,≥2. The second argument, averaged with r≠0 mod p, has means
1−1/p,1/p,0 respectively: subtract the excluded residue class from
the full mean. At q the roles reverse. This proves (9).

The series Σ_(d,e)|K(d,e)|/(de) converges absolutely. The divisor
formula and absolute rearrangement give

    Σ_(k≥1)c_k(D)/k²=σ_(-1)(|D|)/ζ(2).

The identity Σ μ(n)/n²=1/ζ(2) follows by multiplying absolutely
convergent Dirichlet series and using Σ_(d|n)μ(d)=1_(n=1).
Summing the local 2×2 matrices in (9) now gives

    Σ_(d,e≥1)K(d,e)/(de)=S.                         (10)

## 5. Both mixed terms and the finite correction term

The finite product profile modulo L satisfies the exact identity

    ν_L(v)/L=Σ_(d|L)c_d(v)/d.                      (11)

Indeed ν_L(v)=Σ_(g|gcd(L,v))gφ(L/g), by separating the gcd of the
first multiplicand with L. Expanding each Ramanujan sum and using
Σ_(k|n)μ(k)/k=φ(n)/n proves (11).

Consider one mixed term, first without its archimedean weights.
After expanding R_Q, the e-th summand is a bounded periodic function
of v=mn, including v≡T mod p and the two r masks. A period is

    L=p lcm(e,p,q)≤p²qe.

Its modulus is at most one, since |c_e|≤e. On a rectangle of side
lengths at most X, counting each pair of residues gives the exact
complete-residue mean times its area, with error O(XL+L²).
Partitioning the product sublevel region into K rectangles adds
O(X²/K+KX) area/rounding cost. With K=max(1,floor(X^(1/4))) and
e≤Q, summing these bounds gives

    O(X^(7/4)(pqQ)^6)

for the unweighted mixed discrepancy, uniformly in the product cutoff.
This argument works for signed or complex periodic coefficients by
the triangle inequality; no positivity of the correction is assumed.

The complete mean is identified by (11). Formula (9) shows that every
nonzero d paired with e divides L, so the d|L sum in (11) is exactly
the full d≥1 sum in the mixed kernel. The possibly shorter effective
period of c_d(T−pr) divides L/p; the mask and the e-th factor also
have period dividing L/p. Thus no unproved equidistribution assertion
is used to identify the mean.

The archimedean factor rρ_X(T−qr) has supremum and total variation
O(X²) on the support. Partial summation yields

    Σ_r r mask·d_X(T−pr)ρ_X(T−qr)R_Q(T−qr)
      =I Σ_(d≥1,e≤Q)K(d,e)/(de)
         +O(X^(15/4)(pqQ)^6).                      (12)

Interchanging p,q proves the other mixed estimate. If the two product
supports do not overlap, these weighted expressions are all zero.

For the correction-correction term, each (d,e) summand has a period
at most pqde and bounded periodic coefficient. The weight
`rρ_X(T−pr)ρ_X(T−qr)` again has supremum and total variation O(X²).
Complete periods plus the final incomplete period therefore give

    Σ_r r mask·ρ_X(T−pr)R_Q(T−pr)ρ_X(T−qr)R_Q(T−qr)
      =I Σ_(d,e≤Q)K(d,e)/(de)+O(X²pqQ⁴).           (13)

This pays the actual finite endpoints of both mixed terms and of the
finite correction term separately.

## 6. The remaining tail and conclusion

Combining (8), (10), (12), (13), the coherent part of Γ is

    I Σ_(d,e≥1) K(d,e)/(de)1_(d>Q)1_(e>Q).         (14)

In (9), a surviving k must exceed Q/(pq). The absolute sum of the
two weighted local matrices is at most 4. For 0<θ<1, direct use of
the divisor formula gives

    Σ_(k>Y)|c_k(D)|/k²
      ≤ζ(2−θ)Y^(−θ)σ_(θ−1)(|D|).

To verify it, write k=em, bound |μ(m)| by one, and use
`1_(em>Y)≤(em/Y)^θ`. With θ=1/4, (14) is bounded by

    4ζ(7/4)I (Q/(pq))^(−1/4) σ_(-3/4)(|D|).       (15)

Uniformly in positive integer D,

    σ_(-3/4)(D)≤exp(C(log(2D))^(1/4)).

Its Euler factors have logarithms bounded by Cℓ^(-3/4). Split the
prime divisors at log(2D). Below that point the integer power sum is
O((log(2D))^(1/4)); above it, there are at most log D/log 2 prime
divisors, giving the same bound. The case D=1 is immediate.

Now pq≤exp(2(log X)^(1/4)), |D|≤6X²exp((log X)^(1/4)),
I≤C X⁴, and #P²≤exp(2(log X)^(1/4)). Consequently the sum of
(15) over p≠q is at most

    C X⁴ exp(−sqrt(log X)/4+O((log X)^(1/4))).

For the endpoint errors choose, for example, ε=1/120 in (8).
All factors involving p,q,Q and their number of pairs are
exp(O(sqrt(log X)))=X^o(1). Equations (8), (12), (13) therefore
sum to O(X^(4−1/12)) for sufficiently large X.
Both terms are bounded by the right side of (1), after increasing
the absolute threshold and constant. This proves (1) on paper.

## Attack and scope audit

- The excluded diagonal p=q would have D=0 and a divergent coherent
  kernel. It is not hidden in the estimate.
- Primes dividing T are excluded in the actual prime set. The local
  2×2 matrices would change for those primes.
- Both coprimality masks, the archimedean product density and all four
  finite endpoint estimates appear explicitly.
- The weak composite budget retains gcd(a,b,M); applying only the
  unit-coefficient estimate to every Fourier frequency would be invalid.
- No arbitrary Type II coefficient can be inserted into the rectangle
  completion argument. That remains a separate signed problem.
- The prime-divisor amplification of the flat row still loses
  H_P^(-1/2), and the coherent signed term still needs an actual averaged
  Möbius progression theorem. This paper does not prove Goldbach.
- Verdict: **BRIDGE**. The proof assembles classical finite arithmetic
  and Kloosterman completion for the exact centered source proposed in
  the RH-language research. No new scientific knowledge beyond the
  literature is claimed; no external novelty audit has been performed.

## Lean continuation

Formalize the dependency-closed composite estimate, then (2), then the
actual interval count and both mixed estimates. Conductor reduction is
under active leaf verification in `goldbach/KloostermanConductorReduction.lean`.
The complete theorem (1) has no Lean certificate yet. Keep that status
distinct from the already compiled collision classification and source
closure audits.
