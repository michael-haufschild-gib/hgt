# Prime dilation of the actual balanced product source

- **ID:** goldbach-prime-dilation-dispersion
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; actual signed-correlation attack, no Lean premise
- **Parent:** [Goldbach target](goldbach-unconditional-2026-10-23.md), Cycles 11 and 16
- **Sources:** `RHTower/MobiusFirstPrimeDilationCancellation.lean`, BVI residue compensation, and the actual product collision classification

## What changes after the smoothing failures

Both ordinary smoothing and removal of a fixed periodic profile leave too
much unsigned product energy. The next candidate acts on the actual Möbius
argument r=T−mn. For a prime p the exact sign law is

    μ(pr)=−μ(r)·1_(p∤r).

The coprimality mask is essential. The inspected RH source proves the
corresponding negative prime-ratio channels while explicitly retaining
their complementary channels. Its partial negative energy is not a bound
for the complete Goldbach covariance.

This route allows correspondences to depend on the product value. It does
not assert dense integral returns for a fixed family of projective maps.
Two distinct prime dilations produce the exact arithmetic incidence

    qmn−pm'n'=T(q−p).                                (D)

The right side is nonzero for T>0 and p≠q. The common-divisor and endpoint
costs must be retained before estimating the centered incidence.

## Exact first candidate: the flat balanced source

Let X be a positive integer tending to infinity, with integer target
`5X²≤T≤6X²`. Define d_X(v) as the number of products from `(X,2X]²`,
extended by zero to all integers. Define the real archimedean density

    ρ_X(v)=log(v/X²)       for X²≤v≤2X²,
           log(4X²/v)     for 2X²<v≤4X²,
           0              otherwise.

For integer Q≥1 put

    R_Q(v)=Σ_(d≤Q) c_d(v)/d,
    a_(X,Q)(v)=d_X(v)−ρ_X(v)R_Q(v),

where c_d is the classical Ramanujan sum, equivalently the integer divisor
sum `Σ_(e|gcd(d,v)) e μ(d/e)`. This is a specified finite correction,
not an unknown main term chosen to make the conclusion true.

For a fixed B>0 set

    Q=floor(exp(sqrt(log X))),
    P={p prime : (log X)^B<p≤exp((log X)^(1/4)), p∤T}.

These definitions are used only for sufficiently large X, when Q≥1.
For distinct p,q in P define the finite weighted covariance

    Γ_(T,X,Q)(p,q)
      =Σ_(1≤r≤6X²) r · 1_(p∤r and q∤r)
          ·a_(X,Q)(T−pr)·a_(X,Q)(T−qr).

**Candidate D:** for every A>0 there is B>0 such that, uniformly in the
displayed target range and for all sufficiently large X,

    Σ_(p,q∈P, p≠q) |Γ_(T,X,Q)(p,q)| ≪_A X⁴/(log X)^A.  (C)

This is an exact, falsifiable claim about actual integer products. Its
first unresolved point is the centered nonzero-determinant count (D).
The unsigned divisor bound does not imply (C). The local Ramanujan tail,
prime masks and finite interval endpoints must all be audited; no
dependency-closed proof or external novelty claim is made.

## Why this candidate would address a signed sum

The first intended signed target is

    B(T,X)=Σ_(m,n∈(X,2X]) μ(T−mn).

This is a necessary flat-source test of the broader Type II mechanism.
It is not the full marked, coefficient-weighted term from Cycle 11 and
is not an equivalent replacement for Goldbach. Every coefficient and
predecessor mark must be restored after this test is actually proved.

Set `θ_p=(p−1)/p²`, `H_P=Σ_(p∈P)θ_p`, and
`ω_P(r)=Σ_(p∈P)1_(p|r)`. The exact local product count for p∤T has main
term X²θ_p; for distinct p,q its pq counterpart has main term
X²θ_pθ_q. Counting interval residues gives error at most `2X+d`
for modulus d. Thus the d_X-weighted variance of ω_P has main bound
X²H_P; the accumulated boundary error is `X^(1+o(1))` for this prime
pool. Weighted Cauchy bounds the cost of replacing H_P by ω_P by
`O(X² sqrt(H_P))`, plus that explicit boundary error. Quantitative
Mertens estimates are required to verify H_P→∞ for this moving pool.

Finite rearrangement and the exact sign law give

    Σ_r μ(r)d_X(T−r)ω_P(r)
      =−Σ_(p∈P)Σ_(s≤6X²/p, p∤s) μ(s)d_X(T−ps).

Split d_X into its stated correction and a_(X,Q). For the residual,
Cauchy with weight 1/s bounds the square by a harmonic factor times
the sum of its weighted dilation covariances Γ, including the diagonal.
This is the reason for the weight s in (C).

The diagonal has an elementary candidate payment. Pointwise,
`d_X(v)²≤τ(v)²≤d_4(v)` and `|R_Q(v)|≤τ(v)(1+log Q)`.
For p∤T, a four-factor hyperbola decomposition gives

    Σ_(n≤N, n≡T mod p) d_4(n)
      ≪ (N/p)(1+log N)^3 + N^(3/4)(1+log N)^2.

Indeed choose a largest factor; the other three have product at most
N^(3/4), and the remaining factor lies in a single class modulo p.
This gives the displayed main count and one endpoint error per triple.
For the subpower prime pool it bounds the total weighted diagonal by
`O(X⁴ (log X)^4 Σ_(p∈P)p⁻²)`. Taking B sufficiently large pays this
term even after the harmonic Cauchy factor. These deductions still need
their exact finite Lean formulation; no diagonal estimate is imported
as a hypothesis.

The correction term requires an actual Möbius progression estimate.
The identity

    R_Q(v)=Σ_(e≤Q,e|v) Σ_(k≤Q/e) μ(k)/k

turns it into a weighted sum of arithmetic progression sums, with smooth
partial summation. The mask p∤s is removed by a second progression sum
at scale p². Both remain below the square-root progression range because
p and Q are subpower. A proof closure of the needed Möbius mean theorem,
uniform in the target residue, must be inspected or built; it is not
assumed here.

## Current attack obligations

1. Attack (C) for an omitted coherent mode, especially divisors of
   T(p−q), before formalizing any reduction as if it supplied cancellation.
2. The complete-residue local kernel and its centered tail have now been
   derived on paper below. Prove that the finite product incidence has
   this main term with a uniform endpoint error; a complete-period
   calculation alone does not give that transfer.
3. Search the corpus for a complete weighted determinant-discrepancy
   producer. Absolute Kloosterman norms or an unproved dispersion interface
   do not supply it.
4. Close the moving-prime-pool variance and progression dependencies.
5. Only after the flat-source signed estimate is proved, restore the
   actual Type II coefficients and predecessor marks. That extension is
   an additional problem, not an automatic consequence of the flat case.

No Lean theorem asserting (C), a signed saving, or Goldbach is added.
The original all-even proof remains the acceptance criterion.

## Preliminary local-tail attack

Distinct dilations have determinant D=T(q−p)≠0. The natural same-modulus
Ramanujan covariance has terms `c_d(D)/d²`. Its absolute tail can be
bounded without assuming cancellation. Using `|c_d(D)|≤gcd(d,D)`, expand
the gcd by its divisors. For any fixed 0<θ<1 this yields a bound by

    O_θ(Q^(−θ) Σ_(e|D)e^(−1+θ)).

For θ=1/4 the divisor sum is at most `exp(O((log(2|D|))^(1/4)))`:
bound its Euler factors geometrically, then split prime divisors at
log(2|D|). The small part is bounded by the corresponding integer power
sum; the large part uses the logarithmic bound on the number of distinct
prime divisors. Thus Q=exp(sqrt(log X)) pays this tail uniformly for
|D|=X^O(1). Replacing Q by Q/(pq) leaves the same saving for the stated
prime pool.

The calculation below now includes masks and cross-denominator terms.
The finite-interval discrepancy remains to be proved. A complete-period
calculation does not by itself estimate the actual product incidence.

The proposed analytic attack is to complete the reduced congruence in
one row variable and retain the other row's gcd with D. A square-root
Kloosterman producer could then pay the sum of the finite endpoint errors
for the flat source. Its exact modulus dependence, proof closure and
weighted completion cost must be established. This is not automatic for
the arbitrary Type II coefficients: an irregular coefficient can destroy
the cancellation used by an unweighted completion.

## Checked analytic source

The prime-modulus roots `WeilKloosterman.kloosterman_weil_bound` and
`RHTower.norm_kloostermanSum_le_weil` passed a direct leaf import and
`#print axioms` audit. Their closures contain only `propext`,
`Classical.choice`, and `Quot.sound`; the audit log is
`/tmp/hgt-goldbach-prime-dilation-source-audit.log`.
The first theorem constructs its finite-field extension input in its
proof; no analytic estimate is left as a premise of either root.

`KloostermanComposite.lean` also supplies twisted CRT multiplicativity
and the elementary stationary-phase bound `2p^ceil(k/2)` at odd prime
powers with unit inverse coefficient. Both roots passed the same direct
leaf audit with only the three standard foundational axioms; log:
`/tmp/hgt-goldbach-composite-source-audit.log`. These results do not
themselves prove the needed sum over composite row moduli, particularly
at primes dividing the determinant or a Fourier frequency.

## Complete-residue kernel, including both masks

This is a paper derivation, not a new Lean declaration or a proof of (C).
Write D=T(q−p), so D≠0 and gcd(D,pq)=1. For positive d,e let

    K(d,e)=mean_r [1_(gcd(r,pq)=1) c_d(T−pr)c_e(T−qr)],

where the mean is over one period lcm(d,e,pq). Define

    u_0=1, u_1=−1,
    t_(p,0)=1−1/p, t_(p,1)=1/p.

Then K(d,e) vanishes unless

    d=k p^α q^β,   e=k p^γ q^δ,
    gcd(k,pq)=1,   α,β,γ,δ ∈ {0,1}.

In the remaining cases its exact value is

    K(d,e)=c_k(D) u_α t_(p,γ) t_(q,β) u_δ.          (K)

Proof: CRT factors the finite mean. At a prime ℓ outside pq, primitive
additive-character orthogonality kills unequal conductor exponents.
For equal exponent j, the zero-frequency equation pairs the second
character with −p/q times the first; the remaining phase is D/q.
Multiplication by the unit q preserves the Ramanujan sum, giving
c_(ℓ^j)(D). At p, the first affine argument is a unit: its conductor-0
and conductor-1 values are 1 and −1, and every higher conductor vanishes.
The masked mean of the second argument is 1−1/p at conductor 0, 1/p
at conductor 1, and zero thereafter. For the middle value subtract
the excluded residue r=0, whose Ramanujan value is −1, from the zero
full mean. At higher conductor the excluded residue class consists of
unit arguments, where that Ramanujan sum is zero. At q the roles reverse.
These are exactly the four factors in (K).

The resulting full coherent coefficient is

    S=Σ_(d,e≥1) K(d,e)/(de)
     =ζ(2)^(-1) σ_(-1)(|D|)
       ·(p²−p+1)/(p(p+1)) ·(q²−q+1)/(q(q+1)).      (S)

This series is absolutely convergent: (K) leaves sixteen terms for
each k, and the divisor formula for c_k(D) gives absolute convergence
of Σ_k |c_k(D)|/k². The same formula gives
Σ_k c_k(D)/k²=σ_(-1)(|D|)/ζ(2). Removing the p,q Euler factors
divides by (1−p^(-2))(1−q^(-2)); summing the two local 2×2 matrices
then yields (S).

Let χ_Q(d)=1_(d≤Q). Subtracting both mixed coherent terms and adding
the finite R_Q–R_Q term leaves exactly

    Σ_(d,e≥1) K(d,e)/(de) (1−χ_Q(d))(1−χ_Q(e)).     (T)

Every surviving k in (K) exceeds Q/(pq). The absolute sum of the
weighted local matrix entries is at most 4. For 0<θ<1 the divisor
formula, triangle inequality and 1_(em>Y)≤(em/Y)^θ give

    Σ_(k>Y) |c_k(D)|/k²
      ≤ζ(2−θ) Y^(−θ) Σ_(e||D|) e^(θ−1).

Consequently (T) has absolute value at most

    4ζ(7/4) (Q/(pq))^(−1/4) σ_(-3/4)(|D|).

The uniform divisor estimate above makes this exp(−c sqrt(log X))
for the stated Q and prime pool, for some absolute c>0 and large X.
This closes the coherent-tail calculation on paper. It does not yet
identify that coefficient with the finite product count up to an error
small enough for (C).

## Finite-interval attack: exact congruence and remaining estimates

For h∈{1,p,q,pq}, imposing h|r handles the masks by inclusion–exclusion.
Fix the second row y=m'. The original equation is

    qmn−pyn'=D,   mn≡T (mod ph).

No solution exists when q|y or gcd(y,h)>1. Otherwise CRT combines
the two product congruences into mn≡A (mod L), where L=phy and
gcd(A,L)=gcd(D,y). The condition n'∈(X,2X] is the actual hyperbolic strip

    (D+pyX)/q < mn ≤ (D+2pyX)/q.

The complete-residue density in that strip is exactly

    ν_L(A)/L² = (1/(phy))
        Σ_(g|gcd(D,y)) φ(phy/g)/(phy/g).

For the arithmetic row factor β_h(y) given by the divisor sum, an
elementary expansion of φ(n)/n shows, uniformly in Y≥1,

    Σ_(y≤Y, gcd(y,qh)=1) β_h(y)
      =Y σ_(-1)(|D|) A_h + O(τ(|D|)(1+log Y)),

where A_1=ζ(2)^(-1)·p/(p+1)·q/(q+1), and
A_h=A_1 ∏_(ℓ|h)(1−1/ℓ). To see the error, put y=gt,
expand φ(pht)/(pht), and use the at most four divisors of rad(qh)
to impose coprimality. Each floor contributes at most one; summing
its coefficient 1/d costs at most 1+log Y for each g|D. Extending
the absolutely convergent d-sum and the g-sum costs O(τ(|D|)).
Integrating the strip in y gives the density ρ_X(T−pr)ρ_X(T−qr);
the four h-coefficients recover (S).

The next unresolved producer is a quantitative modular-hyperbola
discrepancy, retaining every nonunit gcd. A sufficient intermediate
bound is

    |S(a,b;M)|³ ≤ 512 τ(M)³ M² gcd(a,b,M).

Its [paper proof](../2-fully-proven/goldbach-composite-kloosterman-budget.md)
now uses the audited prime Weil bound, odd-prime-power stationary phase,
a sufficient two-adic eight-root bound, common-factor reduction and CRT.
The full bound has not yet been formalized. Conductor reduction is the
first active Lean step. Completing interval indicators would
then give the nonzero-frequency budget

    O(τ(M) M^(2/3) gcd(c,M)^(1/3) (1+log M)²),

with the separate one-zero-frequency costs
O(τ(M)(1+log M)(|U| gcd(c,M)+|V|)/M).
After m=gu and M=phy/g, summing rows should give X^(5/3+ε)
times explicit subpower factors. A partition into X^(1/6) strips
would then pay the hyperbolic boundaries with a power saving.
This paragraph is a proof plan, not an established finite-interval bound.
Both mixed terms require their own endpoint audit; the complete-residue
kernel alone must not be substituted for those estimates.

Even a proof of (C) would initially yield only the flat-source signed
test. The elementary prime-divisor variance loses H_P^(-1/2), with
H_P of order log log X; no arbitrary logarithmic saving or marked
Type II estimate follows automatically.
