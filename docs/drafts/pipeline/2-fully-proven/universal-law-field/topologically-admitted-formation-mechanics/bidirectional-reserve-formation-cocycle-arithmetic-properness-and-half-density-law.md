# Bidirectional reserve-formation cocycle, arithmetic properness, and half-density law

**Card ID:** ULF-TAFM-27  
**Status:** Fully proved on paper; Lean-certified  
**Programme:** Universal law field / topologically admitted formation mechanics  
**Field candidate:** Bidirectional reserve-formation geometry  
**Scope:** Route-independent fusion, reflection, positivity, recurrence, and literal arithmetic

## 1. Result

The primitive is an **unreduced bidirectional history**, not a scalar route endpoint.  In one
ordered additive channel it is a pair

\[
  x=(x^+,x^-)
\]

in a linearly ordered abelian group.  Formation is componentwise addition and reflection is

\[
  \rho(x^+,x^-)=(x^-,x^+).
\]

Define current, visible variation, reserve, and total activity by

\[
  j(x)=x^+-x^-,\qquad
  V(x)=|j(x)|,\qquad
  R(x)=\min(x^+,x^-),\qquad
  A(x)=x^++x^- .                                      \tag{1}
\]

For two formation histories define the reserve transgression

\[
  \kappa(x,y)=R(x+y)-R(x)-R(y).                         \tag{2}
\]

Then the following are unconditional.

### Theorem A -- reserve-formation laws

For all histories `x,y,z`:

1. **joint reconstruction**

   \[
     A(x)=V(x)+2R(x);                                   \tag{3}
   \]

2. **nonnegative fusion curvature**

   \[
     \kappa(x,y)\ge0;                                   \tag{4}
   \]

3. **exact visible/reserve conservation**

   \[
     V(x)+V(y)=V(x+y)+2\kappa(x,y);                     \tag{5}
   \]

4. **associative cocycle law**

   \[
   \kappa(x,y)+\kappa(x+y,z)
   =\kappa(y,z)+\kappa(x,y+z);                          \tag{6}
   \]

5. **reflection law**

   \[
   j(\rho x)=-j(x),\qquad
   (A,V,R)(\rho x)=(A,V,R)(x),qquad
   \kappa(\rho x,\rho y)=\kappa(x,y).                  \tag{7}
   \]

Thus disappearance of visible current under composition is neither erasure nor cancellation by
definition.  It creates exactly half as much hidden reserve.  Equation (6) says this reserve birth
is independent of parenthesization.

If the two currents have the same sign, `κ(x,y)=0`.  If they have opposite signs, then

\[
  \kappa(x,y)=\min(V(x),V(y)).                           \tag{8}
\]

So `κ` is precisely cross-direction annihilation, not arbitrary slack.

### Theorem B -- arithmetic realization and global properness

Let `a,b` be positive integers, let

\[
  g=\gcd(a,b),\qquad a_0=a/g,\qquad b_0=b/g.
\]

The unreduced arithmetic history `(a,b)` has unique primitive observer `(a₀,b₀)` and diagonal
reserve `g`.  They obey

\[
  ab=(a_0b_0)g^2                                       \tag{9}
\]

and therefore

\[
  \log(ab)=\log(a_0b_0)+2\log g.                       \tag{10}
\]

For a second history `(c,d)`, put

\[
  K(a,b;c,d)=
  \frac{\gcd(ac,bd)}{\gcd(a,b)\gcd(c,d)}.              \tag{11}
\]

The denominator divides the numerator, and the exact multiplicative fusion law is

\[
 \frac a{\gcd(a,b)}\frac b{\gcd(a,b)}
 \frac c{\gcd(c,d)}\frac d{\gcd(c,d)}
 =
 \frac {ac}{\gcd(ac,bd)}\frac {bd}{\gcd(ac,bd)}
 K(a,b;c,d)^2.                                         \tag{12}
\]

Taking logarithms gives the arithmetic instance of (5).  Prime by prime, the valuation of `K` is
the ordered-group transgression `κ`.

Formation is globally proper before observer quotienting: for every natural bound `B`, the set

\[
  \{(a,b)\in\mathbf N_{>0}^2:ab\le B\}                 \tag{13}
\]

is finite.  Yet the primitive observer is not proper.  Every `(k,k)` projects to the same primitive
ray `(1,1)` while its activity is `k²`.  More sharply,

\[
 (a,1)(1,a)=(a,a),                                     \tag{14}
\]

so fusion of a history with its reflection closes the observer current and transfers the entire
visible activity into diagonal reserve.  This is an exact closed-observer/open-history law.

### Theorem C -- unique reflected half-density quotient

For real `α,β` define the logarithmic monomial potential

\[
 \Phi_{\alpha,\beta}(r;x,y)=r-\alpha x-\beta y.         \tag{15}
\]

The diagonal gauge is

\[
 (r;x,y)\longmapsto(r+t;x+t,y+t),                       \tag{16}
\]

and reflection swaps `x,y` while fixing `r`.  Then:

\[
 \Phi_{\alpha,\beta}\text{ is diagonal-gauge invariant}
 \iff \alpha+\beta=1,                                  \tag{17}
\]

\[
 \Phi_{\alpha,\beta}\text{ is reflection invariant}
 \iff \alpha=\beta,                                    \tag{18}
\]

and hence

\[
 \Phi_{\alpha,\beta}\text{ obeys both laws}
 \iff \alpha=\beta=\tfrac12.                           \tag{19}
\]

When `r=R(x)` and `(x,y)=(x⁺,x⁻)`, the unique potential is

\[
 \Phi_{1/2,1/2}(R(x);x^+,x^-)=-\frac12V(x).             \tag{20}
\]

Positivity is therefore the exponential quotient

\[
 \exp\Phi_{1/2,1/2}=\exp(-V/2).                         \tag{21}
\]

It forgets orientation `sign(j)` and diagonal reserve, but not visible magnitude.  Half-density is
forced jointly by diagonal descent and reflection; neither law selects it alone.

### Theorem D -- adelic Haar, KMS, and Selberg are one quotient

For the arithmetic history `(a,b)`, (20) becomes

\[
 \exp\Phi_{1/2,1/2}
 =\frac{\gcd(a,b)}{\sqrt{ab}}
 =\frac1{\sqrt{a_0b_0}}.                                \tag{22}
\]

Let `μ` be normalized Haar measure on the rational finite adeles, so the literal compact-open
lattice satisfies

\[
  \mu(n\widehat{\mathbf Z})=n^{-1}.                     \tag{23}
\]

Since

\[
 a\widehat{\mathbf Z}+b\widehat{\mathbf Z}
   =\gcd(a,b)\widehat{\mathbf Z},\qquad
 a\widehat{\mathbf Z}\cap b\widehat{\mathbf Z}
   =\operatorname{lcm}(a,b)\widehat{\mathbf Z},         \tag{24}
\]

and `gcd(a,b) lcm(a,b)=ab`, one gets

\[
 \frac{\gcd(a,b)}{\sqrt{ab}}
 =\sqrt{\frac{\gcd(a,b)}{\operatorname{lcm}(a,b)}}
 =\sqrt{
   \frac{\mu(\operatorname{lcm}(a,b)\widehat{\mathbf Z})}
        {\mu(\gcd(a,b)\widehat{\mathbf Z})}}.           \tag{25}
\]

The same coefficient is:

- the diagonal-gauge-corrected geometric mean of the KMS/Haar masses `a⁻¹,b⁻¹`;
- the critical half-density on the primitive valuation current;
- the square root of the relative Haar mass of the lattice interval from sum to intersection;
- the Balasubramanian--Conrey--Heath-Brown/Selberg gcd weight on a twisted second-moment ray.

Equation (25) is a prediction of the mechanism in a fourth organ.  It was not inserted from the
Selberg formula: it is forced by (17)--(19), then agrees exactly with the independently present
critical-line coefficient.

## 2. Proof of Theorem A

Write `p=x⁺` and `q=x⁻`.  In any linearly ordered abelian group,

\[
 \max(p,q)+\min(p,q)=p+q                              \tag{26}
\]

and

\[
 \max(p,q)-\min(p,q)=|p-q|.                          \tag{27}
\]

Substituting `max=min+|p-q|` into (26) proves (3).

Translation preserves order, and hence

\[
 \min(p,q)+\min(r,s)\le\min(p+r,q+s).                 \tag{28}
\]

Equation (28) is exactly `κ(x,y)≥0`, proving (4).

Apply (3) to `x`, `y`, and `x+y`.  Total activity is additive:

\[
 A(x+y)=A(x)+A(y).                                    \tag{29}
\]

Consequently

\[
\begin{aligned}
 V(x)+V(y)+2R(x)+2R(y)
   &=V(x+y)+2R(x+y),
\end{aligned}
\]

which rearranges to (5).

For (6), expand both sides from definition (2).  Each equals

\[
 R(x+y+z)-R(x)-R(y)-R(z).                              \tag{30}
\]

Reflection negates `p-q`, preserves its absolute value, preserves `p+q` and `min(p,q)`, and
commutes with componentwise addition.  This proves (7).

If both currents are nonnegative, `q≤p` and `s≤r`; all three reserves in (2) are respectively
`q,s,q+s`, so `κ=0`.  The nonpositive case is identical after reflection.  In the opposite-sign
case write `p=q+u` and `s=r+v` with `u,v≥0`.  Then

\[
 R(x+y)=q+r+\min(u,v),
\]

while `R(x)=q`, `R(y)=r`, proving (8).

## 3. Proof of Theorem B

The divisibilities `g|a` and `g|b` give `a=ga₀`, `b=gb₀`.  Multiplication yields (9), and
positivity permits the logarithm law (10).  Standard gcd cancellation shows `gcd(a₀,b₀)=1`.
Conversely, if `(a,b)=(ha₁,hb₁)` with `gcd(a₁,b₁)=1`, then

\[
 \gcd(a,b)=h\gcd(a_1,b_1)=h,
\]

so the primitive-ray/reserve factorization is unique.

Put `g₁=gcd(a,b)` and `g₂=gcd(c,d)`.  Then `g₁g₂` divides both `ac` and `bd`, hence divides
`g₃=gcd(ac,bd)`.  Thus `K=g₃/(g₁g₂)` is an integer.  Apply (9) to each input and to the product:

\[
 ab=(a_0b_0)g_1^2,
 \quad cd=(c_0d_0)g_2^2,
 \quad acbd=(e_0f_0)g_3^2.
\]

Because `g₃=g₁g₂K`, cancellation gives (12).

At prime `p`, valuations turn multiplication into componentwise addition and gcd into minimum:

\[
 v_p(ac)=v_p(a)+v_p(c),\qquad
 v_p(\gcd(a,b))=\min(v_p(a),v_p(b)).                   \tag{31}
\]

Taking valuations of (11) identifies `v_p(K)` with (2).  Taking the finite `log p`-weighted sum
of (5) proves the logarithmic form of (12).

If `a,b≥1` and `ab≤B`, then `a≤B` and `b≤B`.  The set in (13) is a subset of the finite square
`{1,...,B}²`; hence it is finite.  Equations (14) and (9) prove the recurrence/open-lift claim.

## 4. Proof of Theorem C

Under (16), direct subtraction gives

\[
 \Phi(r+t;x+t,y+t)-\Phi(r;x,y)
 =(1-\alpha-\beta)t.                                  \tag{32}
\]

This vanishes for all `t` iff `α+β=1`, proving (17).  Reflection gives

\[
 \Phi(r;y,x)-\Phi(r;x,y)
 =(\alpha-\beta)(x-y).                                \tag{33}
\]

This vanishes for all `x,y` iff `α=β`, proving (18).  Solving the two linear equations gives (19).
Finally (3) gives

\[
 R-\frac{x^++x^-}{2}
 =R-\frac{V+2R}{2}=-\frac V2,
\]

which proves (20)--(21).

## 5. Proof of Theorem D

Apply (20) in every prime-valuation channel and sum with weight `log p`.  Unique factorization gives

\[
 \sum_p \min(v_p(a),v_p(b))\log p=\log\gcd(a,b)
\]

and

\[
 \sum_p(v_p(a)+v_p(b))\log p=\log(ab).
\]

Exponentiation yields the first equality in (22).  Equation (9) gives the second.

The corpus already proves (23) for the actual rational finite-adele ring.  The local valuation
description of sum and intersection proves (24).  Finally

\[
 \frac{
   \mu(\operatorname{lcm}(a,b)\widehat{\mathbf Z})}
   {\mu(\gcd(a,b)\widehat{\mathbf Z})}
 =\frac{1/\operatorname{lcm}(a,b)}{1/\gcd(a,b)}
 =\frac{\gcd(a,b)}{\operatorname{lcm}(a,b)}
 =\frac{\gcd(a,b)^2}{ab}.
\]

All quantities are positive, so taking the positive square root proves (25).

## 6. What this changes in the universal-law frontier

Earlier ULF work had the ingredients separately:

- carry traffic exceeded signed current by twice counterflow;
- positive integer pairs admitted a primitive-ray/gcd partition;
- finite adeles supplied index and Haar mass;
- half-density and KMS shadows appeared in multiple routes;
- compact recurrence could coexist with open lifted history.

The new content is their one generating law.  Reserve is not an extra coordinate: it is forced by
joint reconstruction (3).  Its birth under fusion is not a metaphor: it is the nonnegative cocycle
(2), obeying (5)--(6).  Arithmetic gcd is not an analogy: it is the literal integrated reserve.
Half-density is not chosen: it is uniquely forced by diagonal gauge and reflection.  Selberg's gcd
weight and the adelic lattice interval are therefore two shadows of the same quotient.

This closes two previously open formation gates:

1. **literal divisor-independent intervention signature:** every prime channel uses
   `(current,visible,reserve,transgression)` with the same relation table (3)--(7);
2. **global source properness:** unreduced positive arithmetic histories have finite activity
   sublevels, while observer recurrence remains compatible with unbounded reserve fibres.

It also changes the remaining RH producer.  Compactness of the reduced observer is not enough, and
boundedness of all raw history is wrong because the source may accumulate reflection-even reserve.
The correct selection target is now:

> prove from the completed arithmetic source that Xi-divisor formation has no cofinal
> cross-orientation reserve production, or that its reserve production is sublinear relative to
> the source-derived primitive-current budget.

By (5), either statement forces visible-current additivity and removes the only channel by which a
closed reflected observer can hide off-neutral formation.  This target is still open and is not
renamed RH: it is a pre-divisor law about the actual source formation process.

## 7. Hostile audit and limitations

1. **Not an RH proof.**  No theorem above bounds reserve production for the completed Xi source.
2. **Not scalar compact descent.**  The scalar modular log is retained as current; the diagonal
   reserve lost by scalar descent is now part of the state.
3. **Not determinant-line repackaging.**  Determinant and Fredholm defects are readouts of local
   visible/reserve balance.  They do not define the primitive.
4. **Not the old carry theorem.**  The previous traffic identity had no associative formation
   transgression, arithmetic gcd integration, half-density uniqueness, or adelic lattice law.
5. **Not the old primitive-ray theorem.**  The previous equivalence partitioned pairs but did not
   identify common-scale birth under composition as a nonnegative cocycle.
6. **Known-parent collision accepted.**  Jordan decomposition in ordered groups, gcd/lcm,
   finite-adele Haar scaling, KMS weights, and Selberg normalization are known.  Novelty is not the
   criterion.  Their forced coupling and resulting source obligation are the point.
7. **Hypertranscendence remains only structurally housed.**  Infinite prime-channel support and
   unbounded reserve/current rank fit the mechanism, but no new HT theorem is claimed here.

## 8. Lean certificate

Formalized exactly in:

- `GaloisForLFunctions.HTGeometry.BidirectionalReserveFormation`: ordered-group reconstruction,
  transgression nonnegativity, visible/reserve conservation, cocycle, reflection, and
  diagonal-gauge/reflection uniqueness of exponent `1/2`;
- `GaloisForLFunctions.RHTower.BidirectionalReserveArithmeticAdelicFormation`: arithmetic
  reduced-product reconstruction, cross-gcd fusion, finite activity sublevels, unbounded diagonal
  observer fibre, reflected closure, actual rational finite-adele Haar mass, critical reduced-ray
  coefficient, and closed capstone.

No stronger source-selection statement is included. Direct foreground elaboration and targeted
leaf build pass; both modules are wired into the universal-law and area umbrellas without umbrella
builds. Capstone axiom audit uses only standard foundations.
