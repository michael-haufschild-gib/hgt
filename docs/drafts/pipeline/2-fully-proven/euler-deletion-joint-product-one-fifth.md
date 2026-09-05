# A sharp one-fifth boundary for the joint deletion exponential product

**Stage:** dependency-closed paper proof. Convergence for actual moduli two and three is Lean-closed; general coprime moduli and sharpness remain paper-only.
**RH status:** no implication. **Novelty:** arithmetic specialization not certified; standard
signature and Banach-algebra arguments are explicitly reused.

## Statement and literal source

For coprime integers `P,Q>1`, put `a_P(n)=1-P[P divides n]`, `L=P*Q`, and
`v_j=a_P(j) X+a_Q(j) Y` for fixed `X,Y` in any complete complex normed unital algebra with
submultiplicative norm and `||1||=1`. All products below append factors on the right.

For every complex `s` with `Re(s)>1/5`, the literal chronological products

`U_N(s)=prod_{n=1}^N exp(n^(-s) (a_P(n) X+a_Q(n) Y))`

converge in algebra norm to a unit. No zero condition or commutation of `X,Y` is assumed.
There is one explicit finite-dimensional complex normed algebra, with fixed generators `X,Y`
and actual moduli `P=2,Q=3`, in which these products fail to converge for every real
`0<s<=1/5`. Thus the uniform assertion over target algebras cannot be extended below this
boundary. Individual targets may have additional cancellations and wider convergence.

This is an admission theorem for a jointly ordered arithmetic object. It does not show that
its limit equals the unit at a zeta zero or derive any critical-line constraint.

## 1. Exact complete-period cancellation through degree four

Let `B(z)=prod_{j=1}^L exp(z v_j)=1+sum_{r>=1} z^r C_r`. The coefficients are universal
noncommutative polynomials in `X,Y`. The finite theorem already verified in Lean constructs
the literal polygon with vertices `(n mod P,n mod Q)` and proves that every polynomial
one-form of coefficient degree at most three has zero integral.

Generalized Green's theorem kills all winding moments of degree at most two. Theorem 1 and
the proof of Corollary 2 of
[Boedihardjo–Ni–Qian (2014)](https://arxiv.org/pdf/1304.0755) then give zero log-signature
through degree four. Consequently the signature, and its evaluation at arbitrary `X,Y`, have

`C_1=C_2=C_3=C_4=0`.

For the concrete moduli-2-and-3 case, Lean now verifies these actual derivatives directly in
`EulerDeletionJointExponentialRemainder`, without any signature theorem. The published bridge
for the general coprime family remains part of the paper proof and is not yet formalized.
In particular it is not inferred from a vague assertion that all moments determine a signature.

For moduli two and three, the same verified arithmetic theorem gives `integral x*y^3 dx=1/10`.
The shuffle identity, since the path starts at the origin, expresses this as six times the sum
of the degree-five word coefficients

`XYYYX, YXYYX, YYXYX, YYYXX`.

Hence the universal coefficient `C_5` is nonzero. This is a symbolic identity, not a
numerical signature calculation.

## 2. A uniform frozen-block bound

Put `M=sum_{j=1}^L ||v_j||`. Absolute expansion of the finite product of exponentials gives

`||C_r|| <= sum_{r_1+...+r_L=r} prod_j ||v_j||^(r_j)/(r_j!) = M^r/r!`.

The finite multinomial identity proves the equality. Therefore

`||B(z)-1|| <= (M |z|)^5 exp(M |z|)/5!`.

All four lower coefficients vanish by Step 1. This estimate is valid in every target algebra
specified in the statement; no norm on an uncompleted infinite tensor space is assumed.

## 3. Actual weights versus one frozen weight per block

Write `w_n=n^(-s)`, `sigma=Re(s)>0`, `z_k=w_(kL+1)`, and

`B_k=prod_{j=1}^L exp(w_(kL+j) v_j)`.

Both the actual and frozen weights have absolute value at most one. For a fixed `v`,
`exp(av)` and `exp(bv)` commute with each other, even though different `v_j` need not
commute. The exponential series and
`exp(av)-exp(bv)=exp(bv)(exp((a-b)v)-1)` give a Lipschitz bound on `|a|,|b|<=1`.
Telescoping the **finite** product, with every factor bounded by `exp(||v_j||)`, yields a
constant `K` independent of `k` such that

`||B_k-B(z_k)|| <= K sum_{j=1}^L |w_(kL+j)-w_(kL+1)|`.

The right side is summable in `k`, since

`sum_k sum_{j=1}^L |w_(kL+j)-w_(kL+1)|`
`<= L sum_{n>=1} |w_(n+1)-w_n| < infinity`.

The last fact is already proved in the corpus for every `sigma>0` as
`RHTower.arithmeticDirichletWeight_summable_variation`. Thus block freezing has a summable
error; it does not replace the literal weights by a different source without control.

## 4. Convergence to a unit, including prefixes inside a block

When `5*sigma>1`, Step 2 gives `sum_k ||B(z_k)-1||<infinity` by the ordinary positive
power-series convergence test. Step 3 then gives `sum_k ||B_k-1||<infinity`.

Every `B_k` is a unit, with inverse given by the reversed product of negated exponentials,
and `||B_k^(-1)||<=exp(M)`. Thus

`||B_k^(-1)-1|| <= exp(M) ||B_k-1||`.

Both the chronological block products and their reversed inverse products converge; their
finite two-sided inverse identities pass to the limits. This is precisely the proved argument
of `GaloisForLFunctions.HTGeometry.NoncommutativeAbel.orderedProduct_converges_to_unit`.
It supplies a unit limit, not merely an arbitrary limit of units.

For `N=kL+r`, `0<=r<L`, the unfinished block has at most `L-1` factors. Its weights tend
to zero uniformly over this finite set, so this remaining product tends to `1`. Multiplying
by the bounded convergent block prefix proves convergence of **every** `U_N`, not just the
subsequence indexed by multiples of `L`.

## 5. Sharpness in one fixed truncated algebra

Let `A` be the complex vector space with basis all words on two letters of length at most
five. Multiply by concatenation when the resulting length is at most five, and by zero
otherwise. Equip it with the coefficient `l1` norm. Multiplication is associative,
submultiplicative, and the empty word is a norm-one unit. Finite dimension makes it complete.
Let `I` be the span of the nonempty words. Then `I^6=0`; take `X,Y` to be the one-letter
basis vectors. These choices are fixed independently of `s`.

For `P=2,Q=3`, Step 1 and nilpotence give the exact identity

`B(z)=1+z^5 C_5`, with `C_5 != 0`.

Moreover `C_5 I=I C_5=0`, so `B(z)` is central in this algebra and its inverse is
`1-z^5 C_5`.

For each real `sigma>0` define the actual blocks as above and set

`E_k=B(z_k)^(-1) B_k`.

Step 3, and the uniformly bounded frozen inverses, give
`sum_k ||E_k-1||<infinity`. The ordered products `E^(N)=E_0...E_(N-1)` therefore
converge. Each belongs to `1+I`. Centrality and `C_5^2=0` now give an **exact** identity
for every finite block prefix:

`B_0...B_(N-1) = E^(N) + C_5 sum_{k=0}^{N-1} (6k+1)^(-5*sigma)`.

Here `C_5 E^(N)=C_5` because `E^(N)-1` lies in `I`. Let `ell` be six times the sum of
the four word-coordinate maps displayed in Step 1. It is a continuous linear functional
with `ell(C_5)=1/10`. Thus its value on the actual product is a convergent term plus
`(1/10) sum_{k<N}(6k+1)^(-5*sigma)`. The latter tends to positive infinity for
`0<5*sigma<=1`, by comparison with the positive harmonic/power series. The block subsequence,
and hence the full literal product, cannot converge.

This argument controls the varying weights at the boundary too. It does not infer divergence
of a perturbed product merely from divergence of its frozen approximation.

## Concrete six-coordinate realization for the sharpness proof

The full truncated word algebra can be replaced by six-by-six coefficient arrays with ordinary
matrix multiplication. Let `E_ij` denote the array with its only nonzero entry, equal to one,
in position `(i,j)`. Set `X=E_01+E_12` and `Y=E_23+E_34+E_45`.
Every product of six generators vanishes; the only five-letter word with a nonzero value is
`XXYYY`, whose value is `E_05`. No spectral construction or spectral theorem enters this realization.

For a closed planar path the `XXYYY` coefficient is
`-(1/6) integral x*y^3 dx`: integrate at the second X, with prefix X integral `x` and
remaining triple Y integral `(-y)^3/3!`. Thus the frozen block is exactly
`1-(z^5/60)E_05`. The `(0,5)` coordinate supplies the nonzero scalar functional used in
Step 5, with negative rather than positive divergence. This realizes the same paper proof
in a smaller fixed target. These finite identities and the literal-source identification are now
Lean-closed in `EulerDeletionJointNilpotentWitness`, with a clean axiom audit and successful
narrow leaf build. The infinite corrected-product argument remains the Lean sharpness objective.

In this realization put `Z=E_05`, `q_k=z_k^5/60`, and `E_k=B_k+q_k Z`.
Since `Z^2=0` and every actual block satisfies `B_k Z=Z B_k=Z`, one has
`E_k-1=B_k-B(z_k)`. Thus the correction has summable displacement for every `Re(s)>0`.
Induction gives the exact identity

`B_0...B_(N-1)=E_0...E_(N-1)-(sum_{k<N}q_k)Z`.

This simpler form needs only convergence of the corrected product. Applying the `(0,5)`
coordinate reduces actual-product divergence to the nonsummability of
`(6k+1)^(-5*sigma)` for real `0<sigma<=1/5`.

## Proof and formalization boundary

The finite prefix, segment, CRT, low-degree, and nonzero-moment identities are Lean-closed in
`EulerDeletionJointPolygonMoment`. The concrete two-and-three derivative bridge and fifth-order
analytic remainder are Lean-closed in `EulerDeletionJointExponentialRemainder`.

`EulerDeletionJointProductOneFifth.sourceProduct_converges_to_unit` now proves the full
convergence assertion for **actual moduli two and three**, arbitrary target algebra and `X,Y`,
and every complex `s` with `Re(s)>1/5`. It controls actual within-block weights by a summable
error, proves convergence of the block inverse products, identifies exact source regrouping,
and handles every unfinished prefix. The scratch proof and six axiom audits passed; the narrow
leaf build passed. The source has no supplied zero, commutation, or cancellation premise.

The general-pair signature bridge and truncated-algebra sharpness theorem remain to be
formalized. The next exact objective is the fixed sharpness witness, including the effect of
varying weights. Proving only divergence of frozen blocks would not close that objective.

No numerical computation was needed. No global novelty certificate or qualifying RH proof
architecture is claimed. Convergence here reaches strictly left of the critical line and holds
without a zero hypothesis, so this admission property alone cannot select that line.
