# A sharp one-fifth boundary for the joint deletion exponential product

**Stage:** 3-formalized; dependency-closed paper proof, fully formalized. Convergence is Lean-closed for **every**
coprime pair of moduli; the sharpness witness is Lean-closed in the fixed six-coordinate target at
the actual moduli two and three.
**RH status:** no implication. **Novelty:** arithmetic specialization not certified; standard
Banach-algebra arguments are explicitly reused, and the low-degree shuffle calculus replacing the
published signature bridge is elementary.

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

Let `B(z)=prod_{j=1}^{L} exp(z v_j)=1+sum_{r>=1} z^r C_r`. The coefficients are universal
noncommutative polynomials in `X,Y`. The literal polygon has vertices `(n mod P,n mod Q)`, closes
after one common period, and CRT factorization of its segment densities makes **every** polynomial
one-form of coefficient degree at most three have zero circulation. This finite arithmetic theorem
is Lean-closed for all coprime pairs in `EulerDeletionJointPolygonMoment`.

The passage from those circulations to `C_1=C_2=C_3=C_4=0` is now carried out by an elementary
shuffle calculus rather than by a published signature theorem. Expand the chronological product as
a formal power series over the `2^r` ordered words of length `r`; the scalar attached to a word is
its literal iterated-integral coefficient `c_w`, defined by appending one straight segment at a
time. Two exact families of identities hold after **every** number of segments, each proved by
induction on the segment count from the one-segment expansion:

* the shuffle relations `c_u c_v = sum_{w in u ⧢ v} c_w` for every pair of words with
  `|u|+|v| <= 4`, and
* the identification of each monomial circulation with an explicit word combination, for example
  `∮ x dy = c_{xy}`, `∮ x^2 dy = 2 c_{xxy}`, `∮ x^3 dy = 6 c_{xxxy}` and
  `∮ x^2 y dy = 2 (c_{xxyy}+c_{xyxy}+c_{yxxy})`.

At the closed period both displacements vanish, so every shuffle right-hand side vanishes, and the
resulting linear system has only the zero solution. Explicitly: `c_x=c_y=0` and the solved forms
`c_{xx}=c_x^2/2`, `c_{xxx}=c_x^3/6`, `c_{xxxx}=c_x^4/24` kill the pure words; the circulations of
degree at most two kill `c_{xy}`, `c_{yx}`, `c_{xxy}`, `c_{yyx}`; the shuffle relations
`x ⧢ xy`, `x ⧢ yx`, `y ⧢ yx`, `y ⧢ xy` then kill the remaining degree-three words; the degree-three
circulations kill `c_{xxxy}` and `c_{yyyx}`; the relations `x ⧢ xxy`, `x ⧢ xyx`, `x ⧢ yxx` and their
mirror images kill the four-letter words with a single minority letter; and for the six balanced
words the relations `xy ⧢ xy`, `y ⧢ xxy`, `x ⧢ xyy`, `x ⧢ yxy`, `x ⧢ yyx` together with the single
mixed circulation `∮ x^2 y dy = 0` force all six to vanish. Consequently the signature, and its
evaluation at arbitrary `X,Y` in any ring, have

`C_1=C_2=C_3=C_4=0`.

This replaces the earlier appeal to generalized Green's theorem together with Theorem 1 and the
proof of Corollary 2 of [Boedihardjo–Ni–Qian (2014)](https://arxiv.org/pdf/1304.0755); that route
remains a correct alternative, but the present argument is dependency-closed inside the corpus and
is the one formalized. The concrete moduli-2-and-3 derivatives verified earlier in
`EulerDeletionJointExponentialRemainder` are now a special case.

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
narrow leaf build. The infinite corrected-product argument is also Lean-closed in
`EulerDeletionJointProductSharpness`.

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

The passage from the degree-three circulations to `C_1=C_2=C_3=C_4=0` is Lean-closed for **all**
coprime pairs in two new modules. `EulerDeletionSignatureWordExpansion` expands a chronological
exponential product as a formal power series over ordered words, identifies the integer-normalized
jet with the factorial multiple of the word coefficient, and proves every shuffle relation of total
degree at most four for an arbitrary velocity list. `EulerDeletionCoprimePolygonSignature`
identifies the seven monomial circulations with explicit word combinations and derives that all
thirty word coefficients of length one to four vanish over one common period; its
`jet_sourceVelocity_eq_zero` has no premise beyond coprimality.

`EulerDeletionJointProductOneFifth.sourceProduct_converges_to_unit` proves the convergence
assertion for the actual moduli two and three, and
`EulerDeletionCoprimeJointProduct.sourceProduct_converges_to_unit` proves it for **every** coprime
pair, arbitrary target algebra and `X,Y`, and every complex `s` with `Re(s)>1/5`. Both control
actual within-block weights by a summable error, prove convergence of the block inverse products,
identify exact source regrouping, and handle every unfinished prefix. Neither supplies a zero,
commutation, or cancellation premise.

Step 2 is Lean-closed exactly as displayed. `norm_coeff_expProd_le` is the multinomial coefficient
estimate `||C_r|| <= M^r/r!`; `tsum_exponentialWord` identifies the chronological product with its
absolutely convergent word series; and `norm_exponentialWord_sub_one_le` gives the explicit
remainder `||B(z)-1|| <= (M|z|)^5 exp(M|z|)/5!` for every factor list whose jets vanish through
order four. The convergence modules use the equivalent asymptotic form `B(z)-1 = O(|z|^5)`,
obtained from the same vanishing jets by the power-series partial-sum comparison.

`EulerDeletionJointProductSharpness` proves the exact corrected-product decomposition for the
actual weights, summability of the correction error throughout `Re(s)>0`, and nonconvergence
in the fixed six-coordinate target for every real `0<s<=1/5`. Its
`positive_real_convergence_iff` classifies convergence in this target exactly by `s>1/5`.
The boundary theorem `oneFifth_sourceProduct_not_convergent` has no supplied premise.
No formalization obligation of this card remains open.

The RH-producing relation is still missing. Further work must obtain a relation forced by an
actual zeta zero and show why an off-line zero cannot satisfy it. Neither the verified product's
existence nor its now-sharp one-fifth boundary supplies that relation.

No numerical computation was needed. No global novelty certificate or qualifying RH proof
architecture is claimed. Convergence here reaches strictly left of the critical line and holds
without a zero hypothesis, so this admission property alone cannot select that line.

## Lean certificate

**Stage:** 3-formalized, for **every** coprime pair of moduli. **RH implication:** none.
**Novelty:** not certified. The [fixed-target sharpness](euler-deletion-joint-product-sharpness.md)
witness is Lean-closed at the actual moduli two and three.

For `a_p(n)=1-p[p divides n]`, coprime moduli `P,Q>1`, arbitrary `X,Y` in any complete complex
normed unital algebra, and every complex `s` with `Re(s)>1/5`, Lean proves that

`prod_{n=1}^N exp(n^(-s)*(a_P(n)X+a_Q(n)Y))`

converges to a unit as `N` tends to infinity. No zero, commutation or cancellation premise is
supplied. The theorem covers the actual weights and every partial prefix, not only the block
subsequence.

Five modules carry the proof.

`EulerDeletionJointPolygonMoment` closes the finite arithmetic input. CRT factorization of the
segment densities of the literal polygon with vertices `(n mod P, n mod Q)` makes every polynomial
one-form of coefficient degree at most three have zero circulation over one common period
(`circulation_low_degree`), and gives the exact nonzero mixed moment
`integral x*y^3 dx = P(P-1)Q(Q-1)(Q-2)/120` (`circulation_one_three`).

`EulerDeletionSignatureWordExpansion`, namespace `RHTower.SignatureWords`, expands a chronological
exponential product as a formal power series over the `2^k` ordered words of each length.
`coeff_pathSeries` is the exact word expansion; `jet_eq_coeff` identifies the integer-normalized
chronological jet with the factorial multiple of the word coefficient; `jet_eq_zero_of_pathCoef`
transports vanishing word coefficients to a vanishing jet in **every** ring and for arbitrary
noncommuting generators; `norm_coeff_expProd_le` is the finite multinomial estimate
`||C_r|| <= M^r/r!`, `tsum_exponentialWord` identifies the product with its absolutely convergent
word series, and `norm_exponentialWord_sub_one_le` is the explicit fifth-order remainder
`||B(z)-1|| <= (M||z||)^5 exp(M||z||)/5!`. The file also proves every shuffle relation of total
degree at most four for an arbitrary velocity list, each an exact identity valid after every
number of segments.

`EulerDeletionCoprimePolygonSignature`, namespace `RHTower.DeletionPolygonSignature`, identifies
the seven monomial circulations with explicit word combinations — `mom_xy`, `mom_yx`, `mom_xxy`,
`mom_yyx`, `mom_xxxy`, `mom_yyyx` and `mom_xxyy` — and proves each of the thirty word coefficients
of length one to four zero over one common period. The capstone `pathCoef_period_eq_zero` and its
jet forms `jet_deletion_velocity_eq_zero` and `jet_sourceVelocity_eq_zero` have no premise beyond
coprimality. No path-signature theorem and no external result is imported.

`EulerDeletionJointExponentialRemainder` and `EulerDeletionJointProductOneFifth` close the actual
moduli two and three, the latter with capstone `sourceProduct_converges_to_unit`.

`EulerDeletionCoprimeJointProduct`, namespace `RHTower.DeletionCoprimeProduct`, closes every
coprime pair at a general block length: `exponentialWord_remainder` turns vanishing jets through
order four into a fifth-order analytic remainder, `sourceBlock_remainder` applies it to the
coprime period block, `summable_actual_block_error` controls the actual within-block weights by a
summable freezing error, `variableBlock_inverse_pair` supplies two-sided inverse blocks from
reversed products of negated exponentials, `sourceProduct_block_mul` is the exact regrouping, and
`sourceProduct_converges_to_unit` is the premise-free capstone.

`lake env lean` passed on every module. Twenty-five axiom audits — `coeff_pathSeries`,
`jet_eq_coeff`, `jet_eq_zero_of_pathCoef`, `norm_coeff_expProd_le`, two shuffle relations,
`mom_xxyy`, `mixed_quartic_zero`, `pathCoef_period_eq_zero`, both jet forms,
`exponentialWord_remainder`, `sourceBlock_remainder`, `summable_actual_block_error`,
`actual_blocks_converge_to_unit`, `sourceProduct_converges_to_unit` and the attenuation-side
capstones — report only `propext`, `Classical.choice` and `Quot.sound`. The narrow final
`lake build` of the three new modules passed and all are wired into the `RHTower` umbrella; no
full or umbrella build ran. Repository-wide `scripts/formal_tools.py lint` passed with every module of this card wired into the `RHTower` umbrella; a later rerun failed only on another session's unwired module `RHTower.Sieve.MenonHarmonicBlockLevelSplitHM`, which names none of this card's modules. No numerical computation and no external proof certificate was used.

Convergence on a region crossing the critical line is not a critical-line selector. The
RH-producing relation is still missing: the paper proof above gives the sharpness witness and the
complete formalization boundary.
