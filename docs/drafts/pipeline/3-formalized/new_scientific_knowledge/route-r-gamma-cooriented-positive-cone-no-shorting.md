# Route R Gamma-cooriented positive-cone no-shorting

- **ID:** `route-r-gamma-cooriented-positive-cone-no-shorting`
- **Stage:** `3-formalized`
- **Type:** THEOREM
- **Route:** R
- **Status:** dependency-closed paper proof and unconditional Lean formalization

## Statement

For a prime-power cell $i=(p,e)$, write

\[
 h_i=\frac{e+1}{2}\log p>0,
 \qquad b_i=\xiGammaEulerPrimitiveBoundaryAmplitude(0,i)>0,
 \qquad r_i=-2h_i.
\]

The actual reflection-odd promoted Gamma exterior is

\[
 D_a(i,j)
 =b_i b_j(h_i-h_j)\sinh\bigl(a(r_i+r_j)\bigr).
 \tag{1}
\]

For distinct cells, define the source-cooriented exterior

\[
 C_a(i,j)=(h_j-h_i)D_a(i,j)
 \tag{2}
\]

and the removable positive gauge

\[
 G_a(i,j)=
 \begin{cases}
 -b_i b_j(h_i-h_j)^2(r_i+r_j),&a=0,\\[1mm]
 -b_i b_j(h_i-h_j)^2
   \dfrac{\sinh(a(r_i+r_j))}{a},&a\ne0.
 \end{cases}
 \tag{3}
\]

Then, unconditionally,

\[
 \boxed{C_a(i,j)=aG_a(i,j),\qquad G_a(i,j)>0.}
 \tag{4}
\]

Consequently, for every finite cell-pair packet $S$, nonnegative weights
$w_{ij}$, at least one strictly positive weight, and every $a\ne0$,

\[
 \boxed{
 a\sum_{(i,j)\in S}w_{ij}C_a(i,j)>0.}
 \tag{5}
\]

In particular, a nonzero positive cooriented combination of actual
prime-power/Gamma boundary defects cannot be a source null-homotopy away
from the critical section.

The same conclusion holds for the complete countable pair field whenever
the positive gauge-weighted family is summable: nonnegative weights with at
least one positive coordinate give

\[
 a\sum_{i,j}w_{ij}C_a(i,j)
 =a^2\sum_{i,j}w_{ij}G_a(i,j)>0.
 \tag{6}
\]

## Proof

Expanding the two modular currents and taking the reflection-odd part gives

\[
 \begin{aligned}
 D_a(i,j)
 &=\frac{b_ib_j(h_i-h_j)}2
   \left(e^{a(r_i+r_j)}-e^{-a(r_i+r_j)}\right)\\
 &=b_ib_j(h_i-h_j)\sinh\bigl(a(r_i+r_j)\bigr),
 \end{aligned}
\]

which is (1). Multiplication by $h_j-h_i=-(h_i-h_j)$ yields

\[
 C_a(i,j)=-b_ib_j(h_i-h_j)^2
   \sinh\bigl(a(r_i+r_j)\bigr).
 \tag{7}
\]

If $a\ne0$, division of (7) by $a$ gives (3)--(4). If $a=0$,
both sides of (4) vanish and the displayed value in (3) is the removable
derivative value.

It remains to prove strict positivity. Since $i\ne j$, unique
factorization of prime powers gives $h_i\ne h_j$, hence
$(h_i-h_j)^2>0$. Also $b_i,b_j>0$ and

\[
 r_i+r_j=-2(h_i+h_j)<0.
\]

At $a=0$, both factors
$-b_ib_j(h_i-h_j)^2$ and $r_i+r_j$ are negative, so their product is
positive. For $a\ne0$, strict monotonicity and oddness of $\sinh$ give

\[
 \frac{\sinh(a(r_i+r_j))}{a}<0:
\]

when $a>0$, its numerator is negative; when $a<0$, its numerator is
positive. The first factor in (3) is again negative, proving $G_a(i,j)>0$.
This proves (4).

For (5), substitute (4):

\[
 a\sum_{S}w_{ij}C_a(i,j)
 =a^2\sum_{S}w_{ij}G_a(i,j)>0.
\]

Here $a^2>0$, every summand on the right is nonnegative, and at least one
is strictly positive. This completes the proof.

## Hostile audit

- No Xi zero, zero location, RH statement, target Cholesky factor, or target
  positivity occurs in the construction or proof.
- Coorientation is source-defined: $h_j-h_i$ is the actual difference of
  the two prime-power half-heights. It is not fitted from a divisor.
- Without coorientation the claim is false: swapping $i,j$ reverses
  $D_a(i,j)$. Multiplying by the simultaneously reversed height difference
  is the essential symmetric source operation.
- The theorem does **not** prove RH. It excludes a whole proposed producer
  category: positive all-pair Gamma shorting reinforces horizontal fracture.
- Corpus search found the fixed `(2,3)` positive-gauge comparison and the
  coordinatewise nonvanishing/injectivity laws, but no arbitrary-cell
  cooriented positive-cone theorem or finite-packet no-shorting consequence.

## Frontier consequence

The surviving source-null-homotopy cannot be a completely positive,
nonnegative, or orthogonal sum of cooriented Gamma boundary cells. It must
introduce sign-indefinite cross-pair incidence (or an equivalent genuinely
nonlocal cancellation) before Hilbert completion while retaining enough
packet provenance for joint conservativity. This removes “positive global
shorting” from Route R and localizes the hard producer to a signed
off-diagonal arithmetic differential.

## Lean certificate

- `formal/GaloisForLFunctions/RHTower/GammaCoorientedPositiveConeNoShorting.lean`
- `xiGammaEulerPrimitiveReflectionOddExterior_eq_sinh`
- `xiGammaEulerPrimitiveCoorientedReflectionOddExterior_eq_mul_gauge`
- `xiGammaEulerPrimitiveCoorientedReflectionGauge_pos`
- `xiGammaEulerPrimitiveCoorientedPositiveCone_noShorting`
- `xiGammaEulerPrimitiveCoorientedPositiveCone_tsum_noShorting`
