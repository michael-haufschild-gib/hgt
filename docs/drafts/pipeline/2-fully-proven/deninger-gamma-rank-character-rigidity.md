# Deninger Gamma rank-character rigidity

- **ID:** `deninger-gamma-rank-character-rigidity`
- **Stage:** 2-fully-proven
- **Type:** POSITIVE SURVIVOR / SOURCE POLARIZATION LEMMA
- **Parent:** `deninger-polarized-transfer-half-density`
- **Lean status:** drafted in `DeningerArithmeticGammaRankRigidity.lean`; direct check pending

## Statement

Over a real closed field, write
\[
 GW\simeq\mathbb Z[\varepsilon]/(\varepsilon^2-1),
 \qquad
 \varepsilon=\langle-1\rangle,
 \qquad
 h=\langle1\rangle+\langle-1\rangle=1+\varepsilon.
\]
Let
\[
 \chi:GW\longrightarrow\mathbb R
\]
be a unital ring character.  If
\[
 \chi(h)>0,                                                        \tag{1}
\]
then \(\chi\) is the rank character:
\[
 \chi(\varepsilon)=1.                                             \tag{2}
\]
Consequently, for the Milnor--Witt quadratic integer
\[
 n_\epsilon=\sum_{j=0}^{n-1}\varepsilon^j,
\]
one has
\[
 \chi(n_\epsilon)=n.                                              \tag{3}
\]

Thus any scalar real realization that is strictly positive on the hyperbolic plane is forced to
use rank, not signature.  The degree law required by Deninger's half-density normalization is
canonical once strict Gamma positivity exists.

## Proof

Since \(\chi\) is unital and multiplicative,
\[
\chi(\varepsilon)^2=\chi(\varepsilon^2)=\chi(1)=1.
\]
Hence \(\chi(\varepsilon)=1\) or \(\chi(\varepsilon)=-1\).  If the second alternative held, then
\[
\chi(h)=\chi(1+\varepsilon)=1-1=0,
\]
contradicting `(1)`.  Therefore \(\chi(\varepsilon)=1\), which is `(2)`.  It follows that
\[
\chi(n_\epsilon)
 =\sum_{j=0}^{n-1}\chi(\varepsilon)^j
 =\sum_{j=0}^{n-1}1
 =n,
\]
proving `(3)`.

## Relation to the bare-transfer no-go

The usual real signature character sends
\[
\varepsilon\longmapsto-1,\qquad h\longmapsto0.
\]
It therefore gives signature \(0\) for even \(n_\epsilon\) and \(1\) for odd \(n_\epsilon\),
recovering the proved indefiniteness obstruction.  The positive Gamma channel cannot be the
signature realization.  It must factor the central quadratic degree through rank.

This does not require forgetting the Milnor--Witt incidence complex.  It says only that the
central push-pull degree operator acts through rank in the positive scalar metric.  Steinberg
boundaries and quadratic orientation remain in the source cochain and cup structure.

## Deninger consequence

In `deninger-polarized-transfer-half-density`, the conjectural equation
\[
\operatorname{Real}^{\mathrm{pol}}_\Gamma(n_\epsilon)=n\,\mathrm{id}
\]
is forced on every scalar positive summand once:

1. the Gamma realization is a unital \(GW\)-module realization;
2. the hyperbolic class acts strictly positively.

The remaining work is construction of that positive Gamma realization and proof that the
push-pull degree action lands in its scalar channel.

## Novelty audit

Classification of the two real characters of \(GW\) is standard.  New content is its use as the
exact rigidity theorem separating Deninger's positive rank channel from the indefinite signature
channel.
