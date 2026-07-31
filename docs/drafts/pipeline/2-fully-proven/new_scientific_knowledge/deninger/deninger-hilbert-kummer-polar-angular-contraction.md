# Hilbert--Kummer polar splitting and angular contraction

- **ID:** `deninger-hilbert-kummer-polar-angular-contraction`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_DENINGER_HILBERT_KUMMER_POLAR_ANGULAR_CONTRACTION`
- **Parent:** `deninger-hilbert-kummer-radial-flow-poisson`
- **Statement:** the Hilbert--Kummer bounded generic character locus
  splits into unitary phase and Hilbert logarithmic modulus; the
  nonzero modulus has contractible infinite-dimensional angular factor,
  so only its radial coordinate contributes ordinary derived
  cohomology.

## Polar decomposition of a character

Let
\[
 V=\overline{\mathbb Q}^{\times}/\mu_\infty
   \otimes_{\mathbb Z}\mathbb Q
\]
and let \(P:\overline{\mathbb Q}^{\times}\to\mathbb C^\times\) be a
generic Deninger character.  Pointwise polar decomposition gives
\[
 P(\alpha)
 =\eta_P(\alpha)\exp L_P([\alpha]),                              \tag{1}
\]
where
\[
 \eta_P(\alpha)=P(\alpha)/|P(\alpha)|\in S^1,\qquad
 L_P([\alpha])=\log|P(\alpha)|\in\mathbb R.                      \tag{2}
\]
Both factors are multiplicative.  The second is a
\(\mathbb Q\)-linear functional on \(V\), and the first retains the
torsion character.

Let \(H=H_{\rm Kum}=L^2(Y,\lambda)\).  On the Hilbert--Kummer bounded
locus, `DAC_DENINGER_HILBERT_KUMMER_RADIAL_SUSPENSION` identifies
\(L_P\) with a unique \(\ell_P\in H'\).  Riesz representation
identifies \(H'\) isometrically with \(H\).  Thus, before Galois and
positive-rational descent, the refined generic locus has the exact
polar form
\[
 \check X_{\rm HK}
 \cong
 \check X_{\rm unit}\times H,                                   \tag{3}
\]
where \(\check X_{\rm unit}\) is the source unitary-character locus
carrying Deninger's Tate--Kummer class.

Under Frobenius,
\[
 (\eta,h)\longmapsto(\eta^q,qh).                                \tag{4}
\]
Galois acts on the first factor by character transport and on the
second by the Allcock--Vaaler unitary representation.

## Angular contraction theorem

`[PROVED HERE] [DAC_DENINGER_HILBERT_KUMMER_POLAR_ANGULAR_CONTRACTION]`

The real Hilbert space \(H=L^2(Y,\lambda)\) is infinite-dimensional
and separable.  Its punctured space has the polar homeomorphism
\[
 H\setminus\{0\}
 \xrightarrow{\sim}
 S(H)\times\mathbb R_{>0},\qquad
 h\longmapsto(h/\|h\|,\|h\|).                                   \tag{5}
\]
The unit sphere \(S(H)\) is contractible.  Consequently
\[
 R\Gamma(S(H),\mathbb R)\simeq\mathbb R[0],                     \tag{6}
\]
and the modulus-angular factor creates no positive-degree ordinary
cohomology.

If a compact group \(G\) acts unitarily on \(H\), then for complete
real or complex coefficient modules on which Haar integration is
defined, invariants are exact.  Applying invariants to `(6)` gives
\[
 R\Gamma(S(H),\mathbb R)^G\simeq\mathbb R[0].                   \tag{7}
\]
Thus coarse Galois invariants do not reintroduce an angular derived
class in the degreewise-invariant coefficient model.

### Proof

The maps in `(5)` and their inverse \((\omega,r)\mapsto r\omega\) are
continuous.

For contractibility, choose a Hilbert isometry
\(H\cong\ell^2(\mathbb N,\mathbb R)\), let \(S\) be the unilateral
shift, and let \(e_0\) be the first basis vector.  No nonzero vector is
an eigenvector of \(S\).  Hence
\[
 K_1(x,t)
 =
 \frac{(1-t)x+tSx}{\|(1-t)x+tSx\|},
 \qquad 0\le t\le1,                                               \tag{8}
\]
is well-defined and deforms the identity of the unit sphere to \(S\).
Since \(e_0\perp\operatorname{im}S\),
\[
 K_2(x,t)
 =
 \sqrt{1-t^2}\,Sx+t e_0                                         \tag{9}
\]
stays on the unit sphere and deforms \(S\) to the constant \(e_0\).
Concatenating `(8)` and `(9)` contracts \(S(H)\), proving `(6)`.

For `(7)`, let \(C^\bullet\) be a complete continuous cochain model.
The inclusion of constants
\(\mathbb R\to C^\bullet(S(H),\mathbb R)\) is a
\(G\)-equivariant quasi-isomorphism by `(6)`.  Compact-group
invariants are exact: an invariant element in a quotient is lifted
arbitrarily and its orbit is averaged with normalized Haar measure.
Taking invariants therefore preserves the quasi-isomorphism.

## Arithmetic interpretation

Combining `(3)` and `(5)`, the nonunitary refined locus is
\[
 \check X_{\rm unit}\times S(H)\times\mathbb R_{>0}.             \tag{10}
\]
The factors have distinct roles:

1. \(\check X_{\rm unit}\) carries the nontrivial pro-torus
   Tate--Kummer/Milnor coefficient.  It is not contracted.
2. \(S(H)\) is the modulus direction and is cohomologically trivial by
   `(6)`--`(7)`.
3. \(\mathbb R_{>0}\) is the canonical Kummer radius.  After
   suspension it carries the dilation flow and Meyer's
   Poisson--zeta complex.
4. The omitted locus \(h=0\) is the unitary boundary.  It supplies the
   radial evaluation \(f(0)\); it must be joined to the real
   Fourier-dual boundary rather than declared acyclic.

This is the source explanation for why the Poisson middle coefficient
has one radial variable despite the infinite-rank Kummer character
space.

## Remaining topological gate

Equations `(6)`--`(7)` are ordinary derived statements.  To obtain the
actual comparison one must still prove their strict nuclear analogue:

- completed tensoring with the Tate--Milnor phase coefficient;
- the mixed \(L^1/L^2\) and residue graph topologies;
- compact support in the radial variable only;
- commutation with the infinite flow sum;
- identification of the \(h=0\) boundary maps with
  \(f(0)\) and \(\mathcal Ff(0)\).

Contractibility alone does not prove those strict locally convex
claims.

## Hostile audit

- No averaging over an infinite-dimensional orthogonal group is used.
- No nonexistent Haar probability on \(S(H)\) is assumed.
- The unitary phase factor is retained; only modulus direction is
  contracted.
- The contraction need not be Galois-equivariant.  Exact compact
  invariants are applied to the equivariant quasi-isomorphism from
  constants instead.
- No zeta zero, RH, CCM object, or numerical computation occurs.

## References

- Daniel Allcock and Jeffrey D. Vaaler,
  *A Banach space determined by the Weil height*:
  https://arxiv.org/abs/0808.1038
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  generic character space and Tate regulator:
  https://arxiv.org/abs/1807.06400

## Log

- 2026-07-27 — Split the bounded character locus into phase and modulus
  and proved the infinite-dimensional modulus sphere contributes no
  angular ordinary cohomology.
