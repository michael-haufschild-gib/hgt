# Affine reciprocal-zeta packets have unbounded differential rank

- **ID:** `affine-reciprocal-zeta-dihedral-packet`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** corpus synthesis from the positive Riemann-divisor frame and the completed
  functional equation
- **Statement:** The countable family
  \[
    \{\zeta(s)\}\cup
    \left\{\frac1{\zeta(ms-k)}:m\geq2,\ k\in\mathbb Z\right\}
  \]
  is jointly differentially algebraically independent over \(\mathbb C(s)\); reflection
  \(s\mapsto1-s\) exchanges the two affine faces \(k\leftrightarrow m-1-k\), while unit
  translation acts by \(k\mapsto k-m\).

## Goal

Identify the differential rank carried by the smallest reciprocal-zeta architecture that is
closed under the Riemann functional equation and affine translation.  Determine whether this
source geometry supplies a zero-sensitive fixed-cycle law capable of proving
\[
  \xi(\rho)=0\quad\Longrightarrow\quad \Re\rho=\frac12.
\]

This card does **not** claim such a law.  Its paper theorem is a rank theorem.  The exact RH open
core is isolated below so that differential freeness is not misreported as zero localization.

## Gates

- [x] 0 → 1 in-progress: source-pure family, exact arithmetic source, determinant attack,
  functional-equation action, and RH passport stated
- [ ] 1 → 2 fully-proven: complete external novelty audit and independent hostile proof audit
- [ ] 2 → 3 formalized: Lean theorem, `lake build` green, formal lint PASS
- [ ] 3 → 4 publication-ready: standalone theorem, proof, literature comparison, Lean certificate

## Corpus audit

The positive hypertranscendental Riemann-divisor frame proves joint differential independence for
the unshifted shells and their reciprocal multipliers \(1/\zeta(ms)\).  Its
\(\Omega\)-leading-echelon theorem assumes distinct grades and therefore does not by itself handle
several shifts with the same dilation \(m\).

The complete positive Kolchin-free resolution supplies the telescoping graph
\[
  \frac1{\zeta(Ks)}
  +\sum_{m\geq K}
   \left(\frac1{\zeta((m+1)s)}-\frac1{\zeta(ms)}\right)=1
\]
on its half-plane of convergence.  It has no internal functional-equation closure: reflection of
\(\zeta(ms)\) introduces the affine argument \(ms-(m-1)\).

No corpus theorem currently proves a norm, sign, flatness, or fixed-cycle law for the reflected
pair.  Existing high-shell and co-Poisson cards explicitly leave that source theorem open.

## External novelty audit

Targeted searches checked:

- Ostrowski/Postnikov differential-independence results for Dirichlet series;
- Pong's differential-algebra framework for arithmetic functions;
- Chiang--Feng difference independence of \(\zeta\);
- work on differential independence of \(\zeta\) relative to Gamma factors;
- exact searches for \(1/\zeta(ms-k)\), \(\zeta(ms-k)\), affine zeta dilations, and reciprocal
  packets.

The search found general parent methods and additive-difference results, but no theorem matching
the countable affine reciprocal family above.  This is evidence only, not proof of priority.

## Arithmetic source

Let \(\mathcal A\) be the \(\mathbb C\)-algebra of arithmetic functions under Dirichlet
convolution.  Put
\[
  (L^r f)(n)=(-\log n)^r f(n),\qquad
  (\partial_qf)(n)=v_q(nq)f(nq)
\]
for \(r\geq0\) and prime \(q\).  Every \(\partial_q\) is a derivation of \(\mathcal A\).

For \(m\geq2\) and \(k\in\mathbb Z\), define
\[
 f_{m,k}(n)=
 \begin{cases}
   \mu(d)d^k,&n=d^m,\\
   0,&\text{otherwise}.
 \end{cases}
\]
Its Dirichlet transform is
\[
  R_{m,k}(s)=\sum_{d\geq1}\frac{\mu(d)d^k}{d^{ms}}
            =\frac1{\zeta(ms-k)}
\]
on \(m\Re s-k>1\).  Thus every source has a finite half-plane of absolute convergence, including
negative \(k\).

## Equal-grade leading-layer lemma

For every prime \(q\), \(r\geq0\), and \(n\geq1\),
\[
 \Omega(n)<m-1
 \quad\Longrightarrow\quad
 \partial_q(L^rf_{m,k})(n)=0.
\]
At the first possible grade,
\[
 \Omega(n)=m-1
 \quad\Longrightarrow\quad
 \partial_q(L^rf_{m,k})(n)
 =
 -m q^k(-m\log q)^r\,
 \mathbf1_{\{q^{m-1}\}}(n).
 \tag{1}
\]

Indeed, nonvanishing implies \(nq=d^m\), hence
\[
 \Omega(n)+1=m\Omega(d).
\]
Below grade \(m-1\) this is impossible.  At equality it forces \(\Omega(d)=1\), so \(d=q\) and
\(n=q^{m-1}\).  Formula (1) then follows from \(\mu(q)=-1\).

## Prime evaluation lemma

Let \(E\subset\mathbb Z\times\mathbb N\) be finite.  The functions
\[
  q\longmapsto q^k(\log q)^r,\qquad (k,r)\in E,
 \tag{2}
\]
are linearly independent on the set of primes.

To prove this, group a putative relation as
\[
  \sum_k q^kP_k(\log q)=0
 \tag{3}
\]
for every prime \(q\).  Choose the largest \(k_*\) with \(P_{k_*}\ne0\), divide by \(q^{k_*}\),
and let the primes tend to infinity.  Every lower-exponent term decays exponentially in
\(\log q\), so (3) forces \(P_{k_*}(x)\to0\) along an unbounded sequence \(x=\log q\).  A nonzero
polynomial cannot tend to zero at \(+\infty\), contradiction.

Consequently, for any finite \(E\) there are \(|E|\) distinct primes \(q_i\) such that the
evaluation matrix
\[
  \big[q_i^k(\log q_i)^r\big]_{i,(k,r)\in E}
 \tag{4}
\]
is invertible.  Otherwise all prime-evaluation vectors would span a proper subspace, producing a
nonzero relation of the form (3).

## Differential-independence theorem

**Theorem.**  The family
\[
  \{\zeta\}\cup\{R_{m,k}:m\geq2,\ k\in\mathbb Z\}
 \tag{5}
\]
is jointly differentially algebraically independent over \(\mathbb C(s)\).

### Proof

It is enough to treat a finite set of functions and a finite jet order \(J\).  Group the
reciprocal sources by \(m\).  In the \(m\)-block, columns are indexed by the finite set of pairs
\((k,r)\) that occur, with \(0\leq r\leq J\).  Choose the same number of distinct primes for rows
so that (4) is invertible.  Give the zeta source \(\mathbf1(n)=1\) grade zero and choose its row
primes by the ordinary log-Vandermonde determinant.

Form the arithmetic-function-valued Jacobian from the selected prime derivations.  Extract its
coefficient at
\[
  N=\prod_i q_i^{e_i},
\]
where \(e_i=0\) in the zeta block and \(e_i=m-1\) in an \(m\)-block.  The lower-grade vanishing in
(1) says that a convolution term at total \(\Omega\)-grade \(\sum_i e_i\) must use the first
nonzero layer in every column.  Unique factorization then forces a contributing determinant
permutation to preserve every equal-\(m\) block.  Formula (1) reduces an \(m\)-block, up to
nonzero row and column scalars, to (4).  Every block determinant is nonzero, so the extracted
coefficient of the full Jacobian determinant is nonzero.

The characteristic-zero Jacobian criterion now proves algebraic independence of every finite jet
rectangle in \(\mathcal A\).  Dirichlet transformation is injective and carries \(L^r\) to the
\(r\)-th ordinary derivative.  A relation over \(\mathbb C(s)\), after clearing denominators,
would give a Dirichlet series with uniformly bounded-degree polynomial coefficients in \(s\).
The least-index exponential-separation argument forces every polynomial coefficient to vanish,
contradicting arithmetic-function independence.  This proves (5). \(\square\)

**Relative corollary.**  Over
\[
  K_\zeta=\mathbb C(s)\langle\zeta\rangle,
\]
the family \(\{R_{m,k}:m\geq2,\ k\in\mathbb Z\}\) remains jointly differentially algebraically
independent.  This is the tower property of algebraic independence applied to (5).

## Dihedral functional-equation geometry

Use the meromorphic factor \(\chi\) defined by
\[
  \zeta(u)=\chi(u)\zeta(1-u).
\]
If \(\ell=m-1-k\), then
\[
  R_{m,k}(1-s)
  =\chi(ms-\ell)R_{m,\ell}(s).
 \tag{6}
\]
Thus reflection acts on affine labels by
\[
  k\longmapsto m-1-k.
\]
Unit translation gives
\[
  R_{m,k}(s+1)=R_{m,k-m}(s).
 \tag{7}
\]
Modulo the translation \(k\mapsto k-m\), the labels \(0,\ldots,m-1\) form a fundamental packet,
and reflection acts by \(k\mapsto-1-k\pmod m\).  Its differential rank is \(m\), hence unbounded
with \(m\).

Important correction: the functional equation alone does **not** force all \(m\) residue faces.
Starting from the positive face \(k=0\), reflection closes only the two-face set
\(\{0,m-1\}\).  The \(m\)-wide packet is canonical only after unit translations are included.

The absolute-convergence walls of the fundamental representatives are
\[
  \Re s>\frac{k+1}{m},\qquad 0\leq k<m.
\]
For odd \(m\), the reflection-fixed label \(k=(m-1)/2\) has wall
\[
  \Re s>\frac12+\frac1{2m},
\]
which approaches the critical line.  This is geometric organization, not zero localization.

## Completed seam and parity-charge compression

Put
\[
 A(u)=\pi^{-u/2}\Gamma(u/2),\qquad
 \Lambda(u)=A(u)\zeta(u),\qquad
 \widehat R_{m,k}(s)=\frac1{\Lambda(ms-k)}.
\]
The completed functional equation \(\Lambda(u)=\Lambda(1-u)\) removes the meromorphic
\(\chi\)-multiplier from (6) and gives the exact permutation law
\[
 \widehat R_{m,k}(1-s)
 =\widehat R_{m,m-1-k}(s).
 \tag{10}
\]
Thus completion is not an additional scalar symmetry: it is the gauge which turns the affine
reflection cocycle into a genuine involution on the packet.

The gauge has a strict two-step recurrence.  If \(u=ms-k\), then
\[
 A(u-2)=\frac{2\pi}{u-2}A(u).
 \tag{11}
\]
Equivalently, all \(A(ms-k)\) with fixed parity of \(k\) lie in one rational multiplicative
Gamma orbit.  There are at most two archimedean charge orbits in a fundamental \(m\)-packet.
Reflection preserves them when \(m\) is odd and exchanges them when \(m\) is even.

The same statement appears directly in the raw reflection cocycle.  With
\[
 \chi(u)=\pi^{u-1/2}\frac{\Gamma((1-u)/2)}{\Gamma(u/2)},
\]
one has
\[
 \frac{\chi(u+2)}{\chi(u)}
 =-\frac{4\pi^2}{u(u+1)}.
 \tag{12}
\]
Hence the reflected seam has two Gamma charge classes even though the raw arithmetic packet has
arbitrarily large ordinary differential rank.

This is the relevant rank mismatch:
\[
 \begin{array}{c}
 \text{\(m\) mutually differentially free arithmetic faces}\\
 \downarrow\ \text{entire Gamma completion}\\
 \text{two archimedean parity-charge classes and one reflection permutation.}
 \end{array}
 \tag{13}
\]
No claim of joint differential algebraic independence after adjoining the Gamma gauges is made;
that requires a differential-disjointness theorem stronger than separate Gamma
hypertranscendence.  Equations (10)--(12), and the raw arithmetic rank theorem, are unconditional.

The mismatch sharpens the RH search boundary.  Any finite ordinary differential identity over
\(K_\zeta\) is excluded by the raw rank theorem, while a norm budget that discards the Gamma
gauges is excluded by the corpus's critical-clock divisor-blindness theorem.  A viable
zero-localizing law must therefore use the **entire completion seam itself**: an infinite,
parity-sensitive coupling which cancels the polar prime/Gamma channels and is not invariant under
the known positive-Euler functional-equation surgeries with off-line zeros.

## Zero-sensitive audit

For the complete normalized positive-face resolution, the coefficient vector attached to
\(a=n^{-s}\) is
\[
 c_K(a)=\big(a^K,(a-1)a^K,(a-1)a^{K+1},\ldots\big).
\]
Its codiagonal telescopes to zero for \(n>1\) and to one for \(n=1\).  Its squared norm is
\[
 e_K(a)=
 |a|^{2K}
|1-a|^2\sum_{j\geq K}|a|^{2j}
=
\frac{2|a|^{2K}(1-|a|\cos\arg a)}{1-|a|^2}.
 \tag{8}
\]
For \(K\geq1\), (8) is strictly increasing in \(|a|\in(0,1)\), hence strictly decreasing in
\(\Re s\).  Therefore equality of positive-face graph energies at \(\rho\) and
\(1-\overline\rho\) would force \(\Re\rho=1/2\).

If \(\rho\) is a zero of \(\xi\) of order \(d\), the first nonzero derivative of
\(\xi(s)c_K(n^{-s})\) is
\[
  \xi^{(d)}(\rho)c_K(n^{-\rho}).
\]
This uses zerohood essentially and identifies the divisor-normal graph jet.  The functional
equation relates the scalar normal jets at \(\rho\) and \(1-\overline\rho\), but it does **not**
identify the two coefficient vectors or their norms.  Thus the needed equality in (8) does not
follow from the functional equation.

The reflected pair has a useful fixed cross-polarization.  Put
\[
  \rho^*=1-\overline\rho,\quad
  a=n^{-\rho},\quad b=n^{-\rho^*}.
\]
Then \(a\overline b=1/n\), independent of \(\rho\).  Direct summation gives
\[
 \langle c_K(a),c_K(b)\rangle
 =
 \left(\frac1n\right)^K
 \frac{(a-1)(\overline b-1)(1/n)^K}{1-1/n}.
 \tag{9}
\]
This is a source-derived cross-kernel, but it does not imply equality of the two diagonal norms.
Cauchy--Schwarz supplies only an inequality already valid for arbitrary \(s\).

## Exact RH open core

To turn this packet into an RH proof, one must prove from the arithmetic source—without assuming a
zero-location, positivity, or spectral statement equivalent to RH—the following kind of theorem:

> **Source-fixed divisor-normal cycle.**  If \(\xi(\rho)=0\), the normalized leading divisor jet
> of the positive complete resolution at \(\rho\) and at \(1-\overline\rho\) has equal diagonal
> graph energy.

Combined with strict monotonicity of (8), this would prove \(\Re\rho=1/2\).  At present, neither
the arithmetic resolution, the functional equation, differential independence, nor the fixed
cross-kernel (9) proves that premise.

The relative differential-independence theorem sharply restricts the form of a possible source
law: it cannot be a nonzero finite ordinary differential-polynomial identity among the affine
reciprocal channels with coefficients in \(K_\zeta\).  A successful law must use genuinely
additional structure, such as reflection/translation, an infinite completion, or a
source-derived Hilbert-space extremality statement.  This restriction is new mathematical
information; it is not itself progress on zero localization.

Equations (10)--(13) make the surviving option more precise: the additional structure must retain
the entire Gamma/Poisson seam and its two parity-charge classes.  Bare reflection, raw packet
rank, and critical-clock energy have already been shown insufficient.

## Hostile audit

- **Potential circularity:** postulating equal reflected energies is an RH-strength premise.
  It must be independently derived from source geometry.
- **Functional-equation overclaim:** reflection swaps two faces; it does not make an off-line
  zero a fixed point.
- **Rank overclaim:** width \(m\) requires translation residues; FE alone gives rank two per
  dilation.
- **Finite-differential dead end:** relative differential independence rules out the hoped-for
  finite ADE closure over \(K_\zeta\).
- **Gamma gap:** adjoining completed Gamma factors changes the coefficient differential field.
  No joint differential-independence claim over that enlarged field is made here.
- **Novelty risk:** the determinant proof extends a known arithmetic-function method.  Priority
  remains pending a broader bibliographic audit even though no exact result was found.
- **RH status:** OPEN.  No theorem here excludes an off-critical zero.

## Log

- 2026-07-28 — Derived equal-grade exponential-polynomial prime blocks and paper proof of
  countable differential independence.
- 2026-07-28 — Identified dihedral label action and corrected the false claim that FE alone forces
  an \(m\)-wide packet.
- 2026-07-28 — Derived exact completed permutation and two-parity Gamma charge compression,
  isolating the infinite-rank-to-two-charge entire seam.
- 2026-07-28 — Derived fixed reflected cross-polarization and isolated missing diagonal-energy
  equality as the source theorem required for RH.
