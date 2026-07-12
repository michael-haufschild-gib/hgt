# Multiplicity depth and symmetric source quotients in the theta spectral problem

## Abstract

Hedenmalm recently associated the zeros of the centered Riemann function

\[
\Xi(z)=\xi\!\left(\frac12+iz\right)
\]

with a theta-driven boundary-value problem and proposed a self-adjointness problem for the
resulting differential-operator pair. We identify the exact role of zero multiplicity in this
architecture.

For a zero \(\alpha\) of analytic multiplicity \(m\), iterated removable division produces a
canonical chain \(Q_{\alpha,0},\ldots,Q_{\alpha,m}\). Its first nonzero value at \(\alpha\) occurs
at depth exactly \(m\), and coordinate multiplication satisfies

\[
zQ_{\alpha,k+1}=\alpha Q_{\alpha,k+1}+Q_{\alpha,k}.
\]

Thus quotienting the common source \(Q_{\alpha,0}=\Xi\) turns a multiple zero into a nontrivial
Jordan chain. This yields two consequences. First, the divisor-value span of the original
Hedenmalm eigenfunctions is exactly the coordinate span of the simple zeros; it is complete in the
multiplicity-exact divisor carrier if and only if all zeros are simple. Second, any faithful source
source-annihilating quotient which faithfully retains the first divided level and intertwines the
first two levels with a symmetric operator forces every Xi zero to be real and simple.

We also give a canonical assumption-free normal form. Each zero contributes a finite Jordan matrix
whose size is its analytic multiplicity. All these matrices are Hermitian if and only if the
Riemann hypothesis holds and every nontrivial zeta zero is simple. The result does not construct
the required symmetric source quotient. It identifies, without multiplicity ambiguity, the exact
carrier that such a construction must produce.

## 1. Introduction

The Hilbert--Pólya principle asks for a self-adjoint spectral object whose spectrum is the set of
ordinates of the nontrivial zeros of the Riemann zeta function. Hedenmalm's theta spectral problem
provides a concrete new setting for this question [1]. Its boundary-value solutions are indexed by
the zeros of \(\Xi\), and the transformed solution at a zero \(\alpha\) is the removable quotient

\[
U_\alpha(z)=-i\frac{\Xi(z)}{\alpha-z}.
\]

Hedenmalm proves uniqueness, up to scalar, of the boundary-value eigenfunction and observes that
one eigenfunction per eigenvalue gives weak support for simplicity of the real zeros. The
multiplicity issue is subtler. At a multiple zero, \(U_\alpha\) is not the zero entire function,
but its value at every Xi zero vanishes. A divisor carrier based only on values therefore loses the
eigenfunction precisely when multiplicity occurs.

The correct replacement is a jet-sensitive divided chain. It reveals a sharp dichotomy:

\[
\text{simple zero}\quad\Longleftrightarrow\quad
\text{one nonzero eigenvector coordinate},
\]

whereas

\[
\text{zero of order }m\ge2\quad\Longrightarrow\quad
\text{a length-}m\text{ Jordan chain after source quotienting}.
\]

A symmetric operator cannot contain a nontrivial Jordan chain. Consequently, a faithful symmetric
completion of the theta problem forces not only the reality of the zeros but also their simplicity.

The argument separates three objects that are often conflated:

1. the nonzero entire eigenfunction;
2. its divisor-value image;
3. the full jet chain required by analytic multiplicity.

This separation leads to an exact positive formulation of the Hilbert--Pólya obligation in the
theta architecture: a successful construction must annihilate the common theta source, retain the
first divided solution at every zero, transport spectral-coordinate multiplication, and produce a
symmetric operator. These conditions already force the centered Xi divisor to be real and simple.

## 2. Centered Xi and the regular Fourier equation

Let

\[
\Xi(z)=\xi\!\left(\frac12+iz\right).
\]

Then \(\Xi\) is entire, satisfies

\[
\Xi(-z)=\Xi(z),\qquad \Xi(\overline z)=\overline{\Xi(z)},
\]

and its zeros are the centered nontrivial zeta zeros, counted with analytic multiplicity.

For an entire function \(F\) and a point \(\alpha\), define its removable divided slope by

\[
\mathcal D_\alpha F(z)=
\begin{cases}
\dfrac{F(z)-F(\alpha)}{z-\alpha},&z\ne\alpha,\\[6pt]
F'(\alpha),&z=\alpha.
\end{cases}
\]

The function \(\mathcal D_\alpha F\) is entire.

For a zero \(\Xi(\alpha)=0\), put

\[
U_\alpha=i\mathcal D_\alpha\Xi.
\]

Away from \(\alpha\),

\[
U_\alpha(z)=i\frac{\Xi(z)}{z-\alpha}
=-i\frac{\Xi(z)}{\alpha-z}.
\]

It satisfies the transformed theta-source equation

\[
(\alpha-z)U_\alpha(z)=-i\Xi(z).                 \tag{2.1}
\]

The theta-cusp source in Hedenmalm's construction is a Schwartz function whose Fourier transform,
with the normalized frequency variable, is exactly \(\Xi\). Thus (2.1) is the regular Fourier-side
form of the theta eigenfunction equation.

### Proposition 2.1. Exact regular solution

If \(\Xi(\alpha)=0\), then \(U_\alpha\) is the unique continuous function on \(\mathbb C\)
satisfying (2.1). In particular, the unique continuous solution is entire.

#### Proof

The displayed quotient verifies (2.1), including at \(z=\alpha\), because both sides vanish there.
If \(V\) is another continuous solution, then

\[
(\alpha-z)V(z)=(\alpha-z)U_\alpha(z)
\]

for all \(z\). Hence \(V(z)=U_\alpha(z)\) for \(z\ne\alpha\). The complement of one point is dense,
so continuity gives equality also at \(\alpha\). \(\square\)

## 3. The canonical divided chain

Define

\[
Q_{\alpha,0}=\Xi,\qquad
Q_{\alpha,k+1}=\mathcal D_\alpha Q_{\alpha,k}\quad(k\ge0).      \tag{3.1}
\]

Every member of the chain is entire, and

\[
U_\alpha=iQ_{\alpha,1}.                                      \tag{3.2}
\]

Let \(m_\alpha\) denote the analytic multiplicity of \(\Xi\) at \(\alpha\).

### Theorem 3.1. Exact multiplicity depth

For every Xi zero \(\alpha\),

\[
Q_{\alpha,k}(\alpha)=0\quad(0\le k<m_\alpha),               \tag{3.3}
\]

while

\[
Q_{\alpha,m_\alpha}(\alpha)\ne0.                            \tag{3.4}
\]

Moreover, for every \(0\le k\le m_\alpha\),

\[
\Xi(z)=(z-\alpha)^kQ_{\alpha,k}(z),                         \tag{3.5}
\]

and \(Q_{\alpha,k}\) is not the zero entire function.

#### Proof

Write the local Taylor expansion as

\[
\Xi(z)=\sum_{n=m_\alpha}^{\infty}a_n(z-\alpha)^n,
\qquad a_{m_\alpha}\ne0.
\]

Removable division shifts the expansion once:

\[
Q_{\alpha,k}(z)=
\sum_{n=m_\alpha}^{\infty}a_n(z-\alpha)^{n-k}
\qquad(0\le k\le m_\alpha).
\]

This gives (3.3), (3.4), and the local form of (3.5). Both sides of (3.5) are entire and agree near
\(\alpha\), hence agree on \(\mathbb C\). If \(Q_{\alpha,k}\) were identically zero, (3.5) would
make \(\Xi\) identically zero, which is false. \(\square\)

### Corollary 3.2. The first quotient detects simplicity

For every Xi zero \(\alpha\),

\[
U_\alpha(\alpha)\ne0
\quad\Longleftrightarrow\quad
m_\alpha=1.                                                 \tag{3.6}
\]

Indeed,

\[
U_\alpha(\alpha)=i\Xi'(\alpha).
\]

At a multiple zero the entire function \(U_\alpha\) remains nonzero, but its base value vanishes.

## 4. The Jordan recurrence

Let \(M_z\) denote multiplication by the spectral coordinate:

\[
(M_zF)(z)=zF(z).
\]

### Theorem 4.1. Divided-chain recurrence

For \(0\le k<m_\alpha\),

\[
M_zQ_{\alpha,k+1}
=\alpha Q_{\alpha,k+1}+Q_{\alpha,k}.                       \tag{4.1}
\]

#### Proof

Since \(Q_{\alpha,k}(\alpha)=0\), removable division gives

\[
Q_{\alpha,k}(z)=(z-\alpha)Q_{\alpha,k+1}(z).
\]

Rearranging yields (4.1). \(\square\)

The first two equations are

\[
M_zQ_{\alpha,1}=\alpha Q_{\alpha,1}+\Xi,                   \tag{4.2}
\]

and, if \(m_\alpha\ge2\),

\[
M_zQ_{\alpha,2}=\alpha Q_{\alpha,2}+Q_{\alpha,1}.          \tag{4.3}
\]

After quotienting the common source \(\Xi\), equation (4.2) makes the first divided quotient an
eigenvector, while (4.3) makes the second quotient a generalized eigenvector. A multiple zero is
therefore encoded by a genuine Jordan chain, not by additional independent eigenvectors.

## 5. The divisor-value defect

Let \(\mathcal Z_\Xi\) be the centered Xi divisor with one copy for every analytic multiplicity.
Its multiplicity-exact value carrier is

\[
\mathcal H_\Xi=\ell^2(\mathcal Z_\Xi).
\]

For an entire function \(F\) whose divisor values are square-summable, write

\[
\mathcal E(F)=\bigl(F(\beta_q)\bigr)_{q\in\mathcal Z_\Xi},
\]

where \(\beta_q\) is the centered spectral point of the divisor copy \(q\).

If \(\alpha\ne\beta\) are Xi zeros, then

\[
U_\alpha(\beta)=0.                                         \tag{5.1}
\]

At the base zero,

\[
U_\alpha(\alpha)=i\Xi'(\alpha).                            \tag{5.2}
\]

### Theorem 5.1. Exact simple-support defect

The algebraic span of the divisor evaluations of the Hedenmalm eigenfunctions is exactly the
coordinate span of the simple part of the Xi divisor:

\[
\operatorname{span}\{\mathcal E(U_\alpha):\Xi(\alpha)=0\}
=
\operatorname{span}\{e_q:\Xi'(\beta_q)\ne0\}.              \tag{5.3}
\]

Consequently,

\[
\overline{\operatorname{span}}\{\mathcal E(U_\alpha):\Xi(\alpha)=0\}
=\mathcal H_\Xi
\quad\Longleftrightarrow\quad
\text{every Xi zero is simple}.                            \tag{5.4}
\]

#### Proof

At a simple zero there is one divisor copy and (5.1)--(5.2) give

\[
\mathcal E(U_\alpha)=i\Xi'(\alpha)e_\alpha,
\]

a nonzero multiple of the corresponding coordinate vector. At a multiple zero,
\(\Xi'(\alpha)=0\), and the eigenfunction vanishes at its own divisor fiber as well as at every
other Xi zero. Its value vector is therefore zero. This proves (5.3). The finite coordinate vectors
are dense in \(\ell^2\), so (5.4) follows. \(\square\)

The theorem explains why a multiplicity-exact carrier based only on divisor values is incomplete:
it repeats the point \(\alpha\) but does not record the jets that distinguish its multiplicity
copies.

## 6. Symmetric source quotients

Let \(\mathcal F\) be the vector space of complex-valued functions on \(\mathbb C\). Let \(H\) be a
complex inner-product space, let

\[
J:\mathcal F\longrightarrow H
\]

be complex-linear, and let \(S:H\to H\) be a symmetric complex-linear operator:

\[
\langle Sx,y\rangle=\langle x,Sy\rangle.                  \tag{6.1}
\]

We call \((J,S)\) a two-level faithful source quotient for the Xi divided chain if

\[
J(\Xi)=0,                                                   \tag{6.2}
\]

\[
J(Q_{\alpha,1})\ne0                                        \tag{6.3}
\]

for every Xi zero \(\alpha\), and

\[
S J(Q_{\alpha,k})=J(M_zQ_{\alpha,k}),qquad k=1,2.          \tag{6.4}
\]

The definition uses one common map and one common symmetric operator for the whole divisor.

We first record the elementary obstruction on which the global theorem rests.

### Lemma 6.1. Symmetric operators have no real Jordan step

Suppose \(S\) is symmetric, \(\alpha\in\mathbb R\), and

\[
Sv_0=\alpha v_0,
\qquad
Sv_1=\alpha v_1+v_0.
\]

Then \(v_0=0\).

#### Proof

By symmetry,

\[
\begin{aligned}
\|v_0\|^2
&=\langle (S-\alpha)v_1,v_0\rangle\\
&=\langle v_1,(S-\alpha)v_0\rangle\\
&=0.
\end{aligned}
\]

Hence \(v_0=0\). \(\square\)

### Theorem 6.2. Local faithful-carrier law

Fix an Xi zero \(\alpha\). Suppose (6.2)--(6.4) hold at \(\alpha\). Then \(\alpha\) is real and
\(m_\alpha=1\).

#### Proof

Equations (4.2), (6.2), and (6.4) give

\[
S J(Q_{\alpha,1})=\alpha J(Q_{\alpha,1}).                  \tag{6.5}
\]

The vector is nonzero by (6.3). Every eigenvalue of a symmetric operator is real, so
\(\alpha\in\mathbb R\).

If \(m_\alpha\ge2\), then (4.3) and (6.4) give

\[
S J(Q_{\alpha,2})
=\alpha J(Q_{\alpha,2})+J(Q_{\alpha,1}).                  \tag{6.6}
\]

Equations (6.5)--(6.6) form a real Jordan step with nonzero first vector, contradicting Lemma 6.1.
Thus \(m_\alpha=1\). \(\square\)

### Theorem 6.3. Global faithful-carrier law

If a two-level faithful symmetric source quotient exists for the whole Xi divided chain, then the
Riemann hypothesis holds and every Xi zero is simple.

#### Proof

Apply Theorem 6.2 at every centered Xi zero. All centered zeros are real, which is the Riemann
hypothesis, and every analytic multiplicity is one. \(\square\)

The theorem is a carrier classification, not an existence theorem. It identifies four concrete
properties whose simultaneous construction suffices:

\[
\boxed{
\text{source annihilation}
+\text{ first-level faithfulness}
+\text{ two-level transport}
+\text{ symmetry}
\Longrightarrow \mathrm{RH}+\text{simplicity}.}
\]

## 7. Canonical local normal form

The divided chain has a finite local matrix independent of any proposed Hilbert completion. For a
zero \(\alpha\) of multiplicity \(m\), define

\[
\mathcal J_\alpha=
\begin{pmatrix}
\alpha&1&0&\cdots&0\\
0&\alpha&1&\ddots&\vdots\\
\vdots&\ddots&\ddots&\ddots&0\\
0&\cdots&0&\alpha&1\\
0&\cdots&\cdots&0&\alpha
\end{pmatrix}\in M_m(\mathbb C).                           \tag{7.1}
\]

Equation (4.1) identifies \(\mathcal J_\alpha\) as the root-module matrix of coordinate
multiplication after quotienting the common source.

### Theorem 7.1. Local Hermitian classification

For every Xi zero \(\alpha\),

\[
\mathcal J_\alpha^*=\mathcal J_\alpha
\quad\Longleftrightarrow\quad
\alpha\in\mathbb R\ \text{ and }\ m_\alpha=1.              \tag{7.2}
\]

#### Proof

If \(\mathcal J_\alpha\) is Hermitian, its diagonal entry \(\alpha\) is real. If \(m\ge2\), the
\((1,2)\) entry is \(1\) while the \((2,1)\) entry is \(0\), contradicting Hermitian symmetry.
Hence \(m=1\). Conversely, when \(m=1\) and \(\alpha\) is real, the matrix is the one-by-one
Hermitian matrix \((\alpha)\). \(\square\)

Let the family \(\{\mathcal J_\alpha\}\) range over the distinct centered Xi zeros, with each
matrix sized by the analytic multiplicity.

### Theorem 7.2. Global Hermitian normal form

\[
\bigl(\mathcal J_\alpha\text{ is Hermitian for every Xi zero }\alpha\bigr)
\quad\Longleftrightarrow\quad
\mathrm{RH}+\text{simplicity}.                             \tag{7.3}
\]

#### Proof

The forward implication follows pointwise from Theorem 7.1: every centered zero is real and every
multiplicity is one. Conversely, RH and simplicity make every local block a one-by-one real
matrix. \(\square\)

Theorem 7.2 is assumption-free. It is not itself a proof of RH, because the matrices are built from
the Xi divisor. Its role is to specify the exact terminal normal form of a multiplicity-faithful
theta spectral construction.

## 8. Consequences for Hilbert--Pólya architectures

The preceding results turn multiplicity from a side condition into an explicit transport law.

First, one eigenfunction per distinct zero is insufficient for a multiplicity-exact self-adjoint
realization unless all zeros are simple. Repeating a divisor point does not create new eigenfunction
states. The missing states are jets, and their canonical divided representatives form a Jordan
chain.

Second, a positive-definite symmetric realization cannot use that Jordan chain to absorb analytic
multiplicity. It must instead force the chain to have length one. In the theta architecture this
means that symmetry plus faithful source transport proves simplicity at the same time as it proves
reality.

Third, a divisor-value metric and a jet-sensitive source quotient serve different purposes. The
former detects the real simple part of the divisor but collapses every multiple-zero eigenfunction.
The latter must retain the first quotient while annihilating only the common source. A successful
construction must therefore use a topology or incidence structure strong enough to distinguish
\(Q_{\alpha,1}\) from \(\Xi\) even when all ordinary divisor values of \(Q_{\alpha,1}\) vanish.

The remaining constructive problem can be stated without a negative formulation:

> Construct one global inner-product-space quotient of the theta-source function module that
> annihilates \(\Xi\), retains every \(Q_{\alpha,1}\), transports coordinate multiplication on the
> first two divided levels, and makes the transported operator symmetric.

By Theorem 6.3, such a construction proves RH and simplicity. By Theorem 7.2, its local root module
must reduce to the canonical real one-dimensional blocks.

## 9. Relation to previous work

Hedenmalm's boundary-value theorem supplies the eigenfunction indexed by each Xi zero and proposes
self-adjointness of an operator pair as the Hilbert--Pólya mechanism [1]. The uniqueness of the
boundary-value eigenfunction is geometric multiplicity one; it does not by itself identify the
analytic multiplicity of the Xi zero.

Jordan chains and root functions are standard tools in the local analysis of operator pencils and
analytic operator families [2,3]. The point here is the exact chain forced by Hedenmalm's theta
source: it is obtained by iterated removable division of \(\Xi\), its depth is exactly the Xi
multiplicity, and source quotienting makes its Jordan structure unavoidable. This produces the
faithful-carrier theorem and the canonical Hermitian normal form above.

The distinction between a spectral interpretation and the positivity needed for RH has long been
emphasized in the Hilbert--Pólya literature [4]. The present results locate that positivity
requirement precisely in the theta problem: positivity cannot merely be placed on a divisor-value
space; it must coexist with faithful transport of the divided source module.

## References

1. H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494, 2026.
   <https://arxiv.org/abs/2606.17494>

2. M. Stiefenhofer, *Diagonalization of operator functions by algebraic methods*,
   arXiv:2411.15905, 2024. <https://arxiv.org/abs/2411.15905>

3. A. Albrecht, P. Howlett, and G. Verma, *Inversion of operator pencils on Banach space using
   Jordan chains when the generalized resolvent has an isolated essential singularity*,
   arXiv:2002.10551, 2020. <https://arxiv.org/abs/2002.10551>

4. J. C. Lagarias, *The Riemann hypothesis: arithmetic and geometry*, in *Surveys in
   Noncommutative Geometry*, Clay Mathematics Proceedings 6, 2006, 127--139.
   <https://www.claymath.org/library/proceedings/cmip06.pdf>
