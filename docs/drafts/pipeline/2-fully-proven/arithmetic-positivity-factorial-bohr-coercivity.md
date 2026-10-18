# Bohr coercivity of the actual factorial correction phases

- **ID:** APT-ROOT-BOHR
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean certificate required)
- **Source:** [Foundational programme](../../../reports/arithmetic-positivity-theory/research-foundational.md), APT-06–07.
- **Audit verdict:** BRIDGE. The proof combines the corpus's exact factorial phase with classical Bernoulli Fourier series and elementary Hilbert-space estimates. Novelty is not established.

## Exact objects and theorem

For each integer \(N\ge1\), put
\[
\varepsilon_N=\texttt{sourceFactorialCollar}\ N,
\qquad \alpha_N=1+\varepsilon_N,
\qquad \lambda_N=N\alpha_N.
\]
Let \(C(u)=\{u\}(1-\{u\})/2\) be the periodic extension of the nonnegative clamped lattice remainder. Define
\[
P(u)=\tfrac14 C(4u)-2C(2u)+4C(u),\qquad
\Phi_N(v)=P(\lambda_Nv)-P(Nv).
\tag{1}
\]
The literal source dictionary is
\[
\texttt{factorialMuntzTailRemainder}\,(N-1)\,(Nv)=\Phi_N(v)
\quad(v\ge0),
\]
and, with the already proved positive amplitude \(a_{N-1}\),
\[
T_{N-1}(x)=a_{N-1}e^{3x/2}\Phi_N(e^{-x})
\quad(x\le0).
\tag{2}
\]
These follow directly from [FactorialMuntzTailPrimitive.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailPrimitive.lean) and [FactorialTailPhase.lean](../../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailPhase.lean). The use of integer fractional parts in the periodic extension agrees with the corpus's natural-floor remainder on nonnegative arguments.

For the functions below define their Bohr square mean by
\[
\mathcal B(F)=\lim_{L\to\infty}\frac1L\int_0^L|F(v)|^2\,dv.
\]
**Paper theorem.** For every finitely supported complex coefficient family \((b_N)_{N\ge1}\), this limit exists and
\[
\mathcal B\!\left(\sum_N b_N\Phi_N\right)
\ge\frac1{8\pi^4}\sum_N|b_N|^2.
\tag{3}
\]
Consequently, the actual correction tails \((T_n)_{n\ge0}\) are linearly independent over \(\mathbb C\). Equation (3) is a uniform statement over all finite coefficient families, not merely a list of positive diagonals.

## Arithmetic separation of the two frequency families

The exact source parameter gives
\[
\alpha_N^3=\frac{4N+1}{4N},\qquad
\lambda_N^3=\frac{N^2(4N+1)}4.
\tag{4}
\]
Every \(\alpha_N\), and therefore every \(\lambda_N\), is irrational. Indeed, if the first ratio were a rational cube, its coprime positive numerator and denominator would both be integer cubes. They differ by one, which is impossible for two positive cubes: \((r+1)^3-r^3>1\) for \(r\ge1\).

Thus no positive integer harmonic of \(\lambda_N\) equals a positive integer harmonic of any integer \(M\). This excludes every mixed shifted/unshifted exact resonance. It does **not** exclude resonances between two shifted families. Those are classified exactly by
\[
k\lambda_N=\ell\lambda_M
\quad\Longleftrightarrow\quad
k^3N^2(4N+1)=\ell^3M^2(4M+1).
\tag{5}
\]
The proof of (3) allows all such shifted/shifted resonances.

A second, finite-scale separation follows from existing source bounds:
\[
\frac1{15}\le N\varepsilon_N\le\frac1{12}.
\tag{6}
\]
The lower bound follows from `sourceFactorialWidth_bounds` and `sourceFactorialWidth_le_collar`; the upper bound is `sourceFactorialCollar_scaled_le_twelfth` in [FactorialMuntzTailPhaseCells.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailPhaseCells.lean). Hence, for every integer \(m\ge2\),
\[
m\lambda_N-\lambda_{mN}
=m(N\varepsilon_N)-(mN)\varepsilon_{mN}
\ge\frac m{15}-\frac1{12}\ge\frac1{20}.
\tag{7}
\]
This separates these particular dilation frequencies uniformly. It is not a bound for all pairs of higher harmonics or for near resonances.

## The exact harmonic filter

The classical Bernoulli expansion gives
\[
C(u)=\frac1{12}-\frac1{2\pi^2}
\sum_{k\ge1}\frac{\cos(2\pi ku)}{k^2}.
\]
This series converges absolutely and uniformly; see [NIST DLMF, §24.8(i), equation 24.8.1](https://dlmf.nist.gov/24.8.E1).

Collecting frequencies in (1) yields
\[
P_0(u):=P(u)-\frac3{16}
=-\frac2{\pi^2}\sum_{k\ge1}\frac{\chi(k)}{k^2}\cos(2\pi ku),
\tag{8}
\]
where \(\chi(k)=1\) for odd \(k\), \(\chi(k)=-1\) for \(k\equiv2\pmod4\), and \(\chi(k)=0\) for \(4\mid k\). To check the filter, the coefficient before multiplication by \(-1/(2\pi^2k^2)\) is
\[
4-8\mathbf1_{2\mid k}+4\mathbf1_{4\mid k}=4\chi(k).
\]
The constant \(3/16\) cancels in every \(\Phi_N\).

## Coercivity of the integer family

For finite \(b\), let
\[
A_k(v)=\sum_N b_N\cos(2\pi kNv).
\]
Orthogonality of distinct positive integer cosine frequencies gives, for every positive integer \(k\),
\[
\|A_k\|_{L^2(0,1)}^2=\frac12\sum_N|b_N|^2.
\]
The elementary tail estimate
\[
\sum_{k\ge2}\frac{|\chi(k)|}{k^2}
\le\frac14+\sum_{k\ge3}\frac1{k^2}\le\frac34
\tag{9}
\]
follows by bounding the latter sum by \(\int_2^\infty x^{-2}\,dx\). The reverse triangle inequality applied to (8), with \(\chi(1)=1\), now gives
\[
\left\|\sum_N b_NP_0(N\,\cdot)\right\|_{L^2(0,1)}
\ge\frac2{\pi^2}\left(1-\frac34\right)
\frac{\|b\|_{\ell^2}}{\sqrt2}.
\]
Squaring proves the lower bound \(\|b\|_{\ell^2}^2/(8\pi^4)\). Every exchange of sums with the finite coefficient sum or with the \(L^2\) norm is justified by the absolute summability in (9).

## Orthogonal separation in the Bohr mean

Write
\[
A(v)=\sum_N b_NP_0(\lambda_Nv),\qquad
B(v)=\sum_N b_NP_0(Nv).
\]
Both are uniform limits of trigonometric polynomials. Their squared means and their mixed mean exist. The mean of a nonconstant exponential is zero, as follows by integrating it explicitly and dividing by \(L\). Equation (4) therefore implies
\[
\lim_{L\to\infty}\frac1L\int_0^L A(v)\overline{B(v)}\,dv=0.
\]
Termwise passage to the mean is legitimate: the double Fourier coefficients are absolutely summable, and every normalized exponential integral has modulus at most one. Consequently
\[
\mathcal B(A-B)=\mathcal B(A)+\mathcal B(B)
\ge\mathcal B(B)=\|B\|_{L^2(0,1)}^2.
\]
The integer-family bound proves (3). No separation between distinct shifted frequencies was assumed.

For linear independence, suppose a finite combination of actual tails vanishes. By (2), its phase combination with coefficients \(b_N=c_{N-1}a_{N-1}\) vanishes for \(v\ge1\). Its Bohr square mean is zero, since the remaining bounded interval contributes zero after division by \(L\). Equation (3) forces every \(b_N=0\), and positivity of every \(a_{N-1}\) forces every \(c_{N-1}=0\).

## Boundary and next mathematical obligation

The Bohr mean is not the physical or Weil energy. For example, the literal physical square mass transforms to
\[
\int_{-\infty}^0\left|\sum_n c_nT_n(x)\right|^2dx
=\int_1^\infty v^{-4}
\left|\sum_N c_{N-1}a_{N-1}\Phi_N(v)\right|^2dv.
\]
Bohr averaging assigns persistent weight to arbitrarily distant phase intervals; this physical integral suppresses them. Equation (3) supplies linear independence and an arithmetic comparison geometry, but no uniform lower bound for this weighted integral and no sign theorem for the complete Weil form.

The [finite-window coercivity proof](arithmetic-positivity-factorial-window-coercivity.md) supplies a separate paper theorem for this transport to physical square mass. The collar bounds separate the four signed first-harmonic frequency families uniformly; Montgomery–Vaughan estimates and the dominant first harmonic then give a fixed-window lower bound and a weighted physical Riesz estimate. That argument needs more than irrationality, and it still gives no signed Weil-energy estimate. Transport to logarithmic energy and control of prime and polar terms remain separate obligations. Related Gram-matrix analysis is established in [Alouges–Darses–Hillion](https://arxiv.org/abs/2006.02953) and [Werner Ehm, *On certain Gram matrices and their associated series*](https://arxiv.org/abs/2405.06349).

The exact theorem (3), its source dictionary, and linear independence require Lean certificates under the arithmetic positivity umbrella. The signed cross-scale Weil problem remains open here.
