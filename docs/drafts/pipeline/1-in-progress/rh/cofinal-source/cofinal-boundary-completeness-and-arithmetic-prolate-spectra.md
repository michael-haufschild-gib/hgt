# Cofinal boundary completeness and arithmetic prolate spectra for finite Weil forms

## Abstract

We establish three complementary results for the finite-aperture Weil forms that occur in the
Connes--Consani--Moscovici approach to the Riemann hypothesis. First, we correct the sign of the
polar contribution in the Fourier representation of the restricted screw-function form. The
corrected term is a rank-two kernel of signature ((1,1)), and its combination with the finite
prime sum is exactly the Fourier--Stieltjes transform of a critical Mellin defect measure. Second,
we prove that a fixed-width two-edge family is already complete for Weil's criterion: if the
Riemann hypothesis is false, then a residual set of fixed smooth boundary profiles has Weil form
unbounded below along a cofinal sequence of apertures. The proof uses Landau's oscillation theorem
and does not require a rightmost off-line zero. Third, for the constrained (h_0)--(h_4) prolate
source used in the finite spectral construction, we determine the universal exterior leakage
measure and prove logarithmically weighted nuclear convergence of its integer-dilation Gram
operators. After insertion of the exact finite-aperture von Mangoldt divisor mask, the resulting
arithmetic operators converge in trace norm to the explicit positive spectrum

\[
 \kappa_k=\frac{16}{11\pi}\frac{\log k}{k}\arcsin\frac1k,
 \qquad k\ge 2.
\]

Their Fredholm determinants converge locally uniformly, and the full raw radial prime charge is
the negative trace of the limiting operator. These results separate the two indispensable axes of
the finite-Weil program: an infinite arithmetic source carrier and a cofinal orientation detector.
The remaining Riemann-hypothesis-bearing theorem is a source-side incidence statement coupling
those axes in the critical Mellin graph topology.

## 1. Introduction

Let (Q_W) be Weil's quadratic form for the completed Riemann zeta function. Its zero-side
polarization is

\[
 Q_W(f,g)=\sum_\rho m_\rho\,widehat f(\rho)
     \overline{\widehat g(1-\overline\rho)},                 \tag{1.1}
\]

on the usual admissible class, with the sum taken symmetrically. Weil's criterion states that
(Q_W(f,f)\ge0) for all admissible (f) if and only if every nontrivial zero lies on the critical
line.

The finite-aperture program restricts the form to logarithmic intervals and approximates its low
spectral modes using prolate spheroidal wave functions. Two logically distinct problems then
appear.

1. The source must retain the complete prime module through the cofinal aperture limit.
2. The test family must remain sensitive to every possible off-line divisor, including one whose
   supremal horizontal displacement is not attained.

The first problem is operator-theoretic; the second is an orientation or negative-index problem.
The results below give an exact carrier for each. They do not prove the source-side positivity
which would couple them.

### 1.1 Main results

The first theorem gives the corrected finite-aperture symbol. With the Fourier convention

\[
 \widehat v(\xi)=\int_{\mathbb R}v(x)e^{i\xi x}\,dx,            \tag{1.2}
\]

put

\[
 m(\xi)=\Re\psi\!\left(\frac14+\frac{i\xi}{2}\right)-\log\pi. \tag{1.3}
\]

For (v\in H_0^1(-a,a)), the restricted form is

\[
 Q_{W,a}(v,v)=\frac1{2\pi}\int_{\mathbb R}W_a(\xi)
       |\widehat v(\xi)|^2\,d\xi,                              \tag{1.4}
\]

where

\[
\begin{aligned}
 W_a(\xi)&=m(\xi)
 -2\sum_{n\le e^{2a}}\frac{\Lambda(n)}{\sqrt n}
          \cos(\xi\log n)+P_a(\xi),\\
 P_a(\xi)&=
 \frac{2\sinh(a)\cos(2a\xi)+4\xi\cosh(a)\sin(2a\xi)}
      {\xi^2+1/4}.
                                                               \tag{1.5}
\end{aligned}
\]

The polar block is

\[
 2\cosh\frac{x-y}{2}
 =2\cosh\frac x2\cosh\frac y2
  -2\sinh\frac x2\sinh\frac y2,                              \tag{1.6}
\]

so it has rank at most two and signature ((1,1)); on the even sector it is positive rank one.

The second theorem is a restricted Weil criterion. Fix a compact interval
(K\Subset(0,L)) with nonempty interior. For (f\in C_K^\infty(0,L;\mathbb R)) and (a>L), set

\[
 \phi_{a,f}(x)=f(a-|x|).                                      \tag{1.7}
\]

Then

\[
 \mathrm{RH}\quad\Longleftrightarrow\quad
 Q_W(\phi_{a,f},\phi_{a,f})\ge0
 \quad\text{for all }a>L\text{ and }f\in C_K^\infty.         \tag{1.8}
\]

More strongly, if RH is false, a residual set of profiles (f) satisfies

\[
 \liminf_{a\to\infty}Q_W(\phi_{a,f},\phi_{a,f})=-\infty.       \tag{1.9}
\]

The third group of results concerns the constrained prolate source. Let (q_\lambda) be the
Fourier transform of the normalized zero-integral combination of the fixed even prolate modes
(0) and (4), and let (d_\lambda) be the mode-(4) concentration deficit. Then

\[
 \frac{\lambda|q_\lambda(\lambda x)|^2}{d_\lambda}\,dx
 \Longrightarrow
 \frac8{11\pi}\frac{dx}{x\sqrt{x^2-1}}                       \tag{1.10}
\]

on ([1,\infty)), with convergence of total masses. The integer-dilation Gram operators converge
in a logarithmically weighted nuclear topology to

\[
 w_k=\frac8{11\pi k}\arcsin\frac1k.                           \tag{1.11}
\]

After von Mangoldt symmetrization, the arithmetic spectrum is

\[
 \kappa_k=2(\log k)w_k
 =\frac{16}{11\pi}\frac{\log k}{k}\arcsin\frac1k.             \tag{1.12}
\]

This is an operator limit, not only a scalar asymptotic.

## 2. The corrected polar term

### 2.1 Distributional sign

In the screw-function representation, write

\[
 r_0(t)=-4(e^{t/2}+e^{-t/2}-2).
                                                               \tag{2.1}
\]

Then

\[
 r_0''(t)=-2\cosh(t/2).                                       \tag{2.2}
\]

The quadratic-form kernel is (-g''(x-y)). Hence the contribution of (r_0) is
(-r_0''=2\cosh(t/2)), not (r_0''). This sign is forced independently by direct integration by
parts and by the digamma reduction of the regular term. In the June 2026 version of Suzuki's
formula, the displayed (+\widehat{r_a''}) has the opposite sign from the distributional formulas
before and after it. Replacing it by (-\widehat{r_a''}) yields (1.5).

### 2.2 Fourier multiplier

Since (x-y\in(-2a,2a)), the polar multiplier is

\[
 P_a(\xi)=\int_{-2a}^{2a}2\cosh(t/2)e^{i\xi t}\,dt.            \tag{2.3}
\]

An elementary integration gives the second formula in (1.5). The apparent poles at
(\xi=\pm i/2) are removable because (2.3) is the Fourier transform of a compactly supported
function. At the origin,

\[
 P_a(0)=8\sinh a.                                             \tag{2.4}
\]

The physical-space factorization (1.6) gives

\[
 Q_{\mathrm{pol},a}(v,v)
 =2|\langle v,\cosh(\cdot/2)\rangle|^2
  -2|\langle v,\sinh(\cdot/2)\rangle|^2.                     \tag{2.5}
\]

It follows that functional-equation parity does not make the polar block positive in the full
space. It selects the positive channel only after restriction to the even sector.

## 3. The critical Mellin defect

Define

\[
 A(h)=\sum_{n\le e^h}\Lambda(n)n^{-1/2},\qquad
 R(h)=4\sinh(h/2)-A(h),\qquad h\ge0.                           \tag{3.1}
\]

For a zero-extended aperture vector (v), let

\[
 C_v(h)=\int_{\mathbb R}v(x+h)\overline{v(x)}\,dx.             \tag{3.2}
\]

The polar and prime measures are respectively

\[
 d[4\sinh(h/2)]=2\cosh(h/2)\,dh,
 \qquad
 dA(h)=\sum_{n\ge2}\Lambda(n)n^{-1/2}\delta_{\log n}.        \tag{3.3}
\]

Consequently the exact coupled term is

\[
 Q_{\mathrm{pol-prime},a}(v,v)
 =2\Re\int_{(0,2a]}C_v(h)\,dR(h).                             \tag{3.4}
\]

This formula is frequency-complete:

\[
 W_a(\xi)=m(\xi)+2\Re\int_{(0,2a]}e^{i\xi h}\,dR(h).          \tag{3.5}
\]

Thus the polar term and the prime main term may not be separated at the critical boundary.

### 3.1 Exact cancellation at zero frequency

Put (X=e^{2a}), (\Psi(X)=\sum_{n\le X}\Lambda(n)), and (E(X)=\Psi(X)-X). Partial summation
gives

\[
 \sum_{n\le X}\frac{\Lambda(n)}{\sqrt n}
 =2\sqrt X-1+\frac{E(X)}{\sqrt X}
  +\frac12\int_1^X E(t)t^{-3/2}\,dt.                          \tag{3.6}
\]

Since (P_a(0)=4\sqrt X-4/\sqrt X), the (4\sqrt X) terms cancel exactly and

\[
 W_a(0)=m(0)+2-\frac4{\sqrt X}
 -\frac{2E(X)}{\sqrt X}-\int_1^X E(t)t^{-3/2}\,dt.            \tag{3.7}
\]

The finite-aperture invariant is therefore a critical Mellin transform of the prime-number-theorem
error, not the prime main term.

### 3.2 Laplace colligation

For (\Re z>1/2),

\[
 \int_0^\infty e^{-zh}\,dR(h)
 =\frac1{z-1/2}+\frac1{z+1/2}
   +\frac{\zeta'(z+1/2)}{\zeta(z+1/2)}.                       \tag{3.8}
\]

The continuous term is the Laplace transform of (2\cosh(h/2)dh); the atomic term is the
absolutely convergent logarithmic derivative of zeta. Equation (3.8) shows that the signed defect
retains the divisor poles deleted by prime-main-term replacement.

## 4. A complete two-edge Weil criterion

We now prove (1.8)--(1.9).

### 4.1 Exact transform

For (f\in C_K^\infty(0,L;\mathbb R)), define

\[
 A_f(w)=\int_0^L f(s)e^{-ws}\,ds.                              \tag{4.1}
\]

Changing variables on the two components of (1.7) gives

\[
 F_{a,f}(w):=\int_{\mathbb R}\phi_{a,f}(x)e^{wx}\,dx
 =e^{aw}A_f(w)+e^{-aw}A_f(-w).                                \tag{4.2}
\]

The function (F_{a,f}) is even. Because (f) is real,
(F_{a,f}(\overline w)=\overline{F_{a,f}(w)}).

Let (w=\delta+i\gamma), (\delta>0), (\gamma>0), represent one off-line quartet. The quartet's
contribution to (1.1) is

\[
 4\Re F_{a,f}(w)^2.                                          \tag{4.3}
\]

### 4.2 Residual nonvanishing

For each fixed (w), the map (f\mapsto A_f(w)) is a nonzero continuous real-linear functional
on the Fréchet space (C_K^\infty). Its nonvanishing set is open and dense. Since the zeta divisor
is countable, the profiles satisfying

\[
 A_f(w)\ne0\quad\text{for every off-line representative }w   \tag{4.4}
\]

form a residual set.

Fix such a profile. If (Z_+) is the multiset of representatives and

\[
 \delta_*=\sup_{w\in Z_+}\Re w,                               \tag{4.5}
\]

the only potentially unbounded part of the off-line sum is

\[
 S_f(a)=4\Re\sum_{w\in Z_+}m_w A_f(w)^2e^{2aw}.               \tag{4.6}
\]

The middle terms and the (e^{-2aw}) terms obtained by expanding (4.3) are uniformly bounded.

### 4.3 Meromorphic Laplace transform

Repeated integration by parts gives, uniformly for (|\Re w|\le1/2),

\[
 |A_f(w)|\le C_{f,N}(1+|\Im w|)^{-N}                          \tag{4.7}
\]

for every (N). Together with (N(T)=O(T\log T)), this permits termwise Laplace transformation
for (\Re s>2\delta_*):

\[
 \mathcal L S_f(s)=2\sum_{w\in Z_+}m_w
 \left(
  \frac{A_f(w)^2}{s-2w}
  +\frac{\overline{A_f(w)^2}}{s-2\overline w}
 \right).                                                    \tag{4.8}
\]

The series extends meromorphically to the plane and has genuine poles at (2w) and
(2\overline w). Its Laplace abscissa is exactly

\[
 \sigma_c=2\delta_*.                                         \tag{4.9}
\]

Indeed the coefficient sum bounds (S_f(a)) by (O(e^{2\delta_*a})). Conversely, an abscissa
smaller than (2\delta_*) would place one of the genuine poles in the holomorphy half-plane of the
Laplace integral.

The meromorphic function (4.8) is nevertheless holomorphic near the real point (2\delta_*).
There is no real nontrivial zeta zero. Nonreal poles cannot accumulate at that finite point because
the zero divisor is locally finite, while poles of unbounded height leave every compact set.

### 4.4 Landau oscillation

Landau's oscillation theorem asserts that the Laplace transform of an eventually nonnegative real
function must be singular at its finite real abscissa of convergence. If (S_f) were bounded below
on a tail, adding a constant there and modifying a compact initial interval would produce such a
function. Its transform would differ from (4.8) by a function holomorphic near
(2\delta_*>0), contradicting Landau's theorem. Therefore

\[
 \liminf_{a\to\infty}S_f(a)=-\infty.                           \tag{4.10}
\]

The on-line contribution is uniformly bounded because

\[
 |F_{a,f}(i\gamma)|\le |A_f(i\gamma)|+|A_f(-i\gamma)|,         \tag{4.11}
\]

and the right side is rapidly decreasing. The bounded remainder in the off-line expansion cannot
offset (4.10). This proves (1.9).

Under RH, (1.1) is a sum of squared moduli, proving positivity on the two-edge family. Conversely,
if RH fails, (1.9) violates that positivity. The restricted criterion (1.8) follows.

## 5. The constrained prolate source

Let (e_{m,\lambda}), (m=0,4), be the normalized even fixed-mode eigenfunctions of the
time--band limiting operator on ([-\lambda,\lambda]), extended by zero. Write

\[
 \chi_m(\lambda)=\text{compressed Fourier eigenvalue},\qquad
 d_m(\lambda)=1-\chi_m(\lambda)^2,\qquad
 \ell_m(\lambda)=\int_{\mathbb R}e_{m,\lambda}(x)\,dx.        \tag{5.1}
\]

Define

\[
 g_\lambda=
 \frac{\ell_4e_{0,\lambda}-\ell_0e_{4,\lambda}}
      {\sqrt{\ell_0^2+\ell_4^2}},
 \qquad q_\lambda=\mathcal Fg_\lambda,
 \qquad d_\lambda=d_4(\lambda).                              \tag{5.2}
\]

Then (\|g_\lambda\|_2=1) and (\int g_\lambda=0). The fixed-mode concentration asymptotics and
the two-mode secular calculation give

\[
 \frac{\|1_{|y|>\lambda}q_\lambda\|_2^2}{d_\lambda}
 \longrightarrow\frac8{11}.                                  \tag{5.3}
\]

Set (c=2\pi\lambda^2). Dunster's radial expansion, normalized at the band edge, has the form

\[
 \frac{\mathcal F(e_{m,\lambda})(\lambda x)}
      {\mathcal F(e_{m,\lambda})(\lambda)}
 =A_{m,c}(x)
 \left[J_0(c\xi_{m,c}(x))+O(c^{-1}\mathcal E_0(c\xi_{m,c}(x)))\right],
                                                               \tag{5.4}
\]

uniformly for (1<x<\infty), where

\[
 \xi_{m,c}(x)\to\sqrt{x^2-1},\qquad A_{m,c}(x)\to x^{-1/2}.  \tag{5.5}
\]

Here (\mathcal E_0) denotes the standard Bessel envelope. Dunster's estimates are uniform at the
Bessel endpoint and at infinity.

## 6. Universal radial leakage

Define finite measures on ([1,\infty)) by

\[
 d\nu_\lambda(x)=
 \frac{\lambda|q_\lambda(\lambda x)|^2}{d_\lambda}\,dx.       \tag{6.1}
\]

### Theorem 6.1

The measures (\nu_\lambda) converge weakly, with convergence of total masses, to

\[
 d\nu_\infty(x)=\frac8{11\pi}\frac{dx}{x\sqrt{x^2-1}}.       \tag{6.2}
\]

In particular (\nu_\infty([1,\infty))=4/11).

### Proof

On compact subintervals of ((1,\infty)), insert the large-argument Bessel expansion

\[
 J_0(z)=\sqrt{\frac2{\pi z}}
 \left(\cos(z-\pi/4)+O(z^{-1})\right).                         \tag{6.3}
\]

The oscillatory term in (\cos^2\theta=(1+\cos2\theta)/2) vanishes by nonstationary phase, leaving

\[
 \frac{dx}{\pi x\sqrt{x^2-1}}.                                \tag{6.4}
\]

Dunster's envelope gives uniform endpoint tightness (O(\sqrt\eta)) on ([1,1+\eta]) and
far-tail tightness (O(R^{-1})) on ([R,\infty)). The endpoint response

\[
 \frac{|\mathcal F(e_{m,\lambda})(\lambda)|^2}
      {\lambda d_m(\lambda)}\longrightarrow2\pi              \tag{6.5}
\]

fixes the normalization. The mode-(0) exterior norm is (O(\lambda^{-4})) relative to mode (4)
at the level of square roots, so its square and cross term vanish after division by (d_\lambda).
The squared coefficient of mode (4) in (5.2) tends to (8/11), proving (6.2). Finally

\[
 \int_1^\infty\frac{dx}{x\sqrt{x^2-1}}=\frac\pi2.             \tag{6.6}
\]

## 7. Weighted nuclear dilation spectrum

For (k\ge1), define

\[
 H_{\lambda,k}(s)=\sqrt{\lambda e^s}\,
 q_\lambda(k\lambda e^s),\qquad s\ge0,                        \tag{7.1}
\]

and the Gram matrix

\[
 G_\lambda(j,k)=\langle H_{\lambda,j},H_{\lambda,k}\rangle_{L^2(ds)}. \tag{7.2}
\]

The diagonal identity

\[
 G_\lambda(k,k)=\frac1k\int_{k\lambda}^\infty|q_\lambda(y)|^2\,dy \tag{7.3}
\]

and Theorem 6.1 give

\[
 \frac{G_\lambda(k,k)}{d_\lambda}\longrightarrow
 w_k:=\frac8{11\pi k}\arcsin\frac1k.                         \tag{7.4}
\]

Let (\Omega_k=1+\log k) and (W=\operatorname{diag}(w_k)).

### Theorem 7.1

The Gram matrices define positive trace-class operators on (\ell^2(\mathbb N_+)), and

\[
 \sum_{j,k\ge1}(\Omega_j+\Omega_k)
 \left|\frac{G_\lambda(j,k)}{d_\lambda}-\delta_{jk}w_k\right|
 \longrightarrow0.                                           \tag{7.5}
\]

Consequently

\[
 \left\|\Omega^{1/2}
 \left(d_\lambda^{-1}G_\lambda-W\right)
 \Omega^{1/2}\right\|_{\mathcal S_1}\longrightarrow0.       \tag{7.6}
\]

### Proof

The radial envelope gives (G_\lambda(k,k)/d_\lambda\le C/k^2). Dominated convergence handles the
diagonal part of (7.5).

For (j,k\ge2), (j\ne k), the exact Liouville phases give

\[
 |G_\lambda(j,k)|
 \le \frac{C d_\lambda}{cjk|j-k|}.                            \tag{7.7}
\]

The phase-preserving remainder estimate follows directly from the transformed radial equation.
If

\[
 W''+c^2W=\psi W,                                             \tag{7.8}
\]

define

\[
 a_+=\frac12e^{-icx}\left(W+\frac{W'}{ic}\right),\qquad
 a_-=\frac12e^{icx}\left(W-\frac{W'}{ic}\right).             \tag{7.9}
\]

Then exactly

\[
 a_+'=\frac{e^{-icx}\psi W}{2ic},\qquad
 a_-'=-\frac{e^{icx}\psi W}{2ic}.                             \tag{7.10}
\]

The exterior potential is short range, so the amplitudes have uniformly bounded variation of
order (c^{-1}). One nonstationary integration by parts proves (7.7), and the Hilbert-kernel sum is
logarithmically summable.

The exceptional first row has a stationary point entering the Bessel endpoint. Uniformly for
(2\le k\le\lambda^2), the pole-uniform Bessel coordinate gives

\[
 \frac{|G_\lambda(1,k)|}{d_\lambda}
 \le Cc^{-1/2}k^{-2}+Cc^{-1}k^{-1}.                           \tag{7.11}
\]

For (k>\lambda^2), the second factor is uniformly exterior and (7.10) yields

\[
 \frac{|G_\lambda(1,k)|}{d_\lambda}\le Ck^{-2}.              \tag{7.12}
\]

The logarithmically weighted low row is
(O(c^{-1/2}+c^{-1}\log^2c)), while the high row is
(O(\lambda^{-2}\log\lambda)). Symmetry handles the first column. This proves (7.5). Decomposition
into matrix units and (2\sqrt{\Omega_j\Omega_k}\le\Omega_j+\Omega_k) gives (7.6).

## 8. The arithmetic trace-class operator

At aperture (\log\lambda), only prime shifts (q\le\lambda^2) occur. Define

\[
 a_\lambda(k)=\sum_{\substack{q\mid k\\2\le q\le\lambda^2}}\Lambda(q). \tag{8.1}
\]

Then

\[
 0\le a_\lambda(k)\le\log k,
 \qquad a_\lambda(k)=\log k\quad(k\le\lambda^2).              \tag{8.2}
\]

Define the symmetric matrix

\[
 \mathcal A_\lambda(j,k)=
 (a_\lambda(j)+a_\lambda(k))G_\lambda(j,k).                   \tag{8.3}
\]

This is the matrix realization of the anticommutator between the dilation Gram operator and the
finite-aperture divisor mask.

### Theorem 8.1

For all sufficiently large (\lambda), (\mathcal A_\lambda) is self-adjoint and trace class, and

\[
 \left\|d_\lambda^{-1}\mathcal A_\lambda
 -\operatorname{diag}(\kappa_k)\right\|_{\mathcal S_1}
 \longrightarrow0,                                           \tag{8.4}
\]

where (\kappa_k) is given by (1.12). More strongly, the matrices converge in the projective norm

\[
 \sum_{j,k\ge1}left|
 \frac{\mathcal A_\lambda(j,k)}{d_\lambda}
 -\delta_{jk}\kappa_k\right|\longrightarrow0.                \tag{8.5}
\]

### Proof

Let

\[
 E_\lambda(j,k)=d_\lambda^{-1}G_\lambda(j,k)-\delta_{jk}w_k. \tag{8.6}
\]

By (8.2),

\[
 a_\lambda(j)+a_\lambda(k)\le\Omega_j+\Omega_k.              \tag{8.7}
\]

Theorem 7.1 therefore makes the weighted error contribution tend to zero. The remaining diagonal
error is

\[
 2\sum_k|a_\lambda(k)-\log k|w_k.                             \tag{8.8}
\]

Every fixed summand is eventually zero and is dominated by the summable sequence
(2(\log k)w_k). Dominated convergence proves (8.5). The projective matrix norm dominates the
trace norm because each matrix unit has trace norm one, proving (8.4).

### 8.1 Spectrum and determinant

The limiting operator is positive. Hence the total negative spectral mass satisfies

\[
 \operatorname{Tr}\left[(d_\lambda^{-1}\mathcal A_\lambda)_-\right]
 \longrightarrow0.                                           \tag{8.9}
\]

Continuity of the Fredholm determinant in trace norm gives, locally uniformly on (\mathbb C),

\[
 \det\!\left(I+z\,d_\lambda^{-1}\mathcal A_\lambda\right)
 \longrightarrow
 D_{\mathrm{arith}}(z):=\prod_{k\ge2}(1+z\kappa_k).           \tag{8.10}
\]

Since

\[
 \kappa_k\sim\frac{16}{11\pi}\frac{\log k}{k^2},            \tag{8.11}
\]

the zero sequence has exponent of convergence (1/2); the genus-zero product
(D_{\mathrm{arith}}) is an entire function of order (1/2).

### 8.2 Prime charge as a trace

The raw radial finite-aperture prime term is

\[
 \mathcal P_\lambda
 =-2\sum_{k\ge2}a_\lambda(k)\sum_{j\ge1}G_\lambda(j,k).       \tag{8.12}
\]

Symmetry gives

\[
 \mathcal P_\lambda=-\sum_{j,k\ge1}\mathcal A_\lambda(j,k). \tag{8.13}
\]

The projective convergence (8.5), which is stronger than trace-norm convergence, permits pairing
with the all-ones matrix. Therefore

\[
 \frac{\mathcal P_\lambda}{d_\lambda}
 \longrightarrow
 -\operatorname{Tr}\operatorname{diag}(\kappa_k)
 =-\frac{16}{11\pi}\sum_{k\ge2}
   \frac{\log k}{k}\arcsin\frac1k.                            \tag{8.14}
\]

Numerically, the positive trace is

\[
 \sum_{k\ge2}\kappa_k=0.4399171643919988702\ldots.           \tag{8.15}
\]

Expanding the arcsine series gives the equivalent identity

\[
 \sum_{k\ge2}\frac{\log k}{k}\arcsin\frac1k
 =-\sum_{r\ge0}\frac{\binom{2r}{r}}{4^r(2r+1)}\zeta'(2r+2).  \tag{8.16}
\]

## 9. Constraint and orientation

The preceding theorems identify two independent structures.

The prolate limit is a source constraint. It transports the integer-dilation module, the exact
finite-prime divisor weights, a positive trace-class spectrum, and a determinant. None of these
objects uses the horizontal position of a zeta zero.

The two-edge theorem is an orientation detector. It proves that every off-line divisor forces
cofinal negative Weil values, even when its transverse supremum is not attained. It does not
construct those values from a positive Euler factorization.

Thus a successful finite-Weil construction must provide a cofinal incidence section

\[
 \text{arithmetic source constraint}
 \quad\longleftrightarrow\quad
 \text{Weil/Krein orientation}.                               \tag{9.1}
\]

Neither coordinate alone is sufficient. This is not merely philosophical: finite rational
surgeries of a meromorphic source can preserve all differential-translation relations while
changing the exact negative-square index. The source field and the orientation chamber are
mathematically independent data; the arithmetic realization must select and transport their
coupling.

For the present CCM source, the exact unresolved statement is the following graph-domain theorem.

> **Critical-incidence theorem.** The intact Poisson-resummed constrained prolate tail converges at
> leakage scale in the graph topology of the signed measure (dR), with the polar counterterm and
> the finite von Mangoldt channel retained jointly; this convergence induces the nonnegative
> cofinal orientation required by (1.8).

The theorem has two layers. Its unconditional analytic layer must first justify the coupled
polar--prime limit. Its sign layer is RH-bearing: by the two-edge completeness theorem, cofinal
nonnegativity on the complete boundary family is already equivalent to RH.

This locates the remaining burden sharply. Finite self-adjoint determinants, a finite prolate
spectrum, or the raw arithmetic trace-class limit do not by themselves carry the Xi divisor.
A completed proof must additionally transport the distinguished orientation through a locally
uniform zero-preserving determinant limit, or prove the equivalent cofinal Weil lower bound.

## 10. References

1. E. Bombieri, *Remarks on Weil's quadratic functional in the theory of prime numbers. I*, Rend.
   Mat. Acc. Lincei **11** (2000), 183--233.
2. A. Connes and C. Consani, *Spectral triples and zeta-cycles*, arXiv:2106.01715.
3. A. Connes, C. Consani, and H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
4. T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, J. Classical Analysis
   **11** (2017), 1--21; arXiv:1601.00699.
5. W. H. J. Fuchs, *On the eigenvalues of an integral equation arising in the theory of
   band-limited signals*, J. Math. Anal. Appl. **9** (1964), 317--330.
6. H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004.
7. H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory*,
   Cambridge Studies in Advanced Mathematics 97, 2007.
8. B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005.
9. D. Slepian, *Some asymptotic expansions for prolate spheroidal wave functions*, J. Math. Phys.
   **44** (1965), 99--140.
10. M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096, version of
    9 June 2026.
11. A. Weil, *Sur les « formules explicites » de la théorie des nombres premiers*, Comm. Sém.
    Math. Univ. Lund, 1952, 252--265.
