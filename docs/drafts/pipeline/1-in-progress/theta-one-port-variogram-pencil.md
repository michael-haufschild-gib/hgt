# Theta Xi as a one-port variogram pencil

- **ID:** TQFQ-PORT
- **Stage:** 1-in-progress
- **Type:** finite algebraic, actual-root chirality, modular-seam, zero-free half-transform and lossless half-line covariance paper proofs; source connection value omission open
- **Source:** literal theta CDF action and the exact Xi determinant operator

## Reinterpretation

The [theta CDF-action quotient](theta-quantile-fourier-action-quotient.md) places every nonzero Xi zero in the spectrum of a matrix

\[
D_{mn}=\frac{\Phi_m-\Phi_{m-n}}{2\pi n},\qquad m,n\in\mathbb Z\setminus\{0\},
\]

where \(\Phi_j=\int_0^1q(t)(1-\cos(2\pi jt))\,dt\) is a literal-source variogram. The variogram supplies a strictly positive bulk energy. Away from a neutral clock direction, possible nonreal spectrum is measured by the phase mismatch between **two scalar boundary moments** of the same mode. At a neutral direction, the boundary term must saturate that energy exactly. This identifies the finite one-port obstruction. The analysis below shows that its signed area has a universal resolvent sign; the remaining source-selected object is the nonperturbative connection coefficient between the two decaying branches.

## Exact finite identity

Fix a finite \(I\subset\mathbb Z\setminus\{0\}\), and use the compression \(D^I\). For \(y\in\mathbb C^I\), set \(x_n=ny_n\) and

\[
S(y)=\sum_{n\in I}y_n,\quad
T(y)=\sum_{n\in I}\Phi_ny_n,\quad
J(y)=\sum_{n\in I}n|y_n|^2,
\]

\[
E(y)=\int_0^1q(t)\left|\sum_{n\in I}y_n(e^{2\pi int}-1)\right|^2dt.
\]

All integrals are finite because each exponential difference vanishes at both singular endpoints. The action is strictly positive: \(E(y)>0\) for \(y\ne0\), since \(q>0\) and a nonzero trigonometric polynomial cannot vanish almost everywhere. With the standard Hermitian pairing, the exact identity is

\[
\boxed{\quad 2\pi\langle y,D^I x\rangle=E(y)-\overline{S(y)}T(y).\quad} \tag{1}
\]

Indeed, write \(Q(y)=\sum_{m,n\in I}\overline y_m y_n\Phi_{m-n}\), which is real because \(\Phi_{-j}=\Phi_j\). Expanding the integral gives \(E=\overline T S+\overline S T-Q\); multiplying the matrix by \(x_n=ny_n\) gives \(2\pi\langle y,D^I x\rangle=\overline T S-Q\). Subtraction proves (1).

If \(D^I x=\lambda x\) and \(x\ne0\), then

\[
\boxed{\quad 2\pi\lambda J(y)=E(y)-\overline{S(y)}T(y).\quad} \tag{2}
\]

In particular, a nonreal eigenvalue requires \(S(y)\ne0\): if \(S=0\), the right side is strictly positive real, so \(J\ne0\) and \(\lambda=E/(2\pi J)\in\mathbb R\). When \(J\ne0\), the entire imaginary part is

\[
\operatorname{Im}\lambda
=-\frac{\operatorname{Im}(\overline S T)}{2\pi J}. \tag{3}
\]

For an actual finite Fourier packet \(f=\sum_{n\in I}x_ne_n\), the moments are the two existing pinned-Volterra ports:

\[
S=-2\pi i\int_0^1Vf(t)\,dt,
\qquad
T=-2\pi\int_0^1Bf(t)\,dt.
\]

Here \(Vf=\sum_n x_n(e_n-1)/(2\pi in)\), \(B=iM_qV\), and reflection of \(q\) removes the sine integral. Thus (1) is a source-boundary energy law, not an arbitrary matrix factorization.

## Exact chirality of the actual root primitive

The [quantile root-mode construction](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmQuantileRootMode.lean), [sharp theta-domain theorem](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaCompactDivisorEigenmode.lean), and [endpoint theorem](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaRootEndpoints.lean) give an actual \(H^1_0(0,1)\) primitive \(g(t)=\mathrm{rootH}(z,t)\) for each theta zero \(z=u+iv\) in the natural strip. Its derivative is the \(L^2\) root mode minus one, and

\[
g'(t)+1=-izq(t)g(t).
\]

Set \(\mathcal J(g)=\sum_{n\ne0}n|\widehat g(n)|^2\), which converges absolutely because \(g\in H^1\). Define the *causal source correlation*

\[
I(z)=\int_{0<t<s<1}e^{iz(Q(s)-Q(t))}\,dt\,ds
     =\int_0^\infty e^{izd}w(d)\,dd,
\qquad
w(d)=\int_{\mathbb R}\rho(x)\rho(x+d)\,dx,
\]

where \(\rho=k/M\). At a zero, \(\int g=I(z)\): the complete character integral vanishes, so the left primitive in \(g=-e^{-izQ(t)}\int_0^t e^{izQ(s)}ds\) becomes the negative of the right tail. Pairing the differential equation with \(\overline g\), integrating, and using \(g(0)=g(1)=0\) gives

\[
2\pi i\mathcal J(g)+\overline{I(z)}=-iz\,\mathcal E(z),
\qquad
\mathcal E(z)=\int_0^1q(t)|g(t)|^2dt>0. \tag{4}
\]

The real part of (4), already represented by the corpus's ordered-correlation flux, is \(\operatorname{Re}I(z)=v\mathcal E(z)\). Its imaginary part supplies the new signed Hardy-energy identity

\[
\boxed{\quad \mathcal J(g)
 =-\frac{\operatorname{Re}(zI(z))}{2\pi v}\quad(v\ne0).} \tag{5}
\]

There is an exact sign evaluation of the numerator. Let \(\varphi(\omega)=\int\rho(x)e^{i\omega x}dx\) and \(d\nu(\omega)=|\varphi(\omega)|^2d\omega/(2\pi)\). Wiener--Khinchin gives \(w(d)=\int e^{i\omega d}d\nu(\omega)\); \(\nu\) is even. For \(v>0\), Fubini and the elementary Laplace integral yield

\[
I(z)=i\int_{\mathbb R}\frac{d\nu(\omega)}{z+\omega},
\qquad
\operatorname{Re}(zI(z))
=2uv\int_{\mathbb R}
\frac{\omega^2\,d\nu(\omega)}
{((u+\omega)^2+v^2)((u-\omega)^2+v^2)}. \tag{6}
\]

The integral is strictly positive for \(u\ne0\), because \(\varphi(0)=1\). For \(v<0\), evenness gives \(I(z)+I(-z)=\varphi(z)^2=0\) at a zero, reducing to \(-z\) in the upper half-plane. Consequently every hypothetical off-real theta zero obeys the **universal chirality law**

\[
\boxed{\quad \operatorname{sgn}\mathcal J(g)=-\operatorname{sgn}(\operatorname{Re}z)
\quad (\operatorname{Im}z\ne0,\ \operatorname{Re}z\ne0).\quad} \tag{7}
\]

This holds for any sufficiently regular even positive source, not only theta. It therefore classifies the hypothetical root mode but cannot exclude it by itself. A genuine theta-specific jump would derive a conflicting Hardy orientation from the literal modular/prime atom source while retaining this exact primitive and its divisor occurrence. The source-to-Hardy comparison is the hard mathematical problem; replacing it with a generic positive-real or parity argument would only reproduce (4).

## Conjecture loop and whole-chain consequence

1. **Conjecture:** conditional negative type of \(\Phi\) alone makes \(D\) real-spectrum. **Fails as a sufficient principle:** the corpus's even, strictly log-concave two-Gaussian source has nonreal Fourier zeros while possessing the same positive variogram construction. Equation (2) identifies the missing channel precisely: \(\overline S T\).
2. **Conjecture:** erase that channel by taking \(S=0\). **Proved for finite compressions:** this gives real eigenvalues, but no source theorem puts all Xi modes in \(S=0\). Erasing the pinned mean would also risk changing the determinant and losing Xi occurrence.
3. **Test and pivot:** (4)--(7) classify the signed Hardy energy of actual modes. The all-parameter Fourier identity (13) then proves that its sign is already fixed for every anti-causal resolvent, with or without an Xi zero. The root-sensitive datum is instead the connection coefficient (14); a source law must control that coefficient directly, beyond generic autocorrelation passivity.

The first prime-flow test is exact but supplies no independent orientation. For \(\Psi_p(t)=F(Q(t)+\log p)\), the signed area \(\mathcal J(g)=(2\pi)^{-1}\operatorname{Im}\int\overline g\,g'\) is invariant under the increasing reparametrization \(t\mapsto\Psi_p(t)\). The root formula gives an affine shift

\[
g(\Psi_p(t))=p^{-iz}g(t)+a_{p,z}(t),\qquad
a_{p,z}(t)=-p^{-iz}e^{-izQ(t)}
  \int_t^{\Psi_p(t)}e^{izQ(s)}ds.
\]

Thus the aperture term and its mixed area pay exactly for \((1-p^{2v})\mathcal J(g)\). This is a reparametrization identity for *every* positive source, so it cannot prove RH. The promising next operation is literal prime **atom deletion before** passing to CDF coordinates: that changes the source mode itself, rather than relabeling the same loop. The corpus's rank-one [prime-translation anomaly](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmPrimeTranslationAnomaly.lean) is the exact source-level comparison to use.

## Prime-atom covariance at the modular seam

There is a lawful way to carry that deletion into the *same actual root mode*, without treating the signed first atom as a positive density on the whole line. Write \(k=\sum_{n\ge1}a_n\) for the completed theta source, \(h=a_1\), and

\[
a_n(x)=n^{-1/2}h(x+\log n),\qquad
R_z(x)=\int_x^\infty e^{iz(y-x)}k(y)\,dy,\qquad
r_z(x)=\int_x^\infty e^{iz(y-x)}h(y)\,dy.
\]

At an Xi zero \(z\), the complete source mode is \(U_z(x)=iR_z(x)\) for \(x\ge0\), and evenness plus zero incidence gives \(U_z(-x)=-iR_{-z}(x)\) for \(x\ge0\). The quantile root primitive is \(g(F(x))=-iU_z(x)/M\), where \(M=\int_{\mathbb R}k\). A change of variables in the signed Hardy area therefore gives the exact **modular-seam law**

\[
\boxed{\quad
2\pi M^2\mathcal J(g)=\mathcal A(z)-\mathcal A(-z),\qquad
\mathcal A(w)=\operatorname{Im}\int_0^\infty\overline{R_w(x)}R'_w(x)\,dx.
\quad} \tag{8}
\]

On \(x\ge0\), every \(a_n\) is nonnegative, and the existing Gaussian atom bound in [Euler--Möbius Stokes inversion](../../../../formal/GaloisForLFunctions/RHTower/EulerHedenmalmMobiusStokesInverse.lean) has the form \(|a_n(x)|\le C e^{-x}e^{-\pi n^2/2}\). For \(|\operatorname{Im}w|<1\), the equation \(R'_{n,w}=-a_n-iwR_{n,w}\) then shows \(\sum_n R_{n,w}\) converges absolutely in \(H^1(0,\infty)\), with \(R_{n,w}(x)=n^{-1/2}r_w(x+\log n)\). Thus both area terms in (8) have an absolutely convergent, source-faithful double expansion:

\[
\boxed{\quad
\mathcal A(w)=\sum_{m,n\ge1}\frac1{\sqrt{mn}}\operatorname{Im}
\int_0^\infty\overline{r_w(x+\log m)}\,r'_w(x+\log n)\,dx.
\quad} \tag{9}
\]

Regrouping the absolutely convergent sum by \(m=dr,n=ds\), \(\gcd(r,s)=1\), yields a more explicit arithmetic kernel:

\[
\mathcal A(w)=\sum_{\substack{r,s\ge1\\(r,s)=1}}\frac1{\sqrt{rs}}
\operatorname{Im}\int_{\log r}^\infty
H_{\lfloor e^y/r\rfloor}\,\overline{r_w(y)}
r'_w\bigl(y+\log(s/r)\bigr)\,dy,
\qquad H_N=\sum_{d=1}^N\frac1d. \tag{10}
\]

The harmonic cutoff is forced by the seam \(x=0\): a pair with common divisor \(d\) contributes only when \(y\ge\log(dr)\). This is the arithmetic information absent from the universal autocorrelation identity (6). Equations (8)--(10) are paper derivations from the corpus's atom scaling, positive-half-line bounds, Green commutation, and root reflection; they have **not** been formalized in Lean. The all-parameter identity (13) below shows that their total sum has a universal sign. Any useful arithmetic estimate must therefore enter a different, connection-sensitive observable, rather than assert an opposite sign for this area.

The first-atom test gives a useful decision about where such a bound must come from. On \(x\ge0\),
\[
h(x)=4\pi^2e^{9x/2}(1-c e^{-2x})e^{-\pi e^{2x}},
\qquad c=3/(2\pi)\in(0,1),
\]
so \((\log h)''=-4c e^{-2x}/(1-c e^{-2x})^2-4\pi e^{2x}<0\). For any real \(v\), set
\[
K_v(x)=\int_0^\infty e^{-vt}h(x+t)\,dt,\qquad
L_v(x)=\int_0^\infty t e^{-vt}h(x+t)\,dt.
\]
Strict log-concavity gives \(h(x+s)h(x+t)>h(x)h(x+s+t)\) for \(s,t>0\). Integrating over \(s,t\) proves the strict tail Turán law \(K_v(x)^2>h(x)L_v(x)\). The first-atom area \(\mathcal A_h(w)=\operatorname{Im}\int_0^\infty\overline{r_w}r'_w\) therefore satisfies the exact local orientation
\[
\left.\frac{\partial}{\partial u}\mathcal A_h(u+iv)\right|_{u=0}
=\int_0^\infty\bigl(hL_v-K_v^2\bigr)\,dx<0. \tag{11}
\]
The same argument applies to every shifted atom \(a_n=n^{-1/2}h(\,\cdot+\log n)\). Every diagonal \(m=n\) term of (9) has the **same** near-axis chirality as the hypothetical off-axis root in (7), even after subtracting its \(-z\) reflection. Thus no diagonal atom can supply a contrary *near-axis* orientation; any such effect must involve off-diagonal integer interference and the seam cutoffs in (10). This is a local diagnostic, not a constraint at known Xi zeros. Equation (11) is presently a paper proof only.

The corpus already proves [strict log-concavity of the completed source](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingQuantumEnergyInequalityEndpoint.lean), so the same tail Turán argument applies to \(k\) itself. Consequently the **complete** seam area also has negative first horizontal derivative at \(u=0\) for every fixed vertical tilt \(v\) in the source strip. The off-diagonal atom sum does not reverse the orientation near the imaginary axis either. This moves the possible source-specific producer to a zero-local, oscillatory comparison at nonzero frequency: static curvature and termwise atom signs cannot give the contrary orientation globally.

There is a second, cofinal test. Because the complete \(k\) is even and Schwartz, integration by parts in the one-sided Green integral, uniformly for \(v\) in any fixed compact interval, gives in \(H^1(0,\infty)\)
\[
R_{u+iv}
=\frac{i k}{u}+\frac{v k-k'}{u^2}+O_{H^1}(|u|^{-3}).
\]
Taking the imaginary part of \(\int\overline R R'\), then integrating \(kk''\) by parts with \(k'(0)=0\), yields
\[
\boxed{\quad
\mathcal A(u+iv)
=-\frac{2}{u^3}\int_0^\infty (k'(x))^2\,dx
+O(|u|^{-4}),\qquad
\mathcal A(u+iv)-\mathcal A(-u-iv)
=-\frac{4}{u^3}\int_0^\infty (k'(x))^2\,dx
+O(|u|^{-4}).
\quad} \tag{12}
\]
The leading term is strictly negative for large positive \(u\), independently of the arithmetic atom split and uniformly across the natural vertical strip. Thus the proposed *unconditional opposite sign for the total seam area* fails at both small and large horizontal frequency. A viable zero-local comparison must cancel this generic kinetic term before using the rational-pair arithmetic; no such renormalized source identity has yet been derived. Equation (12) is a paper asymptotic, not a Lean theorem.

An exact all-parameter check goes further. For \(v>0\), define the anti-causal whole-line response \(V_z(x)=iR_z(x)\), \(z=u+iv\). It belongs to \(H^1(\mathbb R)\) whether or not \(\Xi(z)\) vanishes. With the Fourier convention \(\widehat f(\omega)=\int_{\mathbb R}f(x)e^{i\omega x}dx\), its ODE gives
\[
\widehat V_z(\omega)=\frac{\widehat k(\omega)}{\omega-z},\qquad
\operatorname{Im}\int_{\mathbb R}\overline{V_z}V'_z\,dx
=-\int_{\mathbb R}\frac{\omega|\widehat k(\omega)|^2}
  {(\omega-u)^2+v^2}\,\frac{d\omega}{2\pi}. \tag{13}
\]
Evenness of \(|\widehat k|^2\) makes (13) strictly negative for \(u>0\) and strictly positive for \(u<0\), by pairing \(\omega\) and \(-\omega\). At an Xi zero, \(V_z\) equals the causal source mode \(U_z\), so (13) is the all-parameter origin of (7). The signed area is a **universal resolvent receiver**; it is not itself an independent theta-specific producer.

The actual source-selected datum is the connection between the left- and right-decaying solutions. For all \(z\), let
\[
U_z(x)=-i e^{-izx}\int_{-\infty}^x e^{izy}k(y)\,dy,\qquad
V_z(x)= i e^{-izx}\int_x^\infty e^{izy}k(y)\,dy.
\]
They solve the same first-order forced equation and have the exact homogeneous difference
\[
\boxed{\quad U_z(x)-V_z(x)=-i e^{-izx}\Xi(z).\quad} \tag{14}
\]
Thus Xi is the connection coefficient of two source-selected decaying branches. At a zero, the branches coincide and the mode inherits the superexponential theta decay at **both** ends; ordinary \(H^1\) membership in the upper half-plane only selects the right branch and misses this condition. The next substantive attack must find a theta-arithmetic constraint on the connection coefficient (14), potentially using the one-sided shell expansion and the modular seam, rather than seek an opposite sign for (13). The two-ended incidence is already in [the Lean corpus](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmShiftedSourceEquationExact.lean); the reinterpretation and its proposed arithmetic attack do not establish nonvanishing.

This connection is invisible to every fixed-order large-frequency jet. If \(H(z)=\int_0^\infty k(x)e^{izx}dx\), then \(\Xi(z)=H(z)+H(-z)\). Repeated integration by parts gives boundary expansions for both \(H\) terms, but evenness of the smooth completed \(k\) makes every algebraic boundary coefficient cancel in their sum. The corpus proves the arithmetic version: [each completed odd seam jet is the sum of the shell jets and vanishes](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspShellHedenmalmCurrent.lean). Individual reflected shells retain algebraic Fourier tails; only the complete modular assembly cancels them all. The remaining RH-bearing datum is the full, nonperturbative connection coefficient after this all-order cancellation. A finite jet, total-area sign, or first-atom dominance estimate cannot see its zero set without a new uniform remainder law.

## Positive half-transform and the actual connection problem

There is a positive theorem on the *branch* that does not assume RH. The corpus proves \(k>0\), evenness, and [strict log-concavity on the whole line](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingQuantumEnergyInequalityEndpoint.lean). Therefore \(k'(x)<0\) for \(x>0\). Set \(\mu(x)=-k'(x)>0\) on that ray; \(\int_0^\infty\mu=k(0)\). Integration by parts gives
\[
H(z)=\frac{i}{z}\int_0^\infty\mu(x)(1-e^{izx})\,dx,\qquad
\Xi(z)=\frac{2}{z}\int_0^\infty\mu(x)\sin(zx)\,dx. \tag{15}
\]
If \(\operatorname{Im}z>0\), then
\[
\operatorname{Re}\int_0^\infty\mu(x)(1-e^{izx})\,dx
\ge\int_0^\infty\mu(x)(1-e^{-(\operatorname{Im}z)x})\,dx>0.
\]
For real \(z\ne0\), the real part is \(\int\mu(1-\cos(zx))>0\). Also \(H(0)=\int_0^\infty k>0\). Hence **the literal one-sided theta transform \(H\) has no zero in the closed upper half-plane**. This conclusion is a paper proof using already formalized curvature and positivity; the half-transform statement itself is not yet in Lean.

Thus \(B(z)=-H(-z)/H(z)\) is analytic throughout the upper half-plane, and \(\Xi(z)=0\) there exactly when \(B(z)=1\). On the real boundary \(|B|=1\); at the imaginary axis \(B(iv)<-1\) for \(v>0\). This is a concrete source-selected connection map with a proved zero-free denominator, not a claim that its forbidden value is already excluded. The hard new question is whether the modular and prime structure of \(\mu\) forces \(B\) to omit \(1\) in the interior, despite its oscillating boundary phase. Unlike \(k\) on the positive ray, \(\mu=-\sum_n a'_n\) is **not** termwise positive: the first seam slope is positive, higher shell slopes negative, and their sum vanishes at the modular center. Its positivity is a collective arithmetic fact, so a successful phase theorem would have to use that completion rather than generic monotonicity alone.

The search found an existing, different [zero-free completed-density de Branges channel](../../../../formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedDensityTransversePick.lean) and its exact Xi projective collision. Having two zero-free denominators does not by itself constrain their common collision: both reflected sums are fixed multiples of Xi. The missing theorem remains a source-derived phase restriction that excludes the collision, rather than another regular chart.

## Lossless half-line covariance and a rank-two arithmetic source

The one-sided transform's zero-free half-plane gives a different interpretation of what arithmetic data are sufficient. Put \(k_+(x)=k(x)1_{x\ge0}\) and, for \(t\ge0\),
\[
C(t)=\int_0^\infty k(x)k(x+t)\,dx.
\]
The even extension \(C(|t|)\) is the autocorrelation of \(k_+\). Thus its Fourier transform on the real axis is
\[
S(u)=2\int_0^\infty C(t)\cos(ut)\,dt
    =|H(u)|^2=H(u)H(-u)>0. \tag{16}
\]
This is a **lossless** positive observable for this source, despite the usual phase ambiguity of autocorrelations. Theta's superexponential right tail makes both \(H(z)\) and \(S(z)=H(z)H(-z)\) entire of order at most one. The proved upper-half-plane zero-freeness of \(H\) allocates every zero of \(S\) in the lower half-plane to \(H\), and every upper zero to \(H(-z)\); there are no real zeros to allocate. More generally, suppose two real, strictly decreasing right-half sources have positive seam values, nonzero integrals, and entire transforms of order at most one with the same \(1/v\) imaginary-ray asymptotic. If their \(C\) agree, their transforms have the same zeros. Hadamard factorization then makes their quotient \(e^{az+b}\). Reality and \(H(z)H(-z)=S(z)\) reduce this to \(\pm e^{icz}\), \(c\in\mathbb R\); positivity at \(z=0\) fixes the plus sign. Finally \(H(iv)\sim k(0)/v\) as \(v\to\infty\), so \(c=0\). Hence the two right-half sources, and by even reflection their completed transforms \(\Xi\), coincide. This is a paper proof; the factorization and uniqueness are not formalized in Lean. The general minimum-phase principle is classical, while this theta-source application and the arithmetic expansion below need an independent literature-novelty audit.

The data in (16) have an honest positive arithmetic expansion. On \(x\ge0\), \(k=\sum_{n\ge1}a_n\), where
\[
a_n(x)=n^{-1/2}h(x+\log n)
 =2\pi n^2e^{5x/2}(2\pi n^2e^{2x}-3)e^{-\pi n^2e^{2x}}>0.
\]
The existing Gaussian atom majorant gives absolute convergence in \(L^1(0,\infty)\) and permits Tonelli and dominated convergence. In particular,
\[
C(t)=\sum_{m,n\ge1}\frac1{\sqrt{mn}}
 \int_0^\infty h(x+\log m)h(x+t+\log n)\,dx, \qquad t\ge0, \tag{17}
\]
with every summand positive. On setting \(y=e^{2x}\), the same identity becomes the incomplete rank-two theta-lattice energy
\[
C(t)=2\pi^2 e^{5t/2}\sum_{m,n\ge1}m^2n^2
 \int_1^\infty y^{3/2}
 (2\pi m^2y-3)(2\pi n^2e^{2t}y-3)
 e^{-\pi(m^2+n^2e^{2t})y}\,dy. \tag{18}
\]
All factors inside (18) are positive for \(t\ge0\). The quadratic form \(m^2+n^2e^{2t}\) exposes a two-dimensional lattice structure that the universal resolvent sign (13) erased. Equations (16)--(18) are a candidate *change of problem space*: reconstruct the source-selected phase from an all-order positive arithmetic pair law, then constrain its reflected connection. Positivity of \(C\) alone does not imply RH: a small positive mixture of two centered Gaussians is strictly decreasing on the positive ray and has the same minimum-phase property, but its even Fourier transform has nonreal zeros. A genuine next theorem must use the **specific rank-two modular/arithmetic structure of (18)** to exclude the value \(B(z)=1\); merely proving another covariance-positive inequality would leave the hard obstacle untouched.

The conjecture loop matters here. Deleting multiples of a prime \(p\) gives \(k_p(x)=k(x)-p^{-1/2}k(x+\log p)\), which preserves every completed-transform zero algebraically and is positive on \(x\ge0\). It is negative sufficiently far to the left: for \(t>\log p\), evenness gives \(k_p(-t)=k(t)-p^{-1/2}k(t-\log p)\), and the existing two-sided theta envelope bounds give \(k(t)/k(t-\log p)\to0\). Thus \(k_p\) is not a full-line positive-density source. Conversely, ordinary prime CDF translation only reparametrizes \(g\). The positive-half-line \(H^1\) expansion avoids both mistakes. Full-line termwise quadratic expansion is unjustified: the \(H^1(\mathbb R)\) norms of translated atom responses scale as \(n^{-1/2}\) when finite, hence are not absolutely summable; for other spectral tilts individual left tails can grow. Modular reflection must be applied to the *completed* mode before expanding its two positive-half-line pieces.

These identities do not prove RH. The signed Hardy chirality and its prime-atom expansion are exact receivers; the source-selected open problem is a nonperturbative constraint on the left/right connection coefficient \(\Xi\), or equivalently avoidance of \(1\) by the analytic map \(B\). Equations (4)--(18) are paper derivations from existing Lean source facts plus classical entire-factor uniqueness; their new statements have not been formalized in Lean or independently audited for literature novelty. The frontier map remains read-only.

The [rational-cusp boundary law](../2-fully-proven/theta-rational-cusp-boundary-law.md) gives an exact arithmetic description of the complex-clock edge reached by a high-frequency atom saddle. The *completed* theta source has dense rational singularities there, with leading coefficients equal to nonzero quadratic Gauss sums; its weighted derivative has precise \(\varepsilon^{-5/2}\) growth along each interior approach. Fourth powers of the leading amplitudes, divided by \(i\), have an explicit mod-four charge: positive for odd denominator, zero for denominator congruent to two, negative for denominator divisible by four. This upgrades the direct-series sector obstruction to a natural-boundary theorem and exposes arithmetic phase data that a one-atom saddle misses. After the corpus's exact Ward reduction, the same card constructs the **global one-sided boundary pairing** for both connection branches throughout the Xi zero strip. It is an absolutely convergent Mellin integral of the continuous periodic square-frequency potential \(Q(r)=\sum_{n\ge1}e^{-i\pi n^2r}/n^2\), which obeys \(Q(r+1)+Q(r)=Q(4r)/2\). The pairing's arithmetic phase orientation, not its existence, remains open; the local law alone does not constrain \(B(z)\) or exclude an Xi zero.
