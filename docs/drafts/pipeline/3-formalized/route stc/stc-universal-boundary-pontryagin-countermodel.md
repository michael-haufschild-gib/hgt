# A rank-two theta boundary defect with infinitely many off-real source modes

- **ID:** stc-universal-boundary-pontryagin-countermodel
- **Stage:** 3-formalized
- **Type:** THEOREM (paper); universal finite-index realization no-go
- **Routes:** STC, CSB, K-RVM, MPLF, RHist
- **Status:** [PROVED HERE ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]
- **Dependencies:** elementary Fourier translation, quantile substitution, Hilbert--Schmidt kernel criterion, and the neutral-subspace dimension bound proved below. The general quantile-root and kernel-energy machinery is present in `HedenmalmQuantileRootMode.lean` and `HedenmalmHilbertSchmidtNorm.lean`. No computation or hypothesis about Xi zeros is used.

## The failed conjecture and its positive survivor

The conjecture was that a positive singular metric, compact source inverse, and rank-two monopole--dipole Green defect might admit a universal self-adjoint realization with one negative Pontryagin direction. Such a realization would allow at most one off-real eigenvalue in the upper half-plane. The following explicit source has **infinitely many**, while retaining all those local operator properties. The positive survivor is an exact lower bound: any faithful self-adjoint Pontryagin realization of its first `N` upper-half-plane modes needs negative index at least `N`.

Fix `0<a<1/2`, let `A>0` satisfy `cosh A=1/(2a)`, and choose `L>2A`. Put

\[
 h(x)=e^{-x^4},\qquad
 g(x)=h(x)+a h(x-L)+a h(x+L),\qquad
 M=\int_{\mathbb R}g(x)\,dx.
\]

Then `g` is strictly positive, even, smooth, and has super-Gaussian tails. Its Fourier transform is entire and obeys

\[
 F(z)=\int_{\mathbb R}g(x)e^{izx}\,dx
     =H(z)\bigl(1+2a\cos(Lz)\bigr),\quad
 H(z)=\int_{\mathbb R}h(x)e^{izx}\,dx. \tag{1}
\]

Consequently, for every integer `n`,

\[
 z_n^{\pm}=\frac{(2n+1)\pi\pm iA}{L},\qquad
 F(z_n^{\pm})=0,\qquad
 0<\operatorname{Im}z_n^+<\tfrac12. \tag{2}
\]

No assertion about the zeros of `H` is needed: the explicit multiplier forces (2).

Let `G(x)=M^{-1}\int_{-\infty}^xg(y)dy`, let `Q=G^{-1}:(0,1)\to\mathbb R`, and set `q(t)=Q'(t)=M/g(Q(t))`. On `L²(0,1)` define the source inverse

\[
 (Bf)(t)=i q(t)\left(\int_0^t f(u)du-t\int_0^1 f(u)du\right). \tag{3}
\]

This is Hilbert--Schmidt. Indeed its squared kernel norm is

\[
 \int_0^1 q(t)^2t(1-t)dt
 =M\int_{\mathbb R}\frac{G(x)(1-G(x))}{g(x)}dx. \tag{4}
\]

For `x>L+1` and `y≥x`, each of the three summands of `g` satisfies

\[
 h(y-s)\le h(x-s)e^{-4(x-L)^3(y-x)},\qquad s\in\{0,L,-L\}.
\]

Thus `(1-G(x))/g(x)≤[4M(x-L)^3]^{-1}`. Evenness gives the matching bound at the left tail; the middle is continuous and finite. This proves (4).

The bounded, positive, injective multiplication metric `D=M_q^{-1}` has the universal commutator

\[
 DB-B^*D=iP,\qquad (Pf)(t)=\int_0^1(1-t-u)f(u)du. \tag{5}
\]

`P` has rank two and one positive and one negative direction: with `v(t)=t-1/2`, direct integration gives `P1=-v` and `Pv=-1/12`. Thus (3) has the same **local** hyperbolic monopole--dipole defect as the literal theta inverse.

Every `z=z_n^+` produces an actual nonzero `L²` eigenvector of `B` with eigenvalue `-1/z`. Set

\[
 A_z(t)=\int_0^t e^{izQ(u)}du,\qquad
 R_z(t)=-e^{-izQ(t)}A_z(t),\qquad
 f_z(t)=-izq(t)R_z(t). \tag{6}
\]

By quantile substitution and (1), `A_z(1)=F(z)/M=0`. Differentiating on `(0,1)` gives `R_z'=f_z-1`. To control the endpoint despite the possibly unbounded exponential factor in `R_z`, use `A_z(t)=-M^{-1}\int_{Q(t)}^\infty g(y)e^{izy}dy` at the right endpoint. The preceding tail bound, with `|\operatorname{Im}z|` subtracted from its exponent, gives

\[
 |f_z(t)|\le\frac{|z|}{4(Q(t)-L)^3-|\operatorname{Im}z|}
\]

for `Q(t)` sufficiently large. More precisely, `|R_z(t)|≤g(Q(t))/[M(4(Q(t)-L)^3-|\operatorname{Im}z|)]→0`. The left tail is identical using the integral from `-∞`; on the middle interval `f_z` is continuous. Thus `R_z` vanishes at both endpoints and `f_z` is bounded and belongs to `L²`. Integrating `R_z'=f_z-1` first on compact subintervals and then taking the endpoint limits gives `\int_0^1f_z=1` and `\int_0^t f_z-t=R_z(t)`. Hence (3) yields `Bf_z=(-1/z)f_z`.

Since `Im z_n^+>0`, all `-1/z_n^+` lie in the upper half-plane. Suppose a faithful linearization puts these distinct eigenvalues into a self-adjoint operator `T` on a Pontryagin space of finite negative index `κ`. For upper-half-plane eigenvectors `v_i,v_j`, self-adjointness of the indefinite form gives

\[
 (\lambda_i-\overline{\lambda_j})[v_i,v_j]=0.
\]

Since both eigenvalues lie in the upper half-plane, their span is totally neutral; distinct eigenvalues make the vectors independent. Any totally neutral subspace of a nondegenerate Hermitian space of negative index `κ` has dimension at most `κ` (project to its negative subspace). Therefore the first `N` eigenvalues require `κ≥N`, and no finite-index realization can retain the whole divisor.

## Architectural consequence and limit

Rank-two *pointwise* Green defect does not bound the *global* number of unstable source modes. The defect lives on the same two boundary ports for each parameter, but their parameter-dependent coupling can produce arbitrarily many independent neutral spectral modes. A theta/RH argument based on a finite-index completion must prove an **arithmetic-specific** compatibility law for the actual Euler/modular source; positivity, evenness, rapid decay, Hilbert--Schmidt compactness, and the local boundary identity (5) do not supply it.

The representation should therefore be tested through its **two-parameter transfer/Green kernel** and the negative squares of that kernel, rather than the dimension of a single boundary port. This changes the proposed source law: Euler chronology would need to constrain interactions between *different spectral parameters*, not only conserve the current at each one. Indefinite canonical-system interface theory makes the same distinction between a finite interface and the global monodromy kernel ([Langer--Woracek, 2026](https://arxiv.org/abs/2604.00541)); no theorem from that paper is assumed here.

In STC, `source_pair_symmetric_kernel_two_channel` in `DeningerGammaAllPrimeStokesPairBridge.lean` similarly gives two algebraic one-prime channels on every finite equal-depth packet. The countermodel shows why that finite-packet channel count cannot itself cap the negative index of a completed spectral transfer. The unresolved STC work is to construct the all-prime transfer and prove a source-specific cross-parameter law for it.

This source is a counterfeit, not the Riemann theta source, and (2) does not concern zeta. The theorem rejects the universal index-one interpretation, not a source-specific one. The exact source construction and index bound are formalized in `STCUniversalBoundaryPontryaginCountermodel.lean` (with the generic `HedenmalmCompactSourceEigenmode.lean` and `PontryaginNeutralEigenvectorBound.lean`); see the certificate. Literature novelty of this combined operator countermodel has not been established.

## Log

- 2026-09-27: parameters and three-bump density (positive, even, smooth, dominated by every Gaussian), Fourier factorization (1), zeros (2), quartic tail envelope, finite Hilbert--Schmidt energy (3)--(4), metric commutator and rank-two defect (5), mode envelope and nonzero `L²` eigenvectors with eigenvalues `-1/z_n^+` (6), and the neutral-subspace index bound formalized unconditionally (`STCUniversalBoundaryPontryaginCountermodel.lean`, `HedenmalmCompactSourceEigenmode.lean`, `PontryaginNeutralEigenvectorBound.lean`); certificate `stc-universal-boundary-pontryagin-countermodel-formalized.md`; moved to stage 3.
