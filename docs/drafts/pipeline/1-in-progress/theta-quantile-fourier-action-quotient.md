# Theta quantile Fourier action and one-port quotient

- **ID:** TQFQ
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) for the structural identities; CANDIDATE for spectral orientation
- **Source:** literal theta density, its quantile normal form, and its determinant-bearing pinned Volterra operator
- **Statement:** The nonzero theta divisor is the reciprocal point spectrum of an explicit infinite Fourier matrix built from one CDF action sequence. Strict source log-concavity gives two positive curvature laws for that sequence and its reciprocal-speed dual, but the remaining boundary feedback is one scalar channel.

Corpus anchors: [exact determinant](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaSourceDeterminantIdentity.lean), [reciprocal eigenvalue law](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaSourceCompressedInverseDeterminant.lean), [quantile speed](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmQuantileRootMode.lean), [metric cancellation](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaMetricCommutator.lean), [pinned Volterra boundary](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmPinnedVolterraBoundaryDefect.lean), and [strict theta log-concavity](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspKernelLogConcavity.lean). The frontier map stays read-only.

## Proof chain and exact target

Let $k>0$ be the even completed-theta density, $M=\int_{\mathbb R}k$, $F(x)=M^{-1}\int_{-\infty}^x k$, and $Q=F^{-1}$. On $0<t<1$, put

\[
q(t)=Q'(t)=\frac{M}{k(Q(t))},\qquad h(t)=q(t)^{-1}=\frac{k(Q(t))}{M}.
\]

On $H=L^2(0,1;\mathbb C)$, let $e=1$, $P=I-|e\rangle\langle e|$, and

\[
(Vf)(t)=\int_0^t f(u)\,du-t\int_0^1 f(u)\,du,\qquad B=iM_qV.
\]

The corpus proves $\det_2(I+zB)=\Xi_C(z)/\Xi_C(0)$. Thus a nonzero Xi zero $z$ corresponds to the eigenvalue $\mu=-1/z$ of $B$. The target is a source-derived real-spectrum law for $B$, equivalently for its compression $D=PB|_{e^\perp}$, not a new determinant receiver.

## Paper-proved structural reduction

Because $Be=0$, nonzero point spectra of $B$ and $D$ coincide. If $Bv=\mu v$, then $f=Pv\ne0$ satisfies $Df=\mu f$. Conversely, if $Df=\mu f$, then $v=f+\mu^{-1}\beta(f)e$, with $\beta(f)=\langle e,Bf\rangle$, satisfies $Bv=\mu v$.

Set $T=PM_hP|_{e^\perp}$, $b=Ph$, and $A=iPV|_{e^\perp}$. The pinned Volterra Green identity gives $A=A^*$. Directly multiplying $B$ by $h$ and accounting for the removed constant mode yields the exact one-port equation

\[
                         TD=A-b\beta. \tag{1}
\]

The entire nonselfadjoint part of the quotient is one rank-one boundary feedback. $T$ is positive and injective, but not bounded below for the theta source. Equation (1) does not itself imply real spectrum.

For $n\in\mathbb Z\setminus\{0\}$, let $e_n(t)=e^{2\pi int}$ and define the finite CDF action

\[
\Phi_n=\int_0^1q(t)\bigl(1-\cos(2\pi nt)\bigr)\,dt
       =\int_{\mathbb R}\bigl(1-\cos(2\pi nF(x))\bigr)\,dx,
\quad \Phi_0=0,\quad \Phi_{-n}=\Phi_n.
\]

The second formula follows from $q(t)dt=dx$. Exponential theta tails make the integral finite. Evenness gives $q(1-t)=q(t)$, so the matrix of $D$ in the nonzero Fourier modes is **exactly**

\[
\boxed{\ \langle e_m,De_n\rangle
          =\frac{\Phi_m-\Phi_{n-m}}{2\pi n}\ },
\qquad m,n\ne0. \tag{2}
\]

Indeed, $Ve_n=(e_n-1)/(2\pi in)$, and reflection about $1/2$ kills the sine part of the remaining integrable Fourier difference. This makes the whole divisor-bearing operator an explicit CDF-action matrix; no source Fourier transform or zero is assumed in its entries. The sequence $\Phi$ is conditionally negative definite on $\mathbb Z$: for finitely supported $c_j$ with $\sum c_j=0$,

\[
\sum_{j,l}\overline{c_j}c_l\Phi_{j-l}
   =-\int_0^1q(t)\left|\sum_jc_je^{2\pi ijt}\right|^2dt\le0.
\]

The cancellation at both endpoints makes this integral finite.

## Two curvature laws and the candidate jump

The corpus already proves \((\log k)''<0\). Differentiating the quantile profile gives

\[
h'(t)=(\log k)'(Q(t)),\qquad
h''(t)=q(t)(\log k)''(Q(t))<0,
\]

so $h$ is a strictly concave, symmetric circle profile with $h(0)=h(1)=0$. For every $n\ge1$, two integrations by parts with endpoint cutoff give the exact positive-curvature representation

\[
\boxed{\ -\int_0^1h(t)\cos(2\pi nt)\,dt
 =\frac{1}{(2\pi n)^2}\int_{\mathbb R}
      - (\log k)''(x)\bigl(1-\cos(2\pi nF(x))\bigr)\,dx>0.\ } \tag{3}
\]

Here $-h''(t)dt=-(\log k)''(x)dx$; the endpoint terms vanish because a nonnegative concave profile vanishing at an endpoint has derivative times squared distance tending to zero. Thus $h$ is of strict conditional negative type on the circle. The concavity of this one-dimensional quantile profile is a known isoperimetric fact; the useful new object here is its **simultaneous appearance with the divisor matrix (2)**.

The reciprocal $q=1/h$ is strictly convex. Put $W_n(t)=(1-\cos(2\pi nt))^2/[2(2\pi n)^2]$. Since $W_n''=\cos(2\pi nt)-\cos(4\pi nt)$, integration by parts gives the second source-curvature identity

\[
\boxed{\ \Phi_{2n}-\Phi_n
 =\int_0^1q''(t)W_n(t)\,dt>0.\ } \tag{4}
\]

This remains valid with singular $q$: the finite action implies $\int q(t)\operatorname{dist}(t,\{0,1\})^2dt<\infty$. Convexity and reflection then give $t^3q(t)\to0$ and $t^4|q'(t)|\to0$ at both endpoints; $W_n=O(t^4)$ and $W_n'=O(t^3)$. Consequently the boundary terms vanish. Formula (4) makes every opposite-frequency coupling in (2) strictly nonzero, with opposite signs in its two directions.

A translation-invariant positive convolution metric, including the tempting kernel generated from the negative-type $h$, is diagonal with equal positive weights at $n$ and $-n$. It cannot symmetrize $D$: (2) and (4) give $D_{n,-n}=-D_{-n,n}\ne0$. The positive survivor is a **frequency-folded** source problem: a metric must couple $+n$ and $-n$ and also control all cross-frequency entries. The $\{n,-n\}$ block is

\[
\frac{1}{2\pi n}
\begin{pmatrix}\Phi_n&\Phi_{2n}-\Phi_n\\
-(\Phi_{2n}-\Phi_n)&-\Phi_n\end{pmatrix}.
\]

Its candidate positive symmetrizer has off-diagonal/diagonal ratio $(\Phi_{2n}-\Phi_n)/\Phi_n$. The following inequality proves this ratio lies in $(0,1)$ for every mode; global compatibility remains open.

Symmetry of $q$, the substitution $u=2t$, and strict concavity of $h$ give

\[
\Phi_{2n}=\int_0^1q(u/2)(1-\cos(2\pi nu))\,du
       <2\int_0^1q(u)(1-\cos(2\pi nu))\,du=2\Phi_n,
\]

because $h(u/2)>h(u)/2$ and hence $q(u/2)<2q(u)$ for $0<u<1$. With (4), this yields the strict dyadic interval

\[
                         1<\frac{\Phi_{2n}}{\Phi_n}<2. \tag{5}
\]

Thus **every** opposite-frequency $2\times2$ compression has distinct real nonzero eigenvalues
\(\pm[\Phi_{2n}(2\Phi_n-\Phi_{2n})]^{1/2}/(2\pi n)\)
and a positive symmetrizer

\[
G_n=\begin{pmatrix}1&r_n\\r_n&1\end{pmatrix},\qquad
r_n=(\Phi_{2n}-\Phi_n)/\Phi_n\in(0,1).
\]

The source therefore stabilizes **all paired chiral blocks**, not merely a finite prefix. Off-block couplings remain and can still create nonreal spectrum. An analytic witness is $k_*(x)=e^{-x^2}+e^{-2x^2}$: it is even, positive and strictly log-concave because $(\log k_*)''\le-2+4/e<0$, yet its Fourier transform is $\sqrt\pi e^{-z^2/4}+\sqrt{\pi/2}e^{-z^2/8}$, whose equation $e^{-z^2/8}=-1/\sqrt2$ has nonreal solutions. Thus the global condition must use more than generic log-concavity and the paired-block laws.

The direct sum $G_0=\bigoplus_{n\ge1}G_n$ is a bounded positive injective operator on the mean-zero Fourier space: $0<r_n<1$ makes each block positive and gives $\|G_0\|\le2$. It is a source-built metric with an **exactly cross-frequency** residual $E=G_0D-D^*G_0$: every $\{n,-n\}$ diagonal block of $E$ is zero. For $m,n>0$, $m\ne n$, its positive-frequency entries are

\[
2\pi E_{mn}=
\frac{\Phi_m-\Phi_{|m-n|}+r_m(\Phi_m-\Phi_{m+n})}{n}
-
\frac{\Phi_n-\Phi_{|m-n|}+r_n(\Phi_n-\Phi_{m+n})}{m}.
\tag{6}
\]

The other cross-frequency entries follow from the same matrix (2) and reflection. Equation (6) is a test for this frequency-folded metric, not a necessary RH condition: the canonical metric $T$ already has the different, rank-two defect in (1). No vanishing or sign law for this full residual is established.

## Full cross-frequency Schoenberg core and singular boundary port

There is a positive geometry on **all** frequencies, not only the paired blocks. For nonzero integers $m,n$ set

\[
G_{mn}=\frac{\Phi_m+\Phi_n-\Phi_{m-n}}2,
\quad J_{nn}=\frac1{\pi n},
\quad u_m=1,
\quad v_n=\frac{\Phi_n}{2\pi n}.
\tag{7}
\]

On every finite packet of distinct nonzero frequencies, $G$ is the strict Gram matrix of
$\sqrt{q(t)/2}(e^{2\pi int}-1)$ in $L^2(0,1)$. The functions are square-integrable because
$\Phi_n<\infty$; symmetry $q(1-t)=q(t)$ removes their imaginary mixed integrals. Positivity is
**strict**: a finite trigonometric polynomial $\sum_n c_n(e^{2\pi int}-1)$ vanishing almost
everywhere on $(0,1)$ vanishes identically, and its nonzero-frequency coefficients are the $c_n$.
The full finite Fourier section of (2), with every cross-frequency entry retained, therefore has
the exact decomposition

\[
\boxed{D_I=G_IJ_I-u_Iv_I^{\mathsf T}.}\tag{8}
\]

The counterterm is intrinsic to the literal quotient: $v_n=D_{nn}$ by (2), so
$(GJ)_{mn}=D_{mn}+D_{nn}$. No independent renormalization coefficient or fitted boundary
datum has been inserted.

The port-free $G_IJ_I$ is similar to the Hermitian matrix
$G_I^{1/2}J_IG_I^{1/2}$ and has only nonzero real eigenvalues, with exactly as many positive
and negative eigenvalues as positive and negative frequencies in $I$. Thus all possible nonreal
finite-section spectrum is confined to the **single affine boundary port** in (8). On a
sign-symmetric packet, frequency reflection anticommutes with both terms of (8), so the full
finite-section spectrum remains $\pm$-paired. This is an exact source-level factorization, not a
proof that the port is harmless.

The port cannot be discarded in the infinite limit: $u=(1)_{n\ne0}$ is not an $\ell^2$ vector,
while its subtraction is precisely what makes the original quotient matrix a legitimate operator.
For a general positive even strictly log-concave source the same Gram law holds, yet the
two-Gaussian witness above has infinitely many off-real Fourier zeros. Hence positive bulk Gram,
one-port rank, and strict source concavity together **do not** orient the port. The RH-bearing
question is whether the literal modular theta source gives an additional, coefficient-faithful
boundary-work law for this singular port. A generic rank-one perturbation or a positive metric
for $G_IJ_I$ is not such a law.

A direct Herglotz shortcut already fails on one paired packet. Write
$A=\Phi_n$, $B=\Phi_{2n}$, and let $D_0=G_{\{n,-n\}}J_{\{n,-n\}}$.
Its eigenvalues are $\pm\lambda$, where
$\lambda^2=B(4A-B)/(4\pi^2n^2)>0$. The rank-one secular factor is exactly

\[
1+v^{\mathsf T}(\mu-D_0)^{-1}u
=1+\frac{AB}{2\pi^2n^2(\mu^2-\lambda^2)}.\tag{9}
\]

Its residues at $+\lambda$ and $-\lambda$ have opposite signs, so it is not a
Herglotz function of $\mu$, **even though** this paired block has real spectrum.
Parity suggests the squared variable $\mu^2$; its full-packet residue signs and the
singular-port limit remain unproved. Equation (9) follows by
$D_0^2=\lambda^2I$, $v^{\mathsf T}u=0$, and
$v^{\mathsf T}D_0u=AB/(2\pi^2n^2)$. This is a no-go for a scalar
first-order-passivity interpretation, not a no-go for a squared-parameter source law.

The squared-parameter reformulation has a sharper obstruction than (9). Fix a finite set
$P\subset\mathbb N_{>0}$, retain both signs of each frequency, and fold into the even/odd
reflection sectors. Let $G^+$ and $G^-$ be the two strictly positive Gram blocks,
$K=\operatorname{diag}_{n\in P}(1/(\pi n))$, and $S=K^{1/2}$. Conjugating the parity-folded
matrix by $\operatorname{diag}(S^{-1},S^{-1})$ gives exactly

\[
\widetilde D_P=\begin{pmatrix}0&A-ab^{\mathsf T}\\B&0\end{pmatrix},
\quad A=SG^+S>0,\quad B=SG^-S>0,\quad
a_n=\sqrt{\frac2{\pi n}},\quad
b_n=\frac{\Phi_n}{\sqrt{2\pi n}}.
\tag{10}
\]

Consequently the squared operator on the even sector is similar to

\[
H-xy^{\mathsf T},\qquad
H=B^{1/2}AB^{1/2}>0,\quad x=B^{1/2}a,\quad y=B^{1/2}b.
\tag{11}
\]

This is a positive self-adjoint bulk with one **oblique** boundary intervention, not a
self-adjoint rank-one penalty. Its skew part has the exact invariant

\[
\|xy^{\mathsf T}-yx^{\mathsf T}\|_F^2
=2\bigl[(a^{\mathsf T}Ba)(b^{\mathsf T}Bb)-(a^{\mathsf T}Bb)^2\bigr].
\tag{12}
\]

For any packet containing $n$ and $2n$, (4) gives $\Phi_{2n}>\Phi_n$, whereas
$b_j/a_j=\Phi_j/2$. Thus $a,b$ are not proportional; $B$ is invertible; the right side of
(12) is **strictly positive**. This proves an actual-source no-go: folding and squaring do
not make the literal theta boundary feedback self-adjoint in the canonical positive Gram
metric. It does not rule out another source-built metric or real spectrum. The bulk is already
positive; the hard problem is the *orientation of an oblique singular port*, not a missing
bulk coercivity estimate. Formulae (10)–(12) follow from reflection invariance of $G$,
oddness of $J,v$, evenness of $u$, and the two-vector Gram determinant identity. Strict
obliqueness also holds for other strictly convex reciprocal-speed sources, so it is not
theta-arithmetic selection.

There is also an unavoidable **cofinal counterterm**, not merely a non-self-adjoint finite
correction. Let $I_N=\{\pm1,\ldots,\pm N\}$ and compress the actual bounded quotient $D$
to this packet. Since $\Phi_1>0$,

\[
\|u_{I_N}v_{I_N}^{\mathsf T}\|
=\|u_{I_N}\|\,\|v_{I_N}\|
\ge \frac{\Phi_1}{\pi}\sqrt N,
\qquad
\boxed{\ \|G_{I_N}J_{I_N}\|
\ge \frac{\Phi_1}{\pi}\sqrt N-\|D\|\longrightarrow\infty.\ }
\tag{13}
\]

The first equality is the exact norm of a finite rank-one map, and the second follows from
(8) and the uniform compression bound $\|D_{I_N}\|\le\|D\|$. Thus the real-spectrum
core $GJ$ and the boundary port each diverge in norm while their **difference remains
bounded**. The port is not a perturbation of a pre-existing bounded self-adjoint limit; it
is a compulsory counterterm. This changes the infinite problem's primitive from the bulk
operator to the *paired cancellation* $(GJ,uv^{\mathsf T})$. Any argument taking a positive
bulk limit first in bounded-operator norm is impossible. An unbounded graph or
strong-resolvent construction remains possible, but must transport the port with it. This norm divergence is
generic for finite positive $\Phi_1$; by itself it does not distinguish theta or prove RH.

Status of (7)–(13): dependency-closed paper proof; Lean formalization of the action $\Phi_n$,
its weighted endpoint integrability, the strict Gram and the finite matrix factorization is open.
Schoenberg's negative-type-to-Gram construction and similarity of a positive Gram times a real
diagonal are standard parent theory; priority of this specific quantile-divisor factorization is
unverified. It is a structural bridge, not a claimed RH advance.

## Status and next mathematical test

- Equations (1)–(6), including all-mode real $2\times2$ blocks and the cross-frequency residual: paper derivations above; Lean formalization open. They use the corpus's actual theta source and determinant identity, not numerical evidence.
- Novelty: the one-dimensional quantile-profile concavity is known (the [Bobkov correspondence as recalled here](https://onlinelibrary.wiley.com/doi/10.1002/cpa.70020), equations 2.5–2.6). Novelty of the combined quotient/CDF-action/curvature formulation has not been externally established.
- Hardest obstacle: prove a *theta-specific*, globally compatible orientation of the one-port feedback in (1), or an equivalent real-spectrum theorem for the full infinite matrix (2). Generic log-concavity and CDF negative type are insufficient.
- Route-level reinterpretation: this theta carrier has **exact divisor occurrence** but lacks spectral reality, whereas SQB has a selfadjoint native carrier but lacks source-generated occurrence. A source-faithful transfer between them would attack both gaps at once, but is not constructed. On a $B$-eigenmode $v$ with $f=Pv$, the quotient port is exactly $\beta(f)=\mu\langle e,v\rangle$; it is the same pinned-mean source coefficient used by the corpus's [theta-to-Plücker lift](../../../../formal/GaloisForLFunctions/RHTower/FrankensteinThetaPluckerIntertwiningAnomaly.lean). That module proves a naive coefficient-faithful lift has nonzero physical residual precisely off the critical line; [singular boundary recovery](../../../../formal/GaloisForLFunctions/RHTower/FrankensteinThetaPluckerBoundaryAnomalyRecovery.lean) shows the residual retains the full off-line carrier. The fixed SQB corrected vector likewise retains forcing. Equality of source coefficients does **not** cancel either physical residual. Any genuine transfer must derive its correction from the literal source, before imposing spectral vanishing.
- Next conjecture loop: test whether the *exact square-lattice theta identity*, absent from generic positive log-concave sources, constrains the oblique port's cofinal boundary work. A passivity claim based only on $G$, strict convexity, or finite block reality is already falsified or insufficient. Any candidate must predict a source-side signed identity that fails for the two-Gaussian witness before being promoted to an RH route.
