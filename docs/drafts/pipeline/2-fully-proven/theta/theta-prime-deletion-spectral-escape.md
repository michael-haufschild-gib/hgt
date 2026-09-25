# Prime deletion preserves the Xi divisor while its boundary spectrum escapes

- **ID:** theta-prime-deletion-spectral-escape
- **Stage:** 2-fully-proven (paper)
- **Type:** source-faithful divisor/limit discontinuity and reflected-gauge obstruction
- **Routes:** STC, CSB, U, K-RVM, MPLF, RHist; relevant to the Euler-deletion interface
- **Status:** [PROVED HERE ON PAPER] [LEAN FORMALIZATION OPEN] [NOT AN RH PROOF]
- **Dependencies:** literal atom expansion and compact-local summability in ThetaCuspFinitePrimeSource.lean; bilateral theta transform in ThetaTailFirstMomentKreinTransform.lean; completed critical moment in PrimeArchThetaWardLaplaceHalfDensity.lean; atom Mellin formula in [critical-boundary theorem](theta-euler-critical-boundary-mass-escape.md); classical divergence of reciprocal-prime sum. No numerical computation is used.

## Dual completion theorem

Let $h(x)=\theta\mathrm{CuspSourceTerm}(x,1)$, $a_n(x)=n^{-1/2}h(x+\log n)$, and $k(x)=\sum_{n\ge1}a_n(x)$, the literal completed theta source. Put $T_bf(x)=f(x+b)$, $D_p=1-p^{-1/2}T_{\log p}$, and, for a finite set of primes $S$, $k_S=\prod_{p\in S}D_p\,k$. Products commute. Write $\mathcal L_wf=\int_{\mathbb R}e^{wx}f(x)\,dx$ whenever defined.

For every finite $S$,

$$
\boxed{\quad k_S(x)=\sum_{\substack{n\ge1\\(n,\prod_{p\in S}p)=1}}a_n(x),\qquad
\mathcal L_w k_S=\Xi_C(iw)\prod_{p\in S}(1-p^{-1/2-w}).\quad} \tag{1}
$$

First identity holds pointwise and compact locally; second holds for every complex $w$. Every factor in (1) is zero-free on open Xi strip $|\operatorname{Re}w|<1/2$. Consequently **every finite literal prime deletion has exactly same interior zero divisor, with multiplicities, as Xi**. On $x\ge0$, $k_S$ is a positive sum of actual Gaussian atoms.

If $S_j$ grows through all primes, then $k_{S_j}\to h$ uniformly on every compact $x$-interval: each $n>1$ is eventually deleted, and atom series has a compact-local absolute majorant. Yet seed transform is

$$
\boxed{\quad \mathcal L_w h=(w-1/2)G(w),\qquad
G(w)=\Gamma(w/2+5/4)\pi^{-w/2-1/4}.\quad} \tag{2}
$$

Formula (2) is valid for $\operatorname{Re}w>-5/2$; in particular it has **no zero in open Xi strip**. Finite deletion preserves every Xi zero while compact-local limit has none. Divisor is carried by noncompact source boundary and is not continuous in compact-local source topology.

Discontinuity is visible without choosing any zero. For every real $-1/2<w<1/2$, divergence of $\sum_p1/p$ gives

$$
\boxed{\quad \mathcal L_w k_{S_j}\longrightarrow0,\qquad
\mathcal L_w h=(w-1/2)G(w)<0.\quad} \tag{3}
$$

Indeed $0<p^{-1/2-w}<1$ and $\sum_pp^{-1/2-w}\ge\sum_p1/p=\infty$, so finite Euler factor product tends to zero. At $w=0$, finite deleted sources have positive ordinary integral tending to zero, while seed has integral $-G(0)/2<0$. Residual $k_{S_j}-h$, which vanishes compact locally, carries limiting **positive ordinary mass** $G(0)/2$ at negative cusp. This location is literal: on $x\ge0$, retained atoms are positive and $0\le k_{S_j}(x)\le k(x)$; on bounded intervals atom majorant gives dominated convergence. Thus $\int_{-R}^{\infty}(k_{S_j}-h)\to0$ for every fixed $R$, whereas full ordinary integral tends to $G(0)/2$.

Critical half-density charge behaves differently:

$$
\boxed{\quad \mathcal L_{1/2}k_S
=\frac12\prod_{p\in S}(1-p^{-1}),\qquad
\mathcal L_{1/2}k_{S_j}\longrightarrow0=\mathcal L_{1/2}h.\quad} \tag{4}
$$

Scalar half-charge converges to seed's charge while ordinary and other real-strip Mellin observations fail to converge. Boundary datum needed for Xi connection is a **spectral family**, not its value at one exponent. This is reverse of smooth-number formation $h\to k$, where each finite stage has zero half-charge and completion creates charge $1/2$.

## Reflection test and positive survivor

One can restore exact evenness at finite depth without changing open-strip Xi divisor. For one prime $p$, let $a=\log p$ and

$$
k_p^{\mathrm{sym}}=(1-p^{-1/2}T_a)(1-p^{-1/2}T_{-a})k
=(1+p^{-1})k-p^{-1/2}(k(\cdot+a)+k(\cdot-a)). \tag{5}
$$

This source is real and even, and its transform is

$$
\mathcal L_w k_p^{\mathrm{sym}}
=\Xi_C(iw)(1-p^{-1/2-w})(1-p^{-1/2+w}). \tag{6}
$$

Both factors are zero-free for $|\operatorname{Re}w|<1/2$, so interior divisor is still Xi's. But (6) vanishes at $w=\pm1/2$; both critical endpoint charges are zero. Source is necessarily sign-changing: it is nonzero because its ordinary integral equals $(1-p^{-1/2})^2\Xi_C(0)>0$, while a nonzero nonnegative source cannot have zero integral against $e^{x/2}>0$. **Reflection plus divisor fidelity does not restore missing boundary charge; full-source positivity is an independent constraint.**

There is a sharp positive survivor. Let $\mu$ be any compactly supported, positive, symmetric probability measure and $g=\mu*k$, with $(\mu*k)(x)=\int k(x-t)\,d\mu(t)$. If $g$ has both same ordinary mass and same critical half-density charge as $k$, then $g=k$: symmetry gives

$$
\frac{\mathcal L_{1/2}g}{\mathcal L_{1/2}k}
=\int\cosh(t/2)\,d\mu(t)\ge1,
$$

with equality only for $\mu=\delta_0$. Ordinary-mass condition is automatic for probability convolution. It is needed for normalization: with only ordinary mass fixed, $\mu=(1-\varepsilon)\delta_0+\varepsilon(\delta_L+\delta_{-L})/2$ gives positive even source and multiplier $1-\varepsilon+\varepsilon\cosh(wL)$. It is zero-free in open strip if $0<\varepsilon<1/(1+\cosh(L/2))$, since $|\cosh(wL)|\le\cosh(L/2)$ there, but changes critical charge. Thus **mass plus half-charge rigidifies positive symmetric translation gauges**, while signed reflected Euler deletion escapes that rigidity. This classifies this gauge mechanism; it is not a zero-exclusion theorem for other deformations.

## Proof and exact limit

Atom scaling $a_n(x)=n^{-1/2}h(x+\log n)$ makes $p^{-1/2}T_{\log p}a_n=a_{pn}$. Thus $D_p$ removes exactly indices divisible by $p$. Finite inclusion-exclusion and compact-local absolute convergence prove first half of (1). Translation invariance of Lebesgue integration gives $\mathcal L_w(T_{\log p}k)=p^{-w}\mathcal L_wk$, proving second half from $\mathcal L_wk=\Xi_C(iw)$. Seed formula is exact Gaussian-atom Mellin integral from cited boundary theorem. Its gamma factor has no zeros in stated strip. Euler's reciprocal-prime divergence proves (3) and (4); latter also uses $\Xi_C(i/2)=1/2$. Equation (6) follows by same translation law in both directions. Positive-convolution rigidity follows from strict inequality $\cosh(t/2)>1$ for $t\ne0$.

This theorem **does not orient or exclude any Xi zero**. It rules out deriving orientation from local convergence of literal source, from its single critical half-charge, or from evenness and divisor fidelity after signed reflected deletion. Surviving target is a source-derived law for entire complex boundary/connection family that also retains positivity and actual modular assembly. Equations (1)--(6) and positive-convolution rigidity are paper-proved here; combined Lean formalization remains open. Literature novelty of this combined source/divisor interpretation has not been established.
