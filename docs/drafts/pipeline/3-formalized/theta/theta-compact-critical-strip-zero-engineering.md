# Compact theta perturbations can place a zero inside the Xi strip while preserving finite anchors

- **ID:** theta-compact-critical-strip-zero-engineering
- **Stage:** 3-formalized (paper proof formalized unconditionally in Lean; see `theta-compact-critical-strip-zero-engineering-formalized.md`)
- **Type:** sharp source-class countermodel and finite-anchor no-go
- **Routes:** STC, CSB, U, K-RVM, MPLF, RHist
- **Status:** [PROVED HERE ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]
- **Dependencies:** corpus theorems that completed theta source $k$ is positive, even, globally strongly log-concave and has integrable exponentially weighted derivatives of every order; Fourier identity $\Xi_C(z)=\int_{\mathbb R}e^{-izx}k(x)\,dx$; exponential horizontal decay in [XiHorizontalStripDecay.lean](../../../../formal/GaloisForLFunctions/RHTower/XiHorizontalStripDecay.lean). The prior [derivative-packet theorem](theta-derivative-dark-divisor-packets.md) supplies source facts but places its added zeros outside the natural strip when perturbation is small. No numerical computation is used.

## Theorem

Fix any height $v$ with $0<v<1/2$, any integer $J\ge0$, and any neighborhood of $k$ in Schwartz topology. For every sufficiently large real frequency $u$, there is a real even smooth source $g_u$ such that:

1. $g_u=k$ outside one **fixed** compact interval, independent of $u$; $g_u$ is strictly positive and globally strongly log-concave.
2. $\int x^j g_u(x)\,dx=\int x^j k(x)\,dx$ for every $0\le j\le J$, and
   $\int e^{x/2}g_u(x)\,dx=\int e^{x/2}k(x)\,dx=1/2$.
   Evenness also fixes the reflected $e^{-x/2}$ charge.
3. $g_u\to k$ in Schwartz topology as $u\to+\infty$; in particular $g_u$ eventually lies in the prescribed neighborhood.
4. Its entire Fourier transform $F_{g_u}(z)=\int e^{-izx}g_u(x)\,dx$ satisfies
   $F_{g_u}(u+iv)=0$. This is an off-real zero **inside** $|\operatorname{Im}z|<1/2$.
   At arbitrarily large $u$ with $\Xi_C(u+iv)\ne0$, the perturbation is nonzero.
5. For the compact-support version, every finite literal prime-deletion operator
   $D_S=\prod_{p\in S}(1-p^{-1/2}T_{\log p})$ still has
   $(D_Sg_u)(x)>0$ for all $x\ge0$, **simultaneously for every finite prime set $S$**,
   once $u$ is sufficiently large.

There is also a **real-analytic variant** with the same exact anchors and forced strip zero, still converging to $k$ in Schwartz topology. It cannot equal $k$ outside a compact interval, but satisfies
$g_u(x)/k(x)-1=O_u((1+|x|)^N e^{-x^2/2})$ for some fixed $N$; thus its relative tail error vanishes faster than $e^{-c|x|}$ for every $c>0$. In particular, real analyticity and agreement with every ordinary exponential-order tail asymptotic do not repair the finite-anchor insufficiency.
Its holomorphic continuation also converges to the theta source **uniformly on every compact subset** of the full source strip $|\operatorname{Im}x|<\pi/4$. The forced zero therefore lives beyond all compact-open control of the interior source strip, at moving horizontal frequency.

Thus exact theta tails, positivity, evenness, strong log-concavity, any finite moment depth, ordinary mass, and the critical half-density charge do **not** force zero-freeness in the natural Xi strip. This says nothing about whether the actual theta source has such a zero: $g_u$ lacks its exact infinite modular/Euler assembly and is not real-analytic across the edge of its compact perturbation. It strengthens the prior compact-tail countermodel, which only asserted a nonreal zero somewhere in the complex plane and did not pin the critical charge.

## Paper proof

Choose a nonnegative even $C^\infty$ bump $\psi$, supported in a fixed central interval $[-R,R]$, positive on an open interval. Put $N=\lfloor J/2\rfloor$ and use the $N+2$ even anchor functions

$$
A_0(x)=1,\ A_j(x)=x^{2j}\ (1\le j\le N),\qquad
A_{N+1}(x)=\cosh(x/2).
$$

They are linearly independent on any open interval: a polynomial cannot agree there with a nonzero multiple of $\cosh(x/2)$. Consequently the Gram matrix
$G_{ij}=\int\psi(x)A_i(x)A_j(x)\,dx$ is positive definite and invertible. For any even $b$ with all anchor integrals finite, let

$$
\Pi b=b-\sum_{i=0}^{N+1}c_i(b)\psi A_i,\qquad
c(b)=G^{-1}\left(\int A_jb\right)_{j=0}^{N+1}.
$$

Then $\Pi b$ is real and even when $b$ is; all its required even moments and its $\cosh(x/2)$ charge vanish. Odd moments vanish by symmetry, and on even functions $\int e^{x/2}b=\int\cosh(x/2)b$.

Use two oscillatory packets, both real and even:

$$
b_{1,u}(x)=\psi(x)\cos(ux),\qquad
b_{2,u}(x)=x\psi(x)\sin(ux),\qquad
\widetilde b_{j,u}=\Pi b_{j,u}.
$$

For each fixed anchor $A_j$, integration by parts shows $\int A_jb_{r,u}=O_M(u^{-M})$ for every $M$, since $A_j\psi$ and $xA_j\psi$ are smooth and compactly supported. Thus the coefficients subtracted by $\Pi$ decay faster than every power of $u$. They do not change the following Fourier limits at $z_u=u+iv$.

Writing $E_u(b)=\int e^{-iz_ux}b(x)\,dx$ and splitting cosine and sine into exponentials gives

$$
E_u(\widetilde b_{1,u})\longrightarrow
\frac12\int\psi(x)e^{vx}\,dx=:A>0,
$$

$$
E_u(\widetilde b_{2,u})\longrightarrow
\frac{1}{2i}\int x\psi(x)e^{vx}\,dx=:-iB,\qquad B>0.
$$

Here $B>0$ because evenness gives
$\int x\psi(x)e^{vx}\,dx=2\int_0^\infty x\psi(x)\sinh(vx)\,dx>0$.
The discarded terms at frequency $2u$ vanish by the Riemann--Lebesgue lemma; the anchor corrections have vanishing coefficients. Hence the two complex evaluations, viewed as vectors in $\mathbb R^2$, form a uniformly invertible real matrix for all large $u$.

The weighted source $x\mapsto e^{vx}k(x)$ has integrable derivatives of every order. Repeated integration by parts therefore gives
$|\Xi_C(u+iv)|=O_M(u^{-M})$ for every $M$; the cited Lean horizontal-strip theorem gives the stronger exponential decay directly.
Solve the real two-by-two system uniquely for $\alpha_u,\beta_u$:

$$
\alpha_u E_u(\widetilde b_{1,u})
+\beta_u E_u(\widetilde b_{2,u})=-\Xi_C(u+iv).
$$

Uniform invertibility implies $|\alpha_u|+|\beta_u|=O_M(u^{-M})$ for every $M$.
Set $g_u=k+\alpha_u\widetilde b_{1,u}+\beta_u\widetilde b_{2,u}$.
All anchor identities hold exactly by construction, and Fourier linearity gives $F_{g_u}(z_u)=0$ exactly.

Each fixed derivative of an oscillatory packet grows by at most a fixed power of $u$, while its coefficient decays faster than any power. Since support is fixed, $g_u-k\to0$ in every Schwartz seminorm. On that compact support, $k$ has a positive minimum and its logarithmic curvature has a strict negative maximum; sufficiently small $C^2$ perturbations retain positivity and a negative curvature margin. Outside the support $g_u=k$. This proves global strong log-concavity and every assertion above. Because $\Xi_C$ is a nonzero entire function, it cannot vanish at every sufficiently large point of the horizontal ray $u+iv$, so arbitrarily large choices give a genuinely changed source.

The all-finite-deletion assertion has a uniform margin, not a one-prime-at-a-time limit. Write $\delta_u=g_u-k$, supported in $[-R,R]$. For $x\ge0$,
$$
D_S\delta_u(x)=\sum_{T\subseteq S}(-1)^{|T|}
  \left(\prod_{p\in T}p\right)^{-1/2}
  \delta_u\left(x+\log\prod_{p\in T}p\right).
$$
Only squarefree products at most $e^R$ can contribute. Hence
$|D_S\delta_u(x)|\le C_R\|\delta_u\|_\infty$ with the finite, $S$-independent
$C_R=\sum_{m\le e^R,\ m\ {\rm squarefree}}m^{-1/2}$, and the perturbation is zero for $x>R$.
Meanwhile the exact atom deletion formula gives
$D_Sk(x)=\sum_{(n,\prod S p)=1}a_n(x)\ge a_1(x)=h(x)>0$ on $x\ge0$.
The seed has positive minimum on $[0,R]$; since $\|\delta_u\|_\infty\to0$,
the displayed bounds prove $D_Sg_u>0$ for every $S$ at once.

For analytic variant, repeat the **same projection and two-packet proof** with $\psi(x)=k(x)e^{-x^2}$, which is positive, even and real-analytic by the corpus's holomorphic strip extension of $k$ in [ThetaCuspComplexStrip.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspComplexStrip.lean). This $\psi$ and all weighted derivatives are integrable, so anchor integrals decay faster than any power by integration by parts; the frequency-$2u$ remainders vanish, and $A,B>0$ as above. The resulting perturbation has form $g_u=k(1+r_u)$, where $r_u$ is $e^{-x^2}$ times a finite combination of $\cos(ux)$, $x\sin(ux)$, powers of $x$ and $\cosh(x/2)$. Its coefficients are $O_M(u^{-M})$ for every $M$, by the same uniformly invertible two-by-two system. Thus $\|r_u\|_{C^2(\mathbb R)}\to0$ and $g_u$ remains positive and strongly log-concave: $(\log g_u)''=(\log k)''+(\log(1+r_u))''$, with the second term uniformly small. The displayed relative tail estimate and Schwartz convergence follow from the Gaussian factor. All anchor and zero identities remain exact. This gives a second falsifier after adding analyticity; it still changes the exact Euler coefficients and exact theta tails.

For the claimed holomorphic convergence, fix a compact $K$ in $|\operatorname{Im}z|<\pi/4$ and choose $\delta_K<\delta_0<\pi/4$ with $|\operatorname{Im}z|\le\delta_K$ on $K$. The cited Lean horizontal-decay theorem gives $|\Xi_C(u+iv)|=O(e^{-\delta_0u})$, hence the two packet coefficients have the same bound. On $K$, analytic continuations of $\cos(uz)$ and $\sin(uz)$ are $O_K(e^{\delta_Ku})$; all fixed anchor terms are bounded there. Therefore $g_u-k=O_K(e^{-(\delta_0-\delta_K)u})$. This proves compact-open convergence on the entire source strip without asserting convergence on its boundary.

## Conjecture attack and surviving boundary

- **Conjecture tested:** positivity, reflection, exact tails, any finite moment list, and the exact half-charge might rigidify the zero location of the completed theta source. **False:** the theorem constructs a source with all these properties and a forced interior off-line zero, regardless of RH.
- **Stronger surviving statement:** literal theta source has information beyond these source classes. A successful source-based zero-exclusion proof must use a constraint both packet families violate, such as exact modular/Euler identities; qualitative shape, analyticity, asymptotic tail agreement, finite moments/charges, and even the whole family of finite prime-deletion right-ray positivity inequalities cannot suffice together.
- **Scope limit:** compact variant lacks real analyticity, while analytic variant lacks exact tail equality. Neither preserves full real-zero divisor or exact Euler atom coefficients. The theorem does not refute an argument using those infinite data. Perturbation depends on target frequency and is a falsifier of a proposed sufficient source class, not an RH proof.

The proof is dependency-closed on paper and formalized unconditionally in Lean (certificate `theta-compact-critical-strip-zero-engineering-formalized.md`), including the two-packet interpolation, source positivity and the real-analytic variant. Literature novelty of this exact theta-anchored strip construction has not been established.

## Log

- 2026-09-28: every claim of the compact and real-analytic versions formalized unconditionally in Lean (modules `ThetaCompactStripZeroEngineering`, `ThetaAnalyticStripZeroEngineering`, `ThetaSourceSurgeryToolkit`; general layers `HTGeometry.OscillatoryPacketFourier`, `HTGeometry.EvenAnchorProjection`); moved to stage 3.
