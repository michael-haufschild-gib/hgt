# Modular cusp tail energy, logarithmic trapping, and fixed-step contraction

- **ID:** pm-modular-cusp-tail-energy-and-fixed-step-contraction
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** [Obstacles summary §2.7](../../../reports/review-1911/obstacles-summary.md#27-a-physical-phenomenon-and-a-way-to-test-it) · [PM](../../../reports/review-1911/route-obstacles.md#pm)
- **Statement:** On $\mathrm{PSL}_2(\mathbb{Z})\backslash\mathbb{H}$, every nonzero compact pulse $h$ has strictly positive reflected tail energy $E_h(T)=\int_T^\infty |r_h(u)|^2\,du>0$ at all $T\in\mathbb{R}$; actual compact pulse families supported in $[-S_0,S_0]$ defeat every proposed fixed-step tail-energy contraction $E_h(T+L)/E_h(T)\le\theta<1$ up to sub-logarithmic horizons $T=\alpha\log\Omega$ ($\alpha\in(0,1)$), deep in the escaped tail ($0<E_h(T)\le\eta\|h\|_{L^2}^2$, uniformly in relative phase), and across arbitrary finite lists of separated late epochs; while the Agmon–Sobolev regularity bound $|r_h(T)|^4\le 4E_h(T)E_{h'}(T)$ and iterated-derivative estimates make zero-free strips $\operatorname{Re}\rho\le 1-2\delta$ ($0<\delta\le 1/4$, and RH at $\delta=1/4$) equivalent to asymptotic tail-energy decay $E_h(T)=O_{h,\varepsilon}(e^{-2(\delta-\varepsilon)T})$ and to uniform Sobolev-cone decay $E_h(T)\le K_{\varepsilon,S_0}(\|h\|_{L^2}^2+\|h^{(N_\varepsilon)}\|_{L^2}^2)e^{-2(\delta-\varepsilon)T}$.

## Theorems and Proofs

Let $r_h=\operatorname{pulseReflected} h$, $E_h(T)=\int_T^\infty |r_h(u)|^2\,du$, $E_{g,h}(T)=\int_T^\infty r_g(u)\overline{r_h(u)}\,du$, and $D_h(T,L)=\int_T^{T+L}|r_h(u)|^2\,du=E_h(T)-E_h(T+L)$ ($L\ge 0$).

1. **Polarization and strict tail positivity.** Pointwise expansion gives $E_{c_1 g+c_2 h}(T)=|c_1|^2E_g(T)+|c_2|^2E_h(T)+2\operatorname{Re}(c_1\overline{c_2}E_{g,h}(T))$, opposite-phase averaging $\frac12(E_{g+e^{i\phi}h}(T)+E_{g-e^{i\phi}h}(T))=E_g(T)+E_h(T)$, and four-phase polarization
   $$
   E_{g,h}(T)=\frac14\Big(E_{g+h}(T)-E_{g-h}(T)+iE_{g+ih}(T)-iE_{g-ih}(T)\Big).
   $$
   Suppose $h\in C_c^\infty([-S_0,S_0])$ is nonzero and $E_h(T_0)=0$. Continuity of $r_h$ forces $r_h(u)=0$ for all $u\ge T_0$. Put $B=\max(|T_0|+1,S_0+1)$ and $L_{\mathrm{mid}}(w)=\int_{-B}^B e^{-wu}r_h(u)\,du$. Since $(h*K)(u)=0$ for $u<-B$ and $(h*K)(u)=r_h(u)+m_h e^{u/2}$ everywhere, Fubini against $\int_0^\infty e^{-w\tau}K(\tau)\,d\tau=\varphi(w)$ on $\operatorname{Re} w>1/2$ gives
   $$
   \xi(1+2w)\big((2w-1)L_{\mathrm{mid}}(w)+2m_h e^{(w-1/2)B}\big)=2\pi(1+2w)a_h(-iw)\xi(2w).
   $$
   Both sides are entire on $\mathbb{C}$, so equality holds everywhere. At every critical-line zero $1/2+it$ ($t>0$) of $\xi$, setting $w=-1/4+it/2$ annihilates the left-hand side while $(1+2w)\xi(2w)=(1/2+it)\xi(3/2-it)\ne 0$, forcing $F(t):=a_h(t/2+i/4)=0$. Yet $F$ is entire and nonzero with $|F(z)|\le C e^{(S_0/2)|z|}$, so Jensen's bound limits its positive real zeros in $(0,T]$ to $O(1+T)$, contradicting Alpöge–Furman's superlinear simple-critical lower bound $N_{0,s}(T)\ge \frac{1}{72\pi}T\log T$. Hence $E_h(T)>0$ for all $T\in\mathbb{R}$, and $|E_{g,h}(T)|^2<E_g(T)E_h(T)$ whenever $g,h$ are $\mathbb{C}$-linearly independent.

2. **Local regularity, horocycle receiver, and strip/RH equivalences.** Since $a_{h'}(\xi)=i\xi a_h(\xi)$ and $|\varphi(i\xi)|=1$, dominated differentiation under the Fourier integral yields $r_h'(T)=r_{h'}(T)$ and $E_h'(T)=-|r_h(T)|^2$. For $B\ge T$,
   $$
   |r_h(T)|^2 = |r_h(B)|^2 - 2\int_T^B \operatorname{Re}\big(\overline{r_h(u)}r_{h'}(u)\big)\,du \le |r_h(B)|^2 + 2\sqrt{E_h(T)E_{h'}(T)}.
   $$
   Integrability of $|r_h|^2$ on $(T,\infty)$ forces $\inf_{B\ge T}|r_h(B)|^2=0$, giving $|r_h(T)|^4\le 4E_h(T)E_{h'}(T)$. By the horocycle packet mean identity, $r_h(T)=Y^{-1/2}\int_0^1 \mathcal{F}_h(T+\log Y,x,Y)\,dx$ whenever $T+2\log Y>S_0$. Conversely, if $\|r_h(u)\|\le C e^{-\sigma u}$ for $u\ge 0$, then $\int_{-B}^\infty e^{-wu}r_h(u)\,du$ is holomorphic on $\operatorname{Re} w>-\sigma$; testing $h=\operatorname{excitingPulse}((\rho-1)/2)$ excludes any $\zeta$-zero with $\operatorname{Re}\rho>1-2\sigma$. For pulses supported in $[-S_0,S_0]$, $(1+|\operatorname{Re} w|)^N\le 2^N(1+\|w\|^N)$ and $\|w\|^N\|a_h(w)\|=\|a_{h^{(N)}}(w)\|\le (2\pi)^{-1}e^{\sigma S_0}(\|h\|_{L^1}+\|h^{(N)}\|_{L^1})$ make the contour-shift constant in `pulseReflected_decay_of_zeroFree` uniform over the Sobolev cone: for $0<\delta\le 1/4$,
   $$
   \operatorname{Re}\rho\le 1-2\delta \iff \mathcal{F}_h=O_{h,\varepsilon}(e^{-(\delta-\varepsilon)\tau}) \iff r_h=O_{h,\varepsilon}(e^{-(\delta-\varepsilon)T}) \iff E_h(T)=O_{h,\varepsilon}(e^{-2(\delta-\varepsilon)T})
   $$
   $$
   \iff \forall \sigma\in(0,\delta),\ \forall S_0>0,\ \exists N\in\mathbb{N},\ \exists K>0,\ \forall h\in C_c^\infty([-S_0,S_0]),\ \forall T\ge 0,\ E_h(T)\le K\big(\|h\|_{L^2}^2+\|h^{(N)}\|_{L^2}^2\big)e^{-2\sigma T}.
   $$
   Unconditionally ($\Theta\le 20999/24000$), this Sobolev-cone bound holds for every $0<\sigma<3001/48000$; validity for all $0<\sigma<1/4$ is equivalent to RH.

3. **Path-return decrement and quantitative falsification of fixed-step contraction.** Every prime power $p^k$ ($k\ge 1$) has delay $2k\log p$ and repeated-prime amplitude $\varphi(p^k)/p^k=1-1/p$. For mean-zero $h$ supported in $[-S_0,S_0]$ and $u\le T+L$, only denominators $1\le c\le \lfloor e^{(T+L+S_0)/2}\rfloor$ satisfy $2\log c<u+S_0$, determining $D_h(T,L)$ by a finite path-return sum. For any $b\in C_c^\infty([-S_0,S_0])$, $\Omega\ge 1$, and $a\in\mathbb{R}$, split $J_b(\Omega,a)=\int_0^\infty e^{-i\Omega v}b(a-v)(1-e^{-v})^{-1/2}\,dv$ at $\delta=\Omega^{-1}$: on $(0,\delta]$, $(1-e^{-v})^{-1/2}\le \sqrt{e}\,v^{-1/2}$ integrates to $2\sqrt{e}\,\Omega^{-1/2}$; on $[\delta,R]$ ($R=\max(\delta,a+S_0+1)$), integrating $e^{-i\Omega v}$ by parts uses the exact antiderivative $-\frac{d}{dv}(1-e^{-v})^{-1/2}=\frac12 e^{-v}(1-e^{-v})^{-3/2}$ to yield $\|J_b(\Omega,a)\|\le C_b\Omega^{-1/2}$ uniformly in $a$. Setting $p_\Omega=\frac{1}{i\Omega}\operatorname{meanZeroPulse}(e^{i\Omega\cdot}b_0)=e^{i\Omega\cdot}b_0+\frac{1}{i\Omega}e^{i\Omega\cdot}\operatorname{meanZeroPulse}(b_0)$ for a nonzero bump $b_0$ supported in $[-S_0,S_0]$ gives $\operatorname{meanCoefficient}(p_\Omega)=0$, $\|p_\Omega\|_{L^2}^2\to\|b_0\|_{L^2}^2>0$, and
   $$
   \int_{-\infty}^T |r_{p_\Omega}(u)|^2\,du \le C(b_0,S_0)(T+S_0+1)e^{T+S_0}\Omega^{-1}\qquad (\forall T\ge -S_0,\ \Omega\ge 1).
   $$
   By Plancherel conservation $E_{p_\Omega}(-S_0)=\|p_\Omega\|_{L^2}^2$, along every fixed $T$ and every sub-logarithmic horizon $T(\Omega)=\alpha\log\Omega$ ($0<\alpha<1$), $\lim_{\Omega\to\infty} E_{p_\Omega}(T(\Omega)+L)/E_{p_\Omega}(T(\Omega))=1$. Superposing a fixed escaped pulse $g$ ($E_g(T)\ll\eta$) with a scaled packet $e^{i\phi}w_\Omega$ ($\|w_\Omega\|_{L^2}^2\approx \frac{\eta}{3}\|g\|_{L^2}^2$) defeats every $(L,T_0,\eta,\theta<1)$ simultaneously for all phases $\phi\in\mathbb{R}$ with $0<E_{g+e^{i\phi}w_\Omega}(T)\le\eta\|g+e^{i\phi}w_\Omega\|_{L^2}^2$, and inductive $(K+1)$-packet superpositions stall simultaneously across any $K$ separated late windows $[T_j,T_j+L]$.

## No-go closure
- **Exact killing theorem/mechanism:** Each individual cusp bounce $(1-e^{-v})^{-1/2}\mathbf{1}_{v>0}$ suppresses carrier frequency $\Omega$ by $O(\Omega^{-1/2})$ across the $\le e^{(T+S_0)/2}$ early denominators, while continuous-spectrum unitarity $|\varphi(i\xi)|=1$ preserves total $L^2$ energy, trapping $1-O((T+S_0+1)e^T\Omega^{-1})$ of the wavepacket in the late tail past every sub-logarithmic horizon $T=\alpha\log\Omega$.
- **Strongest positive survivor:** (1) Parameter-free Agmon–Sobolev bound $|r_h(T)|^4\le 4E_h(T)E_{h'}(T)$ and eternal tail positivity $E_h(T)>0$; (2) Uniform Sobolev-cone replacement law $E_h(T)\le K_{\sigma,S_0}(\|h\|_{L^2}^2+\|h^{(N_\sigma)}\|_{L^2}^2)e^{-2\sigma T}$ unconditionally for $0<\sigma<3001/48000$ and equivalent across $0<\sigma<1/4$ to RH.
- **New insight:** Pure $L^2\to L^2$ fixed-step contraction of cusp tail energy is impossible on $\mathrm{PSL}_2(\mathbb{Z})\backslash\mathbb{H}$ even when asymptotic exponential decay holds; exponential cusp escape is intrinsically a derivative-losing $H^N([-S_0,S_0])\to L^2([T,\infty))$ phenomenon governed by the logarithmic cusp delay $\sim \log\Omega$.
- **Status:** Complete paper proof above; proceeding directly to unconditional Lean 4 formalization in `GaloisForLFunctions/BlackHoleRingdown/TailEnergy/`.
