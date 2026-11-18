# Removing proper powers from both Vaughan counts

**Route** PVC. **Stage** 3-formalized.

For $N\ge1$ set $R=\lfloor N^{1/64}\rfloor$, $U=\lfloor N^{31/64}\rfloor$. There is an explicit weight $v_R$, depending only on $R$, for which replacing each $\psi(X)-X$, $X=\lfloor N/d\rfloor$, by
$$
\sum_{U<p\le X/R}(\log p)\,v_R(\lfloor X/p\rfloor)
$$
costs $O(\sqrt N)$ uniformly for $X\le N$. The total error at any width $W$ is $O(\sqrt N\sum_{d\le W}|b_V(d)|)$.

**Square-root correction.** Write $w(j)=1-B_R(j)$ for the [two-moment factorial weight](pvc-log-factorial-middle-primes.md). Set $J=128R^2$, $L(u)=\sum_{j=1}^J u(j)(j^{-1/2}-(j+1)^{-1/2})$, $h_a(j)=\lfloor j/a\rfloor-2\lfloor j/(2a)\rfloor$, and $g=h_R-64h_{64R}$. Each $h_a$ takes values zero and one. Its support begins at $a$, and it equals one on $[a,2a)$. Telescoping gives $L(h_R)\le1/\sqrt R$ and $64L(h_{64R})\ge8(1-1/\sqrt2)/\sqrt R\ge2/\sqrt R$. Since $w$ vanishes on $1\le j<R$ and $|w|\ll R$, $|L(w)|\ll R/\sqrt R$. Thus $v_R=w-[L(w)/L(g)]g$ has $L(v_R)=0$, size $O(R)$, and the same lower support.

**Proper powers.** Put $P(y)=\psi(y)-\theta(y)$. The seven-eighths zero-free strip gives $|\psi(t)-t|\ll t^{9/10}$ above one. The prime-power decomposition gives $P(n)=\sqrt n+O(n^{9/20})$ for positive integers, with both sides zero at zero. In quotient cell $j$, the mass is $P(\lfloor X/j\rfloor)-P(\lfloor X/(j+1)\rfloor)$. Each endpoint differs from $\sqrt{X/j}$ by $O(1+N^{9/20})$. The corresponding model sum through $J$ is $\sqrt X L(v_R)=0$. Larger quotients come from $m\le X/(J+1)$, with total positive mass $O(\sqrt{N/J})$. The weighted error is $O(R^3N^{9/20}+R\sqrt{N/J})=O(\sqrt N)$ since $3/64+9/20<1/2$.

**All prime powers and the cutoff.** Pairing $h_a(\lfloor X/m\rfloor)$ with $\Lambda(m)$ gives $\log(\lfloor X/a\rfloor!)-2\log(\lfloor X/(2a)\rfloor!)=(X/a)\log2+O(1+\log(2a)+\log X)$ for $X\ge1$. The two main terms cancel in $g$. Thus the added correction costs $O(R(1+\log(128R)+\log N))$. The original factorial pairing already removed integer density at this precision. Discarding ordinary primes $p\le U$ costs $O(RU)=O(\sqrt N)$, and the weight vanishes beyond $X/R$. Sum the row errors against the short cofactor coefficients.

**Open.** Bound the signed ordinary-prime sum across distinct products at both widths for arbitrarily large $V$ and every exponent above one half.

**Lean.** `primeWeight_moment` cancels the square-root moment. `proper_prime_power_bound` works for every $1\le R\le N^{1/64}$. `ordinary_prime_middle_interval` gives the uniform two-width conclusion. [Correction](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/AFactorialCorrectionForTheSquareRootDensity.lean) · [Prime interval](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/OrdinaryPrimesInTheFactorialInterval.lean)
