# Prime floor loss on the diagonal

For $a=nD_n$, prove $\\sum_p\\{X_p(a)\\}\\log p\\ge c n^2$ on the original mesh, with one $c>0$ for all sufficiently large $n$. Here $X_p$ is the original signed contact before flooring.

Write $B=(2n+1)^2$, $t=n^2/(2n+1)$. On the outer band the integrated contact is $-tF(p/B)$. Since $F$ is continuously differentiable with distinct endpoint values, a fixed interval $[u,v]$ has $F'\\le-\\lambda<0$. Second-order harmonic quadrature would give $X_p=-tF(p/B)+O(n^{-1})$ uniformly there.

For fixed $e>0$ and large $n$, primes with fractional part below $e$ sharing the same floor satisfy $|p-q|\\le 3eB/(t\\lambda)$. The profile is bounded and there are $O(t)$ such floors. Brun–Titchmarsh bounds the prime log mass in each interval by $O(eB/t)$, since its length is proportional to $n$ and its primes have size proportional to $n^2$. Thus all those primes together cost $O(eB)$ with an absolute implied constant independent of $e$. The whole band has mass at least $(v-u)B/2$. Choosing $e$ small leaves positive mass with fractional part at least $e$.

[Second-order quadrature](../2-fully-proven/acs-the-mesh-error-at-diagonal-multiplicity.md) · [Short-interval sieve bound](../../../../formal/GaloisForLFunctions/RHTower/Sieve/AdaptiveGallagherBrunTitchmarsh.lean)
