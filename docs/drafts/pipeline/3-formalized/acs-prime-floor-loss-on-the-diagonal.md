# Prime floor loss on the diagonal

For $a=nD_n$, the original ordinary floors satisfy $\sum_p\{X_p(a)\}\log p\ge c n^2$ on the original mesh, with one $c>0$ for all sufficiently large $n$. Here $X_p$ is the original signed contact before flooring. More generally, each fixed $K\ge1$ admits a uniform saving at every positive multiplicity $m\le KR$, where $R=2n+1$.

## Proof

Write $B=(2n+1)^2$, $t=n^2/(2n+1)$. On the outer band the integrated contact is $-tF(p/B)$. Since $F$ is continuously differentiable with distinct endpoint values, a fixed interval $[u,v]$ has $F'\le-\lambda<0$. Second-order harmonic quadrature gives $X_p=-tF(p/B)+O(n^{-1})$ uniformly there. The same estimate holds for all $m$ with $R/K\le m\le KR$, $R=2n+1$, on replacing $t$ by $m^2/R$.

For fixed $e>0$ and large $n$, primes with fractional part below $e$ sharing the same floor satisfy $|p-q|\le 3eB/(t\lambda)$. The profile is bounded and there are $O(t)$ such floors. Brun–Titchmarsh bounds the prime log mass in each interval by $O(eB/t)$, since its length is proportional to $n$ and its primes have size proportional to $n^2$. Thus all those primes together cost $O(eB)$ with an absolute implied constant independent of $e$. The whole band has mass at least $(v-u)B/2$. Choosing $e$ small leaves positive mass with fractional part at least $e$.

The argument works uniformly for $d\le t\le K^2R$ with fixed $d>0$. The fiber length $H=3eB/(t\lambda)$ is at least a constant times $R$, and the number of fibers is $O_d(t)$. For smaller $t$, use the negative prime window $e^8B/3<p\le e^8B/2$. The magnitude of its actual contact is at most $16A m^2/\sqrt p\le16At$ by the mass-four bound. Choosing $d\le1/(32A)$ ensures fractional part at least one half at every such prime.

At $m=n$ the global quadrature error is $O(n)$. Thus $n^{-2}\log d_{\rm ord}(nD_n)\le P(D_n)-\delta$ for some $\delta>0$ and all sufficiently large $n$, where $P$ is the signed integrated ordinary-prime contact.

[Second-order quadrature](../3-formalized/acs-the-mesh-error-at-diagonal-multiplicity.md) · [Short-interval sieve bound](../../../../formal/GaloisForLFunctions/RHTower/Sieve/AdaptiveGallagherBrunTitchmarsh.lean)


## Lean

`prime_mass_outside_thin_floor_fibers` bounds the prime weight of the exceptional fibers. [Sieve proof](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/PrimeMassOutsideThinFloorFibers.lean)

`all_multiplicities_through_diagonal_ordinary_floor_loss` proves the uniform loss up to any fixed multiple of the conductor index. `diagonal_log_generator_below_integrated_contact` gives the strict saving on the diagonal. `all_square_sections_at_the_zero_width` gives exponential ordinary-generator decay and exponentially many original sections at every prescribed positive multiplicity up to a constant times $(n+1)^{1-w}$, where $w$ is the zeta zero width. [Square-conductor proof](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheDiagonalOrdinaryFloorLoss.lean)
