# The first quotient band and the largest removable prime wall

- **Stage** 1-in-progress
- **Question** Which part of the ordinary-prime reading can smaller signed rows pay at the critical exponent, and how much would termwise absolute values cost there?

Write \(y=\lfloor\log(X+1)\rfloor^2\), \(Z=X/y\), \(\delta_y=\frac6{\pi^2}\prod_{p\le y}p/(p+1)\). On \(Z/2<m\le Z\), the first quotient floor is one. The rescaled prime reading \((\vartheta(X/m)-\vartheta(y))/y\) approaches \(u-1\) uniformly, with \(u=X/(my)\in[1,2)\). For either squarefree rough cofactor sign, the normalized measure in \(u\), divided by \(Z\delta_y\), tends to \(du/(2u^2)\). Indeed every fixed subinterval in \(m/Z\) has unsigned main term \(\delta_y\) times its length, with error \(O(E_s(y)Z^s)\) by primorial squarefree discrepancy. Its signed error has the same bound for a fixed \(s<1\) from the corpus Mertens bound and finite Euler deletion. Since \(\delta_y\gg1/(y+1)\), both errors are negligible relative to \(Z\delta_y\).

Consequently any constant center \(cy\) on that quotient band incurs at least \((\tfrac12\log(9/8)+o(1))X\delta_y\) in **each sign** after taking absolute values. The minimizing limiting center is \(c=1/3\), because the weighted median of \(u\) is \(4/3\). The original floor center \(c=1\) incurs \(\tfrac12(1-\log 2)X\delta_y\) in each sign to leading order. This obstruction already occurs within the first quotient band.

**Signed alternative.** Omit all surviving proper powers and all ordinary primes in \((y,\lambda y]\), while retaining the same cofactor cutoff. At square-root price the omitted kernel has exact leading coefficient
\[
 \frac{1}{\log X}\left(\sum_{p>y,\ k\ge2,\ p^k\le X}\frac{\log p}{p^{k/2}}
    +\sum_{y<p\le\lambda y}\frac{\log p}{\sqrt p}\right)
 \longrightarrow \frac12+2(\sqrt\lambda-1)\qquad(\lambda\ge1).
\]
The squares give \(\frac12\log X-\log y+O(1)\), the higher powers are bounded, and partial summation of the prime number theorem gives the second term. Hence \(25/16\) is the exact transition for a fixed positive fraction of unused logarithmic weight in the induction. At the endpoint the leading coefficient alone leaves the sign of the residual unresolved. A wall chosen by cumulative prime weight can reserve an exact additive margin while retaining the same limiting ratio. The signed ordinary-prime sum beyond the removable wall still requires cancellation.

**Lean status.** The density and prime-mass estimates are separate inputs. The limiting measure, optimal center and joint wall transition await formalization.
