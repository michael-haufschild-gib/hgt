# The full mixed Weil form on interleaving supports

Present both integral divisors $u,v$ by their signed endpoint jumps on $[1,N]$. The full Weil form contains directed contacts in both directions. Their continuum terms give exactly the two pole-degree products, also when the supports interleave.

For each direction let $c_k$ be its glued quotient coefficient and $F$ its fractional boundary. Let $D=\sum_i u_iv_i\log(i/(2\pi))$ be the true diagonal. Define the real-place polynomial

$$G(x)=\sum_{i\ne j} u_iv_j\big(x^{|i-j|-1}+x^{i+j-1}\big).$$

The two harmonic kernels of the Weil row have these monomials as integral representatives. The full form satisfies

$$W(u,v)-F_{u,v}-F_{v,u}-D=-\sum_k (c_k^{u,v}+c_k^{v,u})(\psi(k)-k)-\tfrac12\int_0^1G(x)\,dx.$$

The continuum degree identity uses $\sum_m v_m=\sum_j j b_j$ for upper jumps $b_j$. Each directed order recovers one divisibility term of the symmetric contact. The zero quotient and the contact diagonal contribute zero. The de la Vallée Poussin weight prices the combined quotient profile and half the $L^1$ norm prices the single jet polynomial. The same distance estimate gives simultaneous completion on arbitrary interleaving supports.

Lean declarations include `interleaved_finite_part`, `interleaved_de_la_vallee_poussin` and `interleaved_distance_to_completion`. [Proofs](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/TheFullWeilFormOnInterleavingDivisors.lean)
