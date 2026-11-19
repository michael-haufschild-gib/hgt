# Completed quotient intersections and their exact power threshold

For $c_k=\sum_{\lfloor j/i\rfloor=k}u_i b_j$, the mixed finite part is $\sum_k c_k(\psi(k)-k)$. The de la Vallée Poussin estimate extends it to all endpoint sequences of finite weighted variation for $W(k)=k\exp(-c\sqrt{\log k})$ with some $c>0$. Its operator bound is independent of both supports. For $\alpha\ge0$, bounding every finite part with weights $k^{1/2+\alpha+\varepsilon}$ for each $\varepsilon>0$ is equivalent to the nontrivial zeta zeros having real parts at most $1/2+\alpha$. The converse tests one effective endpoint at a time and bounds the error from rounding a real cut.

On one effective endpoint the ordinary centered Weil row is $m-\psi(m)+1/[2m(m+1)]$. Littlewood oscillation gives both signs beyond any fixed multiple of $\sqrt m$ at arbitrarily late integer cuts. For mixed opposing divisors the remaining real-place price is $\|UV\|_\infty/[2(L+1)(L+2)]$.

Lean declarations include `completed_endpoint_de_la_vallee_poussin`, `distance_to_completed_intersection`, `mixed_height_width_iff`, `centeredWeilRow_de_la_vallee_poussin` and `effective_endpoint_oscillations`. [Proofs](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/CompletingTheMixedIntersectionInWeightedVariation.lean)
