# Dilation of full Weil combs and interleaved valuation layers

For a finite set $S\subset(N,N+M]$ with $N+M\le QN$, dilate its conductors by the positive integer $d$. Put $H_M=\sum_{j=1}^M1/j$. The full Weil square on $dS$ has coefficient-mass floor
$$
\log(dN/(2\pi))-2\psi(Q)-
\bigl[H_M+M/(4N)+M^3/(2N^3)\bigr]/d .
$$
Indeed, divisibility and ratios are invariant under common dilation. Both pole terms and each off-diagonal real jet divide by $d$, while each diagonal gains $\log d$. The base-window jet row costs at most $H_M+M/(4N)$, the prime row at most $2\psi(Q)$, and the negative pole plane at most $M^3/(2N^3)$ times coefficient mass. The signed Dirichlet-square identity bounds the pairing by its rows. For fixed ratio and $d\ge2$, the floor grows at least as $(1-1/d)\log N-O_{Q,d}(1)$, uniformly over supports and coefficients.

For prime $p$, let $S$ consist of $p$-free cores and pair $da$ with $dp^h b$ for $a,b\in S$, $h\ge1$. An integral ratio from the second to the first layer is impossible before common dilation. In the other direction, $a\mid p^h b$ implies $a\mid b$. The resulting ratio $p^h(b/a)$ is a prime power precisely for $a=b$. Write $I_d$ for the full mixed form with prime contact multiplier $\eta$. With $P=\eta(p^h)\log p\sum_a u_av_a$ there is an exact identity
$$
 I_d+P=G/d,\qquad
 G=\sum_{a,b}u_av_b\bigl(1/a+1/(p^h b)-J(a,p^h b)\bigr).
$$
Here $J$ is the real jet. The layers are disjoint, and their numerical supports may interleave. Refinement by $e$ divides the remaining error by $e$. Consequently $2I_{2d}-I_d=-P$ even when the starting spacing varies at each cutoff. For square-summable sections, truncate at $N$ and round toward zero in units of $1/(N+1)$. The normalized coefficients converge pointwise, their absolute values decrease under rounding, and the same integer families at both spacings realize the completed inner product by dominated convergence, since $2|u_av_a|\le u_a^2+v_a^2$.

If both undilated layers lie in $(N,N+M]$, the absolute row and column sums of the matrix defining $G$ are at most $A=2M/N+H_M+M/(4N)$. Charging each absolute product to the two separate square masses gives $|I_d+P|\le A(\|u\|_2^2+\|v\|_2^2)/(2d)$. At $h=1$ every nonzero matched section has strictly negative ordinary mixed form and strictly positive Liouville mixed form as soon as $d\log p>A$. Both pole degrees and all real jets remain fixed under the twist.

Take all odd cores from $2k+3$ through $4k+7$ and their doubles. The endpoints alternate in the order $2k+3<4k+6<4k+7<8k+14$. Taking $N=2k+2$ and $M=6k+12$ gives one spacing threshold for every nonzero signed vector at that cutoff. On unrestricted unit-spaced windows the harmonic row loss can exhaust the diagonal logarithm, leaving the full-square positivity question open.

`dilated_comb_floor` gives the finite estimate and `eventually_full_comb_on_multiples` its ambient-window consequence. [Dilated Weil square](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/WeilMassOnDilatedCombWindows.lean)

`formBilin_prime_layers` identifies the ordinary pairing. The composition law and mixed bound are `layerPair_compose` and `layerPair_error`. The sign test is `late_odd_layers_opposite_signs`, and `integral_exhaustion_of_prime_layers` gives the completed two-spacing identity. [Interleaved prime layers](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/PrimeContactsBetweenInterleavedValuationLayers.lean)
