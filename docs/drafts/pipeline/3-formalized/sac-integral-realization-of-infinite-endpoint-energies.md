# Integral realization of infinite endpoint energies

At positive separation $n$, take any two real square-summable endpoint sequences $u,v$ and set $E=\|u\|_2^2+\|v\|_2^2$. The absolute sums of the mixed entries are bounded by $d^2 E/[n(n+1)]$ for complete modulus-$d$ graph curvature and $d^2 E/(2n)$ for twice the degree-$d$ real Weil metric. Both square forms are positive semidefinite on the completion.

For the genuine pole-subtracted prefix curvature $G$, the sum of the absolute mixed entries is at most $E/(2n)$. The absolute value of their signed sum is also bounded by the two individual degree-one real Weil energies. To realize these limits with integral divisors, truncate both sequences at $N$, round toward zero after multiplying each coefficient by $N+1$, and divide the integer pairing by $(N+1)^2$.

For the absolute estimates, charge $2|u_i v_j|\le u_i^2+v_j^2$ to the two separate rows. The real kernel is bounded by a beta moment and the complete block kernel by a cubic reciprocal. The majorants telescope as $1/t-1/(t+1)$. Rounding preserves the pointwise absolute majorants, so dominated convergence gives the signed limits and passes the finite Weil energy inequality to them.

Lean declarations include `infinite_block_energy`, `infinite_real_energy`, `integral_sections_realize_both_completions`, `completed_squares_effective` and `infinite_pole_defect_from_integral_divisors`. [Proofs](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/IndependentEnergiesOfInfiniteEndpointSections.lean)
