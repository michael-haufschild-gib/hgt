# Tate limits of small sections on signed spline rays

For every integer spline divisor $a$, let $d$ generate its rational contact ideal and let $A$ be its logarithmic radius from the two pole degrees and the regularized archimedean pairing. Write $H(a)$ for the floor of the logarithm of the number of integers $z$ with $|dz| ≤ e^A$. The dual height $H^*(a)$ uses $d^{-1}$ and $-A$.

For $Q(a)$ given by `integerProbe N a`, the quadratic Tate limits of $H(ma)$ and $H^*(ma)$ are respectively $\max(Q(a),0)$ and $\max(-Q(a),0)$. Their difference recovers the complete signed Weil form for every $a$.

**Proof.** Rounding the contact exponents costs at most the sum of the von Mangoldt weights on the fixed support window. Along a nonzero ray the mesh resolution tends to infinity. Logarithmic quadrature for both degrees and the regularized jet and contact rows gives $(A-\log d)/m^2\to Q(a)$. The exact count is $2\lfloor e^A/d\rfloor+1$. Its logarithmic height differs from $\max(A-\log d,0)$ by a universal bounded error. Apply the same estimate to the inverse ideal.

**Lean.** `tendsto_splineDegree`, `splineCount_tateLimit`, `dualCount_tateLimit`, `splineCount_sub_dualCount_tateLimit`. [SignedSplineSmallSections.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/SignedSplineSmallSections.lean)

**Finite contact ideals.** At each degree $k>1$, the residue size is exactly the cardinality of the quotient by the Frobenius graph contact ideal. At a common mesh, adding packets multiplies their two fractional ideals and their mixed ideal by an integral carry. The carry divides the square of the product of the contact bases on the fixed window, since rounding three real exponents costs at most two. Reversing all coefficients fixes the entire finite section set. [PolarizationOfContactIdeals.lean](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/PolarizationOfContactIdeals.lean)
