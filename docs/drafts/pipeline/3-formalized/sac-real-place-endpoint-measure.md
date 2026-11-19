# Positive measure of the real-place endpoint correction

**Theorem.** The flat upper divisor through $i+k$ has a Weil row at $i$ with finite-place term $(i+k)/i-\psi(\lfloor(i+k)/i\rfloor)$ and diagonal constant $3/(4i)-\log(2\pi)$. The residual entry $D_i(k)$ satisfies

$$2D_i(k)=\int_0^1x^k(1-x)S_i(x)^2\,dx,\qquad S_i(x)=\sum_{a<i}x^a.$$

Thus every shifted Hankel matrix of this residual is positive semidefinite. For signed endpoint polynomials $P,Q$, its exact mixed form is half the integral of $x^L P(x)Q(x)(1-x)S_i(x)^2$.

**Proof.** The row formula gives $2D_i(k)=2H_{k+i}-H_k-H_{k+2i}$. Integrating $x^kS_i(x)$ gives $H_{k+i}-H_k$. Subtract the same integral at $k+i$ and use $(1-x)S_i(x)=1-x^i$. Cauchy–Schwarz on $x^{a/2}$ and $x^{(i-1-a)/2}$ gives $S_i(x)^2\ge i^2x^{i-1}$. Removing this monomial from the density subtracts $i^2(1/(k+i)-1/(k+i+1))$ from $2D_i(k)$.

**Lean.** `realEndpoint_moment`, `realEndpoint_mixed`, `realEndpoint_hankel_nonneg`, `centeredResiduePolynomial_nonneg`, `centeredRealEndpoint_moment`. [Proof](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/TheRealPlaceAfterGluingSignedEndpoints.lean)
