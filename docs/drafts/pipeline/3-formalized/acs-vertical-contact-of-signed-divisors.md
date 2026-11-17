# Vertical contacts of signed conductor divisors

**Stage** 3-formalized. **Route** ACS arithmetic sections on signed integer spline probes.

For conductor $n$, take the integral graph $Y=G_n(T)$ with
$G_n(T)=\sum_{d\mid n}\operatorname{rad}(d)T^d$. Its degree is $n$.
For distinct conductors the content of $G_i-G_j$ is $p$ at a ratio $p^r$
in either direction and $1$ otherwise. Indeed, the first changed power of
each prime gives a coefficient of absolute value $p$. When only the
$p$-exponent changes, every changed divisor contains $p$. Gauss's lemma
therefore computes the order of the quotient of $\mathbb Z$ by all coefficients of the Sylvester determinant of two thickened divisors. Its logarithm sums the pairwise log contacts with the product of their multiplicities. This identity holds for arbitrary support and multiplicities.

On the generic fibre the affine difference has degree $\max(i,j)$. In reciprocal coordinates the elimination polynomial is
$U^i\operatorname{rev}(G_j)-U^j\operatorname{rev}(G_i)$.
For $i<j$, its lowest coefficient is the leading coefficient of $G_j$, at degree $i$. Thus the same graph pair has total horizontal multiplicity $i+j$, the numerator of the polar kernel.

On a log mesh put $w_i=\log(1+1/i)$. Give the lower graph signed weight
$\sqrt i\,w_i f_i$ and the upper graph weight $g_j/\sqrt j$.
At $j=it$ the product is $w_i f_i g_{it}/\sqrt t$. Round each weight
after dilation by $m$. At each base use one resultant for agreeing signs
and one for opposing signs. The difference of their log orders reads
the signed product. With mesh starting at $\lfloor\sqrt m\rfloor$,
rounding costs $O_{f,g,B}(m^{-1/2})$ after division by $m^2$.
Logarithmic quadrature then gives the full smooth prime pairing. On the spline lattice take $m=\sum_i|a_i|$ and sample the spline divided by $m$. Under dilation the normalized profile stays fixed and the thickness scales linearly.

**Lean.** [Integral contacts and resultant multiplicities](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Intersection/ConductorGraphContacts.lean) · [Signed restriction orders](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Intersection/SignedConductorDivisors.lean) · [Smooth prime pairing](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Intersection/ConductorGraphPrimeLimit.lean) · [Spline Tate limit](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Intersection/ConductorGraphSplineCounts.lean) · [Residue cardinality and horizontal multiplicities](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/Intersection/ConductorGraphPolePair.lean). All five files pass direct Lean checks with standard transitive axioms.

**Remaining problem.** Construct one effective object that pays the
same-sign contact debit together with the real-place diagonal and both
pole moments on every signed ray.
