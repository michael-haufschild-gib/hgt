# Effectivity after gluing complete blocks of conductor endpoints

**Question.** For modulus $d\ge2$, glue all lower graphs through each upper endpoint $M$, then subtract $d$ copies of the height through $\lfloor M/d\rfloor$. Let $A_d(n)$ sum the result over $M=dn,\ldots,dn+d-1$. Does the second difference $A_d(n+2)-2A_d(n+1)+A_d(n)$ have a fixed sign and size $O(d^2/(n+1)^3)$ with one constant for all $d$? Both endpoint degrees cancel in this difference.

**Mechanism.** Divisor inversion gives $\log(M!)-d\log(\lfloor M/d\rfloor!)$ at one endpoint. Across successive blocks the log factors occur in opposite pairs with displacements $z=(r+j+1-d)/d$, $0\le r,j<d$. After subtracting the linear term, each paired increment is governed by $\log(1-z^2/(n+1)^2)$. Its variation has a sign even though the individual endpoint errors oscillate with the residue. The arithmetic input is $\sum_{q\mid m}\Lambda(q)=\log m$.

**Incomplete blocks.** Give residue $r$ multiplicity $w_r$. For $t=n+1$ let $g_t(z)=\log(1+z/(t+1))-\log(1+z/t)$. Applying $1-x^{-1}\le\log x\le x-1$ to the ratio gives

$$
\frac{z^2}{t+1+z}\le t(t+1)g_t(z)+z\le\frac{z^2}{t+z}.
$$

Thus the first signed moment is the obstruction to cubic decay. For nonnegative weights with zero first moment the second moment gives a positive intersection, even for an incomplete, asymmetric residue block. For signed weights the next error should be uniform in the absolute second moment. This identifies a larger class than the complete residue blocks.

**Mixed endpoints.** Put $K_d(n)=\Delta^2 A_d(n)$ and $S_d(x)=1+x+\cdots+x^{d-1}$. Integrating each difference of logarithms over its unit increment, then writing the reciprocal as a power integral, gives

$$
 K_d(n)=d\int_0^1\!\int_0^1 x^{dn+dy}\{S_d(x)^2-d^2x^{d-1}\}\,dx\,dy.
$$

The expression in braces equals $\sum_{0\le i<j<d}x^{d-1-(j-i)}(1-x^{j-i})^2$: the two off-diagonal products with gap $j-i$ pair by reflection. Gluing signed shifts in both variables inserts the product $P(x^d)Q(x^d)$ of their endpoint polynomials. Its supremum on the unit interval therefore prices the entire mixed curvature with constant $K_d(n)$, including limits under uniform convergence of the mixed polynomials. This would give effectivity and cubic decay on unbounded conductor supports from factorization alone. The lower family in this construction contains every graph up to the endpoint.
