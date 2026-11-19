# The Liouville sign on the same graph divisors

For smooth compact profiles the ordinary prime contact and the Liouville-twisted contact add to twice the perfect-square contact. Their unscaled sum tends to $2(\int f)(\int g)$ while their leading pole terms have opposite signs. Exponential tilts of a single positive bump realize strict opposite signs eventually.

For full integral prefixes, keep the degree product $M H_M$ and replace each contact $\Lambda(q)$ by $\lambda(q)\Lambda(q)$. At $m=b^2a$ with $a$ squarefree, the square divisors of $m$ are exactly the squares of divisors of $b$. Their von Mangoldt sum is $\log b$. Subtracting the ordinary divisor sum from twice this sum gives the twisted column $-\log a$. It vanishes on squares and is bounded above by $-\log2$ elsewhere. The twisted prefix curvature at $t^2-1$ is at least $\log 2$ and at $t^2-2$ at most $-1/3$, for every $t\ge2$. The positive ordinary Weil-energy comparison therefore distinguishes the actual finite-place sign on unbounded supports.

Lean declarations include `contact_add_liouville`, `tendsto_contact_add_liouville`, `tendsto_liouville_contact`, `exists_eventually_opposite_contacts`, `twistedColumn_squarefree_part` and `opposite_twin_curvatures_at_squares`. [Proofs](../../../../formal/GaloisForLFunctions/SignedArithmeticCorrespondences/TheUnscaledIntersectionOfTheLiouvilleTwin.lean)
