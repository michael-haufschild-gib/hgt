# Effectivity after gluing complete blocks of conductor endpoints

**Question.** For modulus $d\ge2$, glue all lower graphs through each upper endpoint $M$, then subtract $d$ copies of the height through $\lfloor M/d\rfloor$. Let $A_d(n)$ sum the result over $M=dn,\ldots,dn+d-1$. Does the second difference $A_d(n+2)-2A_d(n+1)+A_d(n)$ have a fixed sign and size $O(d^2/(n+1)^3)$ with one constant for all $d$? Both endpoint degrees cancel in this difference.

**Mechanism.** Divisor inversion gives $\log(M!)-d\log(\lfloor M/d\rfloor!)$ at one endpoint. Across successive blocks the log factors occur in opposite pairs with displacements $z=(r+j+1-d)/d$, $0\le r,j<d$. After subtracting the linear term, each paired increment is governed by $\log(1-z^2/(n+1)^2)$. Its variation has a sign even though the individual endpoint errors oscillate with the residue. The arithmetic input is $\sum_{q\mid m}\Lambda(q)=\log m$.

**Scope.** This family has growing ordinary-prime support and independently specified signed multiplicities. Extending its sign to an arbitrary upper divisor requires control of the incomplete residue blocks.
