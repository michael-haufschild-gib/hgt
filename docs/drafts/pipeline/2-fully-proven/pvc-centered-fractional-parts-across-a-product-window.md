# Centered fractional parts across a product window

**PVC · Paper theorem.** Let $1\le H$, $H^4\le a\le b$, $H\le c\le d$, $Z>0$, $U^2\le HZ$ and $16Z\le HL^2$. For coefficients bounded by $A,B$ on the two factor intervals,
$$
\left|\sum_{\substack{a\le p<b,\ c\le v<d\\L<pv\le U}}
\alpha_p\beta_v(\{Z/(pv)\}-1/2)\right|
\ll ABU(1+\log b)(1+\log d)H^{-1/4}.
$$

**Proof.** Split both intervals into truncated dyadic blocks. On any occupied block with lower corner $(P,V)$, one admissible product gives $PV\le U$ and $L<4PV$. Hence $(PV)^2\le HZ$ and $Z\le H(PV)^2$. Extend each coefficient by zero from its truncated block to the full dyadic interval. The [rectangle estimate](pvc-centered-fractional-parts-on-balanced-product-rectangles.md) bounds this block by $O(ABU/H^{1/4})$. The two dyadic block counts cost at most $4(1+\log b)(1+\log d)$.

For the centered Vaughan weight $w_R(\lfloor X/(pv)\rfloor)$, it suffices that $128(128R^2+1)U^2\le HX$ and $16X\le HL^2$. Apply the window bound at $Z=X/t$ for each stencil divisor $1\le t\le128(128R^2+1)$. Grouping pairs of equal product gives the [factorial stencil transfer](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CenteringTheFactorialPrimeWeight.lean), with multiplicative cost $1000(1+\mathrm{mass}(R))$.
