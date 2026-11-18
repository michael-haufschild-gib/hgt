# Centered fractional parts on product rectangles

**PVC · Paper theorem.** Let $1\le H\le V$, $H^4\le P$, and $(PV)^2/H\le Z\le H(PV)^2$. On any sharp product window $L<pv\le U$ in $P\le p<2P$, $V\le v<2V$, one has
$$
\left|\sum_{p,v}\alpha_p\beta_v(\{Z/(pv)\}-1/2)\right|
\ll \|\alpha\|_\infty\|\beta\|_\infty PV H^{-1/4}.
$$

**Proof.** Split $[V,2V)$ into at most $2V/H$ intervals of length at most $H$. In the [bilinear harmonic estimate](pvc-bilinear-reciprocal-phases-on-short-factor-intervals.md), the two curvature parameters satisfy $u\ge1/(16PH)$ and $w\le H^2/(4P)$. Hence $64P\sqrt w+12/\sqrt u\le112H\sqrt P$. Since $H^2\le\sqrt P$, the Schur row sum is at most $113P\sqrt{|h|}$ for $h\ne0$. Write $A=\|\alpha\|_\infty$, $B=\|\beta\|_\infty$. The coefficient energies per interval are at most $PA^2$ and $HB^2$. The harmonic sum thus costs at most $11ABP\sqrt{H}\sqrt{|h|}$ per interval and $22ABPV\sqrt{|h|}/\sqrt H$ overall. This also applies to the separable majorant $|\alpha_p||\beta_v|$, of total mass at most $ABPV$. The [sawtooth transfer](../../../../formal/GaloisForLFunctions/PrimeExponentialSums/FractionalPartsOnIntegerReciprocalBlocks.lean) with smoothing width $H^{-1/4}$ gives the result, including integer arguments.
