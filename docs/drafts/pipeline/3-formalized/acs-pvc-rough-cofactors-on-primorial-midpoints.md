# Rough cofactors on primorial midpoints

Let \(y(x)=\lfloor\log(x)/(4\log4)\rfloor\) and \(L(x)=\prod_{p\le y(x)}p\). At the first milestone, it suffices to bound the primitive large-factor price on centers \(m>1\) satisfying \(L(m)\mid m\). Every admissible cofactor there has **all** its prime factors above \(y(m)\). At the lower prime cutoff \(\lfloor2m^{5/6}\rfloor\), the only remaining cofactors satisfy
\[
 y(m)<\operatorname{minFac}(v)\le v<2m^{1/6}.
\]
The half-power gate uses the same logarithmic lower cutoff and \(v<2\sqrt m\). In both cases the center is \((10\log 2-6\log 3)\varphi(m)\). [All-center factorization](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheTotientTermInTheReflectedCompositePrice.lean#L415)

**Proof.** The elementary primorial estimate gives \(L(n)\le4^{y(n)}\le n^{1/4}\). Take \(m=L(n)\lfloor n/L(n)\rfloor\). Then \(m\le n\), \(n-m<L(n)\), and \(L(m)\mid L(n)\mid m\). For \(n>1\) this gives \(m>1\), since either \(L(n)=1\) or \(m\ge L(n)\ge2\). Monotonicity at the two outside endpoints gives
\[
 D(n)-D(m)\le2\bigl(\theta(3n)-\theta(3m)\bigr)\le6(n-m)\log(3n)\ll\sqrt n.
\]
Thus a one-sided bound at these centers transfers to **every** integer. If \(v\ge2\) and \((v,m)=1\), a prime divisor \(p\le y(m)\) of \(v\) would divide \(L(m)\) and hence \(m\). The upper cutoff follows from \(pv\le4m\) for the selected large prime. In particular, every fixed cofactor eventually disappears on the sampling set.

For \(1/2\le b<1\), write \(H_b(m)\) for the primitive signed price above \(\lfloor2m^b\rfloor\). The criterion \(\Theta\le b\) is equivalent to \(H_b(m)-c\varphi(m)\ll_t m^t\) on these centers for every \(b<t<1\). Apply the all-endpoint factorization error with \(\varepsilon=t-b\) and the midpoint shift above. Both estimates retain the signs at \(3m\). The independent upper bound for the surviving rough cofactors is open. The reciprocal-prime shell proved for the unrestricted linear center cannot by itself be subtracted from this primitive sum. [Midpoint criterion](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMidpointInTwoAdjacentGcdHorizons.lean#L319)

Lean verified `nearby_primorial_midpoint`, `primorial_midpoint_upper_sampling`, `primorial_midpoint_cofactor_range`, and `rough_cofactor_midpoint_upper_spectrum` with `propext`, `Classical.choice`, and `Quot.sound`. [Prime divisor restriction](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/RoughCofactorsAtPrimorialMidpoints.lean#L129) · [Exact threshold](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/RoughCofactorsAtPrimorialMidpoints.lean#L143)
